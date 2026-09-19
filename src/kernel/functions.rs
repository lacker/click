use super::loans::{
    CheckedLoanCallEvidence, CompositeLoanBacking, CompositeProjectionEvidence, LoanId, LoanLedger,
    LoanRefusal, LoanRefusalOperation, LoanRefusalSubject, LoanViewBinding, LoanViewBindings,
    StableViewTransferPlan, append_checked_loan_evidence, concat_checked_loan_evidence,
    empty_checked_loan_evidence_sequence, plan_stable_view_transfer_with_bindings_and_composites,
};
use super::prelude::*;
use std::sync::Arc;

fn execute_c_function_body_paths(
    state: &CState,
    function: &CFunction,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let initial = execute_c_statement_paths(
        state,
        function.body(),
        assumptions,
        environment,
        execution_semantics,
        budget,
    )?;
    if function.control_target_count() == 0 {
        return Ok(initial);
    }
    let mut pending = initial
        .into_iter()
        .map(|path| (path, 0usize))
        .collect::<Vec<_>>();
    let mut completed = Vec::new();
    while let Some((path, jump_count)) = pending.pop() {
        let CStatementOutcome::Jump {
            target,
            state: jump_state,
        } = &path.outcome
        else {
            completed.push(path);
            continue;
        };
        let Some(target) = function.control_target(*target) else {
            completed.push(invalid_goto_path(
                path,
                "goto refers to an unknown function target",
            ));
            continue;
        };
        if jump_count >= function.control_target_count() {
            completed.push(invalid_goto_path(path, "goto control flow is not forward"));
            continue;
        }
        let suffix = execute_c_statement_paths_with_prefix(
            jump_state,
            &target.remaining,
            assumptions,
            environment,
            execution_semantics,
            &path.facts,
            &path.obligations,
            &path.loan_evidence,
            budget,
        )?;
        pending.extend(
            suffix
                .into_iter()
                .map(|suffix_path| (suffix_path, jump_count + 1)),
        );
    }
    budget.check_path_width(completed.len())?;
    Ok(completed)
}

fn execute_c_function_body_verification_paths(
    state: &CState,
    function: &CFunction,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
    variables: &mut KernelVariableGenerator,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let initial = execute_c_statement_verification_paths(
        state,
        function.body(),
        assumptions,
        environment,
        execution_semantics,
        budget,
        variables,
    )?;
    if function.control_target_count() == 0 {
        return Ok(initial);
    }
    let mut pending = initial
        .into_iter()
        .map(|path| (path, 0usize))
        .collect::<Vec<_>>();
    let mut completed = Vec::new();
    while let Some((path, jump_count)) = pending.pop() {
        let CStatementOutcome::Jump {
            target,
            state: jump_state,
        } = &path.outcome
        else {
            completed.push(path);
            continue;
        };
        let Some(target) = function.control_target(*target) else {
            completed.push(invalid_goto_path(
                path,
                "goto refers to an unknown function target",
            ));
            continue;
        };
        if jump_count >= function.control_target_count() {
            completed.push(invalid_goto_path(path, "goto control flow is not forward"));
            continue;
        }
        let mut suffix = execute_c_statement_verification_paths_with_prefix(
            jump_state,
            &target.remaining,
            assumptions,
            environment,
            execution_semantics,
            &path.facts,
            &path.obligations,
            budget,
            variables,
        )?;
        for suffix_path in &mut suffix {
            suffix_path.loan_evidence =
                concat_checked_loan_evidence(&path.loan_evidence, &suffix_path.loan_evidence);
        }
        pending.extend(
            suffix
                .into_iter()
                .map(|suffix_path| (suffix_path, jump_count + 1)),
        );
    }
    budget.check_path_width(completed.len())?;
    Ok(completed)
}

fn invalid_goto_path(path: CStatementExecutionPath, message: &str) -> CStatementExecutionPath {
    CStatementExecutionPath {
        outcome: CStatementOutcome::RuntimeError(CRuntimeError::FunctionContract(
            message.to_string(),
        )),
        facts: path.facts,
        obligations: path.obligations,
        loan_evidence: path.loan_evidence,
    }
}

#[cfg(test)]
mod callback_contract_tests;

#[cfg(test)]
mod pointee_const_return_tests {
    use super::*;

    fn function(constant: bool) -> CFunction {
        CFunction::new(
            CType::UInt8Pointer,
            "text",
            Vec::new(),
            c_return(c_int32_literal(0)),
        )
        .with_return_pointee_constant(constant)
    }

    fn pointer(constant: bool) -> CValue {
        CValue::typed_pointer(Pointer::symbolic(Variable(910)), CType::UInt8Pointer)
            .with_pointer_pointee_constant(constant)
    }

    #[test]
    fn pointee_const_return_coercion_enforces_declared_qualifier() {
        for source_const in [false, true] {
            for return_const in [false, true] {
                let result = coerce_function_return_value(
                    pointer(source_const),
                    &function(return_const),
                    &mut Vec::new(),
                    &PureFactContext::new(),
                );
                assert_eq!(result.is_some(), !source_const || return_const);
                if let Some(CValue::Pointer(pointer)) = result {
                    assert_eq!(pointer.pointee_constant(), return_const);
                }
            }
        }
    }

    #[test]
    fn pointee_const_return_symbolic_result_and_binding_preserve_qualifier() {
        let function = function(true);
        let value = symbolic_function_result(&function, Variable(911));
        assert!(matches!(&value, CValue::Pointer(pointer) if pointer.pointee_constant()));
        let mut state = CState::new();
        set_function_result(&mut state, &function, value);
        assert!(
            matches!(state.locals.binding("result"), Some(CLocalBinding::Object {
            value: CValue::Pointer(pointer), pointee_constant: true, ..
        }) if pointer.pointee_constant())
        );
    }

    #[test]
    fn pointee_const_return_contract_signature_checks_qualifier() {
        let mutable = function(false);
        assert!(!mutable.return_pointee_is_constant());
        let constant = function(true);
        let contract = CFunctionContract::new("text_contract", constant.clone()).unwrap();
        assert!(contract.exactly_matches(&constant));
        assert!(contract.has_compatible_signature_and_resource_vocabulary(&constant));
        assert!(!contract.exactly_matches(&mutable));
        assert!(!contract.has_compatible_signature_and_resource_vocabulary(&mutable));
    }

    #[test]
    fn pointee_const_return_function_address_cannot_convert_to_mutable_callback() {
        let target = function(true);
        let parameter = c_parameter("callback", function(false).function_pointer_type());
        let environment = CExecutionEnvironment::new().with_function(target);
        let value = type_function_address_value(
            &CExpression::FunctionAddress("text".to_string()),
            CValue::typed_pointer(
                Pointer {
                    block: PointerBlock::Function("text".to_string()),
                    offset: PointerOffsetTerm::Constant(0),
                },
                CType::FunctionPointer(CallbackSignature::UNSPECIFIED),
            ),
            Some(&environment),
        );
        assert!(coerce_c_function_argument_without_obligations(&value, &parameter).is_none());
    }

    #[test]
    fn pointee_const_return_arguments_cannot_discard_const() {
        for constant in [false, true] {
            let parameter =
                c_parameter("text", CType::UInt8Pointer).with_pointee_constant(constant);
            assert_eq!(
                coerce_c_function_argument_without_obligations(&pointer(true), &parameter)
                    .is_some(),
                constant
            );
            let callee = CFunction::new(
                CType::Void,
                "consume",
                vec![parameter],
                c_return(c_int32_literal(0)),
            );
            assert_eq!(
                coerce_c_function_arguments(
                    &callee,
                    &[pointer(true)],
                    &[],
                    &PureFactContext::new()
                )
                .is_some(),
                constant
            );
        }
    }

    #[test]
    fn pointee_const_return_string_literal_storage_is_read_only_but_type_is_mutable() {
        let function = CFunction::new(
            CType::UInt8Pointer,
            "literal_source",
            Vec::new(),
            c_return(c_variable("literal")),
        )
        .with_string_literals(vec![CStringLiteral::new("literal", b"ok\0".to_vec())]);
        let state = initialize_c_function_globals(&CState::new(), &function);
        let paths = evaluate_c_expression_paths(
            &state,
            &c_variable("literal"),
            &PureFactContext::new(),
            &mut ExecutionBudget::default(),
        )
        .unwrap();
        let CExpressionOutcome::Value(value) = &paths[0].outcome else {
            panic!("literal must evaluate")
        };
        assert!(
            matches!(value, CValue::Pointer(pointer) if !pointer.pointee_constant()
            && state.memory.is_read_only_block(&pointer.block))
        );
        assert!(
            coerce_function_return_value(
                value.clone(),
                &function,
                &mut Vec::new(),
                &PureFactContext::new()
            )
            .is_some()
        );
    }
}
use std::collections::VecDeque;

// Resource-clause evaluation reports the exact checked resource that a
// failed expression tried to read.  The section worklist below captures that
// fact while each clause runs, allowing only clauses that depend on a newly
// supplied fact to be retried.
thread_local! {
    static RESOURCE_DEPENDENCY_CAPTURE: std::cell::RefCell<Option<Vec<CResourceFact>>> =
        const { std::cell::RefCell::new(None) };
    #[cfg(test)]
    static RESOURCE_CLAUSE_ATTEMPTS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

pub(crate) fn record_resource_dependency(resource: CResourceFact) {
    RESOURCE_DEPENDENCY_CAPTURE.with(|capture| {
        let mut captured = capture.borrow_mut();
        let Some(dependencies) = captured.as_mut() else {
            return;
        };
        if !dependencies.contains(&resource) {
            dependencies.push(resource);
        }
    });
}

fn capture_resource_dependencies<T>(operation: impl FnOnce() -> T) -> (T, Vec<CResourceFact>) {
    RESOURCE_DEPENDENCY_CAPTURE.with(|capture| {
        let previous = capture.replace(Some(Vec::new()));
        let result = operation();
        let captured = capture.replace(previous).unwrap_or_default();
        // Resource expression evaluation can call another checked contract
        // boundary.  Preserve nested missing-resource observations in the
        // enclosing clause's capture instead of dropping them when the inner
        // capture is restored.
        if let Some(active) = capture.borrow_mut().as_mut() {
            for dependency in &captured {
                if !active.contains(dependency) {
                    active.push(dependency.clone());
                }
            }
        }
        (result, captured)
    })
}

#[cfg(test)]
pub(crate) fn measure_resource_clause_attempts<T>(operation: impl FnOnce() -> T) -> (T, usize) {
    RESOURCE_CLAUSE_ATTEMPTS.with(|attempts| {
        let previous = attempts.replace(0);
        let result = operation();
        let measured = attempts.replace(previous);
        (result, measured)
    })
}

#[cfg(test)]
fn record_resource_clause_attempt() {
    RESOURCE_CLAUSE_ATTEMPTS.with(|attempts| attempts.set(attempts.get() + 1));
}
#[derive(Clone, Debug, Eq, PartialEq)]
struct CFunctionResourceTransfer {
    /// The complete checked entry transition.  The two partitions are kept
    /// explicitly so callers cannot accidentally treat a borrowed view as a
    /// consumed capability when reconstructing the caller successor.
    borrowed_inputs: Vec<CCheckedResourceFact>,
    consumed_inputs: Vec<CCheckedResourceFact>,
    /// Checked callee-side borrowed ownership paired with an equivalent
    /// caller-side spelling selected by the exclusive reservation planner.
    /// This is output-sized call-boundary provenance, not a search through
    /// the caller frame.
    canonical_borrowed_owners: Vec<(CResourceFact, CResourceFact)>,
    callee_resources: ResourceContext,
    /// Resources left in the caller after the entry requirements have been
    /// consumed; this is the caller frame for the remainder of the call.
    caller_resources_after_requirements: ResourceContext,
    /// Filled by the verified-application preparer once entry guards and
    /// dependent addresses have been checked.  It is the sole memory-effect
    /// projection used by modular call havoc and its effect fact.
    memory_effects: Vec<CMemoryRange>,
    post_outputs: Option<ResourceContext>,
    /// Every evaluated ensured view, kept beside the composed return
    /// resources so the provenance routes see each one exactly once even
    /// when composition merges or normalizes it away.
    candidate_output_views: Vec<CResourceFact>,
    /// Each viewed piece in the one-level frontier of an ensured owned
    /// composite, with that composite's head: the borrows a produced
    /// composite packages, which the caller side binds to exactly one loan of
    /// this call (step 7).
    produced_borrowing_pieces: Vec<(CResourceFact, CResourceFact)>,
    /// Stable-view transition, when this call was prepared through the
    /// planner. The plan owns the checked successor ledger and is consumed
    /// only after postconditions have been evaluated.
    stable_view_plan: Option<StableViewTransferPlan>,
    /// The bytes of this call's checked view frontier that a planned stable
    /// view does not name directly: a composite view's checked one-level
    /// pieces, and the intrinsic and empty-composite views, which never reach
    /// the planner at all. The declared mutable effects are compared against
    /// these as well, because an effect may not widen the authority the call
    /// actually received (D9). Each piece carries the owned occurrence behind
    /// it, for the same partition read the planned views get: a composite
    /// view's pieces carry that composite's support, while an intrinsic or
    /// empty-composite view has no owner in the caller's context and carries
    /// none, so its bytes are always compared arithmetically.
    checked_view_frontier: Vec<(CMemoryRange, Option<ResourceOccurrenceId>)>,
}

fn callee_state_with_resource_transfer(
    callee_state: CState,
    transfer: &CFunctionResourceTransfer,
) -> CState {
    let callee_state = callee_state.with_resource_context(transfer.callee_resources.clone());
    let Some(plan) = &transfer.stable_view_plan else {
        return callee_state;
    };
    callee_state
        .with_loan_ledger(Some(plan.ledger.clone()))
        .with_loan_participant(Some(plan.callee_participant()))
        .with_loan_view_bindings(plan.callee_view_bindings().clone())
}

/// Re-spell symbolic pointer values that a field-derived borrowed owner was
/// checked against with the exact caller pointer selected by the reservation
/// planner. This is used only to instantiate verified postconditions: the
/// contract footprint and resource transition keep their original checked
/// facts. Restricting the substitution to a zero-based symbolic memory range
/// makes the replacement a direct pointer identity, with no interval
/// arithmetic or authority widening.
fn with_canonical_borrowed_pointer_memory(
    state: &CState,
    canonical_borrowed_owners: &[(CResourceFact, CResourceFact)],
) -> CState {
    let mut replacements = BTreeMap::<Variable, Option<Pointer>>::new();
    for (checked, canonical) in canonical_borrowed_owners {
        let (CResource::Memory(checked), CResource::Memory(canonical)) =
            (checked.resource(), canonical.resource())
        else {
            continue;
        };
        let PointerBlock::Symbolic(variable) = checked.base().block else {
            continue;
        };
        if checked.base().offset != PointerOffsetTerm::Constant(0)
            || checked.start().as_const() != Some(0)
        {
            continue;
        }
        let (canonical_start, _) = canonical.byte_footprint();
        replacements
            .entry(variable)
            .and_modify(|known| {
                if known.as_ref() != Some(&canonical_start) {
                    *known = None;
                }
            })
            .or_insert(Some(canonical_start));
    }
    let memory =
        replacements
            .into_iter()
            .fold(
                state.memory().clone(),
                |memory, (variable, replacement)| match replacement {
                    Some(replacement) => super::reasoning::substitute_pointer_variable_in_memory(
                        &memory,
                        variable,
                        &replacement,
                    ),
                    None => memory,
                },
            );
    state.clone().with_memory(memory)
}

/// `output_assumptions` carries the call's certified output facts (the
/// callee's ensures) on top of `assumptions`, for matching a produced
/// composite's viewed pieces, which are evaluated at the post-state, against
/// the descriptions lent at entry. It is not used to decide obligations.
fn recover_candidate_stable_view_resources(
    caller_state: &CState,
    callee_state: &CState,
    transfer: &CFunctionResourceTransfer,
    return_resources: ResourceContext,
    assumptions: &PureFactContext,
    output_assumptions: &PureFactContext,
    obligations: &[ProofObligation],
) -> Result<
    (
        ResourceContext,
        Option<LoanLedger>,
        Option<super::loans::LoanParticipantId>,
        LoanViewBindings,
        Option<Arc<CheckedLoanCallEvidence>>,
    ),
    CRuntimeError,
> {
    let Some(plan) = &transfer.stable_view_plan else {
        if let Some((head, piece)) = transfer.produced_borrowing_pieces.first() {
            return Err(CRuntimeError::FunctionContract(format!(
                "produced borrowing composite {head:?} packages a view {piece:?} that no viewed input of this call backs"
            )));
        }
        return Ok((
            return_resources,
            caller_state.loan_ledger().cloned(),
            caller_state.loan_participant(),
            caller_state.loan_view_bindings().clone(),
            None,
        ));
    };
    let Some(actual_ledger) = callee_state.loan_ledger() else {
        return Err(CRuntimeError::LoanRefusal(
            LoanRefusal::MissingBacking.diagnostic(LoanRefusalOperation::Recovery),
        ));
    };
    if actual_ledger != &plan.ledger {
        return Err(CRuntimeError::LoanRefusal(
            LoanRefusal::StalePredecessor.diagnostic(LoanRefusalOperation::Recovery),
        ));
    }
    if callee_state.loan_participant() != Some(plan.callee_participant()) {
        return Err(CRuntimeError::LoanRefusal(
            LoanRefusal::WrongHolder.diagnostic(LoanRefusalOperation::Recovery),
        ));
    }
    // A call with nothing lent still has step 7 work when it consumed a
    // borrowing composite (its hold is released) or produced one (its
    // borrow must be backed, which no loan of this call can do).
    if !plan.has_stable_views()
        && plan.transferred_holds.is_empty()
        && transfer.produced_borrowing_pieces.is_empty()
    {
        return Ok((
            return_resources,
            caller_state.loan_ledger().cloned(),
            caller_state.loan_participant(),
            caller_state.loan_view_bindings().clone(),
            None,
        ));
    }
    // Do not use the path assumptions to decide this: they intentionally
    // include the obligation list for later proof discharge, which would
    // make an unresolved return condition appear already proved. Candidate
    // recovery is therefore fail-closed until the return path has no pending
    // obligations at all.
    if !obligations.is_empty() {
        return Err(CRuntimeError::FunctionContract(
            "stable-view call has an undischarged return obligation".to_string(),
        ));
    }
    // Escaping borrows (step 7). Every viewed piece a produced or returned
    // owned composite packages must be backed by exactly one loan of this
    // call: a view lent here (the composite keeps that loan open and holds
    // it), or the hold binding the composite itself brought in (the callee
    // returned it, so it keeps its borrow). None, or more than one, is
    // refused: a composite describing memory no loan stabilizes would let
    // the caller write or free what the composite still reads, and an
    // ambiguous backing cannot be elided.
    let mut escaping = std::collections::BTreeMap::<LoanId, Vec<CResourceFact>>::new();
    let mut rebound_heads = Vec::<(CResourceFact, LoanViewBinding)>::new();
    // A loan backs a piece when one of its permitted descriptions denotes
    // the piece's resource under the certified output facts: the piece was
    // evaluated at the post-state, where the composite's fields are fresh
    // loads the ensures relate to the lent arguments.
    let loan_backs_piece = |loan: LoanId, piece: &CResourceFact| {
        plan.ledger
            .permitted_descriptions(loan)
            .iter()
            .any(|permitted| {
                permitted.is_view()
                    && super::memory_provenance::c_resources_directly_match(
                        permitted.resource(),
                        piece.resource(),
                        output_assumptions,
                    )
            })
    };
    for (head, piece) in &transfer.produced_borrowing_pieces {
        let mut backing_loans = std::collections::BTreeSet::new();
        let mut entering = None;
        for stable_view in plan.stable_views() {
            if loan_backs_piece(stable_view.loan, piece) {
                backing_loans.insert(stable_view.loan);
            }
        }
        for (_, binding) in &plan.transferred_holds {
            if loan_backs_piece(binding.loan, piece) {
                backing_loans.insert(binding.loan);
                entering = Some(binding.clone());
            }
        }
        match (backing_loans.len(), entering) {
            (0, _) => {
                return Err(CRuntimeError::FunctionContract(format!(
                    "produced borrowing composite {head:?} packages a view {piece:?} that no viewed input of this call backs"
                )));
            }
            (1, Some(binding)) => {
                if !rebound_heads.iter().any(|(bound, _)| bound == head) {
                    rebound_heads.push((head.clone(), binding));
                }
            }
            (1, None) => {
                let loan = backing_loans
                    .into_iter()
                    .next()
                    .expect("one backing loan was counted");
                let heads = escaping.entry(loan).or_default();
                if !heads.contains(head) {
                    heads.push(head.clone());
                }
            }
            _ => {
                return Err(CRuntimeError::FunctionContract(format!(
                    "produced borrowing composite {head:?} packages a view {piece:?} that more than one viewed input of this call could back; the borrow cannot be elided"
                )));
            }
        }
    }
    let consumed_holds = plan
        .transferred_holds
        .iter()
        .filter(|(fact, _)| !return_resources.contains_exact_representation(fact))
        .map(|(_, binding)| binding.clone())
        .collect::<Vec<_>>();
    let recovery = plan
        .clone()
        .recover_stable_views(assumptions, &escaping, &consumed_holds)
        .map_err(|error| {
            error
                .loan_diagnostic(LoanRefusalOperation::Recovery)
                .map(CRuntimeError::LoanRefusal)
                .unwrap_or_else(|| {
                    CRuntimeError::FunctionContract("stable-view call recovery refused".to_string())
                })
        })?;
    let loan_evidence = Arc::new(CheckedLoanCallEvidence::new(
        plan.clone(),
        recovery.ledger.clone(),
        recovery.terminal_ledger.clone(),
        recovery.released_holds.clone(),
        recovery.transitions.clone(),
    ));
    // Recheck the kernel-issued discharge evidence from the exact callee root
    // before installing the canonical predecessor root in the caller state.
    recovery
        .recheck_transitions(actual_ledger, plan.caller_participant())
        .map_err(|error| {
            CRuntimeError::LoanRefusal(error.diagnostic_with_subject(
                LoanRefusalOperation::Recovery,
                recovery.diagnostic_subject(),
            ))
        })?;
    let recovered_ledger = recovery.ledger;
    let mut residual = return_resources;
    // A return view can only survive the call scope when it is one of the
    // checked child views that entered the call, when the caller already held
    // a checked outer view that entails it, or when the return published it as
    // a supported projection of an exact owned occurrence the caller still
    // holds.  In particular, an owned input must not let a callee mint an
    // unrelated view whose binding would otherwise be composed into the
    // recovered caller frame after the child scope closes, and a view is never
    // accepted merely because some equal owner happens to satisfy it.
    let mut checked_return_views = std::collections::BTreeSet::new();
    for fact in residual
        .facts()
        .iter()
        .chain(transfer.candidate_output_views.iter())
    {
        if !fact.is_view() || !checked_return_views.insert((*fact).clone()) {
            continue;
        }
        let returned_input = plan
            .stable_views()
            .iter()
            .any(|stable_view| stable_view.requirement.fact == *fact);
        let preserved_outer = caller_state
            .loan_ledger()
            .zip(caller_state.loan_participant())
            .is_some_and(|(ledger, participant)| {
                caller_state
                    .resources()
                    .view_occurrences_for_fact(fact, assumptions)
                    .into_iter()
                    .filter_map(|occurrence| caller_state.loan_view_bindings().get(&occurrence))
                    .any(|binding| {
                        ledger
                            .validate_view_binding(binding.clone(), participant)
                            .is_ok()
                            && ResourceContext::new()
                                .unchecked_with_fact(binding.viewed.clone())
                                .satisfies_fact(fact, assumptions)
                    })
            });
        // A duplicable core published from an exact returned owned occurrence
        // is an observation of that ownership, not a second live capability:
        // the reverse index drops it when the occurrence is consumed or its
        // memory support is invalidated.  Requiring the recorded occurrence
        // keeps this distinct from fact equality against an ambient owner.
        let projected_from_owner =
            residual
                .exact_projection_support(fact)
                .is_some_and(|(support_occurrence, support)| {
                    residual.support_occurrence_is_live(support_occurrence, support)
                });
        // A view of read-only storage is intrinsic read authority rather
        // than a capability this call lent, minted, or must recover: no
        // path may write those bytes, so nothing has to stabilize them,
        // and the caller held the same authority before the call. Entry
        // already decides it with this exact block test, in
        // `install_borrowed_contract_inputs` (such a contract input view
        // gets no borrowed root) and in `intrinsic_read_views` (such a
        // requirement is supplied without a ledger transition; see the
        // implicit-local-authority rule in docs/internals/stable-views.md).
        // The return route has to admit it on the
        // same terms, or a call that merely carries one across its
        // boundary would be refused for having no binding that was never
        // created. Ordinary mutable storage, file-static globals included,
        // is not read-only and still needs one of the three routes above.
        let intrinsic_read_only = matches!(
            fact.resource(),
            CResource::Memory(range)
                if caller_state.memory().is_read_only_block(&range.base().block)
        );
        if !returned_input && !preserved_outer && !projected_from_owner && !intrinsic_read_only {
            return Err(CRuntimeError::FunctionContract(format!(
                "stable-view call returned a view without a checked input child or preserved outer binding: {fact:?}"
            )));
        }
    }
    for stable_view in plan.stable_views() {
        if residual.contains_exact_representation(&stable_view.requirement.fact) {
            residual = residual
                .without_fact(&stable_view.requirement.fact, assumptions)
                .ok_or_else(|| {
                    CRuntimeError::FunctionContract(
                        "stable-view return retained an unrecoverable view".to_string(),
                    )
                })?;
        }
    }
    // The return residual carries the callee's outputs with their support
    // bookkeeping: a core the return published as a projection of a produced
    // owner is recorded against that owner's occurrence, so consuming the
    // owner later drops it. Compose the recovered escrows into that residual
    // rather than rebuilding the residual fact by fact, which would keep the
    // facts and lose what supports them.
    let mut recovered_resources = residual;
    let mut recovered_bindings = recovery.view_bindings;
    for (escrow, hold_binding) in recovery.recovered_escrows {
        if recovered_resources.satisfies_fact(&escrow, assumptions) {
            continue;
        }
        let (next, occurrence) = recovered_resources
            .try_compose_with_fact_with_occurrence(escrow, assumptions)
            .map_err(resource_context_runtime_error)?;
        recovered_resources = next;
        // An escrowed borrowing composite keeps its hold binding across the
        // call: the hold stayed in the ledger while the head was lent, and
        // the recovered head is the occurrence that carries it again.
        if let (Some(binding), Some(occurrence)) = (hold_binding, occurrence) {
            recovered_resources =
                recovered_resources.with_loan_dependency(occurrence, binding.clone());
            recovered_bindings = recovered_bindings.with_inserted(occurrence, binding);
        }
    }
    // The produced and returned borrowing composites carry their holds.
    for (head, binding) in recovery
        .escaped_holds
        .into_iter()
        .map(|escaped| (escaped.head, escaped.binding))
        .chain(rebound_heads)
    {
        let Some(occurrence) = recovered_resources
            .owned_occurrences_for_fact(&head)
            .into_iter()
            .find(|occurrence| recovered_resources.loan_dependency(*occurrence).is_none())
        else {
            return Err(CRuntimeError::FunctionContract(format!(
                "produced borrowing composite {head:?} has no occurrence to carry its borrow"
            )));
        };
        recovered_resources = recovered_resources.with_loan_dependency(occurrence, binding.clone());
        recovered_bindings = recovered_bindings.with_inserted(occurrence, binding);
    }
    Ok((
        recovered_resources,
        Some(recovered_ledger),
        Some(plan.caller_participant()),
        recovered_bindings,
        Some(loan_evidence),
    ))
}

/// One normalized resource clause after its address/argument loads have been
/// checked.  The fact alone is deliberately not enough for a transition:
/// an owned fact can be borrowed at the contract boundary, and an instance
/// can retain entry identity while its fields are checked at post state.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CCheckedResourceFact {
    pub(crate) fact: CResourceFact,
    pub(crate) role: CResourceTransferRole,
    pub(crate) snapshot: CResourceSnapshot,
    pub(crate) clause_position: Option<(usize, usize)>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CFunctionMemoryEffectProjection {
    ranges: Vec<CMemoryRange>,
    evidence_facts: Vec<ExecutionPureFact>,
    /// The owned requirement each projected range came out of, for the ranges
    /// a checked resource transition produced. An explicit effect segment
    /// names no requirement and appears here not at all; the call site reads
    /// this only to recover an effect's caller-side provenance and never to
    /// widen or narrow the ranges themselves.
    range_sources: Vec<(CMemoryRange, CResourceFact)>,
}

impl CFunctionMemoryEffectProjection {
    pub(crate) fn ranges(&self) -> &[CMemoryRange] {
        &self.ranges
    }
}

/// Candidate calls must account for explicit mutable effects separately from
/// the resource transition.  A mutable range is safe beside a lent view only
/// when the kernel has concrete interval evidence or an existing separation
/// fact; an unknown alias is rejected conservatively.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CandidateMemoryRangeRelation {
    Disjoint,
    Overlap,
    SeparationUnproved,
}

/// Whether the kernel's arithmetic proves two ranges separate under the
/// current path assumptions.  This is the separation counterpart of
/// `memory_ranges_proven_overlapping` and follows it exactly: equal element
/// widths, one base frame reached by a syntactic base delta, and the same
/// decision procedure asked for the ordering `end <= start`.  The frame
/// change is directional, so both orders are tried.  An undecided ordering
/// stays undecided, so an unknown alias is still reported as unproved
/// separation rather than as disjointness.
fn candidate_memory_ranges_proven_separate(
    left: &CMemoryRange,
    right: &CMemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    if left.element_width() != right.element_width() {
        return false;
    }
    let separate_in_frame = |anchor: &CMemoryRange, other: &CMemoryRange| {
        crate::instrumentation::record_deterministic_work(1);
        let Some(base_delta) = other
            .base()
            .element_index_from_base_with_width(anchor.base(), anchor.element_width())
        else {
            return false;
        };
        let other_start = Bitvector32Term::add(base_delta.clone(), other.start().clone());
        let other_end = Bitvector32Term::add(base_delta, other.end().clone());
        assumptions.decide(&ConditionTerm::signed_less_equal(
            anchor.end().clone(),
            other_start,
        )) == Some(true)
            || assumptions.decide(&ConditionTerm::signed_less_equal(
                other_end,
                anchor.start().clone(),
            )) == Some(true)
    };
    separate_in_frame(left, right) || separate_in_frame(right, left)
}

/// Index the projected effect ranges by the owned occurrence each was
/// reserved out of: the projection says which requirement produced a range,
/// and the plan says which caller occurrence supplied that requirement.
/// Two sources claiming one range, or one requirement reserved from two
/// occurrences, would not be a partition; such a key records no provenance
/// rather than picking a support, which leaves that effect on the arithmetic
/// comparison.
fn reserved_effect_support_index(
    range_sources: &[(CMemoryRange, CResourceFact)],
    reserved_ownership_supports: &[(CResourceFact, ResourceOccurrenceId)],
) -> BTreeMap<CMemoryRange, Option<ResourceOccurrenceId>> {
    let mut by_requirement = BTreeMap::<&CResourceFact, Option<ResourceOccurrenceId>>::new();
    for (fact, support) in reserved_ownership_supports {
        by_requirement
            .entry(fact)
            .and_modify(|known| {
                if *known != Some(*support) {
                    *known = None;
                }
            })
            .or_insert(Some(*support));
    }
    let mut index = BTreeMap::<CMemoryRange, Option<ResourceOccurrenceId>>::new();
    for (range, source) in range_sources {
        let support = by_requirement.get(source).copied().flatten();
        index
            .entry(canonical_memory_range(range.clone()))
            .and_modify(|known| {
                if *known != support {
                    *known = None;
                }
            })
            .or_insert(support);
    }
    index
}

/// The partition read at a call: a mutable effect reserved out of one owned
/// occurrence and a view lent from a different owned occurrence are bytewise
/// disjoint by the resource context's partition invariant (step 4), so the
/// relation is settled by provenance and the arithmetic oracle is not
/// consulted. This never decides a pair the other way: an effect with no
/// reservation behind it (an explicit `mutable` segment, or a range a
/// composite expansion produced) and a view with no owner behind it (an
/// intrinsic or empty-composite view) carry no provenance, and an effect and
/// a view from the same occurrence -- a partial borrow of one owner, D8 --
/// still need the arithmetic proof.
fn effect_is_disjoint_from_view_by_provenance(
    reserved_effect_supports: &BTreeMap<CMemoryRange, Option<ResourceOccurrenceId>>,
    effect: &CMemoryRange,
    viewed_support: Option<ResourceOccurrenceId>,
) -> bool {
    let Some(viewed_support) = viewed_support else {
        return false;
    };
    let Some(Some(effect_support)) =
        reserved_effect_supports.get(&canonical_memory_range(effect.clone()))
    else {
        return false;
    };
    *effect_support != viewed_support
}

fn candidate_memory_ranges_relation(
    left: &CMemoryRange,
    right: &CMemoryRange,
    assumptions: &PureFactContext,
) -> CandidateMemoryRangeRelation {
    let relation = candidate_memory_ranges_relation_by_bounds(left, right, assumptions);
    // Only an undecided pair reaches the arithmetic oracle, so a proven
    // overlap can never be reinterpreted as separation and the concrete
    // comparison keeps deciding the common case without a query.
    if relation == CandidateMemoryRangeRelation::SeparationUnproved
        && candidate_memory_ranges_proven_separate(left, right, assumptions)
    {
        return CandidateMemoryRangeRelation::Disjoint;
    }
    relation
}

fn candidate_memory_ranges_relation_by_bounds(
    left: &CMemoryRange,
    right: &CMemoryRange,
    assumptions: &PureFactContext,
) -> CandidateMemoryRangeRelation {
    if left.base().blocks_proven_distinct(right.base())
        || assumptions
            .memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(left, right)
    {
        return CandidateMemoryRangeRelation::Disjoint;
    }
    if left.base() == right.base() {
        let (Some(left_start), Some(left_end), Some(right_start), Some(right_end)) = (
            left.start().as_const(),
            left.end().as_const(),
            right.start().as_const(),
            right.end().as_const(),
        ) else {
            return CandidateMemoryRangeRelation::SeparationUnproved;
        };
        let left_width = i64::from(left.element_width());
        let right_width = i64::from(right.element_width());
        let (Some(left_start), Some(left_end), Some(right_start), Some(right_end)) = (
            i64::from(left_start).checked_mul(left_width),
            i64::from(left_end).checked_mul(left_width),
            i64::from(right_start).checked_mul(right_width),
            i64::from(right_end).checked_mul(right_width),
        ) else {
            return CandidateMemoryRangeRelation::SeparationUnproved;
        };
        return if left_end <= right_start || right_end <= left_start {
            CandidateMemoryRangeRelation::Disjoint
        } else {
            CandidateMemoryRangeRelation::Overlap
        };
    }
    let (left_base, left_bytes) = left.byte_footprint();
    let (right_base, right_bytes) = right.byte_footprint();
    let Some(left_start) = left_base.offset.as_const() else {
        return CandidateMemoryRangeRelation::SeparationUnproved;
    };
    let Some(right_start) = right_base.offset.as_const() else {
        return CandidateMemoryRangeRelation::SeparationUnproved;
    };
    let Some(left_length) = left_bytes.as_const() else {
        return CandidateMemoryRangeRelation::SeparationUnproved;
    };
    let Some(right_length) = right_bytes.as_const() else {
        return CandidateMemoryRangeRelation::SeparationUnproved;
    };
    let Some(left_end) = left_start.checked_add(i64::from(left_length)) else {
        return CandidateMemoryRangeRelation::SeparationUnproved;
    };
    let Some(right_end) = right_start.checked_add(i64::from(right_length)) else {
        return CandidateMemoryRangeRelation::SeparationUnproved;
    };
    if left_base.block != right_base.block {
        CandidateMemoryRangeRelation::SeparationUnproved
    } else if left_end <= right_start || right_end <= left_start {
        CandidateMemoryRangeRelation::Disjoint
    } else {
        CandidateMemoryRangeRelation::Overlap
    }
}

#[derive(Clone, Debug)]
enum VerifiedAllocationDeltaError {
    Runtime(CRuntimeError),
    InconsistentReturnedAllocation,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum AllocationContinuity {
    Same,
    Distinct,
    Undecided(ConditionTerm),
    Inconsistent,
}

fn canonical_memory_range(range: CMemoryRange) -> CMemoryRange {
    let base = Pointer {
        block: range.base().block.clone(),
        offset: crate::kernel::eval::canonical_offset_term(&range.base().offset),
    };
    range.with_bounds(
        base,
        crate::kernel::eval::canonical_term(range.start()),
        crate::kernel::eval::canonical_term(range.end()),
    )
}

fn function_needs_outcome_resource_transfer(function: &CFunction) -> bool {
    !function.resource_constructors().is_empty()
        || function
            .composite_resource_definitions()
            .iter()
            .any(CCompositeResourceDefinition::needs_outcome_resource_transfer)
}

fn function_changes_declared_resource_quantities(function: &CFunction) -> bool {
    function.resource_requires() != function.resource_ensures()
}

/// Applies one explicitly authorized abstract-token construction to a return
/// state. Construction is a zero-source resource event: unlike a transfer,
/// it does not consume a caller resource or rely on a body representation.
pub(super) fn construct_c_function_resource(
    state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    result: &CValue,
    constructed: &CResourceFact,
    assumptions: &PureFactContext,
) -> ExecutionResult<Result<CState, CRuntimeError>> {
    let Some(mut evaluation_state) = c_function_entry_state(state, function, arguments) else {
        return Ok(Err(CRuntimeError::FunctionContract(
            "could not bind function arguments for resource construction".to_string(),
        )));
    };
    if function.return_type() != CType::Void {
        set_function_result(&mut evaluation_state, function, result.clone());
    }
    let mut budget = ExecutionBudget::beside_live_state();
    let mut authorized = false;
    for specification in function.resource_constructors() {
        let candidate = match evaluate_function_resource_spec(
            &evaluation_state,
            specification,
            assumptions,
            &mut budget,
        )? {
            Ok(candidate) => candidate,
            Err(error) => return Ok(Err(error)),
        };
        if candidate == *constructed {
            authorized = true;
            break;
        }
    }
    if !authorized {
        return Ok(Err(CRuntimeError::FunctionContract(
            "resource construction is not authorized by the function contract".to_string(),
        )));
    }
    let CResourceFact::Own(CResource::Token { .. }, quantity) = constructed else {
        return Ok(Err(CRuntimeError::FunctionContract(
            "resource construction requires one owned abstract token".to_string(),
        )));
    };
    if quantity.as_const() != Some(1) {
        return Ok(Err(CRuntimeError::FunctionContract(
            "resource construction creates exactly one token".to_string(),
        )));
    }
    if state.resources().contains_exact_representation(constructed) {
        return Ok(Err(CRuntimeError::FunctionContract(
            "resource construction would duplicate an existing token".to_string(),
        )));
    }
    let resources = match state
        .resources()
        .clone()
        .try_compose_with_fact(constructed.clone(), assumptions)
    {
        Ok(resources) => resources,
        Err(error) => return Ok(Err(resource_context_runtime_error(error))),
    };
    Ok(Ok(state.clone().with_resource_context(resources)))
}

fn complete_void_fallthrough(
    function: &CFunction,
    outcome: CStatementOutcome,
) -> CStatementOutcome {
    match (function.return_type(), outcome) {
        (CType::Void, CStatementOutcome::Normal(state)) => CStatementOutcome::Return {
            value: CValue::Void,
            state,
        },
        (_, outcome) => outcome,
    }
}

pub(super) fn execute_c_function_paths(
    state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CFunctionPath>> {
    execute_c_function_paths_with_contract_resources(
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

/// Executes a called function's body across its paths.
///
/// `prepare_contract_resources` says whether the body runs from the contract's
/// own entry resources. A whole-function judgment over a bare caller frame
/// executes the body in that frame; the contract routes cross the resource
/// boundary, so the views the contract declares become loans of this
/// application and recovery returns them.
#[allow(clippy::too_many_arguments)]
pub(super) fn execute_c_function_paths_with_contract_resources(
    state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
    prepare_contract_resources: bool,
) -> ExecutionResult<Vec<CFunctionPath>> {
    budget.consume_function_call()?;
    if arguments.len() != function.parameters().len() {
        return Ok(vec![CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::WrongArity {
                expected: function.parameters().len(),
                actual: arguments.len(),
            }),
            facts: Vec::new(),
            obligations: Vec::new(),

            loan_evidence: empty_checked_loan_evidence_sequence(),
        }]);
    }

    let mut paths = Vec::new();
    for arguments_path in
        evaluate_c_arguments_paths(state, arguments, assumptions, budget, Some(environment))?
    {
        if let Some(outcome) = arguments_path.outcome {
            paths.push(CFunctionPath {
                outcome,
                facts: arguments_path.facts,
                obligations: arguments_path.obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            });
            continue;
        }

        let path_assumptions = assumptions_with_path_context(
            assumptions,
            &arguments_path.facts,
            &arguments_path.obligations,
        );
        let Some((argument_values, argument_obligations)) = coerce_c_function_arguments(
            function,
            &arguments_path.values,
            &arguments_path.obligations,
            &path_assumptions,
        ) else {
            paths.push(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                    argument_binding_error(function, &arguments_path.values).to_string(),
                )),
                facts: arguments_path.facts,
                obligations: arguments_path.obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            });
            continue;
        };
        let Some(callee_state) = bind_c_function_arguments(state, function, &argument_values)
        else {
            paths.push(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                    argument_binding_error(function, &argument_values).to_string(),
                )),
                facts: arguments_path.facts,
                obligations: argument_obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            });
            continue;
        };

        let body_assumptions = assumptions_with_path_context(
            assumptions,
            &arguments_path.facts,
            &argument_obligations,
        );
        let (callee_state, resource_transfer) = if prepare_contract_resources {
            // The contract boundary of a whole-function judgment: the body
            // runs from the resources the contract declares, consumed
            // definitionally. Lending is the call site's job (the planner in
            // `execute_c_function_call_paths`) and the proof's entry
            // construction (`c_state_with_borrowed_contract_inputs`); a
            // judgment over a body that already happened must not lend again.
            let resource_transfer = match prepare_function_resource_transfer(
                state,
                &callee_state,
                function,
                &body_assumptions,
                budget,
                true,
                ResourceTransitionPurpose::FunctionBoundary,
            )? {
                Ok(resource_transfer) => resource_transfer,
                Err(error) => {
                    paths.push(CFunctionPath {
                        outcome: CFunctionOutcome::RuntimeError(error),
                        facts: arguments_path.facts,
                        obligations: argument_obligations,

                        loan_evidence: empty_checked_loan_evidence_sequence(),
                    });
                    continue;
                }
            };
            (
                callee_state_with_resource_transfer(callee_state, &resource_transfer),
                Some(resource_transfer),
            )
        } else {
            (callee_state, None)
        };
        for body_path in execute_c_function_body_paths(
            &callee_state,
            function,
            &body_assumptions,
            environment,
            execution_semantics,
            budget,
        )? {
            let Some((mut facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &arguments_path.facts,
                &argument_obligations,
                &body_path.facts,
                &body_path.obligations,
                assumptions,
            ) else {
                continue;
            };
            if let Some(parameter) = modified_by_value_aggregate_parameter_with_current_ensure(
                &callee_state,
                &body_path.outcome,
                function,
            ) {
                paths.push(CFunctionPath {
                    outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                        format!(
                            "by-value aggregate parameter `{parameter}` is modified, but a postcondition reads its current state"
                        ),
                    )),
                    facts,
                    obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),});
                continue;
            }
            let return_assumptions =
                assumptions_with_path_context(assumptions, &facts, &obligations);
            let (outcome, obligations, loan_evidence) = if let Some(resource_transfer) =
                &resource_transfer
            {
                if resource_transfer.stable_view_plan.is_some()
                    || function_needs_outcome_resource_transfer(function)
                {
                    function_outcome_from_body_with_resource_transfer(
                        state,
                        function,
                        complete_void_fallthrough(function, body_path.outcome),
                        obligations,
                        &return_assumptions,
                        resource_transfer,
                        &argument_values,
                        true,
                        budget,
                    )?
                } else if function_changes_declared_resource_quantities(function) {
                    without_loan_evidence(function_outcome_from_body_with_population_transition(
                        state,
                        function,
                        complete_void_fallthrough(function, body_path.outcome),
                        obligations,
                        &return_assumptions,
                        &argument_values,
                        budget,
                    )?)
                } else {
                    without_loan_evidence(function_outcome_from_body(
                        state,
                        function,
                        complete_void_fallthrough(function, body_path.outcome),
                        obligations,
                        &return_assumptions,
                        None,
                    ))
                }
            } else {
                without_loan_evidence(function_outcome_from_body(
                    state,
                    function,
                    complete_void_fallthrough(function, body_path.outcome),
                    obligations,
                    &return_assumptions,
                    None,
                ))
            };

            append_string_literal_loadable_facts(function, &outcome, &mut facts);

            paths.push(CFunctionPath {
                outcome,
                facts,
                obligations,
                loan_evidence: append_checked_loan_evidence(
                    &body_path.loan_evidence,
                    loan_evidence,
                ),
            });
        }
    }

    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(super) fn execute_c_function_verification_paths(
    state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
    variables: &mut KernelVariableGenerator,
    prepare_contract_resources: bool,
) -> ExecutionResult<Vec<CFunctionPath>> {
    budget.consume_function_call()?;
    if arguments.len() != function.parameters().len() {
        return Ok(vec![CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::WrongArity {
                expected: function.parameters().len(),
                actual: arguments.len(),
            }),
            facts: Vec::new(),
            obligations: Vec::new(),

            loan_evidence: empty_checked_loan_evidence_sequence(),
        }]);
    }

    let mut paths = Vec::new();
    for arguments_path in crate::instrumentation::measure_operation(
        function.name(),
        "independent kernel execution",
        "verification argument evaluation",
        || evaluate_c_arguments_paths(state, arguments, assumptions, budget, Some(environment)),
    )? {
        if let Some(outcome) = arguments_path.outcome {
            paths.push(CFunctionPath {
                outcome,
                facts: arguments_path.facts,
                obligations: arguments_path.obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            });
            continue;
        }

        let path_assumptions = assumptions_with_path_context(
            assumptions,
            &arguments_path.facts,
            &arguments_path.obligations,
        );
        let Some((argument_values, argument_obligations)) = coerce_c_function_arguments(
            function,
            &arguments_path.values,
            &arguments_path.obligations,
            &path_assumptions,
        ) else {
            paths.push(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                    argument_binding_error(function, &arguments_path.values).to_string(),
                )),
                facts: arguments_path.facts,
                obligations: arguments_path.obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            });
            continue;
        };
        let Some(callee_state) = bind_c_function_arguments(state, function, &argument_values)
        else {
            paths.push(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                    argument_binding_error(function, &argument_values).to_string(),
                )),
                facts: arguments_path.facts,
                obligations: argument_obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            });
            continue;
        };

        let body_assumptions = assumptions_with_path_context(
            assumptions,
            &arguments_path.facts,
            &argument_obligations,
        );
        let (callee_state, resource_transfer) = if prepare_contract_resources {
            // The contract boundary of a whole-function judgment: the body
            // runs from the resources the contract declares, consumed
            // definitionally. Lending is the call site's job (the planner in
            // `execute_c_function_call_paths`) and the proof's entry
            // construction (`c_state_with_borrowed_contract_inputs`); a
            // judgment over a body that already happened must not lend again.
            let resource_transfer = match prepare_function_resource_transfer(
                state,
                &callee_state,
                function,
                &body_assumptions,
                budget,
                true,
                ResourceTransitionPurpose::FunctionBoundary,
            )? {
                Ok(resource_transfer) => resource_transfer,
                Err(error) => {
                    paths.push(CFunctionPath {
                        outcome: CFunctionOutcome::RuntimeError(error),
                        facts: arguments_path.facts,
                        obligations: argument_obligations,

                        loan_evidence: empty_checked_loan_evidence_sequence(),
                    });
                    continue;
                }
            };
            (
                callee_state_with_resource_transfer(callee_state, &resource_transfer),
                Some(resource_transfer),
            )
        } else {
            (callee_state, None)
        };
        // A body that is judged as a whole is judged from its own entry, so
        // this is where the declared `decreases` measure is read and the
        // recursion anchor installed. The anchor is derived from the function
        // in hand, not from anything a caller supplies, and a function that
        // declares no measure gets the environment unchanged.
        let anchored_environment = match crate::kernel::termination::c_function_recursion_anchor(
            function,
            &callee_state,
            &body_assumptions,
            budget,
        ) {
            Ok(Some(anchor)) => {
                std::borrow::Cow::Owned(environment.clone().with_recursion_anchor(anchor))
            }
            Ok(None) => std::borrow::Cow::Borrowed(environment),
            Err(message) => {
                paths.push(CFunctionPath {
                    outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                        message,
                    )),
                    facts: arguments_path.facts,
                    obligations: argument_obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),
                });
                continue;
            }
        };
        let body_paths = crate::instrumentation::measure_operation(
            function.name(),
            "independent kernel execution",
            "verification body execution",
            || {
                execute_c_function_body_verification_paths(
                    &callee_state,
                    function,
                    &body_assumptions,
                    &anchored_environment,
                    execution_semantics,
                    budget,
                    variables,
                )
            },
        )?;
        for body_path in body_paths {
            let Some((mut facts, obligations)) = crate::instrumentation::measure_operation(
                function.name(),
                "independent kernel execution",
                "verification fact merge",
                || {
                    merge_execution_pure_facts_and_obligations(
                        &arguments_path.facts,
                        &argument_obligations,
                        &body_path.facts,
                        &body_path.obligations,
                        assumptions,
                    )
                },
            ) else {
                continue;
            };
            if let Some(parameter) = modified_by_value_aggregate_parameter_with_current_ensure(
                &callee_state,
                &body_path.outcome,
                function,
            ) {
                paths.push(CFunctionPath {
                    outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                        format!(
                            "by-value aggregate parameter `{parameter}` is modified, but a postcondition reads its current state"
                        ),
                    )),
                    facts,
                    obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),});
                continue;
            }
            let return_assumptions =
                assumptions_with_path_context(assumptions, &facts, &obligations);
            let (outcome, obligations, loan_evidence) = if let Some(resource_transfer) =
                &resource_transfer
            {
                if resource_transfer.stable_view_plan.is_some()
                    || function_needs_outcome_resource_transfer(function)
                {
                    function_outcome_from_body_with_resource_transfer(
                        state,
                        function,
                        complete_void_fallthrough(function, body_path.outcome),
                        obligations,
                        &return_assumptions,
                        resource_transfer,
                        &argument_values,
                        true,
                        budget,
                    )?
                } else if function_changes_declared_resource_quantities(function) {
                    without_loan_evidence(function_outcome_from_body_with_population_transition(
                        state,
                        function,
                        complete_void_fallthrough(function, body_path.outcome),
                        obligations,
                        &return_assumptions,
                        &argument_values,
                        budget,
                    )?)
                } else {
                    without_loan_evidence(function_outcome_from_body(
                        state,
                        function,
                        complete_void_fallthrough(function, body_path.outcome),
                        obligations,
                        &return_assumptions,
                        None,
                    ))
                }
            } else {
                without_loan_evidence(function_outcome_from_body(
                    state,
                    function,
                    complete_void_fallthrough(function, body_path.outcome),
                    obligations,
                    &return_assumptions,
                    None,
                ))
            };

            append_string_literal_loadable_facts(function, &outcome, &mut facts);

            paths.push(CFunctionPath {
                outcome,
                facts,
                obligations,
                loan_evidence: append_checked_loan_evidence(
                    &body_path.loan_evidence,
                    loan_evidence,
                ),
            });
        }
    }

    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(super) fn execute_c_function_call_paths(
    caller_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CFunctionPath>> {
    if environment.selected_call_contract.is_some() {
        return Ok(vec![CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                "step(Contract) requires a function-pointer call".to_string(),
            )),
            facts: Vec::new(),
            obligations: Vec::new(),

            loan_evidence: empty_checked_loan_evidence_sequence(),
        }]);
    }
    if let Some(rule) = environment.get_external_function_rule(function.name()) {
        // External summaries use the same body-independent application
        // interface as verified rules, but remain an assumption: do not
        // repackage one as `CVerifiedFunctionRule`, whose type carries body
        // safety evidence. Applying the shared rule engine does not execute,
        // inspect, or certify the external body's storage.
        let binder_application = match selected_call_binder_application(
            rule.function.name(),
            rule.function.contract_interface(),
            caller_state,
            environment,
        ) {
            Ok(application) => application,
            Err(message) => return Ok(vec![resource_call_failure(message)]),
        };
        return execute_verified_function_applications(
            caller_state,
            &[CFunctionContractApplication {
                name: rule.function.name(),
                interface_name: rule.function.name(),
                interface: rule.function.contract_interface(),
                storage: Some(&rule.function),
                evidence: None,
                representation_copy: rule.representation_copy(),
            }],
            None,
            binder_application
                .as_ref()
                .map(|application| (0, application)),
            arguments,
            assumptions,
            environment,
            budget,
        );
    }
    // A header-provided `static inline` or `static __always_inline` body has
    // no Click contract to apply.
    // Its checked C body is the call-site semantics, including while the
    // surrounding function is being contract-certified. All other functions
    // retain the normal verified-rule boundary.
    if !function.has_inline_body() {
        match execution_semantics.calls {
            CCallSemantics::ExecuteBodies => {}
            CCallSemantics::ApplyVerifiedRules => {
                let Some(rule) = environment.get_verified_function_rule(function.name()) else {
                    let error = if function.verified_direct_contract_supported() {
                        CRuntimeError::MissingVerifiedFunctionRule(function.name().to_string())
                    } else {
                        CRuntimeError::UnsupportedOpaqueFunctionContract(
                            function.name().to_string(),
                        )
                    };
                    return Ok(vec![CFunctionPath {
                        outcome: CFunctionOutcome::RuntimeError(error),
                        facts: Vec::new(),
                        obligations: Vec::new(),

                        loan_evidence: empty_checked_loan_evidence_sequence(),
                    }]);
                };
                return execute_verified_function_rule(
                    caller_state,
                    rule,
                    arguments,
                    assumptions,
                    environment,
                    budget,
                );
            }
        }
    }
    budget.consume_function_call()?;
    if arguments.len() != function.parameters().len() {
        return Ok(vec![CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::WrongArity {
                expected: function.parameters().len(),
                actual: arguments.len(),
            }),
            facts: Vec::new(),
            obligations: Vec::new(),

            loan_evidence: empty_checked_loan_evidence_sequence(),
        }]);
    }

    let mut paths = Vec::new();
    for arguments_path in evaluate_c_arguments_paths(
        caller_state,
        arguments,
        assumptions,
        budget,
        Some(environment),
    )? {
        if let Some(outcome) = arguments_path.outcome {
            paths.push(CFunctionPath {
                outcome,
                facts: arguments_path.facts,
                obligations: arguments_path.obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            });
            continue;
        }

        let path_assumptions = assumptions_with_path_context(
            assumptions,
            &arguments_path.facts,
            &arguments_path.obligations,
        );
        let Some((argument_values, argument_obligations)) = coerce_c_function_arguments(
            function,
            &arguments_path.values,
            &arguments_path.obligations,
            &path_assumptions,
        ) else {
            paths.push(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                    argument_binding_error(function, &arguments_path.values).to_string(),
                )),
                facts: arguments_path.facts,
                obligations: arguments_path.obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            });
            continue;
        };
        let Some(callee_state) =
            bind_c_function_arguments(caller_state, function, &argument_values)
        else {
            paths.push(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                    argument_binding_error(function, &argument_values).to_string(),
                )),
                facts: arguments_path.facts,
                obligations: argument_obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            });
            continue;
        };

        let body_assumptions = assumptions_with_path_context(
            assumptions,
            &arguments_path.facts,
            &argument_obligations,
        );
        if function.has_inline_body() {
            // An inline body is call-site code: it runs on the caller's own
            // resources and leaves the caller whatever it did not consume.
            // There is no contract boundary to transfer across. Under stable
            // views that includes the caller's loan ledger: the body's stores
            // are checked against the caller's active loans, its own view
            // clauses lend nothing, and any call it makes plans from and
            // recovers to the caller's ledger, whose evidence the path keeps.
            let callee_state = callee_state.with_resource_context(caller_state.resources().clone());
            for body_path in execute_c_function_body_paths(
                &callee_state,
                function,
                &body_assumptions,
                environment,
                execution_semantics,
                budget,
            )? {
                let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                    &arguments_path.facts,
                    &argument_obligations,
                    &body_path.facts,
                    &body_path.obligations,
                    assumptions,
                ) else {
                    continue;
                };
                let return_assumptions =
                    assumptions_with_path_context(assumptions, &facts, &obligations);
                let (outcome, obligations) = function_outcome_from_body(
                    caller_state,
                    function,
                    complete_void_fallthrough(function, body_path.outcome),
                    obligations,
                    &return_assumptions,
                    None,
                );
                paths.push(CFunctionPath {
                    outcome,
                    facts,
                    obligations,

                    loan_evidence: body_path.loan_evidence,
                });
            }
            continue;
        }
        let resource_transfer = match prepare_function_resource_transfer(
            caller_state,
            &callee_state,
            function,
            &body_assumptions,
            budget,
            false,
            ResourceTransitionPurpose::CallSite,
        )? {
            Ok(resource_transfer) => resource_transfer,
            Err(error) => {
                paths.push(CFunctionPath {
                    outcome: CFunctionOutcome::RuntimeError(error),
                    facts: arguments_path.facts,
                    obligations: argument_obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),
                });
                continue;
            }
        };
        let callee_state = callee_state_with_resource_transfer(callee_state, &resource_transfer);
        for body_path in execute_c_function_body_paths(
            &callee_state,
            function,
            &body_assumptions,
            environment,
            execution_semantics,
            budget,
        )? {
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &arguments_path.facts,
                &argument_obligations,
                &body_path.facts,
                &body_path.obligations,
                assumptions,
            ) else {
                continue;
            };
            let return_assumptions =
                assumptions_with_path_context(assumptions, &facts, &obligations);
            let (outcome, obligations, loan_evidence) =
                function_outcome_from_body_with_resource_transfer(
                    caller_state,
                    function,
                    body_path.outcome,
                    obligations,
                    &return_assumptions,
                    &resource_transfer,
                    &argument_values,
                    true,
                    budget,
                )?;

            paths.push(CFunctionPath {
                outcome,
                facts,
                obligations,
                loan_evidence: append_checked_loan_evidence(
                    &body_path.loan_evidence,
                    loan_evidence,
                ),
            });
        }
    }

    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn execute_verified_function_rule(
    caller_state: &CState,
    rule: &CVerifiedFunctionRule,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CFunctionPath>> {
    // A `step(callee(...), { binder: instance })` names exactly this call.
    // The map is the whole binding: every instance binder the callee declares
    // is looked up once, and nothing else is consulted.
    let binder_application = match selected_call_binder_application(
        rule.function.name(),
        rule.function.contract_interface(),
        caller_state,
        environment,
    ) {
        Ok(application) => application,
        Err(message) => return Ok(vec![resource_call_failure(message)]),
    };
    execute_verified_function_applications(
        caller_state,
        &[CFunctionContractApplication {
            name: rule.function.name(),
            interface_name: rule.function.name(),
            interface: rule.function.contract_interface(),
            storage: Some(&rule.function),
            evidence: Some(&rule.function),
            representation_copy: None,
        }],
        None,
        binder_application
            .as_ref()
            .map(|application| (0, application)),
        arguments,
        assumptions,
        environment,
        budget,
    )
}

/// The binder transport the proof selected for a call to `function`, if the
/// step named this callee. The transported instances are exactly the
/// function's own `owns`, `consumes`, and `produces` binders.
fn selected_call_binder_application(
    function_name: &str,
    interface: &CFunctionContractInterface,
    caller_state: &CState,
    environment: &CExecutionEnvironment,
) -> Result<Option<ResourceCallApplication>, &'static str> {
    let Some(transport) = environment.selected_call_binders.as_ref() else {
        return Ok(None);
    };
    if transport.function.as_ref() != function_name {
        return Ok(None);
    }
    // Only the binders required at entry are checked here; a `produces`
    // binder has no instance to check until the call returns.
    let parameters = interface
        .resource_requires()
        .iter()
        .filter(|resource| resource.is_instance())
        .cloned()
        .collect::<Vec<_>>();
    ResourceCallApplication::bind(parameters, transport.bindings.clone(), caller_state).map(Some)
}

/// One candidate contract application. The interface is the complete input
/// to callback preparation. Optional concrete storage supplies only the
/// declaration identity needed to lower a direct function's global and
/// static names. Optional concrete evidence is consulted only by verified
/// direct calls for body-specific safety checks and loadable literal facts.
/// Named callbacks carry neither; external assumptions carry storage but no
/// proof evidence.
#[derive(Clone, Copy)]
struct CFunctionContractApplication<'a> {
    /// Concrete callee name used for diagnostics and call provenance.
    name: &'a str,
    /// Nominal interface name used to distinguish candidates and their source
    /// requirement metadata.
    interface_name: &'a str,
    interface: &'a CFunctionContractInterface,
    storage: Option<&'a CFunction>,
    evidence: Option<&'a CFunction>,
    /// The checked representation-copy effect of a recognized byte-copy
    /// declaration, if this application is one.
    representation_copy: Option<RepresentationCopyEffect>,
}

/// Transfers initialized typed cells across a recognized byte-copy call.
///
/// Only a cell whose complete byte representation lies inside the copied
/// source range moves, and only when both endpoints are constant so the offset
/// mapping and the alignment test are exact. A cell the copy would split, a
/// symbolic range, or a misaligned destination is left alone: the destination
/// keeps its post-havoc state, so the transfer can only add observations the
/// copy's `bytes_equal` guarantee already justified. An untyped source has no
/// cells, so a raw byte copy still establishes nothing typed.
pub(in crate::kernel) fn transfer_representation_copy_cells(
    entry_memory: &CMemory,
    argument_values: &[CValue],
    mut memory: CMemory,
    effect: RepresentationCopyEffect,
) -> CMemory {
    let (Some(destination), Some(source), Some(bytes)) = (
        argument_values.get(effect.destination_argument),
        argument_values.get(effect.source_argument),
        argument_values.get(effect.bytes_argument),
    ) else {
        return memory;
    };
    let (CValue::Pointer(destination), CValue::Pointer(source)) = (destination, source) else {
        return memory;
    };
    let CValue::Int32(bytes) = bytes else {
        return memory;
    };
    let (Some(source_offset), Some(destination_offset), Some(bytes)) = (
        source.pointer().offset.as_const(),
        destination.pointer().offset.as_const(),
        bytes.as_const(),
    ) else {
        return memory;
    };
    let bytes = i64::from(bytes);
    if bytes <= 0 {
        return memory;
    }
    let source_block = source.pointer().block.clone();
    let destination_block = destination.pointer().block.clone();
    // A checked byte copy requires the ranges be separate, so a self-copy in
    // one block is not the recognized effect.
    if source_block == destination_block {
        return memory;
    }
    let source_cells = entry_memory
        .cells
        .iter()
        .filter(|(cell, _)| cell.block == source_block)
        .map(|(cell, value)| (cell.offset.clone(), value.clone()))
        .collect::<Vec<_>>();
    for (cell_offset, value) in source_cells {
        let Some(cell_offset) = cell_offset.as_const() else {
            continue;
        };
        let width = i64::from(value.byte_width());
        if width == 0 {
            continue;
        }
        let relative = cell_offset - source_offset;
        if relative < 0 || relative + width > bytes {
            continue;
        }
        let destination_cell_offset = destination_offset + relative;
        // The copied bytes preserve the source value, but a typed observation
        // at a misaligned destination is not a defined load.
        if destination_cell_offset % width != 0 {
            continue;
        }
        memory = memory.store(
            Pointer {
                block: destination_block.clone(),
                offset: PointerOffsetTerm::Constant(destination_cell_offset),
            },
            value,
        );
    }
    memory
}

fn execute_verified_function_applications(
    caller_state: &CState,
    applications: &[CFunctionContractApplication<'_>],
    selected_contract: Option<usize>,
    resource_application: Option<(usize, &ResourceCallApplication)>,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CFunctionPath>> {
    if applications.is_empty() {
        return Ok(vec![CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                "call requires at least one contract application".to_string(),
            )),
            facts: Vec::new(),
            obligations: Vec::new(),

            loan_evidence: empty_checked_loan_evidence_sequence(),
        }]);
    }
    let application = applications[0];
    if applications
        .iter()
        .any(|application| !application.interface.exceptional_signature().is_empty())
        && (applications.len() != 1
            || selected_contract.is_some()
            || resource_application.is_some()
            || application
                .evidence
                .or(application.storage)
                .is_none_or(|function| {
                    !function.verified_direct_contract_supported()
                        || function.contract_interface() != application.interface
                }))
    {
        return Ok(vec![CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(
                CRuntimeError::UnsupportedOpaqueFunctionContract(application.name.to_string()),
            ),
            facts: Vec::new(),
            obligations: Vec::new(),
            loan_evidence: empty_checked_loan_evidence_sequence(),
        }]);
    }
    // Every named instance the callee declares must be bound by the selected
    // application. The check is one map lookup per declared binder, so an
    // unbound binder is refused here rather than transported silently.
    if let Some(unbound) = applications
        .iter()
        .enumerate()
        .find_map(|(index, application)| {
            let bindings = resource_application
                .filter(|(selected, _)| *selected == index)
                .map(|(_, application)| &application.bindings);
            application
                .interface
                .resource_requires()
                .iter()
                .chain(application.interface.resource_ensures())
                .find(|resource| {
                    resource.instance_identity().is_some_and(|identity| {
                        !bindings.is_some_and(|bindings| bindings.contains_key(&identity))
                    })
                })
                .map(|_| application.name.to_string())
        })
    {
        return Ok(vec![CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                "calls with named resource instances require checked binder transport: `{unbound}` has an unbound instance binder"
            ))),
            facts: vec![],
            obligations: vec![],

            loan_evidence: empty_checked_loan_evidence_sequence(),
        }]);
    }
    budget.consume_function_call()?;
    let existing_variables = crate::instrumentation::measure_operation(
        application.name,
        "verified function rule application",
        "verified call variable collection",
        || {
            let mut existing_variables = BTreeSet::new();
            collect_c_state_bitvector_variables(caller_state, &mut existing_variables);
            for application in applications {
                collect_c_function_contract_interface_bitvector_variables(
                    application.interface,
                    &mut existing_variables,
                );
            }
            for argument in arguments {
                collect_c_expression_bitvector_variables(argument, &mut existing_variables);
            }
            collect_assumption_variables(assumptions, &mut existing_variables);
            existing_variables
        },
    );
    let mut variables = KernelVariableGenerator::fresh_for_execution(existing_variables);
    let memory_identity = variables.next_in(budget)?;
    let result_identity = variables.next_in(budget)?;
    let exceptional_payload_identity =
        match !application.interface.exceptional_signature().is_empty() {
            true => Some(variables.next_in(budget)?),
            false => None,
        };
    let mut paths = Vec::new();
    'arguments: for arguments_path in evaluate_c_arguments_paths(
        caller_state,
        arguments,
        assumptions,
        budget,
        Some(environment),
    )? {
        if let Some(outcome) = arguments_path.outcome {
            paths.push(CFunctionPath {
                outcome,
                facts: arguments_path.facts,
                obligations: arguments_path.obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            });
            continue;
        }

        let mut applicable = Vec::new();
        let mut first_failure = None;
        let mut selected_position = None;
        for (index, application) in applications.iter().enumerate() {
            let prepared = prepare_verified_function_call(
                caller_state,
                *application,
                index,
                arguments,
                arguments_path.clone(),
                applications.len() > 1 || selected_contract.is_some(),
                assumptions,
                environment,
                budget,
                resource_application
                    .filter(|(selected, _)| *selected == index)
                    .map(|(_, application)| application),
            )?;
            match prepared {
                Ok(prepared) => {
                    if selected_contract == Some(index) {
                        selected_position = Some(applicable.len());
                    }
                    applicable.push(prepared);
                }
                Err(failure) => {
                    if selected_contract == Some(index) {
                        paths.push(failure);
                        continue 'arguments;
                    }
                    if first_failure.is_none() {
                        first_failure = Some(failure);
                    }
                }
            }
        }
        if applicable.is_empty() {
            paths.push(first_failure.expect("a nonempty set of callback contracts"));
            continue;
        }
        // Pure conjunction does not duplicate an ownership ledger. An explicit
        // selector chooses one resource transition; absent that choice, do not
        // represent alternative ownership as paths or separating ownership.
        if selected_contract.is_none()
            && applicable.len() > 1
            && applicable.iter().any(|call| {
                !call.interface.resource_requires().is_empty()
                    || !call.interface.resource_ensures().is_empty()
                    || !call.interface.resource_constructors().is_empty()
                    || !call.transfer.memory_effects.is_empty()
            })
        {
            paths.push(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                    "ambiguous callback resource transition; use step(Contract) to select one"
                        .to_string(),
                )),
                facts: arguments_path.facts,
                obligations: arguments_path.obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            });
            continue;
        }
        // Supplementary guarantees are interpreted on the shared post-memory,
        // not an alternative output ledger. In particular, resource counts must
        // not accidentally be evaluated against that interface's input ledger.
        let independent_guarantees_only = selected_contract.is_some()
            && applicable.iter().any(|call| {
                !call.interface.resource_requires().is_empty()
                    || !call.interface.resource_ensures().is_empty()
            });
        let primary = applicable.remove(selected_position.unwrap_or(0));
        let PreparedVerifiedFunctionCall {
            name,
            interface_name: _interface_name,
            storage,
            evidence,
            interface,
            argument_values,
            entry_state,
            entry_contract_state,
            mut transfer,
            mut facts,
            obligations,
            effective_assumptions,
            bindings: selected_bindings,
        } = primary;
        let additional_calls = applicable.into_iter();
        // The planner has checked these effects against the views this call
        // lends; the caller's other active loans (its own contract inputs,
        // an enclosing call's loans) are checked here, so a summary can
        // never havoc memory that is lent elsewhere.
        if let Some(diagnostic) = entry_state.loan_ledger().and_then(|ledger| {
            transfer.memory_effects.iter().find_map(|range| {
                ledger.memory_access_refusal(
                    range,
                    &effective_assumptions,
                    LoanRefusalOperation::MemoryAccess,
                )
            })
        }) {
            paths.push(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::LoanRefusal(diagnostic)),
                facts,
                obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            });
            continue;
        }
        let exceptional_path = if let Some(payload_identity) = exceptional_payload_identity {
            Some(exceptional_direct_function_path(
                caller_state,
                interface,
                evidence
                    .or(storage)
                    .expect("exceptional applications require a direct function declaration"),
                &argument_values,
                &entry_state,
                &entry_contract_state,
                &transfer,
                facts.clone(),
                obligations.clone(),
                &effective_assumptions,
                payload_identity,
                budget,
            )?)
        } else {
            None
        };
        let memory = if transfer.memory_effects.is_empty() {
            entry_state.memory.clone()
        } else {
            entry_state.memory.clone().with_call_memory_havoc(
                memory_identity,
                &transfer.memory_effects,
                &effective_assumptions,
            )
        };
        // A recognized byte-copy declaration transfers initialized typed
        // cells across the copy. It runs after the external contract's havoc,
        // so the copies' `bytes_equal` guarantee is what makes the transferred
        // values the checked ones, and it is the only thing that turns the
        // destination's freshly owned bytes into typed observations.
        let memory = if let Some(effect) = application.representation_copy {
            transfer_representation_copy_cells(
                &entry_state.memory,
                &argument_values,
                memory,
                effect,
            )
        } else {
            memory
        };
        if !transfer.memory_effects.is_empty() {
            facts.push(
                ExecutionPureFact::internal(Proposition::CMemoryEffectSummary {
                    before: entry_state.memory.clone(),
                    after: memory.clone(),
                    mutable_ranges: transfer.memory_effects.clone(),
                })
                .into_certified(),
            );
        }
        let result = symbolic_contract_result(interface, result_identity);
        let mut post_state = entry_state.clone().with_memory(memory);
        if interface.return_type() != CType::Void {
            set_contract_result(&mut post_state, interface, result.clone());
        }
        // A `produces` binder owns nothing at entry: the call creates the
        // instance under the identity the caller's `let` introduced. It is
        // built once, here, so the population transition and the returned
        // resources agree on its fresh fields.
        let mut produced_instances = BTreeMap::new();
        for resource in interface.resource_ensures() {
            let Some(identity) = resource.instance_identity() else {
                continue;
            };
            let Some(schema) = resource.instance_schema() else {
                continue;
            };
            if resource.role() == CResourceTransferRole::Borrow
                || entry_contract_state
                    .owned_resource_instance(identity)
                    .is_some()
            {
                continue;
            }
            let Some(produced) = selected_bindings
                .as_ref()
                .and_then(|bindings| bindings.get(&identity).copied())
            else {
                continue;
            };
            let Some(instance_resource) = resource.instance_resource_spec() else {
                continue;
            };
            let (name, arguments) = match evaluate_function_resource_spec(
                &post_state,
                &instance_resource,
                &effective_assumptions,
                budget,
            )? {
                Ok(CResourceFact::Own(CResource::Composite { name, arguments }, quantity))
                    if quantity.as_const() == Some(1) =>
                {
                    (name, arguments)
                }
                Ok(_) => {
                    return Ok(vec![resource_call_failure(
                        "a produced resource instance requires an owned resource definition",
                    )]);
                }
                Err(error) => {
                    return Ok(vec![CFunctionPath {
                        outcome: CFunctionOutcome::RuntimeError(error),
                        facts,
                        obligations,

                        loan_evidence: empty_checked_loan_evidence_sequence(),
                    }]);
                }
            };
            let fields = fresh_resource_instance_fields(schema, &mut variables, budget)?;
            produced_instances.insert(
                identity,
                ResourceInstance::new(produced, name, arguments, schema.clone(), fields)
                    .expect("fresh symbolic fields have their declared types"),
            );
        }
        let callee_resources = if produced_instances.is_empty() {
            transfer.callee_resources.clone()
        } else {
            transfer.callee_resources.clone().unchecked_with_facts(
                produced_instances
                    .values()
                    .map(|instance| CResourceFact::own(CResource::Instance(instance.clone()))),
            )
        };
        let mut transition_state = post_state.clone().with_resource_context(callee_resources);
        let population_timing = crate::instrumentation::OperationTiming::new(
            name,
            "verified function rule application",
            "verified call population transition",
        );
        let population_transition = match apply_counted_population_transitions_with_interface(
            caller_state,
            &mut transition_state,
            storage,
            interface,
            &argument_values,
            &effective_assumptions,
            true,
            budget,
        )? {
            Ok(transition) => transition,
            Err(error) => {
                paths.push(CFunctionPath {
                    outcome: CFunctionOutcome::RuntimeError(error),
                    facts,
                    obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),
                });
                continue;
            }
        };
        drop(population_timing);
        post_state.counted_populations = transition_state.counted_populations;
        for obligation in &population_transition.postcondition_obligations {
            // The kernel issues `CVerifiedFunctionRule` only after exact
            // contract certification has discharged these postconditions.
            // Applying that rule instantiates certified consequences; it
            // must not turn them back into caller prerequisites.
            facts.push(ExecutionPureFact::certified(
                obligation.proposition().clone(),
            ));
        }
        for proposition in &population_transition.population_facts {
            facts.push(ExecutionPureFact::certified(proposition.clone()));
        }
        let caller_resources_after_requirements =
            match apply_counted_population_transition_resources(
                transfer.caller_resources_after_requirements.clone(),
                &population_transition,
                &effective_assumptions,
            ) {
                Ok(resources) => resources,
                Err(error) => {
                    paths.push(CFunctionPath {
                        outcome: CFunctionOutcome::RuntimeError(error),
                        facts,
                        obligations,

                        loan_evidence: empty_checked_loan_evidence_sequence(),
                    });
                    continue;
                }
            };
        post_state.resources = caller_resources_after_requirements.clone();
        // Returned ownership keeps its identity, not its old field values.
        // Only the ensures below relate fresh post-fields to the entry snapshot.
        for resource in interface.resource_ensures() {
            let Some(identity) = resource.instance_identity() else {
                continue;
            };
            let after = if let Some(produced) = produced_instances.get(&identity) {
                produced.clone()
            } else {
                let Some(before) = entry_contract_state.owned_resource_instance(identity) else {
                    return Ok(vec![resource_call_failure(
                        "returned resource parameter is not owned at call entry",
                    )]);
                };
                let fields =
                    fresh_resource_instance_fields(before.schema(), &mut variables, budget)?;
                ResourceInstance::new(
                    before.identity,
                    before.name.clone(),
                    before.arguments.clone(),
                    before.schema.clone(),
                    fields,
                )
                .expect("fresh symbolic fields have their declared types")
            };
            post_state.resources = match post_state
                .resources
                .clone()
                .try_compose_into_valid_context_delaying_normalization(
                    [CResourceFact::own(CResource::Instance(after))],
                    &effective_assumptions,
                ) {
                Ok(resources) => resources,
                Err(error) => {
                    return Ok(vec![CFunctionPath {
                        outcome: CFunctionOutcome::RuntimeError(resource_context_runtime_error(
                            error,
                        )),
                        facts,
                        obligations,

                        loan_evidence: empty_checked_loan_evidence_sequence(),
                    }]);
                }
            };
        }
        let output_resource_state =
            with_contract_interface_argument_views(&post_state, interface, &argument_values);
        let entry_resource_state =
            with_contract_interface_argument_views(&entry_state, interface, &argument_values);

        let return_resource_timing = crate::instrumentation::OperationTiming::new(
            name,
            "verified function rule application",
            "verified call return resource evaluation",
        );
        let ContractReturnResources {
            return_resources,
            ensured_views: returned_views,
            produced_borrowing_pieces,
        } = match evaluate_contract_return_resources(
            &caller_resources_after_requirements,
            escrowed_owners(&transfer),
            &transfer.canonical_borrowed_owners,
            &entry_resource_state,
            &output_resource_state,
            name,
            interface,
            &effective_assumptions,
            budget,
        )? {
            Ok(resources) => resources,
            Err(error) => {
                paths.push(CFunctionPath {
                    outcome: CFunctionOutcome::RuntimeError(error),
                    facts,
                    obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),
                });
                continue;
            }
        };
        transfer.candidate_output_views = returned_views;
        transfer.produced_borrowing_pieces = produced_borrowing_pieces;
        drop(return_resource_timing);
        transfer.post_outputs = Some(return_resources);
        let return_resources = transfer
            .post_outputs
            .as_ref()
            .expect("the checked transition records post outputs")
            .clone();

        // Lower the ensures before reconciling allocation ownership so the
        // transition can prove exact continuity when the contract states it.
        // An undecided continuity relation remains symbolic in this one call
        // successor; it is not an execution-path split.
        post_state.resources = return_resources.clone();
        let canonical_entry_contract_state = with_canonical_borrowed_pointer_memory(
            &entry_contract_state,
            &transfer.canonical_borrowed_owners,
        );
        let provisional_post_contract_state = with_canonical_borrowed_pointer_memory(
            &with_contract_interface_argument_views(&post_state, interface, &argument_values),
            &transfer.canonical_borrowed_owners,
        );
        let mut provisional_facts = facts.clone();
        let provisional_ensure_timing = crate::instrumentation::OperationTiming::new(
            name,
            "verified function rule application",
            "verified call provisional ensure lowering",
        );
        add_verified_function_ensure_facts_selected_with_interface(
            &mut provisional_facts,
            &obligations,
            &provisional_post_contract_state,
            &canonical_entry_contract_state,
            interface,
            interface.contract_ensures().iter(),
            &effective_assumptions,
            budget,
        )?;
        drop(provisional_ensure_timing);

        let allocation_delta_timing = crate::instrumentation::OperationTiming::new(
            name,
            "verified function rule application",
            "verified call heap allocation delta",
        );
        let allocation_assumptions =
            assumptions_with_path_context(&effective_assumptions, &provisional_facts, &obligations);
        let allocation_delta = apply_verified_heap_allocation_delta(
            post_state.memory.clone(),
            &transfer.callee_resources,
            &caller_resources_after_requirements,
            &return_resources,
            interface,
            &allocation_assumptions,
            post_state.loan_ledger(),
        );
        drop(allocation_delta_timing);
        let (memory, allocation_effects) = match allocation_delta {
            Ok(result) => result,
            Err(VerifiedAllocationDeltaError::Runtime(error)) => {
                paths.push(CFunctionPath {
                    outcome: CFunctionOutcome::RuntimeError(error),
                    facts,
                    obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),
                });
                continue;
            }
            Err(VerifiedAllocationDeltaError::InconsistentReturnedAllocation) => continue,
        };
        facts.extend(allocation_effects);
        post_state.set_memory(memory);
        let post_contract_state = with_canonical_borrowed_pointer_memory(
            &with_contract_interface_argument_views(&post_state, interface, &argument_values),
            &transfer.canonical_borrowed_owners,
        );

        let ensure_timing = crate::instrumentation::OperationTiming::new(
            name,
            "verified function rule application",
            "verified call ensure lowering",
        );
        add_verified_function_ensure_facts_selected_with_interface(
            &mut facts,
            &obligations,
            &post_contract_state,
            &canonical_entry_contract_state,
            interface,
            interface.contract_ensures().iter(),
            &effective_assumptions,
            budget,
        )?;
        drop(ensure_timing);

        // The applicable interfaces share the result and post-call memory,
        // but bind their own argument names against the original entry state.
        for additional in additional_calls {
            let mut additional_facts = additional.facts;
            let entry_fact_count = additional_facts.len();
            let mut additional_post = additional
                .entry_state
                .clone()
                .with_memory(post_state.memory.clone());
            if additional.interface.return_type() != CType::Void {
                set_contract_result(&mut additional_post, additional.interface, result.clone());
            }
            let additional_post = with_contract_interface_argument_views(
                &additional_post,
                additional.interface,
                &additional.argument_values,
            );
            add_verified_function_ensure_facts_selected_with_interface(
                &mut additional_facts,
                &additional.obligations,
                &additional_post,
                &additional.entry_contract_state,
                additional.interface,
                additional
                    .interface
                    .contract_ensures()
                    .iter()
                    .filter(|ensure| {
                        !independent_guarantees_only
                            || spec_proposition_is_state_independent(ensure)
                            || spec_proposition_supports_stateful_memory_refinement(ensure)
                    }),
                &additional.effective_assumptions,
                budget,
            )?;
            facts.extend(additional_facts.into_iter().skip(entry_fact_count));
        }

        let (
            return_resources,
            return_ledger,
            return_participant,
            return_view_bindings,
            loan_evidence,
        ) = match recover_candidate_stable_view_resources(
            caller_state,
            &post_state,
            &transfer,
            return_resources,
            &effective_assumptions,
            &assumptions_with_path_context(&effective_assumptions, &facts, &[]),
            &obligations,
        ) {
            Ok(recovered) => recovered,
            Err(error) => {
                paths.push(CFunctionPath {
                    outcome: CFunctionOutcome::RuntimeError(error),
                    facts,
                    obligations,
                    loan_evidence: empty_checked_loan_evidence_sequence(),
                });
                continue;
            }
        };

        let mut return_state = caller_state.clone();
        return_state.set_memory(post_state.memory.clone());
        return_state.resources = return_resources;
        return_state.loan_ledger = return_ledger;
        return_state.loan_participant = return_participant;
        return_state = return_state.with_loan_view_bindings(return_view_bindings);
        return_state.counted_populations = post_state.counted_populations;
        return_state.next_local_frame = post_state.next_local_frame;
        return_state.next_local_lifetime = post_state.next_local_lifetime;
        let outcome = CFunctionOutcome::Return {
            value: result,
            state: return_state,
        };
        if let Some(function) = evidence {
            append_string_literal_loadable_facts(function, &outcome, &mut facts);
        }
        paths.push(CFunctionPath {
            outcome,
            facts,
            obligations,
            loan_evidence: loan_evidence
                .map(|evidence| {
                    append_checked_loan_evidence(
                        &empty_checked_loan_evidence_sequence(),
                        Some(evidence),
                    )
                })
                .unwrap_or_else(empty_checked_loan_evidence_sequence),
        });
        if let Some(exceptional_path) = exceptional_path {
            paths.push(exceptional_path);
        }
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

/// Builds the exceptional successor of a direct modular call. Its function
/// declaration supplies storage identity, not necessarily body evidence:
/// targeted proofs may assume an unselected callee's checked interface.
/// Entry checking and the unchanged post-memory are shared with the
/// normal application, but the payload and certified facts are specific to
/// this outcome. Keeping this path separate is what prevents ordinary
/// `ensures` from becoming exceptional facts (and vice versa).
fn exceptional_direct_function_path(
    caller_state: &CState,
    interface: &CFunctionContractInterface,
    evidence: &CFunction,
    argument_values: &[CValue],
    entry_state: &CState,
    entry_contract_state: &CState,
    transfer: &CFunctionResourceTransfer,
    mut facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    effective_assumptions: &PureFactContext,
    payload_identity: Variable,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<CFunctionPath> {
    debug_assert!(interface.verified_direct_contract_supported());
    debug_assert!(interface.resource_requires().is_empty());
    debug_assert!(interface.resource_ensures().is_empty());
    debug_assert!(interface.resource_constructors().is_empty());
    debug_assert!(transfer.memory_effects.is_empty());

    let memory = entry_state.memory.clone();

    let payload = symbolic_call_result(CType::Int32, payload_identity);
    let mut post_state = entry_state.clone().with_memory(memory.clone());
    post_state.locals.set_typed(
        C_EXCEPTIONAL_RESULT_NAME.to_string(),
        payload.clone(),
        CType::Int32,
    );
    let post_contract_state =
        with_contract_interface_argument_views(&post_state, interface, argument_values);
    add_verified_function_ensure_facts_selected_with_interface(
        &mut facts,
        &obligations,
        &post_contract_state,
        entry_contract_state,
        interface,
        interface.exceptional_ensures().iter(),
        effective_assumptions,
        budget,
    )?;

    let mut throw_state = caller_state.clone();
    throw_state.set_memory(memory);
    throw_state.next_local_frame = post_state.next_local_frame;
    throw_state.next_local_lifetime = post_state.next_local_lifetime;
    let outcome = CFunctionOutcome::Throw {
        value: payload,
        state: throw_state,
    };
    append_string_literal_loadable_facts(evidence, &outcome, &mut facts);
    Ok(CFunctionPath {
        outcome,
        facts,
        obligations,
        loan_evidence: empty_checked_loan_evidence_sequence(),
    })
}

struct PreparedVerifiedFunctionCall<'a> {
    /// The nominal callee name used for diagnostics and provenance. It is not
    /// a source-body handle for named callbacks.
    name: &'a str,
    interface_name: &'a str,
    /// Concrete declaration identity for global and static storage lowering.
    /// This is not evidence that the function body was checked.
    storage: Option<&'a CFunction>,
    /// Concrete evidence is present only for a verified direct rule. Named
    /// contracts and external assumptions deliberately carry none.
    evidence: Option<&'a CFunction>,
    /// The body-independent interface used to prepare this application. It is
    /// explicit even when it is the concrete function's own interface, so
    /// callback and ordinary calls cannot silently grow separate evaluators.
    interface: &'a CFunctionContractInterface,
    argument_values: Vec<CValue>,
    entry_state: CState,
    entry_contract_state: CState,
    transfer: CFunctionResourceTransfer,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    effective_assumptions: PureFactContext,
    /// The binder map this interface was selected with, if any. A `produces`
    /// binder reads its caller-side identity from exactly this map.
    bindings: Option<std::sync::Arc<BTreeMap<Variable, Variable>>>,
}

/// Finds the exact source snapshot carried by a lowered pure requirement.
/// This is deliberately narrower than the general recursive variable walker:
/// only the logical/condition/bitvector shapes admitted by the source-backed
/// classifier are visited, with the same finite structural budget.
fn source_load_snapshot_for_proposition(
    proposition: &Proposition,
) -> ExecutionResult<Option<CMemorySnapshotIdentity>> {
    const MAX_NODES: usize = 4096;
    enum Work<'a> {
        Proposition(&'a Proposition),
        Condition(&'a ConditionTerm),
        Bitvector(&'a Bitvector32Term),
    }
    let mut work = vec![Work::Proposition(proposition)];
    let mut visited = 0usize;
    let mut snapshot = None;
    while let Some(item) = work.pop() {
        visited = visited.saturating_add(1);
        crate::instrumentation::record_deterministic_work(1);
        if visited > MAX_NODES {
            return Err(ExecutionLimit::ExpressionSteps);
        }
        if crate::kernel::assumptions::reasoning_interrupted() {
            return Err(ExecutionLimit::Deadline);
        }
        match item {
            Work::Proposition(Proposition::ConditionIs(condition, _)) => {
                work.push(Work::Condition(condition));
            }
            Work::Proposition(Proposition::And(left, right))
            | Work::Proposition(Proposition::Or(left, right))
            | Work::Proposition(Proposition::Implies(left, right)) => {
                work.push(Work::Proposition(right));
                work.push(Work::Proposition(left));
            }
            Work::Proposition(Proposition::Not(body))
            | Work::Proposition(Proposition::ForAll { body, .. })
            | Work::Proposition(Proposition::Exists { body, .. }) => {
                work.push(Work::Proposition(body));
            }
            Work::Proposition(_) => return Ok(None),
            Work::Condition(
                ConditionTerm::Bitvector32SignedLessThan(left, right)
                | ConditionTerm::Bitvector32SignedLessEqual(left, right)
                | ConditionTerm::Bitvector32SignedGreaterThan(left, right)
                | ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
                | ConditionTerm::Bitvector32Equal(left, right)
                | ConditionTerm::Bitvector64SignedLessThan(left, right)
                | ConditionTerm::Bitvector64SignedLessEqual(left, right)
                | ConditionTerm::Bitvector64SignedGreaterThan(left, right)
                | ConditionTerm::Bitvector64SignedGreaterEqual(left, right)
                | ConditionTerm::Bitvector64UnsignedLessThan(left, right)
                | ConditionTerm::Bitvector64UnsignedLessEqual(left, right)
                | ConditionTerm::Bitvector64UnsignedGreaterThan(left, right)
                | ConditionTerm::Bitvector64UnsignedGreaterEqual(left, right)
                | ConditionTerm::Bitvector64Equal(left, right)
                | ConditionTerm::Bitvector32SignedAddOverflows(left, right)
                | ConditionTerm::Bitvector32SignedSubtractOverflows(left, right)
                | ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right)
                | ConditionTerm::Bitvector32SignedDivideOverflows(left, right)
                | ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right)
                | ConditionTerm::Bitvector64SignedAddOverflows(left, right)
                | ConditionTerm::Bitvector64SignedSubtractOverflows(left, right)
                | ConditionTerm::Bitvector64SignedMultiplyOverflows(left, right)
                | ConditionTerm::Bitvector64SignedDivideOverflows(left, right)
                | ConditionTerm::Bitvector64SignedShiftLeftOverflows(left, right),
            ) => {
                work.push(Work::Bitvector(right));
                work.push(Work::Bitvector(left));
            }
            Work::Condition(ConditionTerm::Constant(_))
            | Work::Condition(ConditionTerm::Variable(_)) => {}
            Work::Condition(_) => return Ok(None),
            Work::Bitvector(Bitvector32Term::Constant(_))
            | Work::Bitvector(Bitvector32Term::Int64Constant(_))
            | Work::Bitvector(Bitvector32Term::UInt64Constant(_)) => {}
            Work::Bitvector(Bitvector32Term::Variable(variable)) => {
                if crate::kernel::is_load_variable(variable) {
                    let Some((origin, _)) =
                        crate::kernel::registered_load_origin_for_variable(variable)
                    else {
                        return Ok(None);
                    };
                    let identity = CMemorySnapshotIdentity::of(origin.memory());
                    if snapshot.is_some_and(|known| known != identity) {
                        return Ok(None);
                    }
                    snapshot = Some(identity);
                }
            }
            Work::Bitvector(Bitvector32Term::MemoryLoad(memory, _)) => {
                let identity = CMemorySnapshotIdentity::of(memory.memory());
                if snapshot.is_some_and(|known| known != identity) {
                    return Ok(None);
                }
                snapshot = Some(identity);
            }
            Work::Bitvector(
                Bitvector32Term::Add(left, right)
                | Bitvector32Term::Subtract(left, right)
                | Bitvector32Term::Multiply(left, right)
                | Bitvector32Term::Divide(left, right)
                | Bitvector32Term::UnsignedDivide(left, right)
                | Bitvector32Term::Remainder(left, right)
                | Bitvector32Term::UnsignedRemainder(left, right)
                | Bitvector32Term::ShiftLeft(left, right)
                | Bitvector32Term::ArithmeticShiftRight(left, right)
                | Bitvector32Term::LogicalShiftRight(left, right)
                | Bitvector32Term::BitwiseAnd(left, right)
                | Bitvector32Term::BitwiseOr(left, right)
                | Bitvector32Term::BitwiseXor(left, right),
            ) => {
                work.push(Work::Bitvector(right));
                work.push(Work::Bitvector(left));
            }
            Work::Bitvector(Bitvector32Term::BitwiseNot(body)) => {
                work.push(Work::Bitvector(body));
            }
            Work::Bitvector(_) => return Ok(None),
        }
    }
    Ok(snapshot)
}

fn prepare_verified_function_call<'a>(
    caller_state: &CState,
    application: CFunctionContractApplication<'a>,
    candidate_ordinal: usize,
    source_arguments: &[CExpression],
    arguments_path: CArgumentsPath,
    require_established: bool,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    budget: &mut ExecutionBudget,
    resource_application: Option<&ResourceCallApplication>,
) -> ExecutionResult<Result<PreparedVerifiedFunctionCall<'a>, CFunctionPath>> {
    let contract_interface = application.interface;
    if contract_interface.contract_requirement_sources().len()
        != contract_interface.contract_requires().len()
    {
        return Ok(Err(CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                "call requirement source map does not match the selected contract".to_string(),
            )),
            facts: arguments_path.facts,
            obligations: arguments_path.obligations,

            loan_evidence: empty_checked_loan_evidence_sequence(),
        }));
    }
    let mut call_requirement_site = None;
    let initial_obligation_count = arguments_path.obligations.len();
    let path_assumptions = assumptions_with_path_context(
        assumptions,
        &arguments_path.facts,
        &arguments_path.obligations,
    );
    let Some((argument_values, argument_obligations)) = coerce_c_contract_arguments(
        contract_interface,
        &arguments_path.values,
        &arguments_path.obligations,
        &path_assumptions,
    ) else {
        return Ok(Err(CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                contract_argument_binding_error(
                    contract_interface,
                    application.name,
                    &arguments_path.values,
                ),
            )),
            facts: arguments_path.facts,
            obligations: arguments_path.obligations,

            loan_evidence: empty_checked_loan_evidence_sequence(),
        }));
    };
    let Some(mut entry_state) = bind_c_contract_arguments(
        caller_state,
        contract_interface,
        &argument_values,
        application.storage,
    ) else {
        return Ok(Err(CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                contract_argument_binding_error(
                    contract_interface,
                    application.name,
                    &argument_values,
                ),
            )),
            facts: arguments_path.facts,
            obligations: argument_obligations,

            loan_evidence: empty_checked_loan_evidence_sequence(),
        }));
    };
    let path_assumptions =
        assumptions_with_path_context(assumptions, &arguments_path.facts, &argument_obligations);
    if let Some(application) = resource_application {
        entry_state.resource_bindings = Some(application.bindings.clone());
        for parameter in application.parameters.iter() {
            if let Err(error) =
                evaluate_function_resource_spec(&entry_state, parameter, &path_assumptions, budget)?
            {
                return Ok(Err(CFunctionPath {
                    outcome: CFunctionOutcome::RuntimeError(error),
                    facts: arguments_path.facts,
                    obligations: argument_obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),
                }));
            }
        }
    }
    let transfer = match crate::instrumentation::measure_operation(
        application.name,
        "verified function rule application",
        "verified call resource transfer preparation",
        || {
            prepare_contract_resource_transfer(
                caller_state,
                &entry_state,
                application.name,
                contract_interface,
                &path_assumptions,
                budget,
                false,
                ResourceTransitionPurpose::CallSite,
            )
        },
    )? {
        Ok(transfer) => transfer,
        Err(error) => {
            return Ok(Err(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(error),
                facts: arguments_path.facts,
                obligations: argument_obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            }));
        }
    };
    entry_state = callee_state_with_resource_transfer(entry_state, &transfer);
    let entry_contract_state =
        with_contract_interface_argument_views(&entry_state, contract_interface, &argument_values);
    // The callee's pure preconditions are read in the state its entry will
    // hold: the transferred clause set, opened through the composite
    // definitions the way the callee's own entry opens it. A precondition
    // that reads a cell a transferred composite owns (`requires node->left
    // != 0` beside `owns pair(node)`) is then justified by the clause set at
    // the call exactly as at the entry, instead of becoming a caller
    // obligation about a folded composite. The opened context is read here
    // only; the transfer itself keeps the folded heads.
    let precondition_state = if entry_contract_state
        .resources()
        .facts()
        .iter()
        .any(|fact| matches!(fact.resource(), CResource::Composite { .. }))
    {
        let definitions = contract_interface.composite_resource_definitions();
        expand_all_composite_resource_facts(
            entry_contract_state.resources(),
            definitions,
            entry_contract_state.memory(),
            &path_assumptions,
        )
        .map(|opened| {
            let opened = expand_decidable_composite_resource_frontier(
                &opened,
                definitions,
                entry_contract_state.memory(),
                &path_assumptions,
            );
            entry_contract_state.clone().with_resource_context(opened)
        })
        .unwrap_or_else(|| entry_contract_state.clone())
    } else {
        entry_contract_state.clone()
    };
    let mut obligations = argument_obligations;
    let mut facts = arguments_path.facts;
    let mut established_requirements = Vec::new();
    let requirement_timing = crate::instrumentation::OperationTiming::new(
        application.name,
        "verified function rule application",
        "verified call requirement checking",
    );
    for (requirement_ordinal, requirement) in
        contract_interface.contract_requires().iter().enumerate()
    {
        let requirement_assumptions =
            assumptions_with_path_context(&path_assumptions, &facts, &obligations);
        let requirement_assumptions =
            assumptions_with_propositions(&requirement_assumptions, &established_requirements);
        let lowering_assumptions = requirement_assumptions
            .clone()
            .allow_symbolic_contract_loads();
        let mut requirement_source: Option<std::sync::Arc<CallRequirementSource>> = None;
        let source_load_snapshot = std::cell::Cell::new(None);
        let mut source_for_requirement = || {
            if let Some(source) = &requirement_source {
                return source.clone();
            }
            let site = call_requirement_site
                .get_or_insert_with(|| {
                    std::sync::Arc::new(CallRequirementSite::for_requirement(
                        application.name,
                        application.interface_name,
                        candidate_ordinal,
                        source_arguments,
                        &caller_state.memory,
                    ))
                })
                .clone();
            let source = std::sync::Arc::new(CallRequirementSource::new(
                site,
                requirement_ordinal,
                contract_interface
                    .contract_requirement_source(requirement_ordinal)
                    .unwrap_or(None),
                // The interface carries the checked source-map capability;
                // using it keeps this metadata body-independent for named
                // callbacks while matching concrete direct-call metadata.
                contract_interface
                    .contract_requirement_source(requirement_ordinal)
                    .is_some_and(|source_requirement_ordinal| {
                        source_requirement_ordinal.is_some()
                            && spec_proposition_is_state_independent(requirement)
                    }),
                source_load_snapshot.get(),
            ));
            requirement_source = Some(source.clone());
            source
        };
        let requirement_paths = lower_spec_proposition_at_state_with_loop_entry(
            &precondition_state,
            requirement,
            Some(&precondition_state),
            &lowering_assumptions,
            budget,
        )?;
        let mut load_snapshot = None;
        let mut load_snapshot_consistent = true;
        for requirement_path in &requirement_paths {
            let Some(identity) =
                source_load_snapshot_for_proposition(&requirement_path.proposition)?
            else {
                continue;
            };
            if load_snapshot.is_some_and(|known| known != identity) {
                load_snapshot_consistent = false;
            } else {
                load_snapshot = Some(identity);
            }
        }
        if load_snapshot_consistent {
            source_load_snapshot.set(load_snapshot);
        }
        if requirement_paths.is_empty() {
            obligations.push(
                ProofObligation::verification_condition(false_equals_true_proposition())
                    .with_call_requirement_site(source_for_requirement())
                    .with_context(format!("{} precondition", application.name)),
            );
            continue;
        }
        for requirement_path in requirement_paths {
            let path_assumptions = assumptions_with_path_context(
                &requirement_assumptions,
                &requirement_path.facts,
                &requirement_path.obligations,
            );
            for path_obligation in &requirement_path.obligations {
                // The guards this wrap inserts are the obligation's complete
                // recorded head chain: the path obligation under them is a
                // kernel load or overflow condition, which no written
                // connective introduced.
                let (guarded, guard_introductions) = wrap_path_context_with_introductions(
                    path_obligation.proposition().clone(),
                    &requirement_path.facts,
                    &[],
                );
                // Discharge is an exact route or an emitted obligation. A
                // guard the exact routes do not cover is emitted as a
                // required verification condition at the call step,
                // carrying the head chain recorded for it, for the proof
                // side to discharge. The kernel searches for no proof of it.
                // A load the precondition performs is authorized by the
                // clause set the callee receives: the opened transferred
                // context permits the read, so the condition is discharged
                // as it is at the callee's own entry. Only load-shaped
                // conditions are judged this way; the state check answers
                // nothing about any other proposition.
                let load_condition_is_justified = loadability_obligation_shape(
                    path_obligation.proposition(),
                )
                    && super::api::contract_certification::c_state_justifies_loadability_obligation(
                        &precondition_state,
                        &guarded,
                        &requirement_assumptions,
                    );
                if load_condition_is_justified
                    || required_obligation_is_exactly_discharged(&requirement_assumptions, &guarded)
                {
                    super::assumptions::record_reasoning_provenance(
                        &requirement_assumptions,
                        &guarded,
                    );
                } else {
                    let call_requirement_site = source_for_requirement();
                    obligations.push(
                        ProofObligation::verification_condition(guarded.clone())
                            .with_introductions(guard_introductions)
                            .with_call_requirement_site(call_requirement_site.clone())
                            .with_context(format!("{} precondition", application.name)),
                    );
                }
                established_requirements.push(guarded);
            }
            let contract_requirement_is_proven = function_contract_requirement_is_proven(
                &requirement_path.proposition,
                environment,
                budget,
            )?;
            let requirement_is_proven = super::assumptions::capture_implicit_reasoning_provenance(
                || {
                    if contract_requirement_is_proven {
                        return true;
                    }
                    match &requirement_path.proposition {
                            Proposition::ConditionIs(condition, value) => {
                                path_assumptions.proves_exact(&requirement_path.proposition)
                                    || path_assumptions
                                        .has_matching_condition_fact_for_memory_resolution(
                                            condition, *value,
                                        )
                            }
                            Proposition::CResourceSeparate {
                                left: CResource::Memory(left),
                                right: CResource::Memory(right),
                            } => path_assumptions.proves_exact(&requirement_path.proposition)
                                || path_assumptions
                                    .memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
                                        left, right,
                                    ),
                            proposition => path_assumptions.proves_exact(proposition),
                        }
                },
            );
            if requirement_is_proven {
                super::assumptions::record_reasoning_provenance(
                    &path_assumptions,
                    &requirement_path.proposition,
                );
            }
            // The guards this wrap inserts, then the head chain the
            // requirement's own lowering recorded. The record comes from the
            // lowering that produced the obligation, so an introduction on
            // it reaches a hidden guard exactly as on a lowered goal.
            let requirement_introductions = requirement_path.introductions;
            let (guarded_requirement, guards) = wrap_path_context_with_introductions(
                requirement_path.proposition,
                &requirement_path.facts,
                &requirement_path.obligations,
            );
            let mut introductions = guards;
            introductions.extend(requirement_introductions);
            if !requirement_is_proven {
                // Same rule as the guard above: exact routes, then an
                // emitted required verification condition. The general
                // prover decides no precondition.
                if required_obligation_is_exactly_discharged(
                    &requirement_assumptions,
                    &guarded_requirement,
                ) {
                    super::assumptions::record_reasoning_provenance(
                        &requirement_assumptions,
                        &guarded_requirement,
                    );
                } else {
                    let call_requirement_site = source_for_requirement();
                    obligations.push(
                        ProofObligation::verification_condition(guarded_requirement.clone())
                            .with_introductions(introductions)
                            .with_call_requirement_site(call_requirement_site.clone())
                            .with_context(format!("{} precondition", application.name)),
                    );
                }
            }
            established_requirements.push(guarded_requirement);
        }
    }
    drop(requirement_timing);

    // Applicability is determined entirely at entry. In particular, pending
    // obligations must not be assumed to authorize this interface's effects
    // or make its guarantees available to another candidate.
    if require_established && obligations.len() != initial_obligation_count {
        return Ok(Err(CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                "no callback contract has established preconditions".to_string(),
            )),
            facts,
            obligations,

            loan_evidence: empty_checked_loan_evidence_sequence(),
        }));
    }

    // A self-call inside the certification of a function that declares an
    // expression `decreases` measure owes the descent, after the callee's
    // preconditions and read at the same state they were read at: the
    // callee's parameters hold this call's arguments there, and a measure
    // that reads memory sees the memory the callee will see. The obligations
    // are ordinary verification conditions on this path, so a proof that does
    // not discharge them does not get past the step, and an undischarged one
    // is a premise of the path theorem.
    //
    // The anchor names one function and is installed only for the function
    // being certified, so an ordinary call to another verified function is
    // untouched, and so is every function that declares no measure. It is
    // placed after the applicability gate above so a callback candidate is
    // still selected by its preconditions alone.
    if let Some(anchor) = environment.recursion_anchor()
        && anchor.function() == application.name
    {
        // The measure ranked here is the one the anchor was derived from, so
        // the two states being compared are readings of one declared object.
        // An interface applied under this name that declares a different
        // measure is refused rather than ranked by the wrong one.
        if contract_interface.recursion_measure() != Some(anchor.component()) {
            obligations.push(
                ProofObligation::verification_condition(false_equals_true_proposition())
                    .with_context(format!(
                        "the contract applied for the recursive call to `{}` declares a different \
                         `decreases` measure than the one being certified",
                        application.name
                    )),
            );
        } else {
            let descent_assumptions =
                assumptions_with_path_context(&path_assumptions, &facts, &obligations);
            match crate::kernel::termination::collect_recursion_descent_obligations(
                anchor,
                &precondition_state,
                &descent_assumptions,
                budget,
            ) {
                Ok(descent) => obligations.extend(descent),
                // A measure with no value at the call state is a proof failure
                // at the call, never a silently skipped descent.
                Err(message) => obligations.push(
                    ProofObligation::verification_condition(false_equals_true_proposition())
                        .with_context(message),
                ),
            }
        }
    }

    let call_entry_assumptions = assumptions_with_path_context(assumptions, &facts, &obligations);
    let effective_assumptions =
        assumptions_with_propositions(&call_entry_assumptions, &established_requirements)
            .transport_memory_load_condition_facts();

    if let Some(function) = application.evidence
        && let Some(undefined_behavior) = verified_call_uninitialized_read(
            &entry_contract_state,
            function,
            &call_entry_assumptions.transport_memory_load_condition_facts(),
            budget,
        )?
    {
        return Ok(Err(CFunctionPath {
            outcome: CFunctionOutcome::UndefinedBehavior(undefined_behavior),
            facts,
            obligations,

            loan_evidence: empty_checked_loan_evidence_sequence(),
        }));
    }

    let footprint_state = entry_contract_state.clone();
    let footprint_timing = crate::instrumentation::OperationTiming::new(
        application.name,
        "verified function rule application",
        "verified call mutable footprint lowering",
    );
    // Reassemble the transition in source order from its role partitions.
    // This keeps the effect projection tied to the checked role-bearing
    // inputs rather than to a normalized context that erased provenance.
    let mut checked_transition_inputs = transfer.borrowed_inputs.clone();
    checked_transition_inputs.extend(transfer.consumed_inputs.clone());
    checked_transition_inputs.sort_by_key(|checked| checked.clause_position);
    let projection = match project_contract_memory_effects(
        &footprint_state,
        contract_interface,
        Some(&checked_transition_inputs),
        &effective_assumptions,
        budget,
    )? {
        Ok(projection) => projection,
        Err(message) => {
            return Ok(Err(CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                    "could not evaluate mutable footprint: {message}"
                ))),
                facts,
                obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            }));
        }
    };
    // The joint transfer planner has already proved that every mutable input
    // is disjoint from each lent range. Preserve that precise footprint here;
    // rejecting all mutation would also reject the supported viewed-field /
    // owned-field partition.
    let mutable_ranges = projection.ranges;
    let projection_range_sources = projection.range_sources;
    {
        // Compare the effects against the complete checked view frontier, not
        // just the views whose requirement is a plain memory range. A
        // composite view's bytes are its checked one-level pieces, and the
        // intrinsic and empty-composite views never reach the planner at
        // all; the transfer carries both groups for exactly this check.
        //
        // The pair is read by provenance first. A valid resource context is a
        // partition, so an effect reserved out of one owned occurrence and a
        // view lent from a different one are bytewise disjoint by
        // construction; asking the arithmetic oracle about two symbolic
        // ranges it cannot order would refuse what the caller's own partition
        // already settles. Only an effect and a view drawn from the *same*
        // occurrence -- a partial borrow of one owner (D8) -- still need the
        // arithmetic proof, and a range with no provenance on either side
        // always does.
        let reserved_effect_supports = transfer
            .stable_view_plan
            .as_ref()
            .map(|plan| {
                reserved_effect_support_index(
                    &projection_range_sources,
                    &plan.reserved_ownership_supports,
                )
            })
            .unwrap_or_default();
        let viewed_ranges = transfer
            .stable_view_plan
            .as_ref()
            .map(StableViewTransferPlan::stable_views)
            .unwrap_or_default()
            .iter()
            .filter_map(|stable_view| {
                Some((
                    stable_view.requirement.fact.memory_range()?,
                    Some(stable_view.support),
                ))
            })
            .chain(
                transfer
                    .checked_view_frontier
                    .iter()
                    .map(|(range, support)| (range, *support)),
            );
        for (viewed_range, viewed_support) in viewed_ranges {
            if let Some((mutable_range, relation)) = mutable_ranges
                .iter()
                .filter(|mutable_range| {
                    !effect_is_disjoint_from_view_by_provenance(
                        &reserved_effect_supports,
                        mutable_range,
                        viewed_support,
                    )
                })
                .map(|mutable_range| {
                    (
                        mutable_range,
                        candidate_memory_ranges_relation(
                            mutable_range,
                            viewed_range,
                            &effective_assumptions,
                        ),
                    )
                })
                .find(|(_, relation)| *relation != CandidateMemoryRangeRelation::Disjoint)
            {
                let subject = LoanRefusalSubject::with_range(mutable_range.clone());
                let diagnostic = match relation {
                    CandidateMemoryRangeRelation::Overlap => LoanRefusal::ActiveDependency
                        .proven_overlap_diagnostic(LoanRefusalOperation::MemoryAccess, subject),
                    CandidateMemoryRangeRelation::SeparationUnproved => {
                        LoanRefusal::UnsupportedPartition
                            .diagnostic_with_subject(LoanRefusalOperation::MemoryAccess, subject)
                    }
                    CandidateMemoryRangeRelation::Disjoint => unreachable!(),
                };
                return Ok(Err(CFunctionPath {
                    outcome: CFunctionOutcome::RuntimeError(CRuntimeError::LoanRefusal(diagnostic)),
                    facts,
                    obligations,
                    loan_evidence: empty_checked_loan_evidence_sequence(),
                }));
            }
        }
    }
    for fact in projection.evidence_facts {
        if !facts.contains(&fact) {
            facts.push(fact);
        }
    }
    drop(footprint_timing);
    // The projection above is also retained on the transition record below;
    // no later call path reconstructs the footprint from source clauses.
    let mut transfer = transfer;
    transfer.memory_effects = mutable_ranges.clone();
    // A direct store into read-only storage is rejected where it is
    // executed, but a modular call performs its writes abstractly through
    // this footprint. Without the same check, passing read-only storage to
    // a callee that declares it mutable would let the call store there:
    // string-literal bytes are the reachable case, since C0 models a
    // literal as an ordinary `uint8*` and no qualifier catches it.
    if let Some(range) = mutable_ranges
        .iter()
        .find(|range| entry_state.memory.is_read_only_block(&range.base().block))
    {
        return Ok(Err(CFunctionPath {
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                "mutable footprint covers read-only storage `{}`",
                range.base().block
            ))),
            facts,
            obligations,

            loan_evidence: empty_checked_loan_evidence_sequence(),
        }));
    }

    Ok(Ok(PreparedVerifiedFunctionCall {
        name: application.name,
        interface_name: application.interface_name,
        storage: application.storage,
        evidence: application.evidence,
        interface: contract_interface,
        argument_values,
        entry_state,
        entry_contract_state,
        transfer,
        facts,
        obligations,
        effective_assumptions,
        bindings: resource_application.map(|application| application.bindings.clone()),
    }))
}

pub(super) fn execute_c_function_contracts_paths(
    caller_state: &CState,
    contracts: &[&CFunctionContract],
    arguments: &[CExpression],
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CFunctionPath>> {
    let selected = environment.selected_call_contract.as_deref();
    let contracts = contracts
        .iter()
        .copied()
        .filter(|contract| {
            contract.proof_parameters().is_empty() || selected == Some(contract.name())
        })
        .collect::<Vec<_>>();
    if contracts.is_empty() {
        return Ok(vec![resource_call_failure(
            "resource contract requires explicit proof arguments",
        )]);
    }
    let selected_index = selected.and_then(|name| {
        contracts
            .iter()
            .position(|contract| contract.name() == name)
    });
    if selected.is_some() && selected_index.is_none() {
        return Ok(vec![resource_call_failure(
            "selected contract is not available at this call",
        )]);
    }
    let resource_application = if let Some(index) = selected_index {
        let contract = contracts[index];
        let arguments = environment
            .selected_call_resource_arguments
            .as_deref()
            .unwrap_or(&[]);
        if arguments.len() != contract.proof_parameters().len() {
            return Ok(vec![resource_call_failure(
                "resource contract proof argument arity mismatch",
            )]);
        }
        let mut bindings = BTreeMap::new();
        for (parameter, argument) in contract.proof_parameters().iter().zip(arguments) {
            let Some(identity) = parameter.instance_identity() else {
                return Ok(vec![resource_call_failure(
                    "resource proof parameter must be an exclusive instance",
                )]);
            };
            if bindings.insert(identity, *argument).is_some() {
                return Ok(vec![resource_call_failure(
                    "duplicate exclusive resource proof argument",
                )]);
            }
        }
        match ResourceCallApplication::bind(
            contract.proof_parameters().to_vec(),
            std::sync::Arc::new(bindings),
            caller_state,
        ) {
            Ok(application) => Some(application),
            Err(message) => return Ok(vec![resource_call_failure(message)]),
        }
    } else {
        None
    };
    let applications = contracts
        .iter()
        .map(|contract| CFunctionContractApplication {
            name: contract.callee_name(),
            interface_name: contract.name(),
            interface: contract.interface(),
            storage: None,
            evidence: None,
            representation_copy: None,
        })
        .collect::<Vec<_>>();
    execute_verified_function_applications(
        caller_state,
        &applications,
        selected_index,
        selected_index.zip(resource_application.as_ref()),
        arguments,
        assumptions,
        environment,
        budget,
    )
}

#[derive(Debug)]
struct ResourceCallApplication {
    parameters: std::sync::Arc<[CResourceSpec]>,
    bindings: std::sync::Arc<BTreeMap<Variable, Variable>>,
}

impl ResourceCallApplication {
    /// The one checked binding of a callee's instance binders to the caller's
    /// instances, whether the proof wrote a direct call map
    /// (`step(callee(...), { binder: instance })`) or a named contract's
    /// proof arguments (`step(Contract(instance, ...))`). Each bound
    /// parameter must be an exclusive instance the caller owns now, and no
    /// instance may supply two parameters. The surface refuses both mistakes
    /// with source positions; the kernel refuses them here regardless, so a
    /// transport it did not see cannot bind what the proof state lacks. A
    /// binder the map omits is refused by the application engine, which
    /// checks completeness against the interface.
    fn bind(
        parameters: Vec<CResourceSpec>,
        bindings: std::sync::Arc<BTreeMap<Variable, Variable>>,
        caller_state: &CState,
    ) -> Result<Self, &'static str> {
        let mut actuals = BTreeSet::new();
        for parameter in &parameters {
            crate::instrumentation::record_deterministic_work(1);
            let Some(identity) = parameter.instance_identity() else {
                return Err("resource proof parameter must be an exclusive instance");
            };
            let Some(actual) = bindings.get(&identity) else {
                continue;
            };
            if caller_state.owned_resource_instance(*actual).is_none() {
                return Err("resource proof argument is not owned");
            }
            if !actuals.insert(*actual) {
                return Err("duplicate exclusive resource proof argument");
            }
        }
        Ok(Self {
            parameters: parameters.into(),
            bindings,
        })
    }
}

/// Whether an obligation is a load condition, possibly under the premises a
/// lowering path recorded: the only shape the opened-clause-set discharge of
/// a call precondition applies to.
fn loadability_obligation_shape(proposition: &Proposition) -> bool {
    match proposition {
        Proposition::CMemoryLoadable { .. } => true,
        Proposition::Implies(_, body) => loadability_obligation_shape(body),
        Proposition::And(left, right) => {
            loadability_obligation_shape(left) && loadability_obligation_shape(right)
        }
        _ => false,
    }
}

fn resource_call_failure(message: &str) -> CFunctionPath {
    CFunctionPath {
        outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(message.into())),
        facts: vec![],
        obligations: vec![],

        loan_evidence: empty_checked_loan_evidence_sequence(),
    }
}

fn function_contract_requirement_is_proven(
    proposition: &Proposition,
    environment: &CExecutionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    match proposition {
        Proposition::And(left, right) => {
            Ok(
                function_contract_requirement_is_proven(left, environment, budget)?
                    && function_contract_requirement_is_proven(right, environment, budget)?,
            )
        }
        Proposition::Predicate { name, arguments } => {
            let Some(contract_name) = CFunctionContract::surface_name_from_predicate(name) else {
                return Ok(false);
            };
            let [Term::CState(_), Term::CValue(CValue::Pointer(pointer))] = arguments.as_slice()
            else {
                return Ok(false);
            };
            let Pointer {
                block: PointerBlock::Function(target),
                offset: PointerOffsetTerm::Constant(0),
            } = pointer.pointer()
            else {
                return Ok(false);
            };
            let Some(contract) = environment.get_function_contract(contract_name) else {
                return Ok(false);
            };
            if pointer.c_type() != contract.function_pointer_type() {
                return Ok(false);
            }
            if let Some(rule) = environment.get_verified_function_rule(target) {
                return function_refines_named_contract(contract, &rule.function, budget);
            }
            let Some(rule) = environment.get_external_function_rule(target) else {
                return Ok(false);
            };
            function_refines_named_contract(contract, &rule.function, budget)
        }
        _ => Ok(false),
    }
}

/// Prints the explicit refinement theorem that automatic formation could not
/// replace, with every slot filled from the two declarations the check read.
///
/// The skeleton is the expand affordance of the automatic route. It is built
/// from the same `CFunctionContract` and `CFunction` interfaces the check
/// uses — the target's proof parameters, the implementation's binders, and
/// the implementation's C parameter list — so the printed obligation cannot
/// drift from the one that was refused. A target with no proof parameters
/// gets the `unfold(Name)` form, which is the route that already exists.
///
/// `declared_parameter_spellings` carries, per parameter position, the C
/// spelling the caller's source declaration uses where this interface cannot
/// reconstruct it: an aggregate pointer is a layout here, not a struct tag,
/// so `struct node*` would print as the pointer type it is modeled by. The
/// caller supplies the tag rather than the kernel storing one; a position
/// without a supplied spelling keeps this interface's own.
pub(super) fn named_contract_refinement_theorem_skeleton(
    contract: &CFunctionContract,
    function: &CFunction,
    declared_parameter_spellings: &[Option<String>],
) -> String {
    let theorem = format!(
        "{}_is_{}",
        function.name(),
        snake_case_contract_name(contract.name())
    );
    let parameters = function
        .parameters()
        .iter()
        .enumerate()
        .map(|(index, parameter)| {
            let spelling = declared_parameter_spellings
                .get(index)
                .and_then(Option::as_deref)
                .map(str::to_string)
                .unwrap_or_else(|| c_parameter_type_spelling(parameter));
            format!("{spelling} {}", parameter.name())
        })
        .collect::<Vec<_>>()
        .join(", ");
    let target_binders = declared_instance_binder_names(&[contract.proof_parameters()]);
    if target_binders.is_empty() {
        return format!(
            "theorem {theorem}() {{\n    \
             ensures {contract}(&{function}) by {{\n        \
             unfold({contract});\n        \
             simp();\n    \
             }}\n\
             }}",
            contract = contract.name(),
            function = function.name(),
        );
    }
    let implementation_binders = declared_instance_binder_names(&[
        function.resource_requires(),
        function.resource_ensures(),
    ]);
    let introduced =
        introduced_instance_names(target_binders.len().max(implementation_binders.len()));
    let map = |binders: &[String]| {
        binders
            .iter()
            .zip(&introduced)
            .map(|(binder, name)| format!("{binder}: {name}"))
            .collect::<Vec<_>>()
            .join(", ")
    };
    let arguments = function
        .parameters()
        .iter()
        .map(|parameter| parameter.name().to_string())
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "theorem {theorem}() executes {function}({parameters}) {{\n    \
         ensures {contract}(&{function}) as {{ {target} }} by {{\n        \
         step({function}({arguments}), {{ {implementation} }});\n        \
         simp();\n    \
         }}\n\
         }}",
        contract = contract.name(),
        function = function.name(),
        target = map(&target_binders),
        implementation = map(&implementation_binders),
    )
}

/// The binder spellings a declaration introduces, in declaration order, once
/// per identity.
fn declared_instance_binder_names(specs: &[&[CResourceSpec]]) -> Vec<String> {
    let mut seen = BTreeSet::new();
    let mut names = Vec::new();
    for spec in specs.iter().flat_map(|specs| specs.iter()) {
        let Some(identity) = spec.instance_identity() else {
            continue;
        };
        if seen.insert(identity) {
            names.push(spec.instance_binder().unwrap_or_default().to_string());
        }
    }
    names
}

/// Fresh names for the instances the theorem introduces. One instance is
/// `r`; several are numbered so the two maps can name the same instance.
fn introduced_instance_names(count: usize) -> Vec<String> {
    if count == 1 {
        return vec!["r".to_string()];
    }
    (1..=count).map(|index| format!("r{index}")).collect()
}

fn snake_case_contract_name(name: &str) -> String {
    let mut snake = String::with_capacity(name.len() + 4);
    for (index, character) in name.char_indices() {
        if character.is_uppercase() && index != 0 {
            snake.push('_');
        }
        snake.extend(character.to_lowercase());
    }
    snake
}

/// The C0 spelling of a parameter's declared type.
///
/// Struct tags are not part of the kernel interface: an aggregate parameter
/// keeps its layout, not the tag its source wrote, so a pointer to one is
/// spelled by its pointer type. The skeleton is source the user edits, and
/// this is the one slot they may have to correct.
fn c_parameter_type_spelling(parameter: &CParameter) -> String {
    let base = match parameter.c_type() {
        CType::Void => "void",
        CType::Bool => "bool",
        CType::VoidPointer => "void*",
        CType::VoidPointerPointer => "void**",
        CType::Int16 => "int16",
        CType::Int32 => "int32",
        CType::UInt8 => "uint8",
        CType::UInt16 => "uint16",
        CType::UInt32 => "uint32",
        CType::Int64 => "int64",
        CType::UInt64 => "uint64",
        CType::Float32 => "float32",
        CType::Float64 => "float64",
        CType::Int16Pointer => "int16*",
        CType::UInt16Pointer => "uint16*",
        CType::Int32Pointer => "int32*",
        CType::UInt8Pointer => "uint8*",
        CType::UInt32Pointer => "uint32*",
        CType::Int64Pointer => "int64*",
        CType::UInt64Pointer => "uint64*",
        CType::Float32Pointer => "float32*",
        CType::Float64Pointer => "float64*",
        CType::Int16PointerPointer => "int16**",
        CType::UInt16PointerPointer => "uint16**",
        CType::Int32PointerPointer => "int32**",
        CType::UInt8PointerPointer => "uint8**",
        CType::UInt32PointerPointer => "uint32**",
        CType::Int64PointerPointer => "int64**",
        CType::UInt64PointerPointer => "uint64**",
        CType::Float32PointerPointer => "float32**",
        CType::Float64PointerPointer => "float64**",
        CType::FunctionPointer(_) => "void (*)()",
        CType::Int16Array(_) => "int16*",
        CType::Int32Array(_) => "int32*",
        CType::UInt8Array(_) => "uint8*",
        CType::UInt16Array(_) => "uint16*",
        CType::UInt32Array(_) => "uint32*",
        CType::Int64Array(_) => "int64*",
        CType::UInt64Array(_) => "uint64*",
        CType::Float32Array(_) => "float32*",
        CType::Float64Array(_) => "float64*",
    };
    if parameter.pointee_is_constant() {
        format!("const {base}")
    } else {
        base.to_string()
    }
}

/// Proves behavioral callback refinement. Exact matching remains the fast
/// path. The semantic path checks framed memory, abstract-token, and folded
/// composite resource transitions and effect containment, instantiates both
/// interfaces with the same symbolic arguments, then checks preconditions
/// contravariantly and postconditions covariantly. Concrete resource needs and
/// mutable ranges may be narrower than the named contract's upper bounds.
/// Stateful refinement is deliberately limited to memory propositions backed
/// by a nonempty resource transition and unguarded named mutable footprint.
fn function_refines_named_contract(
    contract: &CFunctionContract,
    function: &CFunction,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    if contract.exactly_matches(function) {
        return Ok(true);
    }
    if !contract.has_same_predicate_unfoldings(function) {
        return Ok(false);
    }
    let Some(context) = prepare_automatic_contract_refinement_context(contract, function, budget)
    else {
        return Ok(false);
    };
    function_refines_named_contract_in_case(&context, &[], &BTreeSet::new(), false, budget)
}

pub(super) fn prepare_function_contract_refinement_context(
    contract: &CFunctionContract,
    function: &CFunction,
    budget: &mut ExecutionBudget,
) -> Option<CFunctionContractRefinementContext> {
    if !contract.has_compatible_signature_and_resource_vocabulary(function) {
        return None;
    }
    contract_refinement_context_for_checked_interfaces(contract, function, budget)
}

/// The concrete-pointer formation route's context.
///
/// It differs from the explicit route only in admitting a target that
/// declares proof parameters. The instances those parameters stand for are
/// introduced by [`function_refines_named_contract_in_case`], and only when
/// the binding between the two declarations is forced.
fn prepare_automatic_contract_refinement_context(
    contract: &CFunctionContract,
    function: &CFunction,
    budget: &mut ExecutionBudget,
) -> Option<CFunctionContractRefinementContext> {
    if !contract.has_compatible_signature_and_composite_vocabulary(function) {
        return None;
    }
    contract_refinement_context_for_checked_interfaces(contract, function, budget)
}

fn contract_refinement_context_for_checked_interfaces(
    contract: &CFunctionContract,
    function: &CFunction,
    budget: &mut ExecutionBudget,
) -> Option<CFunctionContractRefinementContext> {
    contract_refinement_context_for_interface(
        contract,
        function.name(),
        function.contract_interface(),
        budget,
    )
}

pub(super) fn contract_refinement_context_for_interface(
    contract: &CFunctionContract,
    function_name: &str,
    function_interface: &CFunctionContractInterface,
    budget: &mut ExecutionBudget,
) -> Option<CFunctionContractRefinementContext> {
    let mut argument_values = Vec::with_capacity(function_interface.parameters().len());
    for parameter in function_interface.parameters() {
        let variable = budget.allocate_kernel_variable().ok()?;
        argument_values.push(symbolic_call_result(parameter.c_type(), variable));
    }
    let result_variable = budget.allocate_kernel_variable().ok()?;
    Some(CFunctionContractRefinementContext {
        contract: contract.clone(),
        function_interface: function_interface.clone(),
        function_name: function_name.to_string(),
        pointer: CPointerValue::new(
            Pointer {
                block: PointerBlock::Function(function_name.to_string()),
                offset: PointerOffsetTerm::Constant(0),
            },
            contract.function_pointer_type(),
        ),
        source_contract: None,
        argument_values,
        result_variable,
        next_kernel_variable: budget.next_kernel_variable(),
    })
}

pub(super) fn function_contract_refinement_entry_state(
    context: &CFunctionContractRefinementContext,
) -> CState {
    with_contract_interface_argument_views(
        &CState::new(),
        &context.contract.interface,
        &context.argument_values,
    )
}

pub(super) fn prepare_contract_refinement_obligations(
    context: &CFunctionContractRefinementContext,
) -> Option<CFunctionContractRefinementObligations> {
    let target = context.contract.interface();
    let source = &context.function_interface;
    let mut budget = ExecutionBudget::continuing_from(context.next_kernel_variable);
    let entry = function_contract_refinement_entry_state(context);
    let source_entry =
        with_contract_interface_argument_views(&CState::new(), source, &context.argument_values);
    let mut assumptions = PureFactContext::new();
    if !assume_contract_propositions(
        &entry,
        &entry,
        target.contract_requires(),
        &mut assumptions,
        &mut budget,
    )
    .ok()?
    {
        return None;
    }
    // A single conservative post memory covers every possible source write.
    // This does not enumerate guard combinations or assert that a guarded
    // write happened. Resource/effect containment is checked independently.
    let ranges = evaluate_contract_mutable_ranges_for_interface(
        source,
        &source_entry,
        &assumptions,
        &mut budget,
        false,
    )
    .ok()??;
    let memory = entry.memory().clone().with_call_memory_havoc(
        budget.allocate_kernel_variable().ok()?,
        &ranges,
        &assumptions,
    );
    let result = symbolic_call_result(source.return_type(), context.result_variable);
    let mut post = entry.clone().with_memory(memory.clone());
    let mut source_post = source_entry.clone().with_memory(memory);
    if source.return_type() != CType::Void {
        set_contract_result(&mut post, target, result.clone());
        set_contract_result(&mut source_post, source, result);
    }
    if !compatible_resource_and_effect_interfaces(
        target,
        source,
        &entry,
        &source_entry,
        &post,
        &source_post,
        &assumptions,
        &mut budget,
    )
    .ok()?
    {
        return None;
    }
    fn conjunction(items: Vec<Proposition>) -> Proposition {
        items
            .into_iter()
            .reduce(|a, b| Proposition::And(Box::new(a), Box::new(b)))
            .unwrap_or(Proposition::ConditionIs(
                ConditionTerm::Constant(true),
                true,
            ))
    }
    fn lower(
        interface: &CFunctionContractInterface,
        specs: &[SpecProposition],
        state: &CState,
        entry: &CState,
        budget: &mut ExecutionBudget,
    ) -> Option<Proposition> {
        let definitions = interface
            .predicate_unfoldings()
            .iter()
            .map(|definition| (definition.body(), definition.predicate()))
            .collect::<BTreeMap<_, _>>();
        let mut propositions = Vec::new();
        for spec in specs {
            let spec = definitions.get(spec).copied().unwrap_or(spec);
            let paths = lower_spec_proposition_at_state_with_loop_entry(
                state,
                spec,
                Some(entry),
                &PureFactContext::new(),
                budget,
            )
            .ok()?;
            let [path] = paths.as_slice() else {
                return None;
            };
            // Lowering facts name reads and other definitional intermediates;
            // they are not clauses of either callback contract. Both sides
            // use the same kernel load identities in these fixed memories.
            propositions.extend(
                path.obligations
                    .iter()
                    .map(|obligation| obligation.proposition().clone()),
            );
            propositions.push(path.proposition.clone());
        }
        Some(conjunction(propositions))
    }
    let target_requires = lower(
        target,
        target.contract_requires(),
        &entry,
        &entry,
        &mut budget,
    )?;
    let source_requires = lower(
        source,
        source.contract_requires(),
        &source_entry,
        &source_entry,
        &mut budget,
    )?;
    let source_ensures = lower(
        source,
        source.contract_ensures(),
        &source_post,
        &source_entry,
        &mut budget,
    )?;
    let target_ensures = lower(
        target,
        target.contract_ensures(),
        &post,
        &entry,
        &mut budget,
    )?;
    let proposition = Proposition::Implies(
        Box::new(target_requires),
        Box::new(Proposition::And(
            Box::new(source_requires),
            Box::new(Proposition::Implies(
                Box::new(source_ensures),
                Box::new(target_ensures),
            )),
        )),
    );
    Some(CFunctionContractRefinementObligations {
        entry,
        post,
        proposition,
    })
}

/// One forced pair of resource declarations: a target contract proof
/// parameter and the implementation binder that must stand for it. Both sides
/// read the same instance identity, so `root.model` on the named side and
/// `t.model` on the implementation side lower to the same term.
struct RefinementInstanceBinding {
    target_identity: Variable,
    implementation_identity: Variable,
    entry: ResourceInstance,
    post: ResourceInstance,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum RefinementSide {
    Target,
    Implementation,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum RefinementPhase {
    Entry,
    Post,
}

/// One declared instance binder, with its family evaluated at the state that
/// declares it.
struct DeclaredResourceInstance {
    identity: Variable,
    family: String,
    schema: ResourceFieldSchema,
    arguments: ResourceArguments,
}

/// Collects the instance binders a declaration names, in declaration order,
/// once per identity. `owns` states the same binder in `requires` and
/// `ensures`; the pair is one binder, not two.
fn evaluate_declared_resource_instances(
    specs: &[&[CResourceSpec]],
    state: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<Vec<DeclaredResourceInstance>>> {
    let mut seen = BTreeSet::new();
    let mut declared = Vec::new();
    for spec in specs.iter().flat_map(|specs| specs.iter()) {
        let Some(identity) = spec.instance_identity() else {
            continue;
        };
        if !seen.insert(identity) {
            continue;
        }
        let Some(schema) = spec.instance_schema() else {
            continue;
        };
        let Some(resource) = spec.instance_resource_spec() else {
            continue;
        };
        let instance = match evaluate_function_resource_spec(state, &resource, assumptions, budget)?
        {
            Ok(CResourceFact::Own(CResource::Composite { name, arguments }, quantity))
                if quantity.as_const() == Some(1) =>
            {
                DeclaredResourceInstance {
                    identity,
                    family: name,
                    schema: schema.clone(),
                    arguments,
                }
            }
            Ok(_) | Err(_) => return Ok(None),
        };
        declared.push(instance);
    }
    Ok(Some(declared))
}

/// Indexes declared binders by resource family. A family that appears twice
/// on one side leaves the binding unforced, so its entry is poisoned rather
/// than ranked.
fn index_declared_instances_by_family(
    declared: &[DeclaredResourceInstance],
) -> Option<BTreeMap<&str, &DeclaredResourceInstance>> {
    let mut index = BTreeMap::new();
    for instance in declared {
        if index.insert(instance.family.as_str(), instance).is_some() {
            return None;
        }
    }
    Some(index)
}

/// Pairs the target contract's proof parameters with the implementation's
/// binders when exactly one pairing is possible, and instantiates one shared
/// instance per pair.
///
/// The pairing is a map lookup per binder: each side is indexed by resource
/// family once, a repeated family on either side refuses, and the two indexes
/// must have the same keys. No candidate is searched, scored, or preferred.
///
/// Each pair gets one entry instance with arbitrary fields, shared by both
/// entry states, and one post instance with fresh arbitrary fields, shared by
/// both post states. Fresh post fields are the same rule an ordinary call
/// applies to returned ownership: the identity survives, the field values do
/// not, and only the implementation's guarantees relate the two.
fn forced_refinement_instance_bindings(
    contract: &CFunctionContractInterface,
    function: &CFunctionContractInterface,
    contract_entry: &CState,
    function_entry: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<Vec<RefinementInstanceBinding>>> {
    let Some(target) = evaluate_declared_resource_instances(
        &[contract.proof_parameters()],
        contract_entry,
        assumptions,
        budget,
    )?
    else {
        return Ok(None);
    };
    let Some(implementation) = evaluate_declared_resource_instances(
        &[function.resource_requires(), function.resource_ensures()],
        function_entry,
        assumptions,
        budget,
    )?
    else {
        return Ok(None);
    };
    if target.is_empty() && implementation.is_empty() {
        return Ok(Some(Vec::new()));
    }
    let (Some(target_index), Some(implementation_index)) = (
        index_declared_instances_by_family(&target),
        index_declared_instances_by_family(&implementation),
    ) else {
        return Ok(None);
    };
    if target_index.len() != implementation_index.len() {
        return Ok(None);
    }
    let mut bindings = Vec::with_capacity(target_index.len());
    for (family, target) in &target_index {
        let Some(implementation) = implementation_index.get(family) else {
            return Ok(None);
        };
        if target.schema != implementation.schema
            || target.arguments.len() != implementation.arguments.len()
            || !target
                .arguments
                .iter()
                .zip(implementation.arguments.iter())
                .all(|(left, right)| {
                    crate::kernel::resource_arguments_proven_equal(left, right, assumptions)
                })
        {
            return Ok(None);
        }
        let identity = budget.allocate_kernel_variable()?;
        let instance = |budget: &mut ExecutionBudget| -> ExecutionResult<ResourceInstance> {
            let fields = arbitrary_resource_instance_fields(&target.schema, budget)?;
            Ok(ResourceInstance::new(
                identity,
                target.family.clone(),
                target.arguments.clone(),
                target.schema.clone(),
                fields,
            )
            .expect("arbitrary fields have their declared types"))
        };
        bindings.push(RefinementInstanceBinding {
            target_identity: target.identity,
            implementation_identity: implementation.identity,
            entry: instance(budget)?,
            post: instance(budget)?,
        });
    }
    Ok(Some(bindings))
}

/// An arbitrary model field of `field_type` named by `variable`.
pub(super) fn resource_instance_field_value(
    field_type: &ResourceFieldType,
    variable: Variable,
) -> AlgebraicValue {
    match field_type {
        ResourceFieldType::Integer => AlgebraicValue::Integer(IntegerTerm::Variable(variable)),
        ResourceFieldType::C(c_type) => AlgebraicValue::C(symbolic_call_result(*c_type, variable)),
        ResourceFieldType::Algebraic(algebraic_type) => AlgebraicValue::Algebraic(AlgebraicTerm {
            algebraic_type: algebraic_type.clone(),
            node: AlgebraicTermNode::Variable(variable),
        }),
    }
}

/// An arbitrary model for one instance, drawn through `variables` so the
/// fields avoid everything that stream reserves as well as everything else
/// the budget has issued.
pub(super) fn fresh_resource_instance_fields(
    schema: &ResourceFieldSchema,
    variables: &mut KernelVariableGenerator,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<ResourceArguments> {
    let mut fields = Vec::with_capacity(schema.fields().len());
    for (_, field_type) in schema.fields() {
        fields.push(resource_instance_field_value(
            field_type,
            variables.next_in(budget)?,
        ));
    }
    Ok(fields.into_iter().collect())
}

pub(super) fn arbitrary_resource_instance_fields(
    schema: &ResourceFieldSchema,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<ResourceArguments> {
    let mut fields = Vec::with_capacity(schema.fields().len());
    for (_, field_type) in schema.fields() {
        fields.push(resource_instance_field_value(
            field_type,
            budget.allocate_kernel_variable()?,
        ));
    }
    Ok(fields.into_iter().collect())
}

/// Installs the shared instances one side reads, under the identities that
/// side's declaration wrote.
fn state_with_refinement_instances(
    state: &CState,
    bindings: &[RefinementInstanceBinding],
    side: RefinementSide,
    phase: RefinementPhase,
    assumptions: &PureFactContext,
) -> Option<CState> {
    if bindings.is_empty() {
        return Some(state.clone());
    }
    let mut state = state.clone();
    let mut names = BTreeMap::new();
    let mut facts = Vec::with_capacity(bindings.len());
    for binding in bindings {
        let declared = match side {
            RefinementSide::Target => binding.target_identity,
            RefinementSide::Implementation => binding.implementation_identity,
        };
        let instance = match phase {
            RefinementPhase::Entry => &binding.entry,
            RefinementPhase::Post => &binding.post,
        };
        names.insert(declared, instance.identity());
        facts.push(CResourceFact::own(CResource::Instance(instance.clone())));
    }
    state.resource_bindings = Some(std::sync::Arc::new(names));
    state.resources = state
        .resources
        .clone()
        .try_compose_into_valid_context_delaying_normalization(facts, assumptions)
        .ok()?;
    Some(state)
}

fn function_refines_named_contract_in_case(
    context: &CFunctionContractRefinementContext,
    case_assumptions: &[Proposition],
    unfolded_predicates: &BTreeSet<String>,
    explicit_case: bool,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    let contract = &context.contract;
    let function_interface = &context.function_interface;
    let contract_interface = contract.interface();
    if !predicate_interfaces_are_explicitly_compatible(
        contract_interface,
        function_interface,
        unfolded_predicates,
    ) {
        return Ok(false);
    }
    let mut propositions = contract_interface
        .contract_requires()
        .iter()
        .chain(contract_interface.contract_ensures())
        .chain(function_interface.contract_requires())
        .chain(function_interface.contract_ensures());
    let state_independent = propositions
        .clone()
        .all(spec_proposition_is_state_independent);
    let supported_syntax = propositions.all(spec_proposition_supports_stateful_memory_refinement);
    let supported_stateful_memory = !state_independent
        && !contract_interface.resource_requires().is_empty()
        && !contract_interface.resource_ensures().is_empty()
        && (!contract_interface.contract_mutable().is_empty()
            || contract_interface.resource_derived_mutable_frame())
        && supported_syntax;
    if !state_independent && !supported_stateful_memory {
        return Ok(false);
    }

    let contract_frame = with_contract_interface_argument_views(
        &CState::new(),
        contract_interface,
        &context.argument_values,
    );
    let function_frame = with_contract_interface_argument_views(
        &CState::new(),
        function_interface,
        &context.argument_values,
    );
    // Resource arguments are written over the two parameter lists, which the
    // views above already bind, so the pairing is decided before either
    // contract's own requirements are assumed.
    let Some(instances) = forced_refinement_instance_bindings(
        contract_interface,
        function_interface,
        &contract_frame,
        &function_frame,
        &PureFactContext::new(),
        budget,
    )?
    else {
        return Ok(false);
    };
    let install = |state: &CState, side, phase| {
        state_with_refinement_instances(state, &instances, side, phase, &PureFactContext::new())
    };
    let (Some(contract_entry), Some(function_entry)) = (
        install(
            &contract_frame,
            RefinementSide::Target,
            RefinementPhase::Entry,
        ),
        install(
            &function_frame,
            RefinementSide::Implementation,
            RefinementPhase::Entry,
        ),
    ) else {
        return Ok(false);
    };
    let mut preconditions = PureFactContext::new();
    if !assume_contract_propositions(
        &contract_entry,
        &contract_entry,
        contract_interface.contract_requires(),
        &mut preconditions,
        budget,
    )? {
        return Ok(false);
    }
    preconditions = assumptions_with_propositions(&preconditions, case_assumptions);
    if !prove_contract_propositions(
        &function_entry,
        &function_entry,
        function_interface.contract_requires(),
        &mut preconditions,
        budget,
    )? {
        return Ok(false);
    }

    let post_memory = if state_independent {
        contract_entry.memory().clone()
    } else {
        let memory_variable = budget.allocate_kernel_variable()?;
        let mutable_ranges = if explicit_case {
            let Some(ranges) = evaluate_decided_contract_mutable_ranges_for_interface(
                function_interface,
                &function_entry,
                &preconditions,
                budget,
            )?
            else {
                return Ok(false);
            };
            ranges
        } else {
            let Some(ranges) = evaluate_contract_mutable_ranges_for_interface(
                contract_interface,
                &contract_entry,
                &preconditions,
                budget,
                true,
            )?
            else {
                return Ok(false);
            };
            ranges
        };
        contract_entry.memory().clone().with_call_memory_havoc(
            memory_variable,
            &mutable_ranges,
            &preconditions,
        )
    };
    let result = symbolic_contract_result(function_interface, context.result_variable);
    // The post states carry the post instances, so a guarantee written over
    // `t.model` reads the fields the call produced while `old(t.model)` still
    // reads the entry fields through the entry state passed alongside.
    let (Some(mut contract_post), Some(mut function_post)) = (
        install(
            &contract_frame.clone().with_memory(post_memory.clone()),
            RefinementSide::Target,
            RefinementPhase::Post,
        ),
        install(
            &function_frame.clone().with_memory(post_memory),
            RefinementSide::Implementation,
            RefinementPhase::Post,
        ),
    ) else {
        return Ok(false);
    };
    if function_interface.return_type() != CType::Void {
        set_contract_result(&mut contract_post, contract_interface, result.clone());
        set_contract_result(&mut function_post, function_interface, result);
    }
    let access_adapter = checked_access_mode_refinement_adapter(
        contract_interface,
        function_interface,
        &contract_entry,
        &function_entry,
        &function_post,
        &preconditions,
        budget,
    )?;
    if access_adapter == Some(false) {
        return Ok(false);
    }
    let resource_and_effects_compatible = if access_adapter == Some(true) {
        // The checked adapter has already established the resource transition
        // and recovery.  Keep the ordinary effect containment check, but do
        // not re-run the algebraic resource comparison that cannot represent
        // the temporary owner-to-view loan scope.
        mutable_footprint_is_compatible_for_interfaces(
            contract_interface,
            function_interface,
            &contract_entry,
            &function_entry,
            &preconditions,
            budget,
        )?
    } else {
        compatible_resource_and_effect_interfaces(
            contract_interface,
            function_interface,
            &contract_entry,
            &function_entry,
            &contract_post,
            &function_post,
            &preconditions,
            budget,
        )?
    };
    if !resource_and_effects_compatible {
        return Ok(false);
    }
    let mut postconditions = preconditions;
    if !assume_contract_propositions(
        &function_post,
        &function_entry,
        function_interface.contract_ensures(),
        &mut postconditions,
        budget,
    )? {
        return Ok(false);
    }
    prove_contract_propositions(
        &contract_post,
        &contract_entry,
        contract_interface.contract_ensures(),
        &mut postconditions,
        budget,
    )
}

/// Predicate bodies are stored as checked, normalized contract propositions,
/// while `predicate_unfoldings` retains their opaque surface identities. Equal
/// unfolding tables need no proof action. Every entry present on only one side
/// must otherwise have its predicate name explicitly opened by the proof.
fn predicate_interfaces_are_explicitly_compatible(
    contract: &CFunctionContractInterface,
    function: &CFunctionContractInterface,
    unfolded_predicates: &BTreeSet<String>,
) -> bool {
    let contract_unfoldings = contract
        .predicate_unfoldings()
        .iter()
        .collect::<BTreeSet<_>>();
    let function_unfoldings = function
        .predicate_unfoldings()
        .iter()
        .collect::<BTreeSet<_>>();
    let permitted = |unfolding: &CPredicateUnfolding| match unfolding.predicate() {
        SpecProposition::Predicate { name, .. } => unfolded_predicates.contains(name),
        _ => false,
    };
    contract_unfoldings
        .difference(&function_unfoldings)
        .chain(function_unfoldings.difference(&contract_unfoldings))
        .all(|unfolding| permitted(unfolding))
}

/// Writes to file-scope or static storage that a checked path performs outside
/// the contract's owned footprint, described for diagnostics. The caller
/// passes the checked resource facts and, for resource-derived contracts, the
/// already prepared projection from certification; this keeps the storage
/// decision on the same transition artifact as modular effects. `None` is
/// retained for explicit-effect callers. Caller memory reached through a
/// pointer is checked by the resource transition at each store; storage is
/// not external memory, so a contract that declares resources but no effect
/// clause is framed here instead: its storage writes must lie inside the owned
/// ranges (startup resources, owned raw ranges, and composite bodies).
pub(crate) fn storage_writes_outside_owned_footprint(
    contract: &CFunction,
    entry: &CState,
    facts: &[ExecutionPureFact],
    assumptions: &PureFactContext,
    transition_resources: Option<&[CCheckedResourceFact]>,
    prepared_projection: Option<&CFunctionMemoryEffectProjection>,
) -> ExecutionResult<Option<Vec<String>>> {
    let is_storage = |pointer: &Pointer| {
        pointer.block.starts_with("global:") || pointer.block.starts_with("static:")
    };
    let storage_writes: Vec<Pointer> =
        crate::kernel::reasoning::memory_effect_write_pointers(facts)
            .into_iter()
            .filter(is_storage)
            .collect();
    let storage_summaries: Vec<&CMemoryRange> = facts
        .iter()
        .filter_map(|fact| match fact.proposition() {
            Proposition::CMemoryEffectSummary { mutable_ranges, .. } => Some(mutable_ranges),
            _ => None,
        })
        .flatten()
        .filter(|range| is_storage(range.base()))
        .collect();
    // Most contracts never touch storage; do not evaluate their owned
    // footprint at all.
    if storage_writes.is_empty() && storage_summaries.is_empty() {
        return Ok(Some(Vec::new()));
    }
    let owned = if let Some(projection) = prepared_projection {
        projection.ranges().to_vec()
    } else {
        let mut budget = ExecutionBudget::beside_live_state();
        match project_contract_memory_effects(
            entry,
            contract.contract_interface(),
            transition_resources,
            assumptions,
            &mut budget,
        )? {
            Ok(projection) => projection.ranges().to_vec(),
            Err(_) => return Ok(None),
        }
    };
    let mut outside = Vec::new();
    for pointer in &storage_writes {
        let covered = owned.iter().any(|range| {
            super::assumptions::pointer_in_memory_range_shallow(pointer, range)
                || assumptions.pointer_in_range_by_shallow_fact_graph_with_width(
                    pointer,
                    range.base(),
                    range.start(),
                    range.end(),
                    range.element_width(),
                )
        });
        if !covered {
            outside.push(format!("{pointer:?}"));
        }
    }
    for range in storage_summaries {
        if !owned
            .iter()
            .any(|parent| super::assumptions::memory_range_shallowly_contained(range, parent))
        {
            outside.push(format!("{range:?}"));
        }
    }
    Ok(Some(outside))
}

/// Project the checked resource transition's memory effects.  This is the
/// only kernel derivation of a contract write footprint: callers consume the
/// ranges and the checked load facts together, while the surface summary is
/// only source metadata used to construct the interface.
pub(crate) fn project_contract_memory_effects(
    entry: &CState,
    interface: &CFunctionContractInterface,
    transition_resources: Option<&[CCheckedResourceFact]>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<CFunctionMemoryEffectProjection, String>> {
    project_contract_memory_effects_with_guard_policy(
        entry,
        interface,
        transition_resources,
        assumptions,
        budget,
        false,
    )
}

/// Evaluate explicit effect segments once for both call projection and
/// refinement containment.  Refinement may require guards to be decided;
/// ordinary call projection keeps an undecided guard conservatively active.
fn project_explicit_memory_segments(
    entry: &CState,
    segments: &[CMemorySegment],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    require_decided_guards: bool,
) -> ExecutionResult<Result<(Vec<CMemoryRange>, Vec<ExecutionPureFact>), String>> {
    let mut projection_assumptions = assumptions.clone();
    let mut ranges = BTreeSet::new();
    let mut evidence_facts = Vec::new();
    for segment in segments {
        if let Some(guard) = segment.guard() {
            match evaluate_guarded_contract_condition(guard, entry, &projection_assumptions, budget)
            {
                Some(true) => {}
                Some(false) => continue,
                None if require_decided_guards => {
                    return Ok(Err("mutable footprint guard is undecided".to_string()));
                }
                None => {}
            }
        }
        match evaluate_loop_effect_segment_with_facts(
            entry,
            segment,
            &projection_assumptions,
            budget,
        )? {
            Ok((segment, facts)) => {
                projection_assumptions =
                    assumptions_with_path_context(&projection_assumptions, &facts, &[]);
                evidence_facts.extend(facts);
                let range = canonical_memory_range(CMemoryRange::new_with_element_width(
                    segment.base,
                    segment.start,
                    segment.end,
                    segment.element_width,
                ));
                ranges.insert(range);
            }
            Err(message) => return Ok(Err(message)),
        }
    }
    Ok(Ok((ranges.into_iter().collect(), evidence_facts)))
}

/// The canonical owned memory ranges one checked owned fact denotes: the
/// fact expanded through the composite definitions over `memory`, every
/// owned range of the expansion in canonical form. This is the one
/// derivation of a resource-derived write footprint, for a function's frame
/// and a loop's declared frame alike; nothing lowered from source is a
/// second source of it. `None` when the expansion is unavailable.
pub(super) fn checked_owned_memory_ranges(
    fact: &CResourceFact,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &PureFactContext,
) -> Option<Vec<CMemoryRange>> {
    let singleton = ResourceContext::new().unchecked_with_fact(fact.clone());
    let expanded =
        expand_all_composite_resource_facts(&singleton, definitions, memory, assumptions)?;
    Some(
        expanded
            .facts()
            .iter()
            .filter_map(|fact| Some(canonical_memory_range(fact.memory_own_range()?.clone())))
            .collect(),
    )
}

pub(crate) fn project_contract_memory_effects_with_guard_policy(
    entry: &CState,
    interface: &CFunctionContractInterface,
    transition_resources: Option<&[CCheckedResourceFact]>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    require_decided_guards: bool,
) -> ExecutionResult<Result<CFunctionMemoryEffectProjection, String>> {
    if interface.resource_derived_mutable_frame() && interface.resource_derived_frame_mixed() {
        return Ok(Err(
            "resource-derived mutable frame mixes explicit effect segments".to_string(),
        ));
    }
    let evaluated_transition;
    let transition_resources = if interface.resource_derived_mutable_frame() {
        match transition_resources {
            Some(resources) => Some(resources),
            None => {
                evaluated_transition = match evaluate_function_resource_context_with_metadata(
                    entry,
                    interface.resource_requires(),
                    interface.composite_resource_definitions(),
                    assumptions,
                    budget,
                )? {
                    Ok((_, checked)) => checked,
                    Err(error) => {
                        return Ok(Err(format!(
                            "could not evaluate resource transition: {error:?}"
                        )));
                    }
                };
                Some(evaluated_transition.as_slice())
            }
        }
    } else {
        None
    };
    if transition_resources.is_some_and(|resources| {
        resources.iter().any(|checked| {
            checked.role == CResourceTransferRole::Produce
                || checked.snapshot == CResourceSnapshot::Post
                || (checked.fact.is_view() && checked.role != CResourceTransferRole::Borrow)
        })
    }) {
        return Ok(Err(
            "resource transition contains an inconsistent transfer role".to_string(),
        ));
    }
    // Canonical ranges are indexed while the transition is projected. This
    // keeps duplicate wrapper members from triggering a quadratic scan.
    let mut ranges = BTreeSet::new();
    let mut evidence_facts = Vec::new();
    let mut range_sources = Vec::new();
    if interface.resource_derived_mutable_frame()
        && let Some(resources) = transition_resources
    {
        for checked in resources {
            // Borrowing is a boundary role, not an access-mode rewrite:
            // `requires owns p` paired with `ensures borrowed p` still gives
            // the body write authority for the entry-selected range.
            if !checked.fact.is_own() {
                continue;
            }
            let Some(expanded) = checked_owned_memory_ranges(
                &checked.fact,
                interface.composite_resource_definitions(),
                entry.memory(),
                assumptions,
            ) else {
                return Ok(Err(
                    "could not expand the checked resource transition".to_string()
                ));
            };
            for range in expanded {
                // Every byte of the expansion belongs to this one requirement,
                // whatever depth it came from, so the requirement is the
                // provenance recorded for each of its ranges.
                range_sources.push((range.clone(), checked.fact.clone()));
                ranges.insert(range);
            }
        }
    }
    // Resource-derived contracts get their memory authority exclusively from
    // the checked transition above.  The surface `contract_mutable` list is
    // a body-proof/read-only diagnostic projection and must not be another
    // modular-call source.  Functions without resource clauses retain their
    // explicit effect segments here.
    let explicit_segments = if !interface.resource_derived_mutable_frame() {
        interface.contract_mutable()
    } else {
        &[]
    };
    let (explicit_ranges, explicit_evidence) = match project_explicit_memory_segments(
        entry,
        explicit_segments,
        assumptions,
        budget,
        require_decided_guards,
    )? {
        Ok(result) => result,
        Err(message) => return Ok(Err(message)),
    };
    ranges.extend(explicit_ranges);
    evidence_facts.extend(explicit_evidence);
    Ok(Ok(CFunctionMemoryEffectProjection {
        ranges: ranges.into_iter().collect(),
        evidence_facts,
        range_sources,
    }))
}

/// Establish the inherited loop frame from the one checked entry transition.
/// The source segments remain attached for diagnostics, but loop execution
/// consumes these fixed ranges thereafter. In particular, a pointer field
/// changed by the body cannot retarget an inherited frame on a back edge.
pub(crate) fn establish_resource_derived_loop_frames(
    function: CFunction,
    entry: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<CFunction, String>> {
    if !function.resource_derived_mutable_frame() {
        return Ok(Ok(function));
    }
    // Quantified resource counts are an entry invariant.  Establish the same
    // non-negativity facts used by contract certification before evaluating
    // the transition, so a later body proof can never be the source of loop
    // authority.  In particular, do not fall back to the retained
    // source-derived segments when this checked setup fails.
    let mut transition_assumptions = assumptions.clone();
    for population in entry.counted_populations.iter() {
        transition_assumptions =
            transition_assumptions.assume_proposition(Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(
                    Bitvector32Term::Constant(0),
                    population.count.clone(),
                ),
                true,
            ));
    }
    let quantity_assumptions = match quantified_resource_requirement_assumptions(
        entry,
        function.resource_requires(),
        &transition_assumptions,
        budget,
    )? {
        Ok(assumptions) => assumptions,
        Err(error) => {
            return Ok(Err(format!(
                "could not evaluate resource quantities: {error:?}"
            )));
        }
    };
    for proposition in quantity_assumptions {
        transition_assumptions = transition_assumptions.assume_proposition(proposition);
    }
    let projection = match project_contract_memory_effects(
        entry,
        function.contract_interface(),
        None,
        &transition_assumptions,
        budget,
    )? {
        Ok(projection) => projection,
        Err(message) => return Ok(Err(message)),
    };
    fn rewrite(statement: &mut CStatement, ranges: &[CMemoryRange]) {
        match statement {
            CStatement::Seq(first, second) => {
                rewrite(std::sync::Arc::make_mut(first), ranges);
                rewrite(std::sync::Arc::make_mut(second), ranges);
            }
            CStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                rewrite(then_branch, ranges);
                rewrite(else_branch, ranges);
            }
            CStatement::While {
                effect_checks,
                body,
                ..
            } => {
                for check in effect_checks {
                    if check.origin() == CLoopEffectOrigin::InheritedResourceDerived {
                        *check = check.clone().with_validated_ranges(ranges.to_vec());
                    }
                }
                rewrite(body, ranges);
            }
            CStatement::Switch { cases, .. } => {
                for case in cases {
                    rewrite(&mut case.body, ranges);
                }
            }
            CStatement::ContinueWithStep { step } => rewrite(step, ranges),
            _ => {}
        }
    }
    let mut body = function.body().clone();
    rewrite(&mut body, projection.ranges());
    Ok(Ok(function.with_body(body)))
}

/// Check that inherited loop-frame metadata was established from the checked
/// entry transition before proof generation. This is an invariant check, not
/// a second evaluator: source expressions are never re-evaluated here.
pub(crate) fn validate_resource_derived_loop_frames(
    function: &CFunction,
    _entry: &CState,
    _assumptions: &PureFactContext,
    _budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<(), String>> {
    fn has_inherited_loop_frame(statement: &CStatement) -> bool {
        match statement {
            CStatement::Seq(first, second) => {
                has_inherited_loop_frame(first) || has_inherited_loop_frame(second)
            }
            CStatement::If {
                then_branch,
                else_branch,
                ..
            } => has_inherited_loop_frame(then_branch) || has_inherited_loop_frame(else_branch),
            CStatement::While {
                effect_checks,
                body,
                ..
            } => {
                effect_checks
                    .iter()
                    .any(|check| check.origin() == CLoopEffectOrigin::InheritedResourceDerived)
                    || has_inherited_loop_frame(body)
            }
            CStatement::Switch { cases, .. } => cases
                .iter()
                .any(|case| has_inherited_loop_frame(&case.body)),
            CStatement::ContinueWithStep { step } => has_inherited_loop_frame(step),
            _ => false,
        }
    }
    if !function.resource_derived_mutable_frame() || !has_inherited_loop_frame(function.body()) {
        return Ok(Ok(()));
    }
    fn check_statement(statement: &CStatement) -> ExecutionResult<Result<(), String>> {
        let check = |checks: &[CLoopEffectCheck]| -> ExecutionResult<Result<(), String>> {
            for effect_check in checks {
                if effect_check.origin() != CLoopEffectOrigin::InheritedResourceDerived {
                    continue;
                }
                let Some(actual) = effect_check.validated_ranges() else {
                    return Ok(Err(
                        "resource-derived loop frame was not established at function entry"
                            .to_string(),
                    ));
                };
                if actual.windows(2).any(|pair| pair[1] <= pair[0]) {
                    return Ok(Err(
                        "inherited loop frame is not in canonical checked form".to_string()
                    ));
                }
            }
            Ok(Ok(()))
        };
        match statement {
            CStatement::Seq(first, second) => {
                if let Err(error) = check_statement(first)? {
                    return Ok(Err(error));
                }
                check_statement(second)
            }
            CStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                if let Err(error) = check_statement(then_branch)? {
                    return Ok(Err(error));
                }
                check_statement(else_branch)
            }
            CStatement::While {
                effect_checks,
                body,
                ..
            } => {
                if let Err(error) = check(effect_checks)? {
                    return Ok(Err(error));
                }
                check_statement(body)
            }
            CStatement::Switch { cases, .. } => {
                for case in cases {
                    if let Err(error) = check_statement(&case.body)? {
                        return Ok(Err(error));
                    }
                }
                Ok(Ok(()))
            }
            CStatement::ContinueWithStep { step } => check_statement(step),
            _ => Ok(Ok(())),
        }
    }
    check_statement(function.body())
}

/// Whether an owned composite the interface requires has a guarded body
/// anywhere under it. A resource-derived footprint used to be lowered from
/// source with the enclosing conditions as guards on every segment beneath
/// them; the kernel now reads the definitions instead, so the refusals those
/// guards produced are unchanged.
fn requirements_reach_a_guarded_composite(interface: &CFunctionContractInterface) -> bool {
    fn composite_name(spec: &CResourceSpec) -> Option<&str> {
        match spec.term() {
            CResourceTerm::Composite { name, .. } => Some(name),
            CResourceTerm::Instance { resource, .. } => match resource.as_ref() {
                CResourceTerm::Composite { name, .. } => Some(name),
                _ => None,
            },
            _ => None,
        }
    }
    fn guarded(
        name: &str,
        definitions: &[CCompositeResourceDefinition],
        active: &mut BTreeSet<String>,
    ) -> bool {
        if !active.insert(name.to_string()) {
            return false;
        }
        let result = definitions
            .iter()
            .find(|definition| definition.name() == name)
            .is_some_and(|definition| {
                definition.condition().is_some()
                    || definition
                        .contains()
                        .iter()
                        .filter(|spec| spec.access() == CResourceAccessMode::Own)
                        .filter_map(composite_name)
                        .any(|child| guarded(child, definitions, active))
            });
        active.remove(name);
        result
    }
    interface
        .resource_requires()
        .iter()
        .filter(|spec| spec.access() == CResourceAccessMode::Own)
        .filter_map(composite_name)
        .any(|name| {
            guarded(
                name,
                interface.composite_resource_definitions(),
                &mut BTreeSet::new(),
            )
        })
}

fn evaluate_contract_mutable_ranges_for_interface(
    interface: &CFunctionContractInterface,
    entry: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    require_unguarded: bool,
) -> ExecutionResult<Option<Vec<CMemoryRange>>> {
    if require_unguarded
        && (interface
            .contract_mutable()
            .iter()
            .any(|s| s.guard().is_some())
            || (interface.resource_derived_mutable_frame()
                && requirements_reach_a_guarded_composite(interface)))
    {
        return Ok(None);
    }
    Ok(
        match project_contract_memory_effects(entry, interface, None, assumptions, budget)? {
            Ok(projection) => Some(projection.ranges),
            Err(_) => None,
        },
    )
}

/// Evaluates exactly the concrete ranges active in one explicit proof case.
///
/// Unlike automatic refinement, this never branches over a guard. Every guard
/// must already be decided by the named preconditions and the proof's written
/// case assumptions. A false guard contributes no possible write; a true guard
/// contributes its ordinary evaluated range.
/// No reaching fixture exists, and none can be written today: the only
/// caller is `function_refines_named_contract_in_case`'s `explicit_case`
/// branch, and its one call site passes `explicit_case: false`. The guard
/// decision below is route-restricted with the rest of package 10(b) so the
/// branch cannot come back carrying a proof search, but its behaviour is
/// unobserved by both fixture harnesses.
fn evaluate_decided_contract_mutable_ranges_for_interface(
    interface: &CFunctionContractInterface,
    entry: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<Vec<CMemoryRange>>> {
    let mut guard_assumptions = assumptions.clone();
    let Some(guards) = lower_refinement_mutable_guards_for_interface(
        interface,
        entry,
        &mut guard_assumptions,
        budget,
    )?
    else {
        return Ok(None);
    };
    let mut ranges = Vec::with_capacity(interface.contract_mutable().len());
    for (segment, guard) in interface.contract_mutable().iter().zip(guards) {
        if let Some(guard) = guard {
            // A refined mutable segment is included, dropped, or leaves the
            // whole footprint undecided. The decision uses the exact routes
            // only; an undecided guard refuses the refinement rather than
            // being settled by a proof search over the ambient context.
            match guard_value_by_exact_routes(&guard_assumptions, &guard) {
                Some(false) => continue,
                Some(true) => {}
                None => return Ok(None),
            }
        }
        let Ok((mut projected, _)) = project_explicit_memory_segments(
            entry,
            std::slice::from_ref(segment),
            &guard_assumptions,
            budget,
            true,
        )?
        else {
            return Ok(None);
        };
        let Some(range) = projected.pop() else {
            return Ok(None);
        };
        ranges.push(range);
    }
    Ok(Some(ranges))
}

fn compatible_resource_and_effect_interfaces(
    contract: &CFunctionContractInterface,
    function: &CFunctionContractInterface,
    contract_entry: &CState,
    function_entry: &CState,
    contract_post: &CState,
    function_post: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    if !resource_transition_is_compatible(
        contract,
        function,
        contract_entry,
        function_entry,
        contract_post,
        function_post,
        assumptions,
        budget,
    )? {
        return Ok(false);
    }
    mutable_footprint_is_compatible_for_interfaces(
        contract,
        function,
        contract_entry,
        function_entry,
        assumptions,
        budget,
    )
}

/// Check an access-mode variance at a refinement boundary with the same
/// checked transfer used by calls.  The algebraic framed-refinement check is
/// intentionally not sufficient here: it can establish that a view's value
/// is contained in an owned value without recording the loan scope that makes
/// the implementation's observation valid.
///
/// `Some(true)` means an owned target requirement was adapted to a viewed
/// implementation requirement and its entry/recovery evidence was checked.
/// `Some(false)` is an explicit view-to-own refusal.  `None` means the two
/// interfaces have no access-mode variance that this adapter handles.
#[allow(clippy::too_many_arguments)]
fn checked_access_mode_refinement_adapter(
    contract: &CFunctionContractInterface,
    function: &CFunctionContractInterface,
    contract_entry: &CState,
    function_entry: &CState,
    function_post: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<bool>> {
    if contract.resource_requires().is_empty() || function.resource_requires().is_empty() {
        return Ok(None);
    }
    let Ok((contract_resources, _)) = evaluate_function_resource_context_with_metadata(
        contract_entry,
        contract.resource_requires(),
        contract.composite_resource_definitions(),
        assumptions,
        budget,
    )?
    else {
        return Ok(Some(false));
    };
    let Ok((function_resources, _)) = evaluate_function_resource_context_with_metadata(
        function_entry,
        function.resource_requires(),
        function.composite_resource_definitions(),
        assumptions,
        budget,
    )?
    else {
        return Ok(Some(false));
    };
    let satisfied_by_mode = |required: &CResourceFact, view: bool| {
        contract_resources.facts().iter().any(|available| {
            available.is_view() == view
                && ResourceContext::new()
                    .unchecked_with_fact(available.clone())
                    .satisfies_fact(required, assumptions)
        })
    };
    let mut own_to_view = false;
    for implementation in function_resources.facts() {
        if implementation.is_view() {
            // A same-mode view is already a shared capability.  Invoke the
            // loan adapter only when this exact requirement is supplied by
            // ownership, including proper subranges; comparing resource
            // terms for equality would miss that common refinement.
            own_to_view |= !satisfied_by_mode(implementation, true)
                && satisfied_by_mode(implementation, false);
            continue;
        }
        let Some(view_requirement) = implementation.core_with_assumptions(assumptions) else {
            continue;
        };
        if !satisfied_by_mode(implementation, false) && satisfied_by_mode(&view_requirement, true) {
            // An implementation requiring exclusive authority cannot be
            // called through an interface that grants only observation.
            return Ok(Some(false));
        }
    }
    if !own_to_view {
        return Ok(None);
    }

    // Evaluate both sides into checked contexts before planning.  Supplying
    // these contexts is what makes the planner consume the exact target owner
    // rather than treating `satisfies_fact` as a capability conversion.
    let caller = contract_entry
        .clone()
        .with_resource_context(contract_resources);
    let callee = function_entry
        .clone()
        .with_resource_context(function_resources.clone());
    let mut transfer = match prepare_contract_resource_transfer(
        &caller,
        &callee,
        "refinement",
        function,
        assumptions,
        budget,
        false,
        ResourceTransitionPurpose::CallSite,
    )? {
        Ok(transfer) => transfer,
        Err(_) => return Ok(Some(false)),
    };
    let callee = callee_state_with_resource_transfer(callee, &transfer);
    let post = function_post
        .clone()
        .with_resource_context(function_resources);
    let ContractReturnResources {
        return_resources: returned,
        ensured_views: returned_views,
        produced_borrowing_pieces,
    } = match evaluate_contract_return_resources(
        &transfer.caller_resources_after_requirements,
        escrowed_owners(&transfer),
        &transfer.canonical_borrowed_owners,
        &caller,
        &post,
        "refinement",
        function,
        assumptions,
        budget,
    )? {
        Ok(result) => result,
        Err(_) => return Ok(Some(false)),
    };
    transfer.candidate_output_views = returned_views;
    transfer.produced_borrowing_pieces = produced_borrowing_pieces;
    if recover_candidate_stable_view_resources(
        &caller,
        &callee,
        &transfer,
        returned,
        assumptions,
        assumptions,
        &[],
    )
    .is_err()
    {
        return Ok(Some(false));
    }
    Ok(Some(true))
}

#[allow(clippy::too_many_arguments)]
fn resource_transition_is_compatible(
    contract: &CFunctionContractInterface,
    function: &CFunctionContractInterface,
    contract_entry: &CState,
    function_entry: &CState,
    contract_post: &CState,
    function_post: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    if exact_resource_interfaces_match(
        contract,
        function,
        contract_entry,
        function_entry,
        contract_post,
        function_post,
        assumptions,
        budget,
    )? {
        return Ok(true);
    }
    framed_resource_transition_refines(
        contract,
        function,
        contract_entry,
        function_entry,
        contract_post,
        function_post,
        assumptions,
        budget,
    )
}

#[allow(clippy::too_many_arguments)]
fn exact_resource_interfaces_match(
    contract: &CFunctionContractInterface,
    function: &CFunctionContractInterface,
    contract_entry: &CState,
    function_entry: &CState,
    contract_post: &CState,
    function_post: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    if contract.resource_requires().len() != function.resource_requires().len()
        || contract.resource_ensures().len() != function.resource_ensures().len()
    {
        return Ok(false);
    }
    for (contract_resource, function_resource) in contract
        .resource_requires()
        .iter()
        .zip(function.resource_requires())
    {
        let contract_resource = match evaluate_function_resource_spec_with_entry(
            contract_entry,
            contract_entry,
            contract_resource,
            assumptions,
            budget,
        )? {
            Ok(resource) => resource,
            Err(_) => return Ok(false),
        };
        let function_resource = match evaluate_function_resource_spec_with_entry(
            function_entry,
            function_entry,
            function_resource,
            assumptions,
            budget,
        )? {
            Ok(resource) => resource,
            Err(_) => return Ok(false),
        };
        if contract_resource != function_resource {
            return Ok(false);
        }
    }
    for (contract_resource, function_resource) in contract
        .resource_ensures()
        .iter()
        .zip(function.resource_ensures())
    {
        let contract_state = match contract_resource.snapshot() {
            CResourceSnapshot::Entry => contract_entry,
            CResourceSnapshot::Current | CResourceSnapshot::Post => contract_post,
        };
        let contract_resource = match evaluate_function_resource_spec_with_entry(
            contract_entry,
            contract_state,
            contract_resource,
            assumptions,
            budget,
        )? {
            Ok(resource) => resource,
            Err(_) => return Ok(false),
        };
        let function_state = match function_resource.snapshot() {
            CResourceSnapshot::Entry => function_entry,
            CResourceSnapshot::Current | CResourceSnapshot::Post => function_post,
        };
        let function_resource = match evaluate_function_resource_spec_with_entry(
            function_entry,
            function_state,
            function_resource,
            assumptions,
            budget,
        )? {
            Ok(resource) => resource,
            Err(_) => return Ok(false),
        };
        if contract_resource != function_resource {
            return Ok(false);
        }
    }
    Ok(true)
}

fn context_contains_only_refinable_resources(resources: &ResourceContext) -> bool {
    resources.facts().iter().all(|resource| {
        matches!(
            resource,
            CResourceFact::Own(CResource::Memory(_) | CResource::Instance(_), quantity)
                if quantity.as_const() == Some(1)
        ) || matches!(
            resource,
            CResourceFact::Own(CResource::Composite { .. } | CResource::Token { .. }, _)
        ) || matches!(
            resource,
            CResourceFact::View(
                CResource::Memory(_) | CResource::Composite { .. } | CResource::Token { .. }
            )
        )
    })
}

fn resource_spec_supports_framed_refinement(resource: &CResourceSpec) -> bool {
    if resource.is_instance() {
        return resource
            .instance_resource_spec()
            .is_some_and(|inner| resource_spec_supports_framed_refinement(&inner));
    }
    matches!(
        resource.family(),
        ResourceFamily::Memory | ResourceFamily::Composite | ResourceFamily::Token
    )
}

fn evaluate_refinement_resource_context(
    state: &CState,
    resources: &[CResourceSpec],
    definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<ResourceContext>> {
    Ok(
        (evaluate_function_resource_context(state, resources, definitions, assumptions, budget)?)
            .ok(),
    )
}

/// Checks that the named requirements can supply the concrete requirements,
/// preserving everything the concrete transition only borrows or does not
/// need as a frame. Then requires `concrete_ensures * frame` to provide the
/// named ensures. The resource context's indexed algebras perform ownership
/// splitting, symbolic exact-resource quantity arithmetic, range containment,
/// exact token and folded-composite identity, and scoped borrowing; no project
/// functions, composite definitions, or unrelated proof state are inspected.
#[allow(clippy::too_many_arguments)]
fn framed_resource_transition_refines(
    contract: &CFunctionContractInterface,
    function: &CFunctionContractInterface,
    contract_entry: &CState,
    function_entry: &CState,
    contract_post: &CState,
    function_post: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    if !contract
        .resource_requires()
        .iter()
        .chain(contract.resource_ensures())
        .chain(function.resource_requires())
        .chain(function.resource_ensures())
        .all(resource_spec_supports_framed_refinement)
    {
        return Ok(false);
    }
    let Some(contract_requires) = evaluate_refinement_resource_context(
        contract_entry,
        contract.resource_requires(),
        contract.composite_resource_definitions(),
        assumptions,
        budget,
    )?
    else {
        return Ok(false);
    };
    let Some(function_requires) = evaluate_refinement_resource_context(
        function_entry,
        function.resource_requires(),
        function.composite_resource_definitions(),
        assumptions,
        budget,
    )?
    else {
        return Ok(false);
    };
    let Some(function_ensures) = evaluate_refinement_resource_context(
        function_post,
        function.resource_ensures(),
        function.composite_resource_definitions(),
        assumptions,
        budget,
    )?
    else {
        return Ok(false);
    };
    let Some(contract_ensures) = evaluate_refinement_resource_context(
        contract_post,
        contract.resource_ensures(),
        contract.composite_resource_definitions(),
        assumptions,
        budget,
    )?
    else {
        return Ok(false);
    };
    if [
        &contract_requires,
        &function_requires,
        &function_ensures,
        &contract_ensures,
    ]
    .into_iter()
    .any(|resources| !context_contains_only_refinable_resources(resources))
    {
        return Ok(false);
    }

    let Some(frame) = contract_requires
        .clone()
        .without_facts(function_requires.facts(), assumptions)
    else {
        return Ok(false);
    };
    let concrete_output = match frame.try_compose_with_facts_delaying_normalization(
        function_ensures.facts().iter().cloned(),
        assumptions,
    ) {
        Ok(resources) => resources,
        Err(_) => return Ok(false),
    };
    Ok(resource_context_definitionally_contains(
        &concrete_output,
        &contract_ensures,
        &[],
        contract_post.memory(),
        assumptions,
    ))
}

/// Checks that every range the implementation may write lies inside the
/// target's checked effect projection. Both projections are built from the
/// same transition/effect evaluator: resource-derived interfaces evaluate
/// their entry resource clauses into role-bearing facts, while explicit
/// interfaces evaluate their guarded segments. Surface `contract_mutable`
/// metadata is never walked as the semantic comparison itself.
///
/// Both guard questions are decided by [`refinement_route_proves`]: exact
/// membership in the refinement assumptions, or the frozen condition checker
/// on a bare condition. A guard this cannot settle is treated as unsettled,
/// which refuses the refinement rather than widening the checked footprint.
/// There is no proof site here to receive an obligation instead: this is a
/// boolean gate on a kernel-formed contract fact, so refusing is the
/// conservative equivalent of emitting one.
///
/// The walk over the contract's declared segments is not a selection. Its only
/// result is whether some declared segment covers the required range; no later
/// check consults which one, and a corpus probe (both fixture harnesses, plus
/// `c_named_contract_refinement_selects_guarded_segment`) found exactly one
/// covering segment at every reached site. So this is a discharge, and a
/// finite disjunction over the declared segments would spell a choice that
/// nothing consumes.
fn mutable_footprint_is_compatible_for_interfaces(
    contract: &CFunctionContractInterface,
    function: &CFunctionContractInterface,
    contract_entry: &CState,
    function_entry: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    if !contract.resource_derived_mutable_frame()
        && !function.resource_derived_mutable_frame()
        && (contract
            .contract_mutable()
            .iter()
            .any(|segment| segment.guard().is_some())
            || function
                .contract_mutable()
                .iter()
                .any(|segment| segment.guard().is_some()))
    {
        return explicit_refinement_effects_are_compatible(
            contract,
            function,
            contract_entry,
            function_entry,
            assumptions,
            budget,
        );
    }
    let contract_projection =
        project_refinement_effects(contract, contract_entry, assumptions, budget)?;
    let function_projection =
        project_refinement_effects(function, function_entry, assumptions, budget)?;
    let (Ok(contract_projection), Ok(function_projection)) =
        (contract_projection, function_projection)
    else {
        return Ok(false);
    };
    // Range containment is indexed by memory family and element width before
    // the proof-sensitive endpoint check. This avoids comparing every
    // implementation range with every unrelated target range while retaining
    // the shallow alias fallback for symbolic blocks.
    let mut available_by_family: BTreeMap<(PointerBlock, u32), Vec<&CMemoryRange>> =
        BTreeMap::new();
    for available in contract_projection.ranges() {
        available_by_family
            .entry((available.base.block.clone(), available.element_width))
            .or_default()
            .push(available);
    }
    Ok(function_projection.ranges().iter().all(|required_range| {
        if let Some(candidates) = available_by_family.get(&(
            required_range.base.block.clone(),
            required_range.element_width,
        )) {
            candidates.iter().any(|available_range| {
                memory_range_covers(available_range, required_range, assumptions)
            })
        } else {
            contract_projection.ranges().iter().any(|available_range| {
                memory_range_covers(available_range, required_range, assumptions)
            })
        }
    }))
}

/// Guarded explicit effects need one projection per implementation guard: the
/// implementation's guard is the active path assumption, while a target guard
/// must already be established on that path. Range lowering itself still goes
/// through the shared projection evaluator.
fn explicit_refinement_effects_are_compatible(
    contract: &CFunctionContractInterface,
    function: &CFunctionContractInterface,
    contract_entry: &CState,
    function_entry: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    let mut guard_assumptions = assumptions.clone();
    let Some(contract_guards) = lower_refinement_mutable_guards_for_interface(
        contract,
        contract_entry,
        &mut guard_assumptions,
        budget,
    )?
    else {
        return Ok(false);
    };
    let Some(function_guards) = lower_refinement_mutable_guards_for_interface(
        function,
        function_entry,
        &mut guard_assumptions,
        budget,
    )?
    else {
        return Ok(false);
    };
    for (required_segment, required_guard) in
        function.contract_mutable().iter().zip(function_guards)
    {
        if required_guard.as_ref().is_some_and(|guard| {
            refinement_route_proves(
                &guard_assumptions,
                &Proposition::Not(Box::new(guard.clone())),
            )
        }) {
            continue;
        }
        let mut active_assumptions = guard_assumptions.clone();
        if let Some(guard) = required_guard {
            active_assumptions = active_assumptions.assume_proposition(guard);
        }
        let Ok((required_ranges, _)) = project_explicit_memory_segments(
            function_entry,
            std::slice::from_ref(required_segment),
            &active_assumptions,
            budget,
            true,
        )?
        else {
            return Ok(false);
        };
        let Some(required_range) = required_ranges.first() else {
            return Ok(false);
        };
        let mut covered = false;
        for (available_segment, available_guard) in
            contract.contract_mutable().iter().zip(&contract_guards)
        {
            if let Some(guard) = available_guard
                && !refinement_route_proves(&active_assumptions, guard)
            {
                continue;
            }
            let mut available_segment = available_segment.clone();
            available_segment.guard = None;
            let Ok((available_ranges, _)) = project_explicit_memory_segments(
                contract_entry,
                std::slice::from_ref(&available_segment),
                &active_assumptions,
                budget,
                true,
            )?
            else {
                continue;
            };
            if available_ranges.iter().any(|available_range| {
                memory_range_covers(available_range, required_range, &active_assumptions)
            }) {
                covered = true;
                break;
            }
        }
        if !covered {
            return Ok(false);
        }
    }
    Ok(true)
}

fn project_refinement_effects(
    interface: &CFunctionContractInterface,
    entry: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<CFunctionMemoryEffectProjection, String>> {
    let mut projection_assumptions = assumptions.clone();
    // Explicit guards retain refinement's exact-route refusal semantics. The
    // resource-derived projection has no independent surface guard list and
    // therefore goes directly through the checked transition evaluator.
    if !interface.resource_derived_mutable_frame() {
        let Some(guards) = lower_refinement_mutable_guards_for_interface(
            interface,
            entry,
            &mut projection_assumptions,
            budget,
        )?
        else {
            return Ok(Err("mutable footprint guard is undecided".to_string()));
        };
        let mut ranges = Vec::new();
        let mut evidence_facts = Vec::new();
        for (segment, guard) in interface.contract_mutable().iter().zip(guards) {
            let mut active_assumptions = projection_assumptions.clone();
            if let Some(guard) = guard {
                if refinement_route_proves(
                    &active_assumptions,
                    &Proposition::Not(Box::new(guard.clone())),
                ) {
                    continue;
                }
                active_assumptions = active_assumptions.assume_proposition(guard.clone());
                if !refinement_route_proves(&active_assumptions, &guard) {
                    return Ok(Err("mutable footprint guard is undecided".to_string()));
                }
            }
            // Guard resolution above is the refinement-specific route. Feed
            // the now unconditional segment to the shared evaluator so range
            // lowering itself remains identical to call/certification paths.
            let mut segment = segment.clone();
            segment.guard = None;
            let Ok((segment_ranges, segment_evidence)) = project_explicit_memory_segments(
                entry,
                std::slice::from_ref(&segment),
                &active_assumptions,
                budget,
                true,
            )?
            else {
                return Ok(Err("could not evaluate mutable footprint".to_string()));
            };
            ranges.extend(segment_ranges);
            evidence_facts.extend(segment_evidence);
        }
        return Ok(Ok(CFunctionMemoryEffectProjection {
            ranges,
            evidence_facts,
            // Explicit segments carry no requirement provenance.
            range_sources: Vec::new(),
        }));
    }
    project_contract_memory_effects_with_guard_policy(
        entry,
        interface,
        None,
        &projection_assumptions,
        budget,
        true,
    )
}

#[cfg(test)]
fn mutable_footprint_is_compatible(
    contract: &CFunction,
    function: &CFunction,
    contract_entry: &CState,
    function_entry: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    mutable_footprint_is_compatible_for_interfaces(
        contract.contract_interface(),
        function.contract_interface(),
        contract_entry,
        function_entry,
        assumptions,
        budget,
    )
}

fn lower_refinement_mutable_guards_for_interface(
    interface: &CFunctionContractInterface,
    entry: &CState,
    assumptions: &mut PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<Vec<Option<Proposition>>>> {
    let mut guards = Vec::with_capacity(interface.contract_mutable().len());
    for segment in interface.contract_mutable() {
        let Some(guard) = segment.guard() else {
            guards.push(None);
            continue;
        };
        if !spec_proposition_is_state_independent(guard) {
            return Ok(None);
        }
        let paths = lower_spec_proposition_at_state_with_loop_entry(
            entry,
            guard,
            Some(entry),
            assumptions,
            budget,
        )?;
        let [path] = paths.as_slice() else {
            return Ok(None);
        };
        for fact in &path.facts {
            *assumptions = assumptions
                .clone()
                .assume_proposition(fact.proposition().clone());
        }
        if path.obligations.iter().any(|obligation| {
            !required_obligation_is_exactly_discharged(assumptions, obligation.proposition())
        }) {
            return Ok(None);
        }
        guards.push(Some(path.proposition.clone()));
    }
    Ok(Some(guards))
}

#[cfg(test)]
mod guarded_mutable_refinement_tests {
    use super::*;

    fn guard(operator: CComparisonOperator, value: u32) -> SpecProposition {
        SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("active")),
            operator,
            right: SpecExpression::CExpression(c_int32_literal(value)),
        }
    }

    fn segment(guard: Option<SpecProposition>, start: u32, end: u32) -> CMemorySegment {
        let segment = CMemorySegment::new(
            c_variable("cells"),
            c_int32_literal(start),
            c_int32_literal(end),
        );
        match guard {
            Some(guard) => segment.with_guard(guard),
            None => segment,
        }
    }

    fn function_with_segment(name: &str, segment: CMemorySegment) -> CFunction {
        c_function(CType::Void, name, Vec::new(), c_return(c_void_value())).with_contract(
            Vec::new(),
            Vec::new(),
            vec![segment],
            Vec::new(),
            true,
        )
    }

    fn entry_state() -> CState {
        CState::new()
            .with_local(
                "active",
                int32(Bitvector32Term::Variable(Variable(980_001))),
            )
            .with_local(
                "cells",
                CValue::pointer(Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: PointerOffsetTerm::Constant(0),
                }),
            )
    }

    fn compatible_with_assumptions(
        contract: &CFunction,
        function: &CFunction,
        assumptions: &PureFactContext,
    ) -> bool {
        let entry = entry_state();
        mutable_footprint_is_compatible(
            contract,
            function,
            &entry,
            &entry,
            assumptions,
            &mut ExecutionBudget::new(),
        )
        .expect("guarded mutable refinement should execute")
    }

    fn compatible(contract: &CFunction, function: &CFunction) -> bool {
        compatible_with_assumptions(contract, function, &PureFactContext::new())
    }

    #[test]
    fn stronger_concrete_guard_and_subrange_refine_named_footprint() {
        let contract = function_with_segment(
            "contract",
            segment(Some(guard(CComparisonOperator::NotEqual, 0)), 0, 2),
        );
        let function = function_with_segment(
            "function",
            segment(Some(guard(CComparisonOperator::Equal, 1)), 1, 2),
        );
        assert!(compatible(&contract, &function));
    }

    #[test]
    fn guarded_concrete_effect_refines_unguarded_named_footprint() {
        let contract = function_with_segment("contract", segment(None, 0, 2));
        let function = function_with_segment(
            "function",
            segment(Some(guard(CComparisonOperator::NotEqual, 0)), 0, 1),
        );
        assert!(compatible(&contract, &function));
    }

    #[test]
    fn unguarded_concrete_effect_does_not_refine_guarded_named_footprint() {
        let contract = function_with_segment(
            "contract",
            segment(Some(guard(CComparisonOperator::NotEqual, 0)), 0, 2),
        );
        let function = function_with_segment("function", segment(None, 0, 1));
        assert!(!compatible(&contract, &function));
    }

    #[test]
    fn named_precondition_can_establish_guard_for_unconditional_concrete_effect() {
        let contract = function_with_segment(
            "contract",
            segment(Some(guard(CComparisonOperator::NotEqual, 0)), 0, 2),
        );
        let function = function_with_segment("function", segment(None, 0, 1));
        let active = Bitvector32Term::Variable(Variable(980_001));
        let assumptions = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
            ConditionTerm::equal(active, Bitvector32Term::Constant(0)),
            false,
        ));
        assert!(compatible_with_assumptions(
            &contract,
            &function,
            &assumptions,
        ));
    }

    #[test]
    fn unrelated_concrete_guard_does_not_refine_named_guard() {
        let contract = function_with_segment(
            "contract",
            segment(Some(guard(CComparisonOperator::GreaterThan, 0)), 0, 2),
        );
        let function = function_with_segment(
            "function",
            segment(Some(guard(CComparisonOperator::LessThan, 0)), 0, 1),
        );
        assert!(!compatible(&contract, &function));
    }

    fn active_is_zero(value: bool) -> PureFactContext {
        PureFactContext::new().assume_proposition(Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::Variable(Variable(980_001)),
                Bitvector32Term::Constant(0),
            ),
            value,
        ))
    }

    /// An available guard that only logical search could discharge is treated
    /// as unsettled, so its segment is not available. The same footprint with
    /// the guard spelled as the exactly available condition is accepted, so
    /// the difference is the route rather than the content.
    #[test]
    fn disjunctive_available_guard_is_not_discharged_by_search() {
        let exact = function_with_segment(
            "contract",
            segment(Some(guard(CComparisonOperator::NotEqual, 0)), 0, 2),
        );
        let disjunctive = function_with_segment(
            "contract",
            segment(
                Some(SpecProposition::Or(
                    Box::new(guard(CComparisonOperator::NotEqual, 0)),
                    Box::new(guard(CComparisonOperator::Equal, 5)),
                )),
                0,
                2,
            ),
        );
        let function = function_with_segment("function", segment(None, 0, 1));
        let assumptions = active_is_zero(false);
        assert!(compatible_with_assumptions(&exact, &function, &assumptions));
        assert!(!compatible_with_assumptions(
            &disjunctive,
            &function,
            &assumptions
        ));
    }

    /// A required segment whose guard is exactly refuted contributes no write,
    /// so nothing has to cover it. Without that refutation the same footprint
    /// is wider than the contract's and is rejected.
    #[test]
    fn exactly_refuted_required_guard_needs_no_cover() {
        let contract = function_with_segment(
            "contract",
            segment(Some(guard(CComparisonOperator::Equal, 1)), 0, 1),
        );
        let function = function_with_segment(
            "function",
            segment(Some(guard(CComparisonOperator::NotEqual, 0)), 0, 2),
        );
        assert!(compatible_with_assumptions(
            &contract,
            &function,
            &active_is_zero(true)
        ));
        assert!(!compatible(&contract, &function));
    }

    #[test]
    fn guard_implication_does_not_relax_range_containment() {
        let contract = function_with_segment(
            "contract",
            segment(Some(guard(CComparisonOperator::NotEqual, 0)), 0, 1),
        );
        let function = function_with_segment(
            "function",
            segment(Some(guard(CComparisonOperator::Equal, 1)), 0, 2),
        );
        assert!(!compatible(&contract, &function));
    }
}

fn assume_contract_propositions(
    state: &CState,
    entry_state: &CState,
    propositions: &[SpecProposition],
    assumptions: &mut PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    for proposition in propositions {
        let paths = lower_spec_proposition_at_state_with_loop_entry(
            state,
            proposition,
            Some(entry_state),
            assumptions,
            budget,
        )?;
        let [path] = paths.as_slice() else {
            return Ok(false);
        };
        for fact in &path.facts {
            *assumptions = assumptions
                .clone()
                .assume_proposition(fact.proposition().clone());
        }
        for obligation in &path.obligations {
            *assumptions = assumptions
                .clone()
                .assume_proposition(obligation.proposition().clone());
        }
        assume_contract_proposition(assumptions, path.proposition.clone());
    }
    Ok(true)
}

/// Adds a contract proposition and the deterministic logical consequences
/// exposed by facts already present in this local refinement context.
fn assume_contract_proposition(assumptions: &mut PureFactContext, proposition: Proposition) {
    *assumptions = assumptions.clone().assume_proposition(proposition.clone());
    match proposition {
        Proposition::Equal(Term::Sequence(left), Term::Sequence(right)) => {
            // Linear decomposition of this explicitly selected premise.
            for (left, right) in
                super::spec::sequence_elements(&left).zip(super::spec::sequence_elements(&right))
            {
                if let Some(equality) = super::spec::integer_sequence_element_equality(left, right)
                {
                    *assumptions = assumptions.clone().assume_proposition(equality);
                }
            }
        }
        Proposition::And(left, right) => {
            assume_contract_proposition(assumptions, *left);
            assume_contract_proposition(assumptions, *right);
        }
        // Modus ponens on an explicitly assumed contract premise, with the
        // antecedent established by the exact routes only. An antecedent
        // those do not decide leaves the implication assumed as written;
        // the consequent then needs an explicit proof step.
        Proposition::Implies(left, right)
            if required_obligation_is_exactly_discharged(assumptions, &left) =>
        {
            assume_contract_proposition(assumptions, *right);
        }
        _ => {}
    }
}

/// The obligation check below is route-restricted with the rest of package
/// 10(b) but has no reaching fixture: a refined requirement's lowered path
/// carries an obligation only when the surrounding refinement context cannot
/// already see the access, and in that case no route — exact or otherwise —
/// discharges it. Attempts through an owned field and through an explicit
/// `requires loadable(...)` both produced obligation-free paths.
fn prove_contract_propositions(
    state: &CState,
    entry_state: &CState,
    propositions: &[SpecProposition],
    assumptions: &mut PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    for proposition in propositions {
        let paths = lower_spec_proposition_at_state_with_loop_entry(
            state,
            proposition,
            Some(entry_state),
            assumptions,
            budget,
        )?;
        let [path] = paths.as_slice() else {
            return Ok(false);
        };
        for fact in &path.facts {
            *assumptions = assumptions
                .clone()
                .assume_proposition(fact.proposition().clone());
        }
        if path.obligations.iter().any(|obligation| {
            !required_obligation_is_exactly_discharged(assumptions, obligation.proposition())
        }) || !contract_refinement_proves(assumptions, &path.proposition)
        {
            return Ok(false);
        }
        for obligation in &path.obligations {
            *assumptions = assumptions
                .clone()
                .assume_proposition(obligation.proposition().clone());
        }
        *assumptions = assumptions
            .clone()
            .assume_proposition(path.proposition.clone());
    }
    Ok(true)
}

/// The exact routes a refinement check may use on one leaf proposition:
/// builtin propositions, indexed exact membership in the assumed facts, and
/// the frozen condition decision procedure on a bare condition. It performs
/// no logical search — it never assumes an antecedent, enumerates ambient
/// candidates, or recursively constructs a derivation. `Not` of a bare
/// condition is the same bare condition with the opposite value, which is how
/// `contains_assumed_exact` and `evaluate_guarded_contract_condition` already
/// read it.
fn refinement_route_proves(assumptions: &PureFactContext, proposition: &Proposition) -> bool {
    if assumptions.proves_exact(proposition) {
        return true;
    }
    match proposition {
        Proposition::ConditionIs(condition, value) => assumptions.decide(condition) == Some(*value),
        Proposition::Not(body) => match body.as_ref() {
            Proposition::ConditionIs(condition, value) => {
                assumptions.decide(condition) == Some(!*value)
            }
            _ => false,
        },
        _ => false,
    }
}

/// Checks one lowered contract clause against the refinement assumptions.
///
/// This is the exact leaf route and nothing else. The logical descent this
/// used to perform — sequence-element alignment, `and` split, `or` arm
/// choice, `implies` with a refuted antecedent, and a search over recorded
/// equality-class rewrites of a comparison's operands — was kernel proof
/// planning: it chose an index alignment, an arm, and a rewrite
/// representative, and issued refinement authority from that choice with no
/// record of it. Those choices now belong to the refinement theorem's proof,
/// where `both`, `left`/`right`, `intro`, `extract`, and `rewrite` spell them
/// and `click expand` prints them. See `prepare_contract_refinement_obligations`,
/// which emits the refinement implication, and
/// `api.rs::prove_c_function_contract_refinement`, which issues authority only
/// from a closed proof of exactly that implication.
fn contract_refinement_proves(assumptions: &PureFactContext, proposition: &Proposition) -> bool {
    refinement_route_proves(assumptions, proposition)
}

fn spec_proposition_is_state_independent(proposition: &SpecProposition) -> bool {
    match proposition {
        SpecProposition::Comparison { left, right, .. } => {
            spec_expression_is_state_independent(left)
                && spec_expression_is_state_independent(right)
        }
        SpecProposition::FloatClassification { expression, .. }
        | SpecProposition::Defined(expression) => spec_expression_is_state_independent(expression),
        SpecProposition::And(left, right)
        | SpecProposition::Or(left, right)
        | SpecProposition::Implies(left, right) => {
            spec_proposition_is_state_independent(left)
                && spec_proposition_is_state_independent(right)
        }
        SpecProposition::Not(body)
        | SpecProposition::ForAllInt32 { body, .. }
        | SpecProposition::ForAllInteger { body, .. }
        | SpecProposition::ForAllPointer { body, .. }
        | SpecProposition::ExistsInt32 { body, .. }
        | SpecProposition::ExistsInteger { body, .. }
        | SpecProposition::ExistsPointer { body, .. } => {
            spec_proposition_is_state_independent(body)
        }
        _ => false,
    }
}

/// The stateful refinement rule admits ordinary scalar propositions whose only
/// stateful operation is a C memory access (possibly below `old`), including
/// finite sequence comparisons and membership, plus resource-field reads and
/// the algebraic values those fields carry. Explicit memory snapshots,
/// `at(...)`, counted-resource populations, and range folds stay outside it:
/// their stateful refinement laws are not written down, so they need an
/// explicit refinement theorem. Mathematical `Integer` comparisons stay
/// outside it for the same reason. The caller separately checks resource and
/// footprint refinement.
///
/// Every variant is listed. A new specification form is excluded until its
/// refinement behaviour has been considered, which a wildcard would silently
/// reverse.
fn spec_proposition_supports_stateful_memory_refinement(proposition: &SpecProposition) -> bool {
    match proposition {
        SpecProposition::SequenceComparison { left, right, .. } => {
            spec_sequence_supports_stateful_memory_refinement(left)
                && spec_sequence_supports_stateful_memory_refinement(right)
        }
        SpecProposition::SequenceMembership { element, sequence } => {
            spec_expression_supports_stateful_memory_refinement(element)
                && spec_sequence_supports_stateful_memory_refinement(sequence)
        }
        SpecProposition::Comparison { left, right, .. } => {
            spec_expression_supports_stateful_memory_refinement(left)
                && spec_expression_supports_stateful_memory_refinement(right)
        }
        SpecProposition::AlgebraicComparison { left, right, .. } => {
            spec_algebraic_expression_supports_stateful_memory_refinement(left)
                && spec_algebraic_expression_supports_stateful_memory_refinement(right)
        }
        SpecProposition::FloatClassification { expression, .. }
        | SpecProposition::Defined(expression) => {
            spec_expression_supports_stateful_memory_refinement(expression)
        }
        SpecProposition::And(left, right)
        | SpecProposition::Or(left, right)
        | SpecProposition::Implies(left, right) => {
            spec_proposition_supports_stateful_memory_refinement(left)
                && spec_proposition_supports_stateful_memory_refinement(right)
        }
        SpecProposition::Not(body)
        | SpecProposition::ForAllInt32 { body, .. }
        | SpecProposition::ForAllInteger { body, .. }
        | SpecProposition::ForAllPointer { body, .. }
        | SpecProposition::ExistsInt32 { body, .. }
        | SpecProposition::ExistsInteger { body, .. }
        | SpecProposition::ExistsPointer { body, .. } => {
            spec_proposition_supports_stateful_memory_refinement(body)
        }
        SpecProposition::IntegerComparison { .. }
        | SpecProposition::Predicate { .. }
        | SpecProposition::ResourceSeparate { .. }
        | SpecProposition::ResourceContains { .. }
        | SpecProposition::MemoryLoadable { .. } => false,
    }
}

fn spec_sequence_supports_stateful_memory_refinement(sequence: &SpecSequenceExpression) -> bool {
    match sequence {
        SpecSequenceExpression::Literal(elements) => elements
            .iter()
            .all(spec_expression_supports_stateful_memory_refinement),
        SpecSequenceExpression::Concat(left, right) => {
            spec_sequence_supports_stateful_memory_refinement(left)
                && spec_sequence_supports_stateful_memory_refinement(right)
        }
    }
}

fn spec_expression_supports_stateful_memory_refinement(expression: &SpecExpression) -> bool {
    match expression {
        // A field read names an instance the two interfaces share. Both the
        // current and the entry projection lower through
        // `resource_instance_at_path` against the state the caller supplies;
        // a projection the state cannot answer refuses the refinement there.
        SpecExpression::ResourceField { .. } => true,
        SpecExpression::Value(_) => true,
        SpecExpression::IntegerToMachine { .. } => false,
        SpecExpression::CExpression(expression) => {
            c_expression_supports_stateful_memory_refinement(expression)
        }
        SpecExpression::Add(left, right)
        | SpecExpression::Subtract(left, right)
        | SpecExpression::Multiply(left, right)
        | SpecExpression::Divide(left, right)
        | SpecExpression::Remainder(left, right)
        | SpecExpression::ShiftLeft(left, right)
        | SpecExpression::ShiftRight(left, right)
        | SpecExpression::BitwiseAnd(left, right)
        | SpecExpression::BitwiseOr(left, right)
        | SpecExpression::BitwiseXor(left, right) => {
            spec_expression_supports_stateful_memory_refinement(left)
                && spec_expression_supports_stateful_memory_refinement(right)
        }
        SpecExpression::BitwiseNot(body) | SpecExpression::Cast(body, _) => {
            spec_expression_supports_stateful_memory_refinement(body)
        }
        SpecExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            spec_proposition_supports_stateful_memory_refinement(condition)
                && spec_expression_supports_stateful_memory_refinement(then_branch)
                && spec_expression_supports_stateful_memory_refinement(else_branch)
        }
        SpecExpression::Let { value, body, .. } => {
            spec_expression_supports_stateful_memory_refinement(value)
                && spec_expression_supports_stateful_memory_refinement(body)
        }
        SpecExpression::PureFunctionApplication { arguments, .. } => arguments
            .iter()
            .all(spec_pure_function_argument_supports_stateful_memory_refinement),
        SpecExpression::PointerOffset {
            pointer, elements, ..
        } => {
            spec_expression_supports_stateful_memory_refinement(pointer)
                && spec_expression_supports_stateful_memory_refinement(elements)
        }
        SpecExpression::MemoryLoad {
            memory: SpecMemory::Current | SpecMemory::FunctionEntry,
            pointer,
            ..
        } => spec_expression_supports_stateful_memory_refinement(pointer),
        SpecExpression::AlgebraicMatch { scrutinee, arms } => {
            spec_algebraic_expression_supports_stateful_memory_refinement(scrutinee)
                && arms
                    .iter()
                    .all(|arm| spec_expression_supports_stateful_memory_refinement(&arm.body))
        }
        SpecExpression::CountedResourceCount { .. }
        | SpecExpression::RangeFold { .. }
        | SpecExpression::LoopEntrySnapshot(_)
        | SpecExpression::MemoryLoad { .. } => false,
    }
}

/// Algebraic values are ordinary terms over instance fields, constructors,
/// match arms, and opaque pure functions. None of them reads memory except
/// through the `SpecExpression` nodes below, which are filtered by the same
/// rule, so an algebraic clause is admitted exactly when its scalar leaves
/// are.
fn spec_algebraic_expression_supports_stateful_memory_refinement(
    expression: &SpecAlgebraicExpression,
) -> bool {
    match &expression.node {
        SpecAlgebraicExpressionNode::Variable(_)
        | SpecAlgebraicExpressionNode::Binding(_)
        | SpecAlgebraicExpressionNode::ResourceField(_) => true,
        SpecAlgebraicExpressionNode::Constructor { fields, .. } => fields
            .iter()
            .all(spec_algebraic_value_supports_stateful_memory_refinement),
        SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
            spec_algebraic_expression_supports_stateful_memory_refinement(scrutinee)
                && arms.iter().all(|arm| {
                    spec_algebraic_expression_supports_stateful_memory_refinement(&arm.body)
                })
        }
        SpecAlgebraicExpressionNode::PureFunctionApplication { arguments, .. } => arguments
            .iter()
            .all(spec_pure_function_argument_supports_stateful_memory_refinement),
    }
}

fn spec_algebraic_value_supports_stateful_memory_refinement(value: &SpecAlgebraicValue) -> bool {
    match value {
        SpecAlgebraicValue::C(expression) => {
            spec_expression_supports_stateful_memory_refinement(expression)
        }
        // Mathematical `Integer` values keep the exclusion that
        // `SpecPureFunctionArgument::Integer` already states.
        SpecAlgebraicValue::Integer(_) => false,
        SpecAlgebraicValue::Algebraic(expression) => {
            spec_algebraic_expression_supports_stateful_memory_refinement(expression)
        }
    }
}

fn spec_pure_function_argument_supports_stateful_memory_refinement(
    argument: &SpecPureFunctionArgument,
) -> bool {
    match argument {
        SpecPureFunctionArgument::Value(expression) => {
            spec_expression_supports_stateful_memory_refinement(expression)
        }
        SpecPureFunctionArgument::Integer(_) => false,
        SpecPureFunctionArgument::Algebraic(expression) => {
            spec_algebraic_expression_supports_stateful_memory_refinement(expression)
        }
        // An array snapshot is an explicit memory image; its stateful
        // refinement law is not written down.
        SpecPureFunctionArgument::ArrayRef { .. } => false,
    }
}

fn c_expression_supports_stateful_memory_refinement(expression: &CExpression) -> bool {
    match expression {
        CExpression::Value(_) | CExpression::Variable(_) | CExpression::FunctionAddress(_) => true,
        CExpression::Cast { expression, .. }
        | CExpression::FloatNegate(expression)
        | CExpression::FloatClassification { expression, .. }
        | CExpression::AddressOf(expression)
        | CExpression::PointerOffsetBytes {
            pointer: expression,
            ..
        }
        | CExpression::Not(expression)
        | CExpression::BitwiseNot(expression)
        | CExpression::Load(expression) => {
            c_expression_supports_stateful_memory_refinement(expression)
        }
        CExpression::TypedLoad { pointer, .. } => {
            c_expression_supports_stateful_memory_refinement(pointer)
        }
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            c_expression_supports_stateful_memory_refinement(condition)
                && c_expression_supports_stateful_memory_refinement(then_branch)
                && c_expression_supports_stateful_memory_refinement(else_branch)
        }
        CExpression::LessThan(left, right)
        | CExpression::LessEqual(left, right)
        | CExpression::GreaterThan(left, right)
        | CExpression::GreaterEqual(left, right)
        | CExpression::Equal(left, right)
        | CExpression::NotEqual(left, right)
        | CExpression::And(left, right)
        | CExpression::Or(left, right)
        | CExpression::Add(left, right)
        | CExpression::Subtract(left, right)
        | CExpression::Multiply(left, right)
        | CExpression::Divide(left, right)
        | CExpression::Remainder(left, right)
        | CExpression::ShiftLeft(left, right)
        | CExpression::ShiftRight(left, right)
        | CExpression::BitwiseAnd(left, right)
        | CExpression::BitwiseOr(left, right)
        | CExpression::BitwiseXor(left, right)
        | CExpression::Index(left, right) => {
            c_expression_supports_stateful_memory_refinement(left)
                && c_expression_supports_stateful_memory_refinement(right)
        }
    }
}

fn spec_expression_is_state_independent(expression: &SpecExpression) -> bool {
    match expression {
        SpecExpression::Value(_) => true,
        SpecExpression::CExpression(expression) => c_expression_is_state_independent(expression),
        SpecExpression::Add(left, right)
        | SpecExpression::Subtract(left, right)
        | SpecExpression::Multiply(left, right)
        | SpecExpression::Divide(left, right)
        | SpecExpression::Remainder(left, right)
        | SpecExpression::ShiftLeft(left, right)
        | SpecExpression::ShiftRight(left, right)
        | SpecExpression::BitwiseAnd(left, right)
        | SpecExpression::BitwiseOr(left, right)
        | SpecExpression::BitwiseXor(left, right) => {
            spec_expression_is_state_independent(left)
                && spec_expression_is_state_independent(right)
        }
        SpecExpression::BitwiseNot(body)
        | SpecExpression::LoopEntrySnapshot(body)
        | SpecExpression::Cast(body, _) => spec_expression_is_state_independent(body),
        SpecExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            spec_proposition_is_state_independent(condition)
                && spec_expression_is_state_independent(then_branch)
                && spec_expression_is_state_independent(else_branch)
        }
        SpecExpression::Let { value, body, .. } => {
            spec_expression_is_state_independent(value)
                && spec_expression_is_state_independent(body)
        }
        SpecExpression::PureFunctionApplication { arguments, .. } => arguments
            .iter()
            .all(spec_pure_function_argument_is_state_independent),
        SpecExpression::PointerOffset {
            pointer, elements, ..
        } => {
            spec_expression_is_state_independent(pointer)
                && spec_expression_is_state_independent(elements)
        }
        _ => false,
    }
}

fn spec_pure_function_argument_is_state_independent(argument: &SpecPureFunctionArgument) -> bool {
    match argument {
        SpecPureFunctionArgument::Value(expression) => {
            spec_expression_is_state_independent(expression)
        }
        SpecPureFunctionArgument::Integer(_) => true,
        SpecPureFunctionArgument::Algebraic(expression) => {
            spec_algebraic_expression_is_state_independent(expression)
        }
        SpecPureFunctionArgument::ArrayRef { .. } => false,
    }
}

/// The datatype reflexivity shortcut may skip evaluation only for expressions
/// that cannot emit a guard or obligation. State independence alone does not
/// imply totality: a mathematical conversion may have a required domain.
pub(super) fn spec_algebraic_expression_is_obligation_free(
    expression: &SpecAlgebraicExpression,
) -> bool {
    match &expression.node {
        SpecAlgebraicExpressionNode::Variable(_) | SpecAlgebraicExpressionNode::Binding(_) => true,
        SpecAlgebraicExpressionNode::Constructor { fields, .. } => {
            fields.iter().all(|field| match field {
                SpecAlgebraicValue::C(value) => spec_value_is_obligation_free(value),
                SpecAlgebraicValue::Integer(value) => spec_integer_is_obligation_free(value),
                SpecAlgebraicValue::Algebraic(value) => {
                    spec_algebraic_expression_is_obligation_free(value)
                }
            })
        }
        SpecAlgebraicExpressionNode::PureFunctionApplication { name, arguments } => {
            name != "to_nat" && arguments.iter().all(spec_argument_is_obligation_free)
        }
        SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
            if !spec_algebraic_expression_is_obligation_free(scrutinee)
                || arms.len() != scrutinee.algebraic_type.variants.len()
            {
                return false;
            }
            let variants = scrutinee
                .algebraic_type
                .variants
                .iter()
                .map(|variant| (variant.name.as_str(), variant.fields.len()))
                .collect::<BTreeMap<_, _>>();
            let mut seen = BTreeSet::new();
            arms.iter().all(|arm| {
                seen.insert(arm.variant.as_str())
                    && variants.get(arm.variant.as_str()) == Some(&arm.bindings.len())
                    && spec_algebraic_expression_is_obligation_free(&arm.body)
            })
        }
        SpecAlgebraicExpressionNode::ResourceField(_) => false,
    }
}

fn spec_argument_is_obligation_free(argument: &SpecPureFunctionArgument) -> bool {
    match argument {
        SpecPureFunctionArgument::Value(value) => spec_value_is_obligation_free(value),
        SpecPureFunctionArgument::Integer(value) => spec_integer_is_obligation_free(value),
        SpecPureFunctionArgument::Algebraic(value) => {
            spec_algebraic_expression_is_obligation_free(value)
        }
        SpecPureFunctionArgument::ArrayRef { .. } => false,
    }
}

fn spec_value_is_obligation_free(value: &SpecExpression) -> bool {
    matches!(
        value,
        SpecExpression::Value(_)
            | SpecExpression::CExpression(
                CExpression::Value(_) | CExpression::Variable(_) | CExpression::FunctionAddress(_)
            )
    )
}

fn spec_integer_is_obligation_free(value: &SpecIntegerExpression) -> bool {
    match value {
        SpecIntegerExpression::Term(_) => true,
        SpecIntegerExpression::Negate(inner) => spec_integer_is_obligation_free(inner),
        SpecIntegerExpression::Add(left, right)
        | SpecIntegerExpression::Subtract(left, right)
        | SpecIntegerExpression::Multiply(left, right) => {
            spec_integer_is_obligation_free(left) && spec_integer_is_obligation_free(right)
        }
        SpecIntegerExpression::PureFunctionApplication { arguments, .. } => {
            arguments.iter().all(spec_argument_is_obligation_free)
        }
        SpecIntegerExpression::AlgebraicMatch { .. } => false,
        SpecIntegerExpression::FromMachine(_) | SpecIntegerExpression::ResourceField(_) => false,
        SpecIntegerExpression::RangeFold { .. } => false,
    }
}

pub(super) fn spec_algebraic_expression_is_state_independent(
    expression: &SpecAlgebraicExpression,
) -> bool {
    match &expression.node {
        SpecAlgebraicExpressionNode::ResourceField(_) => false,
        SpecAlgebraicExpressionNode::Variable(_) | SpecAlgebraicExpressionNode::Binding(_) => true,
        SpecAlgebraicExpressionNode::Constructor { fields, .. } => {
            fields.iter().all(|field| match field {
                SpecAlgebraicValue::C(expression) => {
                    spec_expression_is_state_independent(expression)
                }
                SpecAlgebraicValue::Integer(_) => true,
                SpecAlgebraicValue::Algebraic(expression) => {
                    spec_algebraic_expression_is_state_independent(expression)
                }
            })
        }
        SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
            spec_algebraic_expression_is_state_independent(scrutinee)
                && arms
                    .iter()
                    .all(|arm| spec_algebraic_expression_is_state_independent(&arm.body))
        }
        SpecAlgebraicExpressionNode::PureFunctionApplication { arguments, .. } => arguments
            .iter()
            .all(spec_pure_function_argument_is_state_independent),
    }
}

fn c_expression_is_state_independent(expression: &CExpression) -> bool {
    match expression {
        CExpression::Value(_) | CExpression::Variable(_) | CExpression::FunctionAddress(_) => true,
        CExpression::Cast { expression, .. }
        | CExpression::FloatNegate(expression)
        | CExpression::FloatClassification { expression, .. }
        | CExpression::PointerOffsetBytes {
            pointer: expression,
            ..
        }
        | CExpression::Not(expression)
        | CExpression::BitwiseNot(expression) => c_expression_is_state_independent(expression),
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            c_expression_is_state_independent(condition)
                && c_expression_is_state_independent(then_branch)
                && c_expression_is_state_independent(else_branch)
        }
        CExpression::LessThan(left, right)
        | CExpression::LessEqual(left, right)
        | CExpression::GreaterThan(left, right)
        | CExpression::GreaterEqual(left, right)
        | CExpression::Equal(left, right)
        | CExpression::NotEqual(left, right)
        | CExpression::And(left, right)
        | CExpression::Or(left, right)
        | CExpression::Add(left, right)
        | CExpression::Subtract(left, right)
        | CExpression::Multiply(left, right)
        | CExpression::Divide(left, right)
        | CExpression::Remainder(left, right)
        | CExpression::ShiftLeft(left, right)
        | CExpression::ShiftRight(left, right)
        | CExpression::BitwiseAnd(left, right)
        | CExpression::BitwiseOr(left, right)
        | CExpression::BitwiseXor(left, right) => {
            c_expression_is_state_independent(left) && c_expression_is_state_independent(right)
        }
        CExpression::AddressOf(_)
        | CExpression::Load(_)
        | CExpression::TypedLoad { .. }
        | CExpression::Index(_, _) => false,
    }
}

/// Whether a specification expression reads a by-value aggregate parameter
/// from the current callee state. Entry-state reads (`old(...)`) use
/// `SpecMemory::FunctionEntry` and are intentionally ignored: they describe
/// the caller's argument image, which is stable across the call.
fn spec_expression_reads_current_parameter(
    expression: &SpecExpression,
    parameter_name: &str,
) -> bool {
    match expression {
        SpecExpression::Value(_) | SpecExpression::ResourceField { .. } => false,
        SpecExpression::IntegerToMachine { value, .. } => {
            spec_integer_expression_reads_current_parameter(value, parameter_name)
        }
        SpecExpression::CExpression(expression) => {
            c_expression_mentions_variable(expression, parameter_name)
        }
        SpecExpression::AlgebraicMatch { scrutinee, arms } => {
            spec_algebraic_expression_reads_current_parameter(scrutinee, parameter_name)
                || arms
                    .iter()
                    .any(|arm| spec_expression_reads_current_parameter(&arm.body, parameter_name))
        }
        SpecExpression::CountedResourceCount { arguments, .. } => arguments
            .iter()
            .flatten()
            .any(|argument| spec_expression_reads_current_parameter(argument, parameter_name)),
        SpecExpression::Add(left, right)
        | SpecExpression::Subtract(left, right)
        | SpecExpression::Multiply(left, right)
        | SpecExpression::Divide(left, right)
        | SpecExpression::Remainder(left, right)
        | SpecExpression::ShiftLeft(left, right)
        | SpecExpression::ShiftRight(left, right)
        | SpecExpression::BitwiseAnd(left, right)
        | SpecExpression::BitwiseOr(left, right)
        | SpecExpression::BitwiseXor(left, right) => {
            spec_expression_reads_current_parameter(left, parameter_name)
                || spec_expression_reads_current_parameter(right, parameter_name)
        }
        SpecExpression::BitwiseNot(body)
        | SpecExpression::Cast(body, _)
        | SpecExpression::LoopEntrySnapshot(body) => {
            spec_expression_reads_current_parameter(body, parameter_name)
        }
        SpecExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            spec_proposition_reads_current_parameter(condition, parameter_name)
                || spec_expression_reads_current_parameter(then_branch, parameter_name)
                || spec_expression_reads_current_parameter(else_branch, parameter_name)
        }
        SpecExpression::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            spec_expression_reads_current_parameter(start, parameter_name)
                || spec_expression_reads_current_parameter(end, parameter_name)
                || spec_expression_reads_current_parameter(initial, parameter_name)
                || spec_expression_reads_current_parameter(body, parameter_name)
        }
        SpecExpression::Let { value, body, .. } => {
            spec_expression_reads_current_parameter(value, parameter_name)
                || spec_expression_reads_current_parameter(body, parameter_name)
        }
        SpecExpression::PureFunctionApplication { arguments, .. } => {
            arguments.iter().any(|argument| {
                spec_pure_function_argument_reads_current_parameter(argument, parameter_name)
            })
        }
        SpecExpression::PointerOffset {
            pointer, elements, ..
        } => {
            spec_expression_reads_current_parameter(pointer, parameter_name)
                || spec_expression_reads_current_parameter(elements, parameter_name)
        }
        SpecExpression::MemoryLoad {
            memory: SpecMemory::FunctionEntry | SpecMemory::Fixed(_),
            ..
        } => false,
        SpecExpression::MemoryLoad { pointer, .. } => {
            spec_expression_reads_current_parameter(pointer, parameter_name)
        }
    }
}

fn spec_integer_expression_reads_current_parameter(
    expression: &SpecIntegerExpression,
    parameter_name: &str,
) -> bool {
    match expression {
        SpecIntegerExpression::Term(_) | SpecIntegerExpression::ResourceField(_) => false,
        SpecIntegerExpression::PureFunctionApplication { arguments, .. } => {
            arguments.iter().any(|argument| {
                spec_pure_function_argument_reads_current_parameter(argument, parameter_name)
            })
        }
        SpecIntegerExpression::AlgebraicMatch { scrutinee, arms } => {
            spec_algebraic_expression_reads_current_parameter(scrutinee, parameter_name)
                || arms.iter().any(|arm| {
                    spec_integer_expression_reads_current_parameter(&arm.body, parameter_name)
                })
        }
        SpecIntegerExpression::FromMachine(machine) => {
            spec_expression_reads_current_parameter(machine, parameter_name)
        }
        SpecIntegerExpression::Negate(inner) => {
            spec_integer_expression_reads_current_parameter(inner, parameter_name)
        }
        SpecIntegerExpression::Add(left, right)
        | SpecIntegerExpression::Subtract(left, right)
        | SpecIntegerExpression::Multiply(left, right) => {
            spec_integer_expression_reads_current_parameter(left, parameter_name)
                || spec_integer_expression_reads_current_parameter(right, parameter_name)
        }
        SpecIntegerExpression::RangeFold {
            index,
            initial,
            body,
            ..
        } => {
            let index_reads = match index {
                SpecIntegerRangeFoldIndex::Int32 { start, end } => {
                    spec_expression_reads_current_parameter(start, parameter_name)
                        || spec_expression_reads_current_parameter(end, parameter_name)
                }
                SpecIntegerRangeFoldIndex::Integer { start, end } => {
                    spec_integer_expression_reads_current_parameter(start, parameter_name)
                        || spec_integer_expression_reads_current_parameter(end, parameter_name)
                }
            };
            index_reads
                || spec_integer_expression_reads_current_parameter(initial, parameter_name)
                || spec_integer_expression_reads_current_parameter(body, parameter_name)
        }
    }
}

fn spec_proposition_reads_current_parameter(
    proposition: &SpecProposition,
    parameter_name: &str,
) -> bool {
    match proposition {
        SpecProposition::IntegerComparison { left, right, .. } => {
            spec_integer_expression_reads_current_parameter(left, parameter_name)
                || spec_integer_expression_reads_current_parameter(right, parameter_name)
        }
        SpecProposition::AlgebraicComparison { left, right, .. } => {
            spec_algebraic_expression_reads_current_parameter(left, parameter_name)
                || spec_algebraic_expression_reads_current_parameter(right, parameter_name)
        }
        SpecProposition::SequenceMembership { element, sequence } => {
            spec_expression_reads_current_parameter(element, parameter_name)
                || spec_sequence_reads_current_parameter(sequence, parameter_name)
        }
        SpecProposition::SequenceComparison { left, right, .. } => {
            spec_sequence_reads_current_parameter(left, parameter_name)
                || spec_sequence_reads_current_parameter(right, parameter_name)
        }
        SpecProposition::Comparison { left, right, .. } => {
            spec_expression_reads_current_parameter(left, parameter_name)
                || spec_expression_reads_current_parameter(right, parameter_name)
        }
        SpecProposition::FloatClassification { expression, .. }
        | SpecProposition::Defined(expression) => {
            spec_expression_reads_current_parameter(expression, parameter_name)
        }
        SpecProposition::And(left, right)
        | SpecProposition::Or(left, right)
        | SpecProposition::Implies(left, right) => {
            spec_proposition_reads_current_parameter(left, parameter_name)
                || spec_proposition_reads_current_parameter(right, parameter_name)
        }
        SpecProposition::Not(body)
        | SpecProposition::ForAllInt32 { body, .. }
        | SpecProposition::ForAllInteger { body, .. }
        | SpecProposition::ForAllPointer { body, .. }
        | SpecProposition::ExistsInt32 { body, .. }
        | SpecProposition::ExistsInteger { body, .. }
        | SpecProposition::ExistsPointer { body, .. } => {
            spec_proposition_reads_current_parameter(body, parameter_name)
        }
        SpecProposition::Predicate { arguments, .. } => {
            arguments.iter().any(|argument| match argument {
                SpecPredicateArgument::Value(expression) => {
                    spec_expression_reads_current_parameter(expression, parameter_name)
                }
                SpecPredicateArgument::ArrayRef { memory, pointer } => {
                    !matches!(memory, SpecMemory::FunctionEntry | SpecMemory::Fixed(_))
                        && spec_expression_reads_current_parameter(pointer, parameter_name)
                }
            })
        }
        SpecProposition::ResourceSeparate { left, right }
        | SpecProposition::ResourceContains {
            parent: left,
            child: right,
        } => {
            spec_resource_reads_current_parameter(left, parameter_name)
                || spec_resource_reads_current_parameter(right, parameter_name)
        }
        SpecProposition::MemoryLoadable {
            memory,
            base,
            start,
            end,
            ..
        } => {
            !matches!(memory, SpecMemory::FunctionEntry | SpecMemory::Fixed(_))
                && (spec_expression_reads_current_parameter(base, parameter_name)
                    || spec_expression_reads_current_parameter(start, parameter_name)
                    || spec_expression_reads_current_parameter(end, parameter_name))
        }
    }
}

fn spec_sequence_reads_current_parameter(
    sequence: &SpecSequenceExpression,
    parameter_name: &str,
) -> bool {
    match sequence {
        SpecSequenceExpression::Literal(elements) => elements
            .iter()
            .any(|element| spec_expression_reads_current_parameter(element, parameter_name)),
        SpecSequenceExpression::Concat(left, right) => {
            spec_sequence_reads_current_parameter(left, parameter_name)
                || spec_sequence_reads_current_parameter(right, parameter_name)
        }
    }
}

fn spec_resource_reads_current_parameter(resource: &SpecResource, parameter_name: &str) -> bool {
    match resource {
        SpecResource::Memory {
            base, start, end, ..
        } => {
            spec_expression_reads_current_parameter(base, parameter_name)
                || spec_expression_reads_current_parameter(start, parameter_name)
                || spec_expression_reads_current_parameter(end, parameter_name)
        }
        SpecResource::Composite { arguments, .. } | SpecResource::Token { arguments, .. } => {
            arguments
                .iter()
                .any(|argument| spec_expression_reads_current_parameter(argument, parameter_name))
        }
    }
}

fn spec_algebraic_expression_reads_current_parameter(
    expression: &SpecAlgebraicExpression,
    parameter_name: &str,
) -> bool {
    match &expression.node {
        SpecAlgebraicExpressionNode::Variable(_)
        | SpecAlgebraicExpressionNode::Binding(_)
        | SpecAlgebraicExpressionNode::ResourceField(_) => false,
        SpecAlgebraicExpressionNode::Constructor { fields, .. } => {
            fields.iter().any(|field| match field {
                SpecAlgebraicValue::C(expression) => {
                    spec_expression_reads_current_parameter(expression, parameter_name)
                }
                SpecAlgebraicValue::Integer(_) => false,
                SpecAlgebraicValue::Algebraic(expression) => {
                    spec_algebraic_expression_reads_current_parameter(expression, parameter_name)
                }
            })
        }
        SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
            spec_algebraic_expression_reads_current_parameter(scrutinee, parameter_name)
                || arms.iter().any(|arm| {
                    spec_algebraic_expression_reads_current_parameter(&arm.body, parameter_name)
                })
        }
        SpecAlgebraicExpressionNode::PureFunctionApplication { arguments, .. } => {
            arguments.iter().any(|argument| {
                spec_pure_function_argument_reads_current_parameter(argument, parameter_name)
            })
        }
    }
}

fn spec_pure_function_argument_reads_current_parameter(
    argument: &SpecPureFunctionArgument,
    parameter_name: &str,
) -> bool {
    match argument {
        SpecPureFunctionArgument::Value(expression) => {
            spec_expression_reads_current_parameter(expression, parameter_name)
        }
        SpecPureFunctionArgument::Integer(_) => false,
        SpecPureFunctionArgument::Algebraic(expression) => {
            spec_algebraic_expression_reads_current_parameter(expression, parameter_name)
        }
        SpecPureFunctionArgument::ArrayRef {
            memory, pointer, ..
        } => {
            !matches!(memory, SpecMemory::FunctionEntry | SpecMemory::Fixed(_))
                && spec_expression_reads_current_parameter(pointer, parameter_name)
        }
    }
}

fn c_expression_mentions_variable(expression: &CExpression, name: &str) -> bool {
    match expression {
        CExpression::Variable(variable) => variable == name,
        CExpression::Value(_) | CExpression::FunctionAddress(_) => false,
        CExpression::Cast { expression, .. }
        | CExpression::FloatNegate(expression)
        | CExpression::FloatClassification { expression, .. }
        | CExpression::AddressOf(expression)
        | CExpression::PointerOffsetBytes {
            pointer: expression,
            ..
        }
        | CExpression::Not(expression)
        | CExpression::Load(expression)
        | CExpression::TypedLoad {
            pointer: expression,
            ..
        }
        | CExpression::BitwiseNot(expression) => c_expression_mentions_variable(expression, name),
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            c_expression_mentions_variable(condition, name)
                || c_expression_mentions_variable(then_branch, name)
                || c_expression_mentions_variable(else_branch, name)
        }
        CExpression::LessThan(left, right)
        | CExpression::LessEqual(left, right)
        | CExpression::GreaterThan(left, right)
        | CExpression::GreaterEqual(left, right)
        | CExpression::Equal(left, right)
        | CExpression::NotEqual(left, right)
        | CExpression::And(left, right)
        | CExpression::Or(left, right)
        | CExpression::Add(left, right)
        | CExpression::Subtract(left, right)
        | CExpression::Multiply(left, right)
        | CExpression::Divide(left, right)
        | CExpression::Remainder(left, right)
        | CExpression::ShiftLeft(left, right)
        | CExpression::ShiftRight(left, right)
        | CExpression::BitwiseAnd(left, right)
        | CExpression::BitwiseOr(left, right)
        | CExpression::BitwiseXor(left, right)
        | CExpression::Index(left, right) => {
            c_expression_mentions_variable(left, name)
                || c_expression_mentions_variable(right, name)
        }
    }
}

fn c_expression_takes_address_of_variable(expression: &CExpression, name: &str) -> bool {
    match expression {
        CExpression::AddressOf(expression) => c_expression_mentions_variable(expression, name),
        CExpression::Value(_) | CExpression::Variable(_) | CExpression::FunctionAddress(_) => false,
        CExpression::Cast { expression, .. }
        | CExpression::FloatNegate(expression)
        | CExpression::FloatClassification { expression, .. }
        | CExpression::PointerOffsetBytes {
            pointer: expression,
            ..
        }
        | CExpression::Not(expression)
        | CExpression::Load(expression)
        | CExpression::TypedLoad {
            pointer: expression,
            ..
        }
        | CExpression::BitwiseNot(expression) => {
            c_expression_takes_address_of_variable(expression, name)
        }
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            c_expression_takes_address_of_variable(condition, name)
                || c_expression_takes_address_of_variable(then_branch, name)
                || c_expression_takes_address_of_variable(else_branch, name)
        }
        CExpression::LessThan(left, right)
        | CExpression::LessEqual(left, right)
        | CExpression::GreaterThan(left, right)
        | CExpression::GreaterEqual(left, right)
        | CExpression::Equal(left, right)
        | CExpression::NotEqual(left, right)
        | CExpression::And(left, right)
        | CExpression::Or(left, right)
        | CExpression::Add(left, right)
        | CExpression::Subtract(left, right)
        | CExpression::Multiply(left, right)
        | CExpression::Divide(left, right)
        | CExpression::Remainder(left, right)
        | CExpression::ShiftLeft(left, right)
        | CExpression::ShiftRight(left, right)
        | CExpression::BitwiseAnd(left, right)
        | CExpression::BitwiseOr(left, right)
        | CExpression::BitwiseXor(left, right)
        | CExpression::Index(left, right) => {
            c_expression_takes_address_of_variable(left, name)
                || c_expression_takes_address_of_variable(right, name)
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ParameterAccessRange {
    start: u32,
    end: u32,
}

fn parameter_access_range(start: u32, width: u32) -> Option<ParameterAccessRange> {
    (width > 0).then_some(())?;
    Some(ParameterAccessRange {
        start,
        end: start.checked_add(width)?,
    })
}

impl ParameterAccessRange {
    fn overlaps(self, other: Self) -> bool {
        self.start < other.end && other.start < self.end
    }
}

fn c_expression_parameter_offset(expression: &CExpression, parameter_name: &str) -> Option<u32> {
    match expression {
        CExpression::Variable(variable) if variable == parameter_name => Some(0),
        CExpression::PointerOffsetBytes { pointer, bytes } => {
            c_expression_parameter_offset(pointer, parameter_name)?.checked_add(*bytes)
        }
        CExpression::Cast { expression, .. } => {
            c_expression_parameter_offset(expression, parameter_name)
        }
        _ => None,
    }
}

fn spec_expression_constant(expression: &SpecExpression) -> Option<u32> {
    let SpecExpression::Value(value) = expression else {
        return None;
    };
    match value {
        CValue::Int16(term)
        | CValue::Int32(term)
        | CValue::UInt8(term)
        | CValue::UInt16(term)
        | CValue::UInt32(term)
        | CValue::Int64(term)
        | CValue::UInt64(term) => term.as_const(),
        CValue::Void | CValue::Float32(_) | CValue::Float64(_) | CValue::Pointer(_) => None,
        CValue::Bool(term) => term.as_const(),
    }
}

fn spec_expression_parameter_offset(
    expression: &SpecExpression,
    parameter_name: &str,
) -> Option<u32> {
    match expression {
        SpecExpression::CExpression(expression) => {
            c_expression_parameter_offset(expression, parameter_name)
        }
        SpecExpression::Cast(expression, _) | SpecExpression::LoopEntrySnapshot(expression) => {
            spec_expression_parameter_offset(expression, parameter_name)
        }
        SpecExpression::PointerOffset {
            pointer,
            elements,
            byte_width,
        } => spec_expression_parameter_offset(pointer, parameter_name)?
            .checked_add(spec_expression_constant(elements)?.checked_mul(*byte_width)?),
        _ => None,
    }
}

fn statement_writes_aggregate_parameter(
    statement: &CStatement,
    parameter_name: &str,
    writes: &mut Vec<ParameterAccessRange>,
    unknown_write: &mut bool,
) {
    match statement {
        CStatement::Store { pointer, .. } => {
            if c_expression_parameter_offset(pointer, parameter_name).is_some()
                || c_expression_mentions_variable(pointer, parameter_name)
            {
                *unknown_write = true;
            }
        }
        CStatement::TypedStore {
            pointer,
            value_type,
            ..
        } => {
            if let Some(offset) = c_expression_parameter_offset(pointer, parameter_name) {
                if let Some(range) = parameter_access_range(offset, value_type.byte_width()) {
                    writes.push(range);
                }
            } else if c_expression_mentions_variable(pointer, parameter_name) {
                *unknown_write = true;
            }
        }
        CStatement::CopyAggregate { target, layout, .. } => {
            if let Some(offset) = c_expression_parameter_offset(target, parameter_name) {
                if let Some(range) = parameter_access_range(offset, layout.size_bytes()) {
                    writes.push(range);
                }
            } else if c_expression_mentions_variable(target, parameter_name) {
                *unknown_write = true;
            }
        }
        CStatement::Update { target, .. } => {
            if c_expression_mentions_variable(target, parameter_name) {
                *unknown_write = true;
            }
        }
        CStatement::Call { arguments, .. } | CStatement::CallAssign { arguments, .. } => {
            if arguments
                .iter()
                .any(|argument| c_expression_takes_address_of_variable(argument, parameter_name))
            {
                *unknown_write = true;
            }
        }
        CStatement::Seq(first, second) => {
            statement_writes_aggregate_parameter(first, parameter_name, writes, unknown_write);
            statement_writes_aggregate_parameter(second, parameter_name, writes, unknown_write);
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            statement_writes_aggregate_parameter(
                then_branch,
                parameter_name,
                writes,
                unknown_write,
            );
            statement_writes_aggregate_parameter(
                else_branch,
                parameter_name,
                writes,
                unknown_write,
            );
        }
        CStatement::TryCatchInt32 {
            try_body, handler, ..
        } => {
            statement_writes_aggregate_parameter(try_body, parameter_name, writes, unknown_write);
            statement_writes_aggregate_parameter(handler, parameter_name, writes, unknown_write);
        }
        CStatement::ContinueWithStep { step } => {
            statement_writes_aggregate_parameter(step, parameter_name, writes, unknown_write);
        }
        CStatement::While { body, .. } => {
            statement_writes_aggregate_parameter(body, parameter_name, writes, unknown_write);
        }
        CStatement::Switch { cases, .. } => {
            for case in cases {
                statement_writes_aggregate_parameter(
                    &case.body,
                    parameter_name,
                    writes,
                    unknown_write,
                );
            }
        }
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Goto { .. }
        | CStatement::Declare { .. }
        | CStatement::DeclareAggregate { .. }
        | CStatement::Assign { .. }
        | CStatement::HeapAllocate { .. }
        | CStatement::HeapFree { .. }
        | CStatement::Assert { .. }
        | CStatement::Throw(_)
        | CStatement::Return(_) => {}
    }
}

fn spec_expression_current_parameter_accesses(
    expression: &SpecExpression,
    parameter_name: &str,
    reads: &mut Vec<ParameterAccessRange>,
    unknown_read: &mut bool,
) {
    match expression {
        SpecExpression::Value(_) | SpecExpression::ResourceField { .. } => {}
        SpecExpression::IntegerToMachine { .. } => *unknown_read = true,
        SpecExpression::CExpression(expression) => {
            if c_expression_mentions_variable(expression, parameter_name) {
                *unknown_read = true;
            }
        }
        SpecExpression::AlgebraicMatch { scrutinee, arms } => {
            spec_algebraic_expression_current_parameter_accesses(
                scrutinee,
                parameter_name,
                reads,
                unknown_read,
            );
            for arm in arms {
                spec_expression_current_parameter_accesses(
                    &arm.body,
                    parameter_name,
                    reads,
                    unknown_read,
                );
            }
        }
        SpecExpression::CountedResourceCount { arguments, .. } => {
            for argument in arguments.iter().flatten() {
                spec_expression_current_parameter_accesses(
                    argument,
                    parameter_name,
                    reads,
                    unknown_read,
                );
            }
        }
        SpecExpression::Add(left, right)
        | SpecExpression::Subtract(left, right)
        | SpecExpression::Multiply(left, right)
        | SpecExpression::Divide(left, right)
        | SpecExpression::Remainder(left, right)
        | SpecExpression::ShiftLeft(left, right)
        | SpecExpression::ShiftRight(left, right)
        | SpecExpression::BitwiseAnd(left, right)
        | SpecExpression::BitwiseOr(left, right)
        | SpecExpression::BitwiseXor(left, right) => {
            spec_expression_current_parameter_accesses(left, parameter_name, reads, unknown_read);
            spec_expression_current_parameter_accesses(right, parameter_name, reads, unknown_read);
        }
        SpecExpression::BitwiseNot(body)
        | SpecExpression::Cast(body, _)
        | SpecExpression::LoopEntrySnapshot(body) => {
            spec_expression_current_parameter_accesses(body, parameter_name, reads, unknown_read);
        }
        SpecExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            spec_proposition_current_parameter_accesses(
                condition,
                parameter_name,
                reads,
                unknown_read,
            );
            spec_expression_current_parameter_accesses(
                then_branch,
                parameter_name,
                reads,
                unknown_read,
            );
            spec_expression_current_parameter_accesses(
                else_branch,
                parameter_name,
                reads,
                unknown_read,
            );
        }
        SpecExpression::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            spec_expression_current_parameter_accesses(start, parameter_name, reads, unknown_read);
            spec_expression_current_parameter_accesses(end, parameter_name, reads, unknown_read);
            spec_expression_current_parameter_accesses(
                initial,
                parameter_name,
                reads,
                unknown_read,
            );
            spec_expression_current_parameter_accesses(body, parameter_name, reads, unknown_read);
        }
        SpecExpression::Let { value, body, .. } => {
            spec_expression_current_parameter_accesses(value, parameter_name, reads, unknown_read);
            spec_expression_current_parameter_accesses(body, parameter_name, reads, unknown_read);
        }
        SpecExpression::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                spec_pure_function_argument_current_parameter_accesses(
                    argument,
                    parameter_name,
                    reads,
                    unknown_read,
                );
            }
        }
        SpecExpression::PointerOffset {
            pointer, elements, ..
        } => {
            spec_expression_current_parameter_accesses(
                pointer,
                parameter_name,
                reads,
                unknown_read,
            );
            spec_expression_current_parameter_accesses(
                elements,
                parameter_name,
                reads,
                unknown_read,
            );
        }
        SpecExpression::MemoryLoad {
            memory: SpecMemory::FunctionEntry | SpecMemory::Fixed(_),
            ..
        } => {}
        SpecExpression::MemoryLoad {
            memory: SpecMemory::Current,
            pointer,
            value_type,
        } => {
            if let Some(offset) = spec_expression_parameter_offset(pointer, parameter_name) {
                if let Some(range) = parameter_access_range(offset, value_type.byte_width()) {
                    reads.push(range);
                }
            } else if spec_expression_reads_current_parameter(pointer, parameter_name) {
                *unknown_read = true;
            }
        }
        SpecExpression::MemoryLoad {
            memory: SpecMemory::LoopEntry,
            pointer,
            ..
        } => {
            if spec_expression_reads_current_parameter(pointer, parameter_name) {
                *unknown_read = true;
            }
        }
    }
}

fn spec_proposition_current_parameter_accesses(
    proposition: &SpecProposition,
    parameter_name: &str,
    reads: &mut Vec<ParameterAccessRange>,
    unknown_read: &mut bool,
) {
    match proposition {
        SpecProposition::IntegerComparison { .. } => {}
        SpecProposition::AlgebraicComparison { left, right, .. } => {
            spec_algebraic_expression_current_parameter_accesses(
                left,
                parameter_name,
                reads,
                unknown_read,
            );
            spec_algebraic_expression_current_parameter_accesses(
                right,
                parameter_name,
                reads,
                unknown_read,
            );
        }
        SpecProposition::SequenceMembership { element, sequence } => {
            spec_expression_current_parameter_accesses(
                element,
                parameter_name,
                reads,
                unknown_read,
            );
            spec_sequence_current_parameter_accesses(sequence, parameter_name, reads, unknown_read);
        }
        SpecProposition::SequenceComparison { left, right, .. } => {
            spec_sequence_current_parameter_accesses(left, parameter_name, reads, unknown_read);
            spec_sequence_current_parameter_accesses(right, parameter_name, reads, unknown_read);
        }
        SpecProposition::Comparison { left, right, .. } => {
            spec_expression_current_parameter_accesses(left, parameter_name, reads, unknown_read);
            spec_expression_current_parameter_accesses(right, parameter_name, reads, unknown_read);
        }
        SpecProposition::FloatClassification { expression, .. }
        | SpecProposition::Defined(expression) => {
            spec_expression_current_parameter_accesses(
                expression,
                parameter_name,
                reads,
                unknown_read,
            );
        }
        SpecProposition::And(left, right)
        | SpecProposition::Or(left, right)
        | SpecProposition::Implies(left, right) => {
            spec_proposition_current_parameter_accesses(left, parameter_name, reads, unknown_read);
            spec_proposition_current_parameter_accesses(right, parameter_name, reads, unknown_read);
        }
        SpecProposition::Not(body)
        | SpecProposition::ForAllInt32 { body, .. }
        | SpecProposition::ForAllInteger { body, .. }
        | SpecProposition::ForAllPointer { body, .. }
        | SpecProposition::ExistsInt32 { body, .. }
        | SpecProposition::ExistsInteger { body, .. }
        | SpecProposition::ExistsPointer { body, .. } => {
            spec_proposition_current_parameter_accesses(body, parameter_name, reads, unknown_read);
        }
        SpecProposition::Predicate { arguments, .. } => {
            for argument in arguments {
                match argument {
                    SpecPredicateArgument::Value(expression) => {
                        spec_expression_current_parameter_accesses(
                            expression,
                            parameter_name,
                            reads,
                            unknown_read,
                        );
                    }
                    SpecPredicateArgument::ArrayRef { memory, pointer } => {
                        if !matches!(memory, SpecMemory::FunctionEntry | SpecMemory::Fixed(_))
                            && spec_expression_reads_current_parameter(pointer, parameter_name)
                        {
                            *unknown_read = true;
                        }
                    }
                }
            }
        }
        SpecProposition::ResourceSeparate { left, right }
        | SpecProposition::ResourceContains {
            parent: left,
            child: right,
        } => {
            spec_resource_current_parameter_accesses(left, parameter_name, reads, unknown_read);
            spec_resource_current_parameter_accesses(right, parameter_name, reads, unknown_read);
        }
        SpecProposition::MemoryLoadable {
            memory,
            base,
            start,
            end,
            ..
        } => {
            if !matches!(memory, SpecMemory::FunctionEntry | SpecMemory::Fixed(_))
                && (spec_expression_reads_current_parameter(base, parameter_name)
                    || spec_expression_reads_current_parameter(start, parameter_name)
                    || spec_expression_reads_current_parameter(end, parameter_name))
            {
                *unknown_read = true;
            }
        }
    }
}

fn spec_sequence_current_parameter_accesses(
    sequence: &SpecSequenceExpression,
    parameter_name: &str,
    reads: &mut Vec<ParameterAccessRange>,
    unknown_read: &mut bool,
) {
    match sequence {
        SpecSequenceExpression::Literal(elements) => {
            for element in elements {
                spec_expression_current_parameter_accesses(
                    element,
                    parameter_name,
                    reads,
                    unknown_read,
                );
            }
        }
        SpecSequenceExpression::Concat(left, right) => {
            spec_sequence_current_parameter_accesses(left, parameter_name, reads, unknown_read);
            spec_sequence_current_parameter_accesses(right, parameter_name, reads, unknown_read);
        }
    }
}

fn spec_resource_current_parameter_accesses(
    resource: &SpecResource,
    parameter_name: &str,
    reads: &mut Vec<ParameterAccessRange>,
    unknown_read: &mut bool,
) {
    match resource {
        SpecResource::Memory {
            base, start, end, ..
        } => {
            if spec_expression_reads_current_parameter(base, parameter_name)
                || spec_expression_reads_current_parameter(start, parameter_name)
                || spec_expression_reads_current_parameter(end, parameter_name)
            {
                *unknown_read = true;
            }
        }
        SpecResource::Composite { arguments, .. } | SpecResource::Token { arguments, .. } => {
            for argument in arguments {
                spec_expression_current_parameter_accesses(
                    argument,
                    parameter_name,
                    reads,
                    unknown_read,
                );
            }
        }
    }
}

fn spec_algebraic_expression_current_parameter_accesses(
    expression: &SpecAlgebraicExpression,
    parameter_name: &str,
    reads: &mut Vec<ParameterAccessRange>,
    unknown_read: &mut bool,
) {
    match &expression.node {
        SpecAlgebraicExpressionNode::Variable(_)
        | SpecAlgebraicExpressionNode::Binding(_)
        | SpecAlgebraicExpressionNode::ResourceField(_) => {}
        SpecAlgebraicExpressionNode::Constructor { fields, .. } => {
            for field in fields {
                match field {
                    SpecAlgebraicValue::C(expression) => {
                        spec_expression_current_parameter_accesses(
                            expression,
                            parameter_name,
                            reads,
                            unknown_read,
                        );
                    }
                    SpecAlgebraicValue::Integer(_) => {}
                    SpecAlgebraicValue::Algebraic(expression) => {
                        spec_algebraic_expression_current_parameter_accesses(
                            expression,
                            parameter_name,
                            reads,
                            unknown_read,
                        );
                    }
                }
            }
        }
        SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
            spec_algebraic_expression_current_parameter_accesses(
                scrutinee,
                parameter_name,
                reads,
                unknown_read,
            );
            for arm in arms {
                spec_algebraic_expression_current_parameter_accesses(
                    &arm.body,
                    parameter_name,
                    reads,
                    unknown_read,
                );
            }
        }
        SpecAlgebraicExpressionNode::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                spec_pure_function_argument_current_parameter_accesses(
                    argument,
                    parameter_name,
                    reads,
                    unknown_read,
                );
            }
        }
    }
}

fn spec_pure_function_argument_current_parameter_accesses(
    argument: &SpecPureFunctionArgument,
    parameter_name: &str,
    reads: &mut Vec<ParameterAccessRange>,
    unknown_read: &mut bool,
) {
    match argument {
        SpecPureFunctionArgument::Value(expression) => {
            spec_expression_current_parameter_accesses(
                expression,
                parameter_name,
                reads,
                unknown_read,
            );
        }
        SpecPureFunctionArgument::Integer(_) => {}
        SpecPureFunctionArgument::Algebraic(expression) => {
            spec_algebraic_expression_current_parameter_accesses(
                expression,
                parameter_name,
                reads,
                unknown_read,
            );
        }
        SpecPureFunctionArgument::ArrayRef {
            memory, pointer, ..
        } => {
            if !matches!(memory, SpecMemory::FunctionEntry | SpecMemory::Fixed(_))
                && spec_expression_reads_current_parameter(pointer, parameter_name)
            {
                *unknown_read = true;
            }
        }
    }
}

/// Rejects a postcondition that would expose a modified by-value aggregate
/// parameter through the caller-side contract view. This source-level check
/// runs while the function contract is assembled, before any proof tactic can
/// publish the private copy as a caller fact.
pub(crate) fn modified_by_value_aggregate_parameter_with_current_ensure_in_source(
    function: &CFunction,
) -> Option<String> {
    function
        .parameters()
        .iter()
        .filter(|parameter| parameter.aggregate_layout().is_some())
        .find(|parameter| {
            let mut writes = Vec::new();
            let mut unknown_write = false;
            statement_writes_aggregate_parameter(
                function.source_body(),
                parameter.name(),
                &mut writes,
                &mut unknown_write,
            );
            if writes.is_empty() && !unknown_write {
                return false;
            }
            let mut reads = Vec::new();
            let mut unknown_read = false;
            for ensure in function.contract_ensures() {
                spec_proposition_current_parameter_accesses(
                    ensure,
                    parameter.name(),
                    &mut reads,
                    &mut unknown_read,
                );
            }
            (unknown_write && (unknown_read || !reads.is_empty()))
                || (unknown_read && !writes.is_empty())
                || writes
                    .iter()
                    .any(|write| reads.iter().any(|read| write.overlaps(*read)))
        })
        .map(|parameter| parameter.name().to_string())
}

fn statement_outcome_state(outcome: &CStatementOutcome) -> Option<&CState> {
    match outcome {
        CStatementOutcome::Normal(state)
        | CStatementOutcome::Break(state)
        | CStatementOutcome::Continue(state)
        | CStatementOutcome::Jump { state, .. } => Some(state),
        CStatementOutcome::Return { state, .. } | CStatementOutcome::Throw { state, .. } => {
            Some(state)
        }
        CStatementOutcome::VerificationDiverges
        | CStatementOutcome::UndefinedBehavior(_)
        | CStatementOutcome::RuntimeError(_) => None,
    }
}

fn aggregate_parameter_copy_changed(
    entry_state: &CState,
    outcome: &CStatementOutcome,
    parameter: &CParameter,
) -> bool {
    let Some(exit_state) = statement_outcome_state(outcome) else {
        return false;
    };
    let Some(CLocalBinding::AggregateObject { slot, layout, .. }) =
        entry_state.locals.binding(parameter.name())
    else {
        return false;
    };
    let end = i64::from(layout.size_bytes());
    entry_state
        .memory
        .differing_cell_pointers(&exit_state.memory)
        .into_iter()
        .any(|pointer| {
            pointer.block == slot.block
                && pointer
                    .offset
                    .as_const()
                    .is_some_and(|offset| offset >= 0 && offset < end)
        })
}

fn modified_by_value_aggregate_parameter_with_current_ensure(
    entry_state: &CState,
    outcome: &CStatementOutcome,
    function: &CFunction,
) -> Option<String> {
    let ensures = match outcome {
        CStatementOutcome::Return { .. } => function.contract_ensures(),
        CStatementOutcome::Throw { .. } => function.exceptional_ensures(),
        _ => &[],
    };
    function
        .parameters()
        .iter()
        .filter(|parameter| parameter.aggregate_layout().is_some())
        .find(|parameter| {
            aggregate_parameter_copy_changed(entry_state, outcome, parameter)
                && ensures.iter().any(|ensure| {
                    spec_proposition_reads_current_parameter(ensure, parameter.name())
                })
        })
        .map(|parameter| parameter.name().to_string())
}

#[cfg(test)]
fn add_verified_function_ensure_facts(
    facts: &mut Vec<ExecutionPureFact>,
    obligations: &[ProofObligation],
    post_contract_state: &CState,
    entry_contract_state: &CState,
    function: &CFunction,
    effective_assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<()> {
    add_verified_function_ensure_facts_selected_with_interface(
        facts,
        obligations,
        post_contract_state,
        entry_contract_state,
        function.contract_interface(),
        function.contract_ensures().iter(),
        effective_assumptions,
        budget,
    )
}

fn add_verified_function_ensure_facts_selected_with_interface<'a>(
    facts: &mut Vec<ExecutionPureFact>,
    obligations: &[ProofObligation],
    post_contract_state: &CState,
    entry_contract_state: &CState,
    interface: &CFunctionContractInterface,
    ensures: impl Iterator<Item = &'a SpecProposition>,
    effective_assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<()> {
    for ensure in ensures {
        let ensure_assumptions =
            assumptions_with_path_context(effective_assumptions, facts, obligations);
        // A verified callee certifies that its ensures, including the memory
        // loads used to state them, are well-defined. Lower those loads into
        // explicit path obligations here instead of asking the general prover
        // to rediscover each contextual range proof while applying the call
        // rule. The obligations are retained below as certified consequences
        // of the verified contract.
        let lowering_assumptions = ensure_assumptions
            .clone()
            .allow_symbolic_contract_loads()
            .defer_non_exact_loadability_obligations();
        let ensure_paths = lower_spec_proposition_at_state_with_loop_entry(
            post_contract_state,
            ensure,
            Some(entry_contract_state),
            &lowering_assumptions,
            budget,
        )?;
        for ensure_path in ensure_paths {
            for path_obligation in &ensure_path.obligations {
                facts.push(ExecutionPureFact::certified(wrap_path_context(
                    path_obligation.proposition().clone(),
                    &ensure_path.facts,
                    &[],
                )));
            }
            facts.push(ExecutionPureFact::certified(wrap_path_context(
                ensure_path.proposition.clone(),
                &ensure_path.facts,
                &[],
            )));
            let specialized_assumptions = assumptions_with_path_context(
                &ensure_assumptions,
                &ensure_path.facts,
                &ensure_path.obligations,
            );
            // The callee's ensure holds under its own leading premises. Where
            // one of those premises is exactly available at this call, the
            // consequent is available too, and publishing it saves every
            // caller an `extract`. This is the kernel's modus ponens, so it
            // walks only the ensure's own implication chain and cites each
            // discharged premise exactly: an indexed hit in the call context,
            // or a premise already discharged above it in this chain. A
            // premise neither route settles ends the walk, and the ensure
            // stays available as the implication it was written as, for the
            // proof to discharge with `extract`.
            let mut specialized = ensure_path.proposition.clone();
            let mut discharged_premises: Vec<Proposition> = Vec::new();
            while let Proposition::Implies(premise, body) = specialized {
                let available = specialized_assumptions.proves_exact(&premise)
                    || discharged_premises
                        .iter()
                        .any(|discharged| discharged == premise.as_ref());
                if !available {
                    specialized = Proposition::Implies(premise, body);
                    break;
                }
                discharged_premises.push((*premise).clone());
                specialized = *body;
            }
            if !discharged_premises.is_empty() {
                facts.push(ExecutionPureFact::certified(wrap_path_context(
                    specialized,
                    &ensure_path.facts,
                    &[],
                )));
            }
            add_normalized_verified_ensure_facts(
                facts,
                &ensure_path.proposition,
                &ensure_assumptions,
                &ensure_path.facts,
                &ensure_path.obligations,
            );
        }
        // Preserve the source identity of a named predicate ensure. The
        // expanded `ensure` above is the operational authority; this exact
        // registered pair is its definitional surface identity.
        if let Some(unfolding) = interface
            .predicate_unfoldings()
            .iter()
            .find(|unfolding| unfolding.body() == ensure)
        {
            let predicate_paths = lower_spec_proposition_at_state_with_loop_entry(
                post_contract_state,
                unfolding.predicate(),
                Some(entry_contract_state),
                &lowering_assumptions,
                budget,
            )?;
            for predicate_path in predicate_paths {
                if predicate_path.obligations.is_empty() {
                    facts.push(ExecutionPureFact::certified(predicate_path.proposition));
                }
            }
        }
    }
    Ok(())
}

/// Publishes direct constant equalities that are consequences of a verified
/// callee ensure and the caller's already-established path facts. Modular
/// calls intentionally havoc mutable memory, so a later call may see a
/// symbolic load rather than the previous call's materialized cell. Keeping
/// the original ensure is sound but can leave the surface certificate with an
/// arithmetic chain it cannot express as an exact assumption. These derived
/// equalities preserve the callee's post-state transition without retaining a
/// pre-havoc cell.
fn add_normalized_verified_ensure_facts(
    facts: &mut Vec<ExecutionPureFact>,
    ensure: &Proposition,
    ensure_assumptions: &PureFactContext,
    ensure_facts: &[ExecutionPureFact],
    ensure_obligations: &[ProofObligation],
) {
    if !ensure_obligations.is_empty()
        || !facts
            .iter()
            .any(|fact| matches!(fact.proposition(), Proposition::CMemoryEffectSummary { .. }))
        || !crate::kernel::eval::proposition_mentions_registered_load_variable(ensure)
    {
        return;
    }
    let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) = ensure
    else {
        return;
    };
    let assumptions = assumptions_with_path_context(ensure_assumptions, ensure_facts, &[])
        .assume_proposition(ensure.clone());
    let Some(left_value) = assumptions.known_signed_constant_after_normalization(left) else {
        return;
    };
    let Some(right_value) = assumptions.known_signed_constant_after_normalization(right) else {
        return;
    };
    if left_value != right_value {
        return;
    }
    let constant = Bitvector32Term::Constant(left_value as i32 as u32);
    for term in [left.as_ref(), right.as_ref()] {
        if signed_bitvector_constant(term).is_some() {
            continue;
        }
        let normalized = wrap_path_context(
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(Box::new(term.clone()), Box::new(constant.clone())),
                true,
            ),
            ensure_facts,
            &[],
        );
        if !facts.iter().any(|fact| fact.proposition() == &normalized) {
            facts.push(ExecutionPureFact::certified(normalized));
        }
    }
}

/// No fixture in either harness reaches the refutation below; the kernel
/// test `continuity_requires_both_the_allocation_base_and_size` pins it, and
/// fails when the route is denied.
fn allocation_continuity(
    input_base: &Pointer,
    input_bytes: &Bitvector32Term,
    output_base: &Pointer,
    output_bytes: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> AllocationContinuity {
    if pointers_proven_equal_for_memory_resolution(input_base, output_base, assumptions) {
        if bitvector_terms_proven_equal_for_memory_resolution(
            input_bytes,
            output_bytes,
            assumptions,
        ) {
            return AllocationContinuity::Same;
        }
        let condition = ConditionTerm::Bitvector32Equal(
            Box::new(input_bytes.clone()),
            Box::new(output_bytes.clone()),
        );
        // Two allocation sizes at one base are the same allocation, a
        // refuted one, or an undecided pair. The refutation uses the exact
        // fact index and the frozen condition checker on the bare condition;
        // anything else stays undecided and travels on as a condition the
        // consumer must settle.
        if required_obligation_is_exactly_discharged(
            assumptions,
            &Proposition::ConditionIs(condition.clone(), false),
        ) {
            AllocationContinuity::Inconsistent
        } else {
            AllocationContinuity::Undecided(condition)
        }
    } else if pointers_proven_distinct_for_memory_resolution(input_base, output_base, assumptions) {
        AllocationContinuity::Distinct
    } else {
        AllocationContinuity::Undecided(ConditionTerm::pointer_equal(
            input_base.clone(),
            output_base.clone(),
        ))
    }
}

#[cfg(test)]
mod allocation_continuity_tests {
    use super::*;

    fn external_pointer(variable: u64) -> Pointer {
        Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(
                Bitvector32Term::Variable(Variable(variable)),
                4,
            ),
        }
    }

    #[test]
    fn continuity_requires_both_the_allocation_base_and_size() {
        let assumptions = PureFactContext::new();
        let input = external_pointer(930_000);
        assert_eq!(
            allocation_continuity(
                &input,
                &Bitvector32Term::Constant(4),
                &input,
                &Bitvector32Term::Constant(4),
                &assumptions,
            ),
            AllocationContinuity::Same,
        );
        assert_eq!(
            allocation_continuity(
                &input,
                &Bitvector32Term::Constant(4),
                &input,
                &Bitvector32Term::Constant(8),
                &assumptions,
            ),
            AllocationContinuity::Inconsistent,
        );
        assert_eq!(
            allocation_continuity(
                &Pointer {
                    block: PointerBlock::Heap(930_002),
                    offset: PointerOffsetTerm::Constant(0),
                },
                &Bitvector32Term::Constant(4),
                &Pointer {
                    block: PointerBlock::Heap(930_003),
                    offset: PointerOffsetTerm::Constant(0),
                },
                &Bitvector32Term::Constant(4),
                &assumptions,
            ),
            AllocationContinuity::Distinct,
        );

        let other = external_pointer(930_001);
        assert_eq!(
            allocation_continuity(
                &input,
                &Bitvector32Term::Constant(4),
                &other,
                &Bitvector32Term::Constant(4),
                &assumptions,
            ),
            AllocationContinuity::Undecided(ConditionTerm::pointer_equal(input, other)),
        );
    }
}

/// A callee that retires an allocation identity, by a definite free or by a
/// contract that leaves continuity undecided, gives up every byte of it; a
/// live loan over any of those bytes forbids that exactly as a direct `free`
/// would (D6, D10). Every retire path consults the ledger that carries this
/// call's own loans, because lending has already removed the owner from the
/// preserved caller residual.
fn refuse_retiring_a_lent_allocation(
    ledger: Option<&LoanLedger>,
    base: &Pointer,
    bytes: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> Result<(), VerifiedAllocationDeltaError> {
    let Some(ledger) = ledger else {
        return Ok(());
    };
    let whole_allocation = CMemoryRange::new_with_element_width(
        base.clone(),
        Bitvector32Term::Constant(0),
        bytes.clone(),
        1,
    );
    match ledger.memory_access_refusal(
        &whole_allocation,
        assumptions,
        LoanRefusalOperation::MemoryAccess,
    ) {
        Some(diagnostic) => Err(VerifiedAllocationDeltaError::Runtime(
            CRuntimeError::LoanRefusal(diagnostic),
        )),
        None => Ok(()),
    }
}

fn apply_verified_heap_allocation_delta(
    mut memory: CMemory,
    input_resources: &ResourceContext,
    preserved_caller_resources: &ResourceContext,
    output_resources: &ResourceContext,
    interface: &CFunctionContractInterface,
    assumptions: &PureFactContext,
    ledger: Option<&LoanLedger>,
) -> Result<(CMemory, Vec<ExecutionPureFact>), VerifiedAllocationDeltaError> {
    let mut effects = Vec::new();
    let input = expand_all_composite_resource_facts(
        input_resources,
        interface.composite_resource_definitions(),
        &memory,
        assumptions,
    )
    .ok_or_else(|| {
        VerifiedAllocationDeltaError::Runtime(CRuntimeError::FunctionContract(
            "could not inspect input allocation effects at call".to_string(),
        ))
    })?;
    let output = expand_all_composite_resource_facts(
        output_resources,
        interface.composite_resource_definitions(),
        &memory,
        assumptions,
    )
    .ok_or_else(|| {
        VerifiedAllocationDeltaError::Runtime(CRuntimeError::FunctionContract(
            "could not inspect output allocation effects at call".to_string(),
        ))
    })?;
    // Returned projections describe the successor allocation. They decide
    // whether an input allocation continues, but they are not resources that
    // survived from the caller and therefore cannot be stale after the old
    // allocation is freed.
    let preserved = expand_all_composite_resource_facts(
        preserved_caller_resources,
        interface.composite_resource_definitions(),
        &memory,
        assumptions,
    )
    .ok_or_else(|| {
        VerifiedAllocationDeltaError::Runtime(CRuntimeError::FunctionContract(
            "could not inspect preserved caller allocation effects at call".to_string(),
        ))
    })?;
    let allocation_assumptions = input
        .observable_facts_assuming_valid(assumptions)
        .into_iter()
        .fold(assumptions.clone(), |assumptions, fact| {
            assumptions.assume_proposition(fact)
        });
    let mut output_allocations_by_block =
        BTreeMap::<PointerBlock, Vec<(Pointer, Bitvector32Term)>>::new();
    for (base, bytes) in output.facts().iter().filter_map(CResourceFact::allocation) {
        output_allocations_by_block
            .entry(base.block.clone())
            .or_default()
            .push((base.clone(), bytes.clone()));
    }

    for allocation in input.facts().iter().filter_map(|fact| {
        fact.allocation()
            .map(|(base, bytes)| (fact, base.clone(), bytes.clone()))
    }) {
        let (fact, base, bytes) = allocation;
        if output
            .cached_support_exposing_fact(fact, &allocation_assumptions)
            .is_some()
            || expose_composite_resource_fact(
                &output,
                fact,
                interface.composite_resource_definitions(),
                &memory,
                &allocation_assumptions,
            )
            .is_some()
        {
            continue;
        }
        if let Some(output_allocations) = output_allocations_by_block.get(&base.block) {
            let mut retained = false;
            let mut continuity_is_undecided = false;
            for (output_base, output_bytes) in output_allocations {
                match allocation_continuity(
                    &base,
                    &bytes,
                    output_base,
                    output_bytes,
                    &allocation_assumptions,
                ) {
                    AllocationContinuity::Same => retained = true,
                    AllocationContinuity::Distinct => {}
                    AllocationContinuity::Undecided(_) => continuity_is_undecided = true,
                    AllocationContinuity::Inconsistent => {
                        return Err(VerifiedAllocationDeltaError::InconsistentReturnedAllocation);
                    }
                }
            }
            if retained {
                continue;
            }
            // A contract that does not decide allocation continuity admits a
            // deallocating implementation. Therefore no independent caller
            // resource may still refer to the input allocation. Retire the
            // consumed allocation occurrence without asserting a C `free`;
            // the output occurrence is installed below even when it later
            // proves to have the same pointer value.
            if continuity_is_undecided {
                for resource in preserved.facts() {
                    if !resource.may_refer_to_memory_block(&base.block)
                        || resource.is_proven_separate_from_allocation(
                            &base,
                            &bytes,
                            &allocation_assumptions,
                        )
                    {
                        continue;
                    }
                    return Err(VerifiedAllocationDeltaError::Runtime(
                        CRuntimeError::StaleResourceAfterFree {
                            resource: resource.clone(),
                        },
                    ));
                }
                // Lending removed the owner from the preserved residual, so
                // the scan above cannot see a view the caller still holds
                // over these bytes; the ledger can (docs/internals/stable-views.md).
                refuse_retiring_a_lent_allocation(ledger, &base, &bytes, &allocation_assumptions)?;
                memory = memory.retire_contract_heap_allocation_claim(&base);
                continue;
            }
        }
        // Only the untransferred caller frame survives independently across
        // the call. Any such resource that can still refer to an allocation
        // the contract definitely retires makes this transition unsafe.
        for resource in preserved.facts() {
            if !resource.may_refer_to_memory_block(&base.block)
                || resource.is_proven_separate_from_allocation(
                    &base,
                    &bytes,
                    &allocation_assumptions,
                )
            {
                continue;
            }
            return Err(VerifiedAllocationDeltaError::Runtime(
                CRuntimeError::StaleResourceAfterFree {
                    resource: resource.clone(),
                },
            ));
        }
        refuse_retiring_a_lent_allocation(ledger, &base, &bytes, &allocation_assumptions)?;
        let before_free = memory.clone();
        if memory.live_heap_block_size(&base).is_none() {
            memory = memory
                .with_heap_allocation_claim(base.clone(), bytes.clone())
                .ok_or(VerifiedAllocationDeltaError::Runtime(
                    CRuntimeError::InvalidFree(CInvalidFree::NonHeapPointer),
                ))?;
        }
        memory = memory.free_heap_block(&base).map_err(|error| {
            VerifiedAllocationDeltaError::Runtime(CRuntimeError::InvalidFree(error))
        })?;
        effects.push(ExecutionPureFact::internal(
            Proposition::CHeapAllocationFreed {
                before: before_free,
                after: memory.clone(),
                allocation_base: base,
                bytes,
            },
        ));
    }

    for fact in output.facts() {
        let Some((base, bytes)) = fact.allocation() else {
            continue;
        };
        if input.satisfies_fact(fact, &allocation_assumptions)
            || memory.live_heap_block_size(base).is_some()
        {
            continue;
        }
        memory = memory
            .with_heap_allocation_claim(base.clone(), bytes.clone())
            .ok_or_else(|| {
                VerifiedAllocationDeltaError::Runtime(CRuntimeError::FunctionContract(
                    "returned allocation conflicts with an existing or deallocated identity"
                        .to_string(),
                ))
            })?;
    }
    Ok((memory, effects))
}

fn with_contract_argument_views(state: &CState, function: &CFunction, values: &[CValue]) -> CState {
    with_contract_interface_argument_views(state, function.contract_interface(), values)
}

fn with_contract_interface_argument_views(
    state: &CState,
    interface: &CFunctionContractInterface,
    values: &[CValue],
) -> CState {
    let mut state = state.clone();
    for (parameter, value) in interface.parameters().iter().zip(values) {
        if parameter.aggregate_layout().is_some() {
            // Aggregate parameters are already represented by the copied
            // address-backed object installed by argument binding. Keeping
            // that binding lets contract field accesses inspect the copy
            // rather than accidentally replacing it with the caller's source
            // pointer.
            continue;
        }
        // Keep the contract view identical to the typed parameter binding.
        // In particular, a C null-pointer constant arrives here as the
        // caller's int32 `0`, but the callee parameter is a pointer.  Using
        // the raw caller value would overwrite the correctly coerced binding
        // and make pointer preconditions impossible to lower.
        let value = coerce_c_contract_argument_without_obligations(value, parameter)
            .expect("function arguments were type-checked before building contract views");
        let value = value
            .with_pointer_pointee_volatile(parameter.pointee_is_volatile())
            .with_pointer_pointee_constant(parameter.pointee_is_constant());
        state.locals.set_typed_with_all_qualifiers(
            parameter.name().to_string(),
            value.clone(),
            parameter.c_type(),
            parameter.is_volatile(),
            parameter.pointee_is_volatile(),
            parameter.is_constant(),
            parameter.pointee_is_constant(),
        );
        if let CValue::Pointer(pointer) = &value {
            let Some(element_width) = parameter.c_type().pointee_type().map(CType::byte_width)
            else {
                // An opaque object pointer carries identity and qualifiers,
                // but no element width. Do not manufacture a contract view
                // that would make an untyped dereference look loadable.
                continue;
            };
            state.resources = state
                .resources
                .unchecked_with_fact(CResourceFact::view_memory(
                    CMemoryRange::new_with_element_width(
                        pointer.pointer().clone(),
                        Bitvector32Term::Constant(0),
                        Bitvector32Term::Constant(i32::MAX as u32),
                        element_width,
                    ),
                ));
        }
    }
    state
}

fn set_function_result(state: &mut CState, function: &CFunction, value: CValue) {
    set_contract_result(state, function.contract_interface(), value);
}

fn set_contract_result(state: &mut CState, interface: &CFunctionContractInterface, value: CValue) {
    if let Some(layout) = interface.return_aggregate_layout()
        && let CValue::Pointer(pointer) = &value
    {
        state.set_memory(if matches!(pointer.block, PointerBlock::Symbolic(_)) {
            state
                .memory
                .clone()
                .with_block_without_derivation(pointer.block.clone(), layout.size_bytes())
        } else {
            state
                .memory
                .clone()
                .with_block(pointer.block.clone(), layout.size_bytes())
        });
        state.locals.set_aggregate_object_at(
            "result".to_string(),
            layout.clone(),
            pointer.pointer().clone(),
        );
        return;
    }
    state.locals.set_typed_with_all_qualifiers(
        "result".to_string(),
        value.with_pointer_pointee_constant(interface.return_pointee_is_constant()),
        interface.return_type(),
        false,
        false,
        false,
        interface.return_pointee_is_constant(),
    );
}

fn materialize_aggregate_return(
    state: &mut CState,
    function: &CFunction,
    value: CValue,
) -> Option<CValue> {
    let layout = function.return_aggregate_layout()?;
    let CValue::Pointer(pointer) = value else {
        return None;
    };
    if pointer.is_null() {
        return None;
    }
    let source = pointer.pointer().clone();
    let frame = state.next_local_frame;
    let destination = CMemory::frame_local_pointer(frame, "__return");
    state.set_memory(
        state
            .memory
            .clone()
            .with_block(destination.block.clone(), layout.size_bytes()),
    );
    state.set_memory(copy_aggregate_fields(
        state.memory.clone(),
        &source,
        &destination,
        layout,
    ));
    state.next_local_frame = frame.saturating_add(1);
    Some(CValue::typed_pointer(destination, function.return_type()))
}

fn coerce_function_return_value(
    value: CValue,
    function: &CFunction,
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Option<CValue> {
    // Plain struct returns use `uint8*` as their internal ABI slot, while the
    // source expression that supplies the value retains the pointee type of
    // the object it addresses (for example, `int32*` for `return *source`).
    // The aggregate return materializer copies through the pointer and is the
    // type boundary that validates the complete object. The C0 struct model
    // uses `int32*` for a struct pointer and `uint8*` for an address-backed
    // struct value, so only those two data-pointer views cross this boundary.
    if function.return_aggregate_layout().is_some()
        && let CValue::Pointer(pointer) = &value
        && matches!(pointer.c_type(), CType::Int32Pointer | CType::UInt8Pointer)
        && !pointer.pointer().block.is_function()
    {
        return Some(CValue::typed_pointer(
            pointer.pointer().clone(),
            function.return_type(),
        ));
    }
    coerce_c_value_with_pointee_constant(
        value,
        function.return_type(),
        function.return_pointee_is_constant(),
        obligations,
        assumptions,
    )
}

pub(super) fn coerce_c_value_with_pointee_constant(
    value: CValue,
    c_type: CType,
    pointee_constant: bool,
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Option<CValue> {
    // This is an implicit conversion boundary. Explicit C casts have their
    // own rules; storage read-only status is independently checked on writes.
    if matches!(&value, CValue::Pointer(pointer) if pointer.pointee_constant())
        && c_type.is_pointer()
        && !pointee_constant
    {
        return None;
    }
    Some(
        coerce_c_value_to_type(value, c_type, obligations, assumptions)?
            .with_pointer_pointee_constant(pointee_constant),
    )
}

#[cfg(test)]
fn symbolic_function_result(function: &CFunction, variable: Variable) -> CValue {
    symbolic_contract_result(function.contract_interface(), variable)
}

fn symbolic_contract_result(interface: &CFunctionContractInterface, variable: Variable) -> CValue {
    symbolic_call_result(interface.return_type(), variable)
        .with_pointer_pointee_constant(interface.return_pointee_is_constant())
}

pub(crate) fn symbolic_call_result(c_type: CType, variable: Variable) -> CValue {
    match c_type {
        CType::Void => CValue::Void,
        CType::Bool => crate::kernel::bool_value(Bitvector32Term::Variable(variable)),
        CType::VoidPointer | CType::VoidPointerPointer => {
            CValue::typed_pointer(Pointer::symbolic(variable), c_type)
        }
        CType::Int16 => CValue::Int16(Bitvector32Term::Variable(variable)),
        CType::Int32 => CValue::Int32(Bitvector32Term::Variable(variable)),
        CType::UInt8 => CValue::UInt8(Bitvector32Term::Variable(variable)),
        CType::UInt16 => CValue::UInt16(Bitvector32Term::Variable(variable)),
        CType::UInt32 => CValue::UInt32(Bitvector32Term::Variable(variable)),
        CType::Int64 => CValue::Int64(Bitvector32Term::Variable(variable)),
        CType::UInt64 => CValue::UInt64(Bitvector32Term::Variable(variable)),
        CType::Float32 => CValue::Float32(Bitvector32Term::Variable(variable)),
        CType::Float64 => CValue::Float64(Bitvector32Term::Variable(variable)),
        CType::Int16Pointer
        | CType::UInt16Pointer
        | CType::Int32Pointer
        | CType::UInt8Pointer
        | CType::UInt32Pointer
        | CType::Int64Pointer
        | CType::UInt64Pointer
        | CType::Int16PointerPointer
        | CType::UInt16PointerPointer
        | CType::Int32PointerPointer
        | CType::UInt8PointerPointer
        | CType::UInt32PointerPointer
        | CType::Int64PointerPointer
        | CType::UInt64PointerPointer
        | CType::Float32Pointer
        | CType::Float64Pointer
        | CType::Float32PointerPointer
        | CType::Float64PointerPointer => {
            CValue::typed_pointer(Pointer::symbolic(variable), c_type)
        }
        CType::FunctionPointer(_) => {
            CValue::typed_pointer(Pointer::symbolic_function(variable), c_type)
        }
        CType::Int32Array(_)
        | CType::UInt8Array(_)
        | CType::Int16Array(_)
        | CType::UInt16Array(_)
        | CType::UInt32Array(_)
        | CType::Int64Array(_)
        | CType::UInt64Array(_)
        | CType::Float32Array(_)
        | CType::Float64Array(_) => {
            unreachable!("C functions cannot return array values")
        }
    }
}

pub(super) fn add_memory_store_obligation(
    memory: &CMemory,
    pointer: &Pointer,
    value: &CValue,
    mut obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Option<Vec<ProofObligation>> {
    if memory.can_store_concretely(pointer, value) {
        return Some(obligations);
    }

    add_proof_obligation(
        &mut obligations,
        assumptions,
        Proposition::CMemoryCanStore {
            memory: memory.clone(),
            pointer: pointer.clone(),
            byte_width: value.byte_width(),
        },
    )?;
    Some(obligations)
}

pub(super) fn evaluate_c_arguments_paths(
    state: &CState,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    environment: Option<&CExecutionEnvironment>,
) -> ExecutionResult<Vec<CArgumentsPath>> {
    let mut paths = vec![CArgumentsPath {
        values: Vec::new(),
        outcome: None,
        facts: Vec::new(),
        obligations: Vec::new(),
    }];

    for argument in arguments {
        let mut next_paths = Vec::new();
        for path in paths {
            if path.outcome.is_some() {
                next_paths.push(path);
                continue;
            }

            let argument_assumptions =
                assumptions_with_path_context(assumptions, &path.facts, &path.obligations);
            for argument_path in
                evaluate_c_expression_paths(state, argument, &argument_assumptions, budget)?
            {
                let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                    &path.facts,
                    &path.obligations,
                    &argument_path.facts,
                    &argument_path.obligations,
                    assumptions,
                ) else {
                    continue;
                };

                match argument_path.outcome {
                    CExpressionOutcome::Value(value) => {
                        let value = type_function_address_value(argument, value, environment);
                        let mut values = path.values.clone();
                        values.push(value);
                        next_paths.push(CArgumentsPath {
                            values,
                            outcome: None,
                            facts,
                            obligations,
                        });
                    }
                    CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                        next_paths.push(CArgumentsPath {
                            values: path.values.clone(),
                            outcome: Some(CFunctionOutcome::UndefinedBehavior(undefined_behavior)),
                            facts,
                            obligations,
                        })
                    }
                    CExpressionOutcome::RuntimeError(error) => next_paths.push(CArgumentsPath {
                        values: path.values.clone(),
                        outcome: Some(CFunctionOutcome::RuntimeError(error)),
                        facts,
                        obligations,
                    }),
                }
            }
        }
        budget.check_path_width(next_paths.len())?;
        paths = next_paths;
    }

    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn type_function_address_value(
    expression: &CExpression,
    value: CValue,
    environment: Option<&CExecutionEnvironment>,
) -> CValue {
    let CExpression::FunctionAddress(name) = expression else {
        return value;
    };
    let Some(environment) = environment else {
        return value;
    };
    let Some(function) = environment.get_function(name) else {
        return value;
    };
    match value {
        CValue::Pointer(pointer)
            if pointer.block.is_function()
                && pointer.c_type() == CType::FunctionPointer(CallbackSignature::UNSPECIFIED) =>
        {
            // Return and parameter qualifications belong to the callback
            // signature, not to the function-pointer object's pointee view.
            CValue::typed_pointer(pointer.into_pointer(), function.function_pointer_type())
        }
        value => value,
    }
}

fn argument_binding_error(function: &CFunction, values: &[CValue]) -> String {
    contract_argument_binding_error(function.contract_interface(), function.name(), values)
}

fn contract_argument_binding_error(
    interface: &CFunctionContractInterface,
    name: &str,
    values: &[CValue],
) -> String {
    if interface
        .parameters()
        .iter()
        .zip(values)
        .any(|(parameter, value)| {
            matches!(
                (parameter.c_type(), value),
                (CType::FunctionPointer(expected), CValue::Pointer(actual))
                    if actual.block.is_function()
                        && actual.c_type() != CType::FunctionPointer(expected)
            )
        })
    {
        format!(
            "incompatible signature for function pointer argument to {}",
            name
        )
    } else {
        format!("could not bind arguments for {name}")
    }
}

/// A function-level path carries the loadability of its own string literals
/// across the call boundary. This is intentionally derived from the function
/// metadata rather than by scanning all read-only memory, so a call summary
/// cannot accidentally certify an unrelated block.
fn append_string_literal_loadable_facts(
    function: &CFunction,
    outcome: &CFunctionOutcome,
    facts: &mut Vec<ExecutionPureFact>,
) {
    let state = match outcome {
        CFunctionOutcome::Return { state, .. } | CFunctionOutcome::Throw { state, .. } => state,
        _ => return,
    };
    for literal in function.string_literals() {
        let base =
            CMemory::string_literal_pointer(function.name(), literal.name(), literal.bytes());
        let proposition = Proposition::CMemoryLoadable {
            memory: state.memory.clone(),
            base,
            bytes: Bitvector32Term::Constant(literal.bytes().len() as u32),
        };
        if !facts.iter().any(|fact| fact.proposition() == &proposition) {
            facts.push(ExecutionPureFact::certified(proposition));
        }
    }
}

/// Collect the expressions that read memory when a function body is executed.
///
/// A verified call normally applies the function's contract without executing
/// its body. That is sound for external memory, whose initialization is part
/// of the caller's loadability authority, but a caller's automatic object has
/// a separate initialization history. Keeping the read expressions lets the
/// call boundary recheck that history without rerunning the body or treating a
/// resource transfer as an initialization event.
fn collect_c_memory_read_expressions(statement: &CStatement, reads: &mut Vec<CExpression>) {
    fn values(expression: &CExpression, reads: &mut Vec<CExpression>) {
        match expression {
            CExpression::Value(_) | CExpression::Variable(_) | CExpression::FunctionAddress(_) => {}
            CExpression::Cast { expression, .. }
            | CExpression::FloatNegate(expression)
            | CExpression::FloatClassification { expression, .. }
            | CExpression::PointerOffsetBytes {
                pointer: expression,
                ..
            }
            | CExpression::Not(expression)
            | CExpression::BitwiseNot(expression) => values(expression, reads),
            CExpression::Conditional {
                condition,
                then_branch,
                else_branch,
            } => {
                values(condition, reads);
                values(then_branch, reads);
                values(else_branch, reads);
            }
            CExpression::AddressOf(target) => lvalue_address(target, reads),
            CExpression::Load(pointer) => {
                reads.push(expression.clone());
                values(pointer, reads);
            }
            CExpression::TypedLoad {
                pointer,
                value_type,
                ..
            } => {
                if !matches!(
                    value_type,
                    CType::Int32Array(_)
                        | CType::UInt8Array(_)
                        | CType::Int16Array(_)
                        | CType::UInt16Array(_)
                        | CType::UInt32Array(_)
                        | CType::Int64Array(_)
                        | CType::UInt64Array(_)
                        | CType::Float32Array(_)
                        | CType::Float64Array(_)
                ) {
                    reads.push(expression.clone());
                }
                values(pointer, reads);
            }
            CExpression::Index(base, index) => {
                reads.push(expression.clone());
                values(base, reads);
                values(index, reads);
            }
            CExpression::LessThan(left, right)
            | CExpression::LessEqual(left, right)
            | CExpression::GreaterThan(left, right)
            | CExpression::GreaterEqual(left, right)
            | CExpression::Equal(left, right)
            | CExpression::NotEqual(left, right)
            | CExpression::And(left, right)
            | CExpression::Or(left, right)
            | CExpression::Add(left, right)
            | CExpression::Subtract(left, right)
            | CExpression::Multiply(left, right)
            | CExpression::Divide(left, right)
            | CExpression::Remainder(left, right)
            | CExpression::ShiftLeft(left, right)
            | CExpression::ShiftRight(left, right)
            | CExpression::BitwiseAnd(left, right)
            | CExpression::BitwiseOr(left, right)
            | CExpression::BitwiseXor(left, right) => {
                values(left, reads);
                values(right, reads);
            }
        }
    }

    fn lvalue_address(expression: &CExpression, reads: &mut Vec<CExpression>) {
        match expression {
            CExpression::Variable(_) => {}
            CExpression::Load(pointer) | CExpression::TypedLoad { pointer, .. } => {
                values(pointer, reads)
            }
            CExpression::Index(base, index) => {
                values(base, reads);
                values(index, reads);
            }
            _ => values(expression, reads),
        }
    }

    match statement {
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Goto { .. }
        | CStatement::Declare { .. }
        | CStatement::DeclareAggregate { .. } => {}
        CStatement::ContinueWithStep { step } => collect_c_memory_read_expressions(step, reads),
        CStatement::CopyAggregate { target, source, .. } => {
            lvalue_address(target, reads);
            values(source, reads);
        }
        CStatement::Assign { expression, .. } => values(expression, reads),
        CStatement::CallAssign { arguments, .. } | CStatement::Call { arguments, .. } => {
            for argument in arguments {
                values(argument, reads);
            }
        }
        CStatement::HeapAllocate { bytes, .. } => values(bytes, reads),
        CStatement::HeapFree { pointer } => values(pointer, reads),
        CStatement::Assert { condition, .. } => values(condition, reads),
        CStatement::Seq(first, second) => {
            collect_c_memory_read_expressions(first, reads);
            collect_c_memory_read_expressions(second, reads);
        }
        CStatement::TryCatchInt32 {
            try_body, handler, ..
        } => {
            collect_c_memory_read_expressions(try_body, reads);
            collect_c_memory_read_expressions(handler, reads);
        }
        CStatement::Return(expression) | CStatement::Throw(expression) => values(expression, reads),
        CStatement::Store { pointer, value } | CStatement::TypedStore { pointer, value, .. } => {
            lvalue_address(pointer, reads);
            values(value, reads);
        }
        CStatement::Update {
            target, operand, ..
        } => {
            values(target, reads);
            values(operand, reads);
        }
        CStatement::If {
            condition,
            then_branch,
            else_branch,
        } => {
            values(condition, reads);
            collect_c_memory_read_expressions(then_branch, reads);
            collect_c_memory_read_expressions(else_branch, reads);
        }
        CStatement::While {
            condition, body, ..
        } => {
            values(condition, reads);
            collect_c_memory_read_expressions(body, reads);
        }
        CStatement::Switch { expression, cases } => {
            values(expression, reads);
            for case in cases {
                collect_c_memory_read_expressions(&case.body, reads);
            }
        }
    }
}

fn c_expression_mentions_pointer_parameter(
    expression: &CExpression,
    pointer_parameters: &BTreeSet<String>,
) -> bool {
    match expression {
        CExpression::Value(_) | CExpression::FunctionAddress(_) => false,
        CExpression::Variable(name) => pointer_parameters.contains(name),
        CExpression::Cast { expression, .. }
        | CExpression::FloatNegate(expression)
        | CExpression::FloatClassification { expression, .. }
        | CExpression::AddressOf(expression)
        | CExpression::PointerOffsetBytes {
            pointer: expression,
            ..
        }
        | CExpression::Not(expression)
        | CExpression::BitwiseNot(expression)
        | CExpression::Load(expression) => {
            c_expression_mentions_pointer_parameter(expression, pointer_parameters)
        }
        CExpression::TypedLoad { pointer, .. } => {
            c_expression_mentions_pointer_parameter(pointer, pointer_parameters)
        }
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            c_expression_mentions_pointer_parameter(condition, pointer_parameters)
                || c_expression_mentions_pointer_parameter(then_branch, pointer_parameters)
                || c_expression_mentions_pointer_parameter(else_branch, pointer_parameters)
        }
        CExpression::LessThan(left, right)
        | CExpression::LessEqual(left, right)
        | CExpression::GreaterThan(left, right)
        | CExpression::GreaterEqual(left, right)
        | CExpression::Equal(left, right)
        | CExpression::NotEqual(left, right)
        | CExpression::And(left, right)
        | CExpression::Or(left, right)
        | CExpression::Add(left, right)
        | CExpression::Subtract(left, right)
        | CExpression::Multiply(left, right)
        | CExpression::Divide(left, right)
        | CExpression::Remainder(left, right)
        | CExpression::ShiftLeft(left, right)
        | CExpression::ShiftRight(left, right)
        | CExpression::BitwiseAnd(left, right)
        | CExpression::BitwiseOr(left, right)
        | CExpression::BitwiseXor(left, right)
        | CExpression::Index(left, right) => {
            c_expression_mentions_pointer_parameter(left, pointer_parameters)
                || c_expression_mentions_pointer_parameter(right, pointer_parameters)
        }
    }
}

fn verified_call_uninitialized_read(
    entry_state: &CState,
    function: &CFunction,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<CUndefinedBehavior>> {
    // Aggregate copies have their own field-by-field initialization checks at
    // execution time. Their lowered lvalues also include typed array views
    // that are not scalar reads of a transferred pointer parameter.
    if function
        .parameters()
        .iter()
        .any(|parameter| parameter.aggregate_layout().is_some())
    {
        return Ok(None);
    }
    let mut reads = Vec::new();
    collect_c_memory_read_expressions(function.body(), &mut reads);
    let pointer_parameters = function
        .parameters()
        .iter()
        .filter(|parameter| parameter.c_type().is_pointer())
        .map(|parameter| parameter.name().to_string())
        .collect::<BTreeSet<_>>();
    for read in reads
        .into_iter()
        .filter(|read| c_expression_mentions_pointer_parameter(read, &pointer_parameters))
    {
        for path in evaluate_c_expression_paths(entry_state, &read, assumptions, budget)? {
            if let CExpressionOutcome::UndefinedBehavior(undefined_behavior) = path.outcome
                && undefined_behavior == CUndefinedBehavior::UninitializedRead
            {
                return Ok(Some(undefined_behavior));
            }
        }
    }
    Ok(None)
}

pub(super) fn bind_c_function_arguments(
    caller_state: &CState,
    function: &CFunction,
    values: &[CValue],
) -> Option<CState> {
    // Preserve the historical value-only representation for parameters whose
    // addresses never escape. Besides avoiding unnecessary memory cells, this
    // keeps ordinary call summaries unchanged. A frame is needed only when
    // the function body actually contains an address-taking expression for a
    // parameter.
    let mut address_taken = BTreeSet::new();
    crate::kernel::loops::collect_address_taken_locals(function.body(), &mut address_taken);
    let address_taken_parameters = function
        .parameters()
        .iter()
        // Taking the address of a pointer parameter's pointee (for example
        // `&p[1]`) mentions `p` while addressing the pointed-to object, not the
        // parameter object itself. A volatile pointer parameter is different:
        // its own object is the access, so it needs an address-backed slot for
        // the volatile event to name.
        .filter(|parameter| {
            (address_taken.contains(parameter.name()) || parameter.is_volatile())
                && (parameter.is_volatile() && parameter.c_type().is_pointer()
                    || matches!(
                        parameter.c_type(),
                        CType::Int16
                            | CType::Int32
                            | CType::UInt8
                            | CType::UInt16
                            | CType::UInt32
                            | CType::Float32
                            | CType::Float64
                    ))
        })
        .map(|parameter| parameter.name())
        .collect::<BTreeSet<_>>();
    let frame = caller_state.next_local_frame();
    let has_aggregate_parameters = function
        .parameters()
        .iter()
        .any(|parameter| parameter.aggregate_layout().is_some());
    let mut callee_state = CState::new()
        .with_memory(caller_state.memory.clone())
        .with_resource_context(caller_state.resources.clone())
        .with_next_local_frame(
            if address_taken_parameters.is_empty() && !has_aggregate_parameters {
                frame
            } else {
                frame.saturating_add(1)
            },
        )
        .with_next_local_lifetime(caller_state.next_local_lifetime());
    callee_state.counted_populations = caller_state.counted_populations.clone();
    // A function entry is a lexical/frame rebind, not an authority reset.
    // Preserve an already-active candidate loan through calls whose resource
    // interface is empty; the resource-transfer planner may replace these
    // fields with a checked callee participant when it lends new views.
    callee_state.loan_ledger = caller_state.loan_ledger.clone();
    callee_state.loan_participant = caller_state.loan_participant;
    callee_state.loan_view_bindings = caller_state.loan_view_bindings.clone();
    callee_state = initialize_c_function_globals(&callee_state, function);
    for (parameter, value) in function.parameters().iter().zip(values) {
        if let Some(layout) = parameter.aggregate_layout() {
            let CValue::Pointer(pointer) = value else {
                return None;
            };
            if pointer.is_null() {
                return None;
            }
            let source = pointer.pointer().clone();
            let slot = CMemory::frame_local_pointer(frame, parameter.name());
            register_block_alignment(&slot.block, layout.alignment_bytes());
            // Preserve the caller's memory snapshot for symbolic source
            // loads. Declaring the destination first would make an unknown
            // external field load depend on the callee's fresh block and
            // prevent entry facts from relating it to the caller's value.
            callee_state.set_memory(copy_aggregate_fields(
                callee_state.memory.clone(),
                &source,
                &slot,
                layout,
            ));
            callee_state.set_memory(
                callee_state
                    .memory
                    .clone()
                    .with_block(slot.block.clone(), layout.size_bytes()),
            );
            callee_state.locals.set_aggregate_object_at(
                parameter.name().to_string(),
                layout.clone(),
                slot,
            );
            continue;
        }
        let value = coerce_c_function_argument_without_obligations(value, parameter)?
            .with_pointer_pointee_volatile(parameter.pointee_is_volatile())
            .with_pointer_pointee_constant(parameter.pointee_is_constant());
        if address_taken_parameters.contains(parameter.name()) {
            let slot = CMemory::frame_local_pointer(frame, parameter.name());
            register_block_alignment(&slot.block, parameter.c_type().abi_alignment());
            callee_state.set_memory(
                callee_state
                    .memory
                    .clone()
                    .with_block(slot.block.clone(), value.byte_width())
                    .store(slot.clone(), value.clone()),
            );
            callee_state.locals.set_typed_qualified_with_all_qualifiers(
                parameter.name().to_string(),
                value,
                parameter.c_type(),
                slot,
                parameter.is_volatile(),
                parameter.pointee_is_volatile(),
                parameter.is_constant(),
                parameter.pointee_is_constant(),
            );
        } else {
            callee_state.locals.set_typed_with_all_qualifiers(
                parameter.name().to_string(),
                value,
                parameter.c_type(),
                parameter.is_volatile(),
                parameter.pointee_is_volatile(),
                parameter.is_constant(),
                parameter.pointee_is_constant(),
            );
        }
    }
    Some(callee_state)
}

/// Binds only the locals needed to instantiate a body-independent contract
/// interface. This intentionally does not inspect a statement body or collect
/// address-taken locals. A direct application can additionally supply its
/// concrete declaration identity so global and static names in the interface
/// resolve to the program's stable storage; that identity is not body-proof
/// evidence. Named callbacks supply no concrete storage.
fn bind_c_contract_arguments(
    caller_state: &CState,
    interface: &CFunctionContractInterface,
    values: &[CValue],
    storage: Option<&CFunction>,
) -> Option<CState> {
    if values.len() != interface.parameters().len() {
        return None;
    }
    let frame = caller_state.next_local_frame();
    let has_aggregate_parameters = interface
        .parameters()
        .iter()
        .any(|parameter| parameter.aggregate_layout().is_some());
    let mut callee_state = CState::new()
        .with_memory(caller_state.memory.clone())
        .with_resource_context(caller_state.resources.clone())
        .with_next_local_frame(if has_aggregate_parameters {
            frame.saturating_add(1)
        } else {
            frame
        })
        .with_next_local_lifetime(caller_state.next_local_lifetime());
    callee_state.counted_populations = caller_state.counted_populations.clone();
    callee_state.loan_ledger = caller_state.loan_ledger.clone();
    callee_state.loan_participant = caller_state.loan_participant;
    callee_state.loan_view_bindings = caller_state.loan_view_bindings.clone();
    if let Some(function) = storage {
        callee_state = initialize_c_function_globals(&callee_state, function);
    }
    for (parameter, value) in interface.parameters().iter().zip(values) {
        if let Some(layout) = parameter.aggregate_layout() {
            let CValue::Pointer(pointer) = value else {
                return None;
            };
            if pointer.is_null() {
                return None;
            }
            let source = pointer.pointer().clone();
            let slot = CMemory::frame_local_pointer(frame, parameter.name());
            register_block_alignment(&slot.block, layout.alignment_bytes());
            callee_state.set_memory(copy_aggregate_fields(
                callee_state.memory.clone(),
                &source,
                &slot,
                layout,
            ));
            callee_state.set_memory(
                callee_state
                    .memory
                    .clone()
                    .with_block(slot.block.clone(), layout.size_bytes()),
            );
            callee_state.locals.set_aggregate_object_at(
                parameter.name().to_string(),
                layout.clone(),
                slot,
            );
            continue;
        }
        let value = coerce_c_function_argument_without_obligations(value, parameter)?
            .with_pointer_pointee_volatile(parameter.pointee_is_volatile())
            .with_pointer_pointee_constant(parameter.pointee_is_constant());
        callee_state.locals.set_typed_with_all_qualifiers(
            parameter.name().to_string(),
            value,
            parameter.c_type(),
            parameter.is_volatile(),
            parameter.pointee_is_volatile(),
            parameter.is_constant(),
            parameter.pointee_is_constant(),
        );
    }
    Some(callee_state)
}

fn coerce_c_function_argument_without_obligations(
    value: &CValue,
    parameter: &CParameter,
) -> Option<CValue> {
    coerce_c_contract_argument_without_obligations(value, parameter)
}

fn coerce_c_contract_argument_without_obligations(
    value: &CValue,
    parameter: &CParameter,
) -> Option<CValue> {
    let mut obligations = Vec::new();
    let value = coerce_c_value_with_pointee_constant(
        value.clone(),
        parameter.c_type(),
        parameter.pointee_is_constant(),
        &mut obligations,
        &PureFactContext::new(),
    )?;
    obligations.is_empty().then_some(value)
}

fn coerce_c_function_arguments(
    function: &CFunction,
    values: &[CValue],
    existing_obligations: &[ProofObligation],
    assumptions: &PureFactContext,
) -> Option<(Vec<CValue>, Vec<ProofObligation>)> {
    coerce_c_contract_arguments(
        function.contract_interface(),
        values,
        existing_obligations,
        assumptions,
    )
}

fn coerce_c_contract_arguments(
    interface: &CFunctionContractInterface,
    values: &[CValue],
    existing_obligations: &[ProofObligation],
    assumptions: &PureFactContext,
) -> Option<(Vec<CValue>, Vec<ProofObligation>)> {
    if values.len() != interface.parameters().len() {
        return None;
    }
    let mut obligations = existing_obligations.to_vec();
    let mut coerced = Vec::with_capacity(values.len());
    for (parameter, value) in interface.parameters().iter().zip(values) {
        if parameter.aggregate_layout().is_some() {
            coerced.push(value.clone());
        } else {
            coerced.push(coerce_c_value_with_pointee_constant(
                value.clone(),
                parameter.c_type(),
                parameter.pointee_is_constant(),
                &mut obligations,
                assumptions,
            )?);
        }
    }
    Some((coerced, obligations))
}

/// Installs the stable global and static-local bindings needed by a function's
/// entry and contract states. Existing memory is preserved so nested calls
/// observe writes performed by their caller. Ordinary function entry declares
/// missing storage without restoring its initializer; reads then remain
/// symbolic until a caller state or a precondition constrains them. The
/// startup-only storage constructor passes `true` to materialize initializers.
/// Static locals use a function-qualified block identity and are therefore
/// initialized once for the whole symbolic execution, not once per call frame.
pub(crate) fn initialize_c_function_globals(state: &CState, function: &CFunction) -> CState {
    initialize_c_function_globals_owned(state.clone(), function, false)
}

/// Constructs a fresh startup state, never an ordinary call transition.
/// Storage identities coalesce aliases before permissions are issued. No
/// incoming state is accepted, so this cannot replenish consumed resources.
pub(crate) fn initialize_c_program_storage(
    functions: impl IntoIterator<Item = CFunction>,
) -> CState {
    let mut state = CState::new();
    for function in functions {
        state = initialize_c_function_globals_owned(state, &function, true);
        // Private source spellings are lexical bindings, not program globals.
        state.locals = CLocalEnvironment::default();
    }
    state.resources = initial_static_resources(&state.memory, || {});
    state
}

/// Partition physical storage using its initialized cell types. Adjacent
/// cells of one width form an ordinary typed array range; padding and opaque
/// union storage remain byte ranges. No cross-width ownership rule is added.
fn initial_static_resources(memory: &CMemory, mut visit: impl FnMut()) -> ResourceContext {
    let mut cells_by_block = BTreeMap::<PointerBlock, Vec<(u32, u32)>>::new();
    for (pointer, value) in memory.cells.iter() {
        visit();
        let PointerOffsetTerm::Constant(offset) = pointer.offset else {
            unreachable!("static initializers have constant cell offsets");
        };
        cells_by_block
            .entry(pointer.block.clone())
            .or_default()
            .push((
                u32::try_from(offset).expect("static cell offset"),
                value.byte_width(),
            ));
    }
    let mut resources = ResourceContext::default();
    for (identity, block) in memory.blocks.iter() {
        visit();
        let size = block.size().as_const().expect("static block size");
        let mut ranges = Vec::<(u32, u32, u32)>::new();
        let mut cursor = 0;
        for &(offset, width) in cells_by_block.get(identity).into_iter().flatten() {
            visit();
            assert!(offset >= cursor && offset.checked_add(width).is_some_and(|end| end <= size));
            if offset > cursor {
                ranges.push((cursor, offset, 1));
            }
            if let Some((_, end, previous_width)) = ranges.last_mut()
                && *end == offset
                && *previous_width == width
            {
                *end = offset + width;
            } else {
                ranges.push((offset, offset + width, width));
            }
            cursor = offset + width;
        }
        if cursor < size {
            ranges.push((cursor, size, 1));
        }
        for (start, end, width) in ranges {
            visit();
            let range = CMemoryRange::new_with_element_width(
                Pointer {
                    block: identity.clone(),
                    offset: PointerOffsetTerm::Constant(i64::from(start)),
                },
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant((end - start) / width),
                width,
            );
            resources = resources.unchecked_with_fact(if block.is_read_only() {
                CResourceFact::view_memory(range)
            } else {
                CResourceFact::own_memory(range)
            });
        }
    }
    resources
}

#[cfg(test)]
mod program_entry_tests;

fn initialize_c_function_globals_owned(
    mut state: CState,
    function: &CFunction,
    initialize_missing_storage: bool,
) -> CState {
    for literal in function.string_literals() {
        let slot =
            CMemory::string_literal_pointer(function.name(), literal.name(), literal.bytes());
        if !state.memory.has_block(&slot.block) {
            state.set_memory(
                state
                    .memory
                    .clone()
                    .with_read_only_block(slot.block.clone(), literal.bytes().len() as u32),
            );
            for (offset, byte) in literal.bytes().iter().copied().enumerate() {
                state.set_memory(state.memory.clone().store(
                    Pointer {
                        block: slot.block.clone(),
                        offset: PointerOffsetTerm::Constant(offset as i64),
                    },
                    uint8(u32::from(byte)),
                ));
            }
        }
        state.locals.set_array_object_at(
            literal.name().to_string(),
            CType::UInt8,
            literal.bytes().len() as u32,
            slot.clone(),
        );
        let literal_resource = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
            slot,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(literal.bytes().len() as u32),
            1,
        ));
        if !function.is_program_entry()
            && !state
                .resources
                .contains_exact_representation(&literal_resource)
        {
            state.resources = state
                .resources
                .clone()
                .unchecked_with_fact(literal_resource);
        }
    }
    for global in function.global_variables() {
        let slot = CMemory::global_pointer(global.kernel_name());
        register_block_alignment(&slot.block, global.c_type().abi_alignment());
        if !state.memory.has_block(&slot.block) {
            state.set_memory(state.memory.clone().with_block_or_read_only(
                slot.block.clone(),
                global.c_type().byte_width(),
                global.is_constant(),
            ));
            if initialize_missing_storage || global.is_constant() {
                state.set_memory(
                    state
                        .memory
                        .clone()
                        .store(slot.clone(), global.initial_value().clone()),
                );
            } else {
                state.set_memory(materialize_symbolic_cell(
                    state.memory.clone(),
                    &slot,
                    global.c_type(),
                ));
            }
        } else if !initialize_missing_storage
            && !global.is_constant()
            && global.c_type().is_object_pointer()
            && state
                .memory
                .known_value(&slot)
                .is_some_and(|value| symbolic_pointer_placeholder(&value, &slot))
        {
            // Resource setup may declare a pointer's storage before the
            // global binding is installed. Replace an untyped placeholder
            // with the authoritative typed symbolic pointer cell.
            state.set_memory(materialize_symbolic_cell(
                state.memory.clone(),
                &slot,
                global.c_type(),
            ));
        }
        state.locals.set_global_with_all_qualifiers(
            global.kernel_name().to_string(),
            global.c_type(),
            slot.clone(),
            global.is_volatile(),
            global.pointee_is_volatile(),
            global.is_constant(),
            global.pointee_is_constant(),
        );
        if global.kernel_name() != global.name() && !state.locals.contains_name(global.name()) {
            state.locals.set_global_with_all_qualifiers(
                global.name().to_string(),
                global.c_type(),
                slot,
                global.is_volatile(),
                global.pointee_is_volatile(),
                global.is_constant(),
                global.pointee_is_constant(),
            );
        }
    }
    for global_array in function.global_arrays() {
        let slot = CMemory::global_pointer(global_array.kernel_name());
        register_block_alignment(&slot.block, global_array.element_type().abi_alignment());
        let bytes = global_array
            .length()
            .checked_mul(global_array.element_type().byte_width())
            .expect("validated C global array size");
        if !state.memory.has_block(&slot.block) {
            state.set_memory(state.memory.clone().with_block_or_read_only(
                slot.block.clone(),
                bytes,
                global_array.is_constant(),
            ));
            if initialize_missing_storage || global_array.is_constant() {
                for (index, value) in global_array.initial_values().iter().enumerate() {
                    state.set_memory(
                        state.memory.clone().store(
                            slot.offset_by_bytes(
                                u32::try_from(index)
                                    .expect("validated C global array length")
                                    .saturating_mul(global_array.element_type().byte_width()),
                            ),
                            value.clone(),
                        ),
                    );
                }
            } else {
                state.set_memory(materialize_symbolic_array(
                    state.memory.clone(),
                    &slot,
                    global_array.element_type(),
                    global_array.length(),
                ));
            }
        }
        state.locals.set_array_object_at_with_constant(
            global_array.kernel_name().to_string(),
            global_array.element_type(),
            global_array.length(),
            slot.clone(),
            global_array.is_constant(),
        );
        if global_array.kernel_name() != global_array.name()
            && !state.locals.contains_name(global_array.name())
        {
            state.locals.set_array_object_at_with_constant(
                global_array.name().to_string(),
                global_array.element_type(),
                global_array.length(),
                slot,
                global_array.is_constant(),
            );
        }
    }
    for global_aggregate in function.global_aggregates() {
        let slot = CMemory::global_pointer(global_aggregate.kernel_name());
        register_block_alignment(&slot.block, global_aggregate.layout().alignment_bytes());
        if !state.memory.has_block(&slot.block) {
            state.set_memory(state.memory.clone().with_block_or_read_only(
                slot.block.clone(),
                global_aggregate.layout().size_bytes(),
                global_aggregate.is_constant(),
            ));
            if initialize_missing_storage || global_aggregate.is_constant() {
                state.set_memory(zero_aggregate_fields(
                    state.memory.clone(),
                    &slot,
                    global_aggregate.layout(),
                ));
                state.set_memory(initialize_aggregate_fields(
                    state.memory.clone(),
                    &slot,
                    global_aggregate.initializers(),
                ));
            } else {
                state.set_memory(materialize_symbolic_aggregate_fields(
                    state.memory.clone(),
                    &slot,
                    global_aggregate.layout(),
                ));
            }
        }
        state.locals.set_aggregate_object_at_with_constant(
            global_aggregate.kernel_name().to_string(),
            global_aggregate.layout().clone(),
            slot.clone(),
            global_aggregate.is_constant(),
        );
        if global_aggregate.kernel_name() != global_aggregate.source_name()
            && !state.locals.contains_name(global_aggregate.source_name())
        {
            state.locals.set_aggregate_object_at_with_constant(
                global_aggregate.source_name().to_string(),
                global_aggregate.layout().clone(),
                slot,
                global_aggregate.is_constant(),
            );
        }
    }
    for global_aggregate_array in function.global_aggregate_arrays() {
        let slot = CMemory::global_pointer(global_aggregate_array.kernel_name());
        register_block_alignment(
            &slot.block,
            global_aggregate_array.layout().alignment_bytes(),
        );
        let bytes = global_aggregate_array
            .length()
            .checked_mul(global_aggregate_array.layout().size_bytes())
            .expect("validated C global aggregate array size");
        if !state.memory.has_block(&slot.block) {
            state.set_memory(state.memory.clone().with_block_or_read_only(
                slot.block.clone(),
                bytes,
                global_aggregate_array.is_constant(),
            ));
            if initialize_missing_storage || global_aggregate_array.is_constant() {
                state.set_memory(zero_aggregate_array_fields(
                    state.memory.clone(),
                    &slot,
                    global_aggregate_array.layout(),
                    global_aggregate_array.length(),
                ));
                state.set_memory(initialize_aggregate_fields(
                    state.memory.clone(),
                    &slot,
                    global_aggregate_array.initializers(),
                ));
            } else {
                state.set_memory(materialize_symbolic_aggregate_array(
                    state.memory.clone(),
                    &slot,
                    global_aggregate_array.layout(),
                    global_aggregate_array.length(),
                ));
            }
        }
        state.locals.set_array_object_at_with_constant(
            global_aggregate_array.kernel_name().to_string(),
            CType::UInt8,
            bytes,
            slot.clone(),
            global_aggregate_array.is_constant(),
        );
        if global_aggregate_array.kernel_name() != global_aggregate_array.source_name()
            && !state
                .locals
                .contains_name(global_aggregate_array.source_name())
        {
            state.locals.set_array_object_at_with_constant(
                global_aggregate_array.source_name().to_string(),
                CType::UInt8,
                bytes,
                slot,
                global_aggregate_array.is_constant(),
            );
        }
    }
    for static_local in function.static_variables() {
        let slot = CMemory::static_pointer(function.name(), static_local.kernel_name());
        register_block_alignment(&slot.block, static_local.c_type().abi_alignment());
        if !state.memory.has_block(&slot.block) {
            state.set_memory(state.memory.clone().with_block_or_read_only(
                slot.block.clone(),
                static_local.c_type().byte_width(),
                static_local.is_constant(),
            ));
            // A qualified resource can materialize the cell before this
            // function's storage declaration is installed. Adding block
            // metadata must not overwrite that existing value.
            if (initialize_missing_storage || static_local.is_constant())
                && state.memory.known_value(&slot).is_none()
            {
                state.set_memory(
                    state
                        .memory
                        .clone()
                        .store(slot.clone(), static_local.initial_value().clone()),
                );
            } else if !initialize_missing_storage
                && !static_local.is_constant()
                && state.memory.known_value(&slot).is_none()
            {
                state.set_memory(materialize_symbolic_cell(
                    state.memory.clone(),
                    &slot,
                    static_local.c_type(),
                ));
            }
        } else if !initialize_missing_storage
            && !static_local.is_constant()
            && static_local.c_type().is_object_pointer()
            && state
                .memory
                .known_value(&slot)
                .is_some_and(|value| symbolic_pointer_placeholder(&value, &slot))
        {
            state.set_memory(materialize_symbolic_cell(
                state.memory.clone(),
                &slot,
                static_local.c_type(),
            ));
        }
        state.locals.set_global_with_all_qualifiers(
            static_local.kernel_name().to_string(),
            static_local.c_type(),
            slot.clone(),
            static_local.is_volatile(),
            static_local.pointee_is_volatile(),
            static_local.is_constant(),
            static_local.pointee_is_constant(),
        );
        // Contract C fragments use the source spelling. A nested static may
        // have a kernel-only name to distinguish it from another object in a
        // sibling block; expose the spelling only when the callee has not
        // already installed a parameter or another visible binding with it.
        if static_local.kernel_name() != static_local.source_name()
            && !state.locals.contains_name(static_local.source_name())
        {
            state.locals.set_global_with_all_qualifiers(
                static_local.source_name().to_string(),
                static_local.c_type(),
                slot,
                static_local.is_volatile(),
                static_local.pointee_is_volatile(),
                static_local.is_constant(),
                static_local.pointee_is_constant(),
            );
        }
    }
    for static_array in function.static_arrays() {
        let slot = CMemory::static_pointer(function.name(), static_array.kernel_name());
        register_block_alignment(&slot.block, static_array.element_type().abi_alignment());
        let bytes = static_array
            .length()
            .checked_mul(static_array.element_type().byte_width())
            .expect("validated C static local array size");
        if !state.memory.has_block(&slot.block) {
            state.set_memory(state.memory.clone().with_block_or_read_only(
                slot.block.clone(),
                bytes,
                static_array.is_constant(),
            ));
            if initialize_missing_storage || static_array.is_constant() {
                for (index, value) in static_array.initial_values().iter().enumerate() {
                    state.set_memory(
                        state.memory.clone().store(
                            slot.offset_by_bytes(
                                u32::try_from(index)
                                    .expect("validated C static local array length")
                                    .saturating_mul(static_array.element_type().byte_width()),
                            ),
                            value.clone(),
                        ),
                    );
                }
            } else {
                state.set_memory(materialize_symbolic_array(
                    state.memory.clone(),
                    &slot,
                    static_array.element_type(),
                    static_array.length(),
                ));
            }
        }
        state.locals.set_array_object_at_with_constant(
            static_array.kernel_name().to_string(),
            static_array.element_type(),
            static_array.length(),
            slot.clone(),
            static_array.is_constant(),
        );
        if static_array.kernel_name() != static_array.source_name()
            && !state.locals.contains_name(static_array.source_name())
        {
            state.locals.set_array_object_at_with_constant(
                static_array.source_name().to_string(),
                static_array.element_type(),
                static_array.length(),
                slot,
                static_array.is_constant(),
            );
        }
    }
    for static_aggregate in function.static_aggregates() {
        let slot = CMemory::static_pointer(function.name(), static_aggregate.kernel_name());
        register_block_alignment(&slot.block, static_aggregate.layout().alignment_bytes());
        if !state.memory.has_block(&slot.block) {
            state.set_memory(state.memory.clone().with_block_or_read_only(
                slot.block.clone(),
                static_aggregate.layout().size_bytes(),
                static_aggregate.is_constant(),
            ));
            if initialize_missing_storage || static_aggregate.is_constant() {
                state.set_memory(zero_aggregate_fields(
                    state.memory.clone(),
                    &slot,
                    static_aggregate.layout(),
                ));
                state.set_memory(initialize_aggregate_fields(
                    state.memory.clone(),
                    &slot,
                    static_aggregate.initializers(),
                ));
            } else {
                state.set_memory(materialize_symbolic_aggregate_fields(
                    state.memory.clone(),
                    &slot,
                    static_aggregate.layout(),
                ));
            }
        }
        state.locals.set_aggregate_object_at_with_constant(
            static_aggregate.kernel_name().to_string(),
            static_aggregate.layout().clone(),
            slot.clone(),
            static_aggregate.is_constant(),
        );
        if static_aggregate.kernel_name() != static_aggregate.source_name()
            && !state.locals.contains_name(static_aggregate.source_name())
        {
            state.locals.set_aggregate_object_at_with_constant(
                static_aggregate.source_name().to_string(),
                static_aggregate.layout().clone(),
                slot,
                static_aggregate.is_constant(),
            );
        }
    }
    for static_aggregate_array in function.static_aggregate_arrays() {
        let slot = CMemory::static_pointer(function.name(), static_aggregate_array.kernel_name());
        register_block_alignment(
            &slot.block,
            static_aggregate_array.layout().alignment_bytes(),
        );
        let bytes = static_aggregate_array
            .length()
            .checked_mul(static_aggregate_array.layout().size_bytes())
            .expect("validated C static aggregate array size");
        if !state.memory.has_block(&slot.block) {
            state.set_memory(state.memory.clone().with_block_or_read_only(
                slot.block.clone(),
                bytes,
                static_aggregate_array.is_constant(),
            ));
            if initialize_missing_storage || static_aggregate_array.is_constant() {
                state.set_memory(zero_aggregate_array_fields(
                    state.memory.clone(),
                    &slot,
                    static_aggregate_array.layout(),
                    static_aggregate_array.length(),
                ));
                state.set_memory(initialize_aggregate_fields(
                    state.memory.clone(),
                    &slot,
                    static_aggregate_array.initializers(),
                ));
            } else {
                state.set_memory(materialize_symbolic_aggregate_array(
                    state.memory.clone(),
                    &slot,
                    static_aggregate_array.layout(),
                    static_aggregate_array.length(),
                ));
            }
        }
        state.locals.set_array_object_at_with_constant(
            static_aggregate_array.kernel_name().to_string(),
            CType::UInt8,
            bytes,
            slot.clone(),
            static_aggregate_array.is_constant(),
        );
        if static_aggregate_array.kernel_name() != static_aggregate_array.source_name()
            && !state
                .locals
                .contains_name(static_aggregate_array.source_name())
        {
            state.locals.set_array_object_at_with_constant(
                static_aggregate_array.source_name().to_string(),
                CType::UInt8,
                bytes,
                slot,
                static_aggregate_array.is_constant(),
            );
        }
    }
    state
}

fn materialize_symbolic_cell(mut memory: CMemory, pointer: &Pointer, c_type: CType) -> CMemory {
    let symbolic_base = symbolic_memory_base(&memory, pointer);
    let value = if c_type.is_object_pointer() {
        Some(symbolic_pointer_cell_load(&symbolic_base, pointer, c_type))
    } else {
        symbolic_load_value(&symbolic_base, pointer, c_type)
    };
    if let Some(value) = value {
        memory = memory.store(pointer.clone(), value);
    }
    memory
}

fn symbolic_pointer_placeholder(value: &CValue, storage: &Pointer) -> bool {
    let CValue::Pointer(value) = value else {
        return false;
    };
    value.pointer().block == storage.block
        && !matches!(value.pointer().offset, PointerOffsetTerm::Constant(_))
}

fn symbolic_pointer_cell_load(memory: &CMemory, pointer: &Pointer, value_type: CType) -> CValue {
    let load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(memory.clone()),
        Box::new(pointer.clone()),
    );
    let (variable, _) = crate::kernel::eval::load_variable_for_term(&load)
        .expect("symbolic pointer cells must be backed by memory loads");
    CValue::typed_pointer(Pointer::symbolic(variable), value_type)
}

/// Returns the stable symbolic value of a pointer object whose storage is not
/// available in the current function's C state. Contract-only references to
/// an external pointer use the same canonical load identity as ordinary entry
/// initialization, so resource transfer follows the current pointer value.
pub(crate) fn stable_symbolic_pointer_cell_value(pointer: &Pointer, value_type: CType) -> CValue {
    let memory = CMemory::new()
        .with_block_without_derivation(pointer.block.clone(), value_type.byte_width());
    symbolic_pointer_cell_load(&memory, pointer, value_type)
}

/// Returns the stable symbolic value for a typed static-storage cell. The
/// backing memory contains only the storage block, so resource lowering and
/// ordinary function entry derive the same load identity even when the
/// caller has not yet materialized the surrounding object.
fn symbolic_memory_base(memory: &CMemory, pointer: &Pointer) -> CMemory {
    let size = memory
        .blocks
        .get(&pointer.block)
        .and_then(|block| block.size().as_const())
        .expect("symbolic static-storage block has a constant size");
    CMemory::new().with_block_without_derivation(pointer.block.clone(), size)
}

fn materialize_symbolic_array(
    mut memory: CMemory,
    base: &Pointer,
    element_type: CType,
    length: u32,
) -> CMemory {
    for index in 0..length {
        let pointer = base.offset_by_bytes(index.saturating_mul(element_type.byte_width()));
        memory = materialize_symbolic_cell(memory, &pointer, element_type);
    }
    memory
}

fn materialize_symbolic_aggregate_fields(
    mut memory: CMemory,
    base: &Pointer,
    layout: &CAggregateLayout,
) -> CMemory {
    for field in layout.fields() {
        let field_base = base.offset_by_bytes(field.offset_bytes());
        match field.c_type() {
            CType::Int32Array(length) => {
                memory = materialize_symbolic_array(memory, &field_base, CType::Int32, length);
            }
            CType::UInt8Array(length) => {
                memory = materialize_symbolic_array(memory, &field_base, CType::UInt8, length);
            }
            CType::Float32Array(length) => {
                memory = materialize_symbolic_array(memory, &field_base, CType::Float32, length);
            }
            CType::Float64Array(length) => {
                memory = materialize_symbolic_array(memory, &field_base, CType::Float64, length);
            }
            _ => {
                memory = materialize_symbolic_cell(memory, &field_base, field.c_type());
            }
        }
    }
    for union in layout.unions() {
        let union_base = base.offset_by_bytes(union.offset_bytes());
        for field in union.fields() {
            let pointer = union_base.offset_by_bytes(field.offset_bytes());
            let symbolic_base = symbolic_memory_base(&memory, &pointer);
            if let Some(value) = symbolic_load_value(&symbolic_base, &pointer, field.c_type()) {
                memory = memory.store_union(pointer, field.c_type(), value);
            }
        }
    }
    memory
}

fn materialize_symbolic_aggregate_array(
    mut memory: CMemory,
    base: &Pointer,
    layout: &CAggregateLayout,
    length: u32,
) -> CMemory {
    for index in 0..length {
        let element_base = base.offset_by_bytes(
            index
                .checked_mul(layout.size_bytes())
                .expect("validated aggregate symbolic offset"),
        );
        memory = materialize_symbolic_aggregate_fields(memory, &element_base, layout);
    }
    memory
}

fn zero_aggregate_fields(
    mut memory: CMemory,
    base: &Pointer,
    layout: &CAggregateLayout,
) -> CMemory {
    for field in layout.fields() {
        let (element_type, element_count) = match field.c_type() {
            CType::Int16
            | CType::Int32
            | CType::UInt8
            | CType::UInt16
            | CType::UInt32
            | CType::Int64
            | CType::UInt64
            | CType::Float32
            | CType::Float64
            | CType::VoidPointer
            | CType::Int32Pointer
            | CType::UInt8Pointer
            | CType::Float32Pointer
            | CType::Float64Pointer
            | CType::Int32PointerPointer
            | CType::UInt8PointerPointer
            | CType::Float32PointerPointer
            | CType::Float64PointerPointer
            // Static storage zero-initializes a callback field to a null
            // function pointer, just like a data-pointer field.
            | CType::FunctionPointer(_) => (field.c_type(), 1),
            CType::Int32Array(length) => (CType::Int32, length),
            CType::UInt8Array(length) => (CType::UInt8, length),
            CType::Float32Array(length) => (CType::Float32, length),
            CType::Float64Array(length) => (CType::Float64, length),
            _ => continue,
        };
        let zero = match element_type {
            CType::Bool => CValue::Bool(Bitvector32Term::Constant(0)),
            CType::Int16 => int16(0),
            CType::Int32 => int32(0),
            CType::UInt8 => uint8(0),
            CType::UInt16 => uint16(0),
            CType::UInt32 => uint32(0),
            CType::Int64 => CValue::Int64(Bitvector32Term::Constant(0)),
            CType::UInt64 => CValue::UInt64(Bitvector32Term::Constant(0)),
            CType::Float32 => CValue::Float32(Bitvector32Term::Constant(0)),
            CType::Float64 => CValue::Float64(Bitvector32Term::UInt64Constant(0)),
            CType::Int32Pointer
            | CType::UInt8Pointer
            | CType::Float32Pointer
            | CType::Float64Pointer
            | CType::Int32PointerPointer
            | CType::UInt8PointerPointer
            | CType::Float32PointerPointer
            | CType::Float64PointerPointer
            | CType::FunctionPointer(_) => CValue::typed_pointer(Pointer::null(), element_type),
            CType::Int16Array(_)
            | CType::Int32Array(_)
            | CType::UInt8Array(_)
            | CType::UInt16Array(_)
            | CType::UInt32Array(_)
            | CType::Int64Array(_)
            | CType::UInt64Array(_)
            | CType::Float32Array(_)
            | CType::Float64Array(_)
            | CType::Void
            | CType::VoidPointer
            | CType::VoidPointerPointer => {
                continue;
            }
            CType::Int16Pointer
            | CType::UInt16Pointer
            | CType::UInt32Pointer
            | CType::Int64Pointer
            | CType::UInt64Pointer
            | CType::Int16PointerPointer
            | CType::UInt16PointerPointer
            | CType::UInt32PointerPointer
            | CType::Int64PointerPointer
            | CType::UInt64PointerPointer => continue,
        };
        for index in 0..element_count {
            let offset = field
                .offset_bytes()
                .checked_add(
                    index
                        .checked_mul(element_type.byte_width())
                        .expect("validated aggregate zero field offset"),
                )
                .expect("validated aggregate zero field offset");
            memory = memory.store(base.offset_by_bytes(offset), zero.clone());
        }
    }
    for union in layout.unions() {
        let union_base = base.offset_by_bytes(union.offset_bytes());
        for field in union.fields() {
            if let Some(value) = zero_union_member_value(field.c_type()) {
                memory = memory.store_union(
                    union_base.offset_by_bytes(field.offset_bytes()),
                    field.c_type(),
                    value,
                );
            }
        }
    }
    memory
}

fn zero_union_member_value(c_type: CType) -> Option<CValue> {
    Some(match c_type {
        CType::Int32 => int32(0),
        CType::UInt8 => uint8(0),
        CType::Int32Pointer
        | CType::UInt8Pointer
        | CType::Int32PointerPointer
        | CType::UInt8PointerPointer
        | CType::FunctionPointer(_) => CValue::typed_pointer(Pointer::null(), c_type),
        _ => return None,
    })
}

fn initialize_aggregate_fields(
    mut memory: CMemory,
    base: &Pointer,
    initializers: &[CAggregateInitializer],
) -> CMemory {
    for initializer in initializers {
        memory = memory.store(
            base.offset_by_bytes(initializer.offset_bytes()),
            initializer.value().clone(),
        );
    }
    memory
}

fn zero_aggregate_array_fields(
    mut memory: CMemory,
    base: &Pointer,
    layout: &CAggregateLayout,
    length: u32,
) -> CMemory {
    for index in 0..length {
        let element_base = base.offset_by_bytes(
            index
                .checked_mul(layout.size_bytes())
                .expect("validated aggregate array zero offset"),
        );
        memory = zero_aggregate_fields(memory, &element_base, layout);
    }
    memory
}

/// Copy the modeled cells of an address-backed aggregate into a distinct
/// destination block. Fixed scalar-array fields and flattened embedded-struct
/// array leaves are copied one cell at a time. Pointer fields are
/// shallow-copied: the pointer value is duplicated,
/// but the pointed-to allocation is not. Missing cells in automatic storage
/// remain missing so an uninitialized source field stays uninitialized in the
/// copy; opaque/external source cells are represented by typed symbolic loads.
/// Whether a borrowed local view names storage its block actually has.
///
/// Only a range whose bounds are constant can be placed against the block's
/// extent. One with symbolic bounds keeps the previous treatment: it is the
/// caller's own stack object either way, and tightening that case belongs
/// with the range-arithmetic work rather than here.
fn local_view_range_within_block(range: &CMemoryRange, memory: &CMemory) -> bool {
    let (Some(start), Some(end)) = (range.start().as_const(), range.end().as_const()) else {
        return true;
    };
    if end <= start {
        return true;
    }
    let Some(bytes) = (end - start).checked_mul(range.element_width()) else {
        return false;
    };
    let base = range
        .base()
        .offset_by_elements(range.start().clone(), range.element_width());
    memory.access_in_bounds(&base, bytes)
}

/// Whole-struct assignment copies every member (C11 6.5.16.1p2), but
/// `copy_aggregate_fields` skips a carried field with no source cell. Copying
/// from never-written source storage would then leave the destination's own
/// cell in place and readable. Every aggregate-copy path (direct assignment,
/// return materialization, return assignment) reports that skipped read as an
/// uninitialized read instead, matching what member-wise assignment reports
/// through the ordinary load path.
fn aggregate_copy_reads_uninitialized(
    memory: &CMemory,
    source: &Pointer,
    layout: &CAggregateLayout,
) -> bool {
    // Mirror the carried-field classification in `copy_aggregate_fields`: a
    // field type this copy cannot carry drops the destination cells instead
    // of leaving them readable, so it cannot go stale here.
    for field in layout.fields() {
        let (element_type, element_count) = match field.c_type() {
            CType::Int16
            | CType::Int32
            | CType::UInt8
            | CType::UInt16
            | CType::UInt32
            | CType::Int64
            | CType::UInt64
            | CType::Float32
            | CType::Float64 => (field.c_type(), 1),
            CType::Int32Array(length) => (CType::Int32, length),
            CType::UInt8Array(length) => (CType::UInt8, length),
            CType::Int32Pointer
            | CType::UInt8Pointer
            | CType::Int32PointerPointer
            | CType::UInt8PointerPointer
            | CType::FunctionPointer(_) => (field.c_type(), 1),
            _ => continue,
        };
        for index in 0..element_count {
            let element_offset = field
                .offset_bytes()
                .checked_add(
                    index
                        .checked_mul(element_type.byte_width())
                        .expect("validated aggregate field offset"),
                )
                .expect("validated aggregate field offset");
            if uninitialized_aggregate_copy_source_cell(
                memory,
                &source.offset_by_bytes(element_offset),
                element_type,
            ) {
                return true;
            }
        }
    }
    for union in layout.unions() {
        let union_source = source.offset_by_bytes(union.offset_bytes());
        // A union with any readable member is initialized storage: the copy
        // carries the active member view and skips the rest, so no member
        // read is uninitialized. Only a wholly unread union can leave the
        // destination holding a stale cell.
        let union_initialized = union.fields().iter().any(|field| {
            let source_field = union_source.offset_by_bytes(field.offset_bytes());
            // Mirror `copy_aggregate_union_member`: a value stored through
            // any member is carried.
            memory
                .known_union_value(&source_field, field.c_type())
                .is_some()
                || memory
                    .known_value(&source_field)
                    .is_some_and(|value| field.c_type().accepts(&value))
        });
        if union_initialized {
            continue;
        }
        for field in union.fields() {
            let source_field = union_source.offset_by_bytes(field.offset_bytes());
            if uninitialized_aggregate_copy_source_cell(memory, &source_field, field.c_type()) {
                return true;
            }
        }
    }
    false
}

/// Mirrors the silent skip in `copy_aggregate_fields`: no source cell and not
/// a zeroed heap address. Reading such a cell is a read of uninitialized
/// storage when the address is a live local or an uninitialized heap cell;
/// anything else (external or symbolic memory) reads back as an unconstrained
/// symbolic load rather than stale storage.
fn uninitialized_aggregate_copy_source_cell(
    memory: &CMemory,
    source_field: &Pointer,
    element_type: CType,
) -> bool {
    if memory.known_value(source_field).is_some() {
        return false;
    }
    if memory.is_zeroed_heap_address(source_field, element_type.byte_width()) {
        return false;
    }
    memory.is_uninitialized_heap_address(source_field, element_type.byte_width())
        || (source_field.block.starts_with("local:")
            && memory.access_in_bounds(source_field, element_type.byte_width()))
}

/// Every aggregate-copy path goes through this wrapper so a copy from
/// uninitialized source storage is reported as an uninitialized read instead
/// of silently keeping the destination's old value. The raw
/// `copy_aggregate_fields` is deliberately module-private; new call sites in
/// other modules must use this checked form.
pub(super) fn copy_aggregate_fields_checked(
    memory: CMemory,
    source: &Pointer,
    destination: &Pointer,
    layout: &CAggregateLayout,
) -> Result<CMemory, CUndefinedBehavior> {
    if aggregate_copy_reads_uninitialized(&memory, source, layout) {
        return Err(CUndefinedBehavior::UninitializedRead);
    }
    Ok(copy_aggregate_fields(memory, source, destination, layout))
}

// Module-private on purpose: cross-module aggregate copies must go through
// `copy_aggregate_fields_checked` so the uninitialized-source read is always
// reported. (Aggregate argument binding below keeps the raw form for now;
// diagnosing uninitialized reads of call arguments is a separate follow-up.)
fn copy_aggregate_fields(
    mut memory: CMemory,
    source: &Pointer,
    destination: &Pointer,
    layout: &CAggregateLayout,
) -> CMemory {
    for field in layout.fields() {
        let (element_type, element_count) = match field.c_type() {
            CType::Int16
            | CType::Int32
            | CType::UInt8
            | CType::UInt16
            | CType::UInt32
            | CType::Int64
            | CType::UInt64
            | CType::Float32
            | CType::Float64 => (field.c_type(), 1),
            CType::Int32Array(length) => (CType::Int32, length),
            CType::UInt8Array(length) => (CType::UInt8, length),
            CType::Int32Pointer
            | CType::UInt8Pointer
            | CType::Int32PointerPointer
            | CType::UInt8PointerPointer
            // A callback field is an eight-byte pointer value; carry it so a
            // copied table still dispatches to the same concrete target.
            | CType::FunctionPointer(_) => (field.c_type(), 1),
            // A field this copy cannot carry must not leave the destination's
            // previous value in place: C copies every member, so a stale cell
            // would be readable as the destination's old contents. Drop those
            // cells instead, which reads back as unknown rather than wrong.
            unsupported => {
                memory = memory.without_field_cells(destination, field.offset_bytes(), unsupported);
                continue;
            }
        };
        for index in 0..element_count {
            let element_offset = field
                .offset_bytes()
                .checked_add(
                    index
                        .checked_mul(element_type.byte_width())
                        .expect("validated aggregate field offset"),
                )
                .expect("validated aggregate field offset");
            let source_field = source.offset_by_bytes(element_offset);
            let destination_field = destination.offset_by_bytes(element_offset);
            let value = memory.known_value(&source_field).or_else(|| {
                if memory.is_zeroed_heap_address(&source_field, element_type.byte_width()) {
                    return match element_type {
                        CType::Int16 => Some(int16(0)),
                        CType::Int32 => Some(int32(0)),
                        CType::UInt8 => Some(uint8(0)),
                        CType::Int32Pointer
                        | CType::UInt8Pointer
                        | CType::Int32PointerPointer
                        | CType::UInt8PointerPointer => {
                            Some(CValue::typed_pointer(Pointer::null(), element_type))
                        }
                        CType::UInt16 => Some(uint16(0)),
                        CType::UInt32 => Some(uint32(0)),
                        CType::Int64 => Some(CValue::Int64(Bitvector32Term::Constant(0))),
                        CType::UInt64 => Some(CValue::UInt64(Bitvector32Term::Constant(0))),
                        CType::Float32 => Some(CValue::Float32(Bitvector32Term::Constant(0))),
                        CType::Float64 => Some(CValue::Float64(Bitvector32Term::UInt64Constant(0))),
                        _ => None,
                    };
                }
                if memory.has_block(&source_field.block)
                    && !matches!(source_field.block, PointerBlock::Symbolic(_))
                    && memory.access_in_bounds(&source_field, element_type.byte_width())
                {
                    return None;
                }
                match element_type {
                    CType::Int16 => Some(CValue::Int16(crate::kernel::canonical_form_of_load(
                        crate::kernel::intern_c_memory(memory.clone()),
                        source_field,
                    ))),
                    CType::Int32 => Some(CValue::Int32(crate::kernel::canonical_form_of_load(
                        crate::kernel::intern_c_memory(memory.clone()),
                        source_field,
                    ))),
                    CType::UInt8 => Some(CValue::UInt8(crate::kernel::canonical_form_of_load(
                        crate::kernel::intern_c_memory(memory.clone()),
                        source_field,
                    ))),
                    CType::Int32Pointer
                    | CType::UInt8Pointer
                    | CType::Int32PointerPointer
                    | CType::UInt8PointerPointer => {
                        let pointee_type = element_type.pointee_type()?;
                        let load = crate::kernel::canonical_form_of_load(
                            crate::kernel::intern_c_memory(memory.clone()),
                            source_field.clone(),
                        );
                        Some(CValue::typed_pointer(
                            Pointer {
                                block: source_field.block.clone(),
                                offset: PointerOffsetTerm::scale_int32(
                                    load,
                                    i64::from(pointee_type.byte_width()),
                                ),
                            },
                            element_type,
                        ))
                    }
                    CType::UInt16 => Some(CValue::UInt16(crate::kernel::canonical_form_of_load(
                        crate::kernel::intern_c_memory(memory.clone()),
                        source_field,
                    ))),
                    CType::UInt32 => Some(CValue::UInt32(crate::kernel::canonical_form_of_load(
                        crate::kernel::intern_c_memory(memory.clone()),
                        source_field,
                    ))),
                    CType::Int64 => Some(CValue::Int64(crate::kernel::canonical_form_of_load(
                        crate::kernel::intern_c_memory(memory.clone()),
                        source_field,
                    ))),
                    CType::UInt64 => Some(CValue::UInt64(crate::kernel::canonical_form_of_load(
                        crate::kernel::intern_c_memory(memory.clone()),
                        source_field,
                    ))),
                    CType::Float32 => Some(CValue::Float32(crate::kernel::canonical_form_of_load(
                        crate::kernel::intern_c_memory(memory.clone()),
                        source_field,
                    ))),
                    CType::Float64 => Some(CValue::Float64(crate::kernel::canonical_form_of_load(
                        crate::kernel::intern_c_memory(memory.clone()),
                        source_field,
                    ))),
                    _ => None,
                }
            });
            if let Some(value) = value {
                memory = memory.store(destination_field, value);
            }
        }
    }
    for union in layout.unions() {
        let source_union = source.offset_by_bytes(union.offset_bytes());
        let destination_union = destination.offset_by_bytes(union.offset_bytes());
        for field in union.fields() {
            let source_field = source_union.offset_by_bytes(field.offset_bytes());
            let Some(value) = copy_aggregate_union_member(&memory, &source_field, field.c_type())
            else {
                continue;
            };
            memory = memory.store_union(
                destination_union.offset_by_bytes(field.offset_bytes()),
                field.c_type(),
                value,
            );
        }
    }
    memory
}

fn copy_aggregate_union_member(
    memory: &CMemory,
    source_field: &Pointer,
    element_type: CType,
) -> Option<CValue> {
    if let Some(value) = memory.known_union_value(source_field, element_type) {
        return Some(value);
    }
    if let Some(value) = memory.known_value(source_field)
        && element_type.accepts(&value)
    {
        return Some(value);
    }
    if memory.is_zeroed_heap_address(source_field, element_type.byte_width()) {
        return zero_union_member_value(element_type);
    }
    if memory.has_block(&source_field.block)
        && !matches!(source_field.block, PointerBlock::Symbolic(_))
        && memory.access_in_bounds(source_field, element_type.byte_width())
    {
        return None;
    }
    let load = crate::kernel::canonical_form_of_load(
        crate::kernel::intern_c_memory(memory.clone()),
        source_field.clone(),
    );
    Some(match element_type {
        CType::Int32 => CValue::Int32(load),
        CType::UInt8 => CValue::UInt8(load),
        CType::Int32Pointer
        | CType::UInt8Pointer
        | CType::Int32PointerPointer
        | CType::UInt8PointerPointer
        | CType::FunctionPointer(_) => {
            let pointer = if matches!(element_type, CType::FunctionPointer(_)) {
                match load {
                    Bitvector32Term::Variable(variable) => Pointer::symbolic_function(variable),
                    load => Pointer {
                        block: source_field.block.clone(),
                        offset: PointerOffsetTerm::scale_int32(load, 1),
                    },
                }
            } else {
                let pointee_type = element_type.pointee_type()?;
                Pointer {
                    block: source_field.block.clone(),
                    offset: PointerOffsetTerm::scale_int32(
                        load,
                        i64::from(pointee_type.byte_width()),
                    ),
                }
            };
            CValue::typed_pointer(pointer, element_type)
        }
        _ => return None,
    })
}

fn evaluate_resource_population_body_resources(
    required_resources: &ResourceContext,
    callee_state: &CState,
    definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    include_ordinary: bool,
) -> ExecutionResult<Result<ResourceContext, CRuntimeError>> {
    let mut body_resources = ResourceContext::new();
    let evaluation_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads();
    for required in required_resources.facts() {
        let (name, arguments) = match required.resource() {
            CResource::Composite { name, arguments } | CResource::Token { name, arguments } => {
                (name, arguments)
            }
            CResource::Memory(_) | CResource::Instance(_) => continue,
        };
        let Some(definition) = definitions
            .iter()
            .find(|definition| definition.name() == name)
        else {
            continue;
        };
        if !include_ordinary && !definition.is_counted_population() {
            continue;
        }
        if definition.parameters().len() != arguments.len() {
            return Ok(Err(CRuntimeError::FunctionContract(format!(
                "counted population `{name}` received the wrong number of arguments"
            ))));
        }
        let mut population_state = callee_state.clone();
        for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
            let Some(argument) = argument.as_c_value() else {
                return Ok(Err(CRuntimeError::TypeMismatch));
            };
            if parameter.c_type() != argument.c_type() {
                return Ok(Err(CRuntimeError::TypeMismatch));
            }
            population_state.locals.set_typed(
                parameter.name().to_string(),
                argument.clone(),
                parameter.c_type(),
            );
        }
        let Some(body_active) = evaluate_composite_resource_body_condition(
            definition,
            &population_state,
            &evaluation_assumptions,
            budget,
        ) else {
            return Ok(Err(CRuntimeError::FunctionContract(format!(
                "counted population `{name}` body condition is not decidable"
            ))));
        };
        if !body_active {
            continue;
        }
        for contained in definition.contains() {
            let fact = match evaluate_function_resource_spec(
                &population_state,
                contained,
                &evaluation_assumptions,
                budget,
            )? {
                Ok(fact) => fact,
                Err(error) => return Ok(Err(error)),
            };
            if !body_resources.satisfies_fact(&fact, assumptions) {
                body_resources = match body_resources
                    .try_compose_with_facts_delaying_normalization([fact], assumptions)
                {
                    Ok(resources) => resources,
                    Err(error) => return Ok(Err(resource_context_runtime_error(error))),
                };
            }
        }
    }
    Ok(Ok(body_resources))
}

fn prepare_function_resource_transfer(
    caller_state: &CState,
    callee_state: &CState,
    function: &CFunction,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    preserve_explicit_representation: bool,
    purpose: ResourceTransitionPurpose,
) -> ExecutionResult<Result<CFunctionResourceTransfer, CRuntimeError>> {
    prepare_contract_resource_transfer(
        caller_state,
        callee_state,
        function.name(),
        function.contract_interface(),
        assumptions,
        budget,
        preserve_explicit_representation,
        purpose,
    )
}

/// Unfolds exactly the folded composite owners a call's own requirements
/// need, and nothing else.
///
/// The definitional transfer consumes each requirement with
/// [`consume_resource_fact_definitionally`], which unfolds a caller composite
/// on demand. The stable-view planner instead selects concrete backing before
/// it lends anything, so it needs the same frontier present as facts. Only a
/// composite whose expansion actually supplies an unsupported requirement is
/// opened, so an unrelated folded resource keeps its packaging and stays
/// re-foldable in the residual, and only non-recursive definitions are
/// opened, which keeps a recursive frontier an explicit refusal.
fn candidate_planning_resources(
    caller_resources: &ResourceContext,
    requirements: &[CCheckedResourceFact],
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &PureFactContext,
) -> ResourceContext {
    let supported = |resources: &ResourceContext, requirement: &CCheckedResourceFact| {
        resources
            .directly_supporting_owned_entry(&requirement.fact, assumptions)
            .is_some()
            || (requirement.fact.is_view()
                && !resources
                    .view_occurrences_for_fact(&requirement.fact, assumptions)
                    .is_empty())
    };
    let mut resources = caller_resources.clone();
    for requirement in requirements {
        // A viewed composite requirement is lent folded, through the checked
        // composite backing, so opening it here would destroy the head that
        // is the restoration recipe. An owned composite requirement is
        // transferred, not lent: a held composite that contains it one level
        // down is opened to supply it, exactly as the definitional route
        // consumes it (the caller keeps the other pieces and refolds).
        if (requirement.fact.is_view()
            && matches!(requirement.fact.resource(), CResource::Composite { .. }))
            || supported(&resources, requirement)
        {
            continue;
        }
        // Exactly one level, and only the composite that actually answers
        // this requirement: an expansion that does not supply it is not a
        // reason to destroy its packaging.
        let opened = resources
            .facts()
            .iter()
            .filter(|fact| {
                fact.is_own()
                    && matches!(fact.resource(), CResource::Composite { name, .. }
                    if definitions.iter().any(|definition| {
                        definition.name() == name && !definition.is_recursive()
                    }))
            })
            .cloned()
            .collect::<Vec<_>>()
            .into_iter()
            .find_map(|composite| {
                crate::instrumentation::record_deterministic_work(1);
                expand_composite_resource_fact(
                    &resources,
                    &composite,
                    definitions,
                    memory,
                    assumptions,
                )
                .filter(|expanded| supported(expanded, requirement))
            });
        if let Some(opened) = opened {
            resources = opened;
        }
    }
    resources
}

/// One checked owned-interface-to-viewed-implementation adapter for a
/// composite view (docs/internals/stable-views.md).
struct CompositeViewAdapter {
    /// The planning resources this adapter works from. Unchanged in the
    /// owned-composite form; in the materialized form the caller's covering
    /// owners have been replaced by the head below.
    resources: ResourceContext,
    /// The owned composite the lend escrows.
    head: CResourceFact,
    /// The viewed descriptions the loan permits beside its own head.
    adapted: Vec<CResourceFact>,
    /// What recovery hands back instead of the head, when the head was
    /// materialized for this call.
    restored: Vec<CResourceFact>,
}

/// Back a viewed composite `C(args)` the caller does not own by an owned
/// description of the same authority.
///
/// The rule: `C`'s kernel-checked one-level frontier, evaluated in the
/// caller's memory, must be covered piecewise by owned authority the caller
/// holds, and `C`'s definition facts must already hold at the call. They are
/// what `observe(C)` publishes inside the callee, so they are established
/// here rather than assumed. Two covering forms are admitted:
///
/// * an owned composite `D` in the caller whose own checked frontier covers
///   `C`'s: `D`'s head is escrowed and `views C(args)` becomes an additional
///   permitted description of that loan, exactly like a projection. Recovery
///   restores `D`;
/// * the caller's owned frontier itself: `owns C(args)` is materialized out
///   of exactly those facts for the call, and recovery restores them, so a
///   `views` requirement leaves the caller's packaging as it found it.
///
/// Anything else is refused by returning `None`, which leaves the ordinary
/// missing-backing diagnostic naming the viewed clause. A counted population
/// is refused: its body is population-wide, not one unit's frontier. So is a
/// borrowing composite, whose fold needs step 7's hold.
///
/// The materialized head carries no sidecar binding, so a hold a consumed
/// owned occurrence carried does not travel with it. That direction only
/// costs a later refusal -- the hold stays in the ledger and the loan behind
/// it cannot be ended -- and no owned frontier piece carries one today,
/// since a hold lives on the viewed piece an unfold hands it to.
fn candidate_composite_view_adapter(
    resources: &ResourceContext,
    required: &CResourceFact,
    definitions: &[CCompositeResourceDefinition],
    caller_state: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<CompositeViewAdapter>> {
    let CResource::Composite { name, arguments } = required.resource() else {
        return Ok(None);
    };
    let Some(definition) = definitions
        .iter()
        .find(|definition| definition.name() == name)
    else {
        return Ok(None);
    };
    if definition.is_counted_population()
        || definition.is_recursive()
        || !definition.facts_are_loan_stable()
    {
        return Ok(None);
    }
    let head = CResourceFact::own(required.resource().clone());
    let Some(frontier) = checked_one_level_frontier(&head, definitions, caller_state, assumptions)
    else {
        return Ok(None);
    };
    // An empty frontier protects nothing and is handled before planning; an
    // exclusive instance cannot be viewed at all (D12). A borrowing
    // composite -- one whose body views storage it does not own -- is step
    // 7's mechanism: folding one places a hold on the loan behind the viewed
    // piece, which this rule does not do, so it stays out of the adapter.
    if frontier.is_empty()
        || frontier
            .iter()
            .any(|child| !child.is_own() || matches!(child.resource(), CResource::Instance(_)))
    {
        return Ok(None);
    }
    if !composite_definition_facts_hold(definition, arguments, caller_state, assumptions, budget)? {
        return Ok(None);
    }
    // The materialized form: the caller's own owners already cover the
    // frontier piecewise, so the head is exactly those facts under another
    // name and recovery gives them back unchanged.
    if let Some(remaining) = remove_frontier(resources.clone(), &frontier, assumptions)
        && let Ok(materialized) = remaining.try_compose_with_fact(head.clone(), assumptions)
    {
        return Ok(Some(CompositeViewAdapter {
            resources: materialized,
            head,
            adapted: Vec::new(),
            restored: frontier,
        }));
    }
    // The owned-composite form: one folded owner in the caller whose checked
    // frontier covers this one. Only the caller's own composite facts are
    // examined, and each is expanded at most once.
    let owners = resources
        .facts()
        .iter()
        .filter(|fact| fact.is_own() && matches!(fact.resource(), CResource::Composite { .. }))
        .cloned()
        .collect::<Vec<_>>();
    for owner in owners {
        crate::instrumentation::record_deterministic_work(1);
        let CResource::Composite {
            name: owner_name, ..
        } = owner.resource()
        else {
            continue;
        };
        let Some(owner_definition) = definitions
            .iter()
            .find(|definition| definition.name() == owner_name)
        else {
            continue;
        };
        // A counted population's body is population-wide, so one unit's head
        // is not the restoration recipe a lend needs (step 5).
        if owner_definition.is_counted_population()
            || owner_definition.is_recursive()
            || !owner_definition.facts_are_loan_stable()
        {
            continue;
        }
        // The escrow has to name one occurrence, as a same-composite lend
        // does: two equal-looking owners are not the same authority (law 5).
        if resources.owned_occurrences_for_fact(&owner).len() != 1 {
            continue;
        }
        let Some(owner_frontier) =
            checked_one_level_frontier(&owner, definitions, caller_state, assumptions)
        else {
            continue;
        };
        let covering = ResourceContext::new().unchecked_with_facts(owner_frontier);
        if remove_frontier(covering, &frontier, assumptions).is_none() {
            continue;
        }
        return Ok(Some(CompositeViewAdapter {
            resources: resources.clone(),
            head: owner,
            adapted: vec![required.clone()],
            restored: Vec::new(),
        }));
    }
    Ok(None)
}

/// The kernel's own one-level expansion of one owned composite head, read in
/// the caller's memory. This is the same boundary the composite lend and
/// `project` use, so nothing enters a loan that the definition does not
/// contain.
fn checked_one_level_frontier(
    head: &CResourceFact,
    definitions: &[CCompositeResourceDefinition],
    caller_state: &CState,
    assumptions: &PureFactContext,
) -> Option<Vec<CResourceFact>> {
    let singleton = ResourceContext::new().unchecked_with_fact(head.clone());
    let (_, children, _) = expand_composite_resource_fact_with_children(
        &singleton,
        head,
        definitions,
        caller_state.memory(),
        assumptions,
    )?;
    Some(children)
}

/// Removes a checked frontier from a context piecewise, or reports that the
/// context does not cover it. Each piece is consumed incrementally, so a
/// wider owned range is split rather than swallowed whole.
fn remove_frontier(
    mut resources: ResourceContext,
    frontier: &[CResourceFact],
    assumptions: &PureFactContext,
) -> Option<ResourceContext> {
    for piece in frontier {
        crate::instrumentation::record_deterministic_work(1);
        resources = resources.without_fact_incrementally(piece, assumptions)?;
    }
    Some(resources)
}

/// Whether a composite definition's body facts already hold at the call.
///
/// This mirrors what the surface `fold` requires of the facts it re-asserts:
/// each fact is lowered at the state the definition's parameters are bound
/// in and must be available by the kernel's exact routes. There is no search
/// here; a fact the caller has not established is a prompt refusal the proof
/// can answer with an explicit step.
fn composite_definition_facts_hold(
    definition: &CCompositeResourceDefinition,
    arguments: &[AlgebraicValue],
    caller_state: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    if definition.facts().is_empty() {
        return Ok(true);
    }
    if definition.parameters().len() != arguments.len() {
        return Ok(false);
    }
    let mut state = CState::new()
        .with_memory(caller_state.memory().clone())
        .with_resource_context(caller_state.resources().clone());
    for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
        let Some(argument) = argument.as_c_value() else {
            return Ok(false);
        };
        if parameter.c_type() != argument.c_type() {
            return Ok(false);
        }
        state.locals.set_typed(
            parameter.name().to_string(),
            argument.clone(),
            parameter.c_type(),
        );
    }
    if bind_composite_witnesses(definition, arguments, &mut state, assumptions).is_none() {
        return Ok(false);
    }
    if evaluate_composite_resource_body_condition(definition, &state, assumptions, budget)
        != Some(true)
    {
        return Ok(false);
    }
    for fact in definition.facts() {
        let paths = lower_spec_proposition_at_state_with_loop_entry(
            &state,
            fact,
            Some(&state),
            assumptions,
            budget,
        )?;
        let [path] = paths.as_slice() else {
            return Ok(false);
        };
        let mut established = assumptions.clone();
        for load in &path.facts {
            established = established.assume_proposition(load.proposition().clone());
        }
        if !contract_refinement_proves(&established, &path.proposition) {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Why a contract's resource transition is being prepared. The two purposes
/// consume the same declared requirements from the same caller context and
/// hand the callee the same authority; they differ only in whether the
/// caller lends. `call_site_and_function_boundary_transitions_agree_on_the_callee_entry`
/// pins that agreement.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ResourceTransitionPurpose {
    /// A call site: the caller lends its authority, so the views the callee
    /// declares become loans of this application and recovery returns them.
    CallSite,
    /// A function's own boundary: a whole-function judgment executes,
    /// certifies, or reads the body's outcome from the resources the contract
    /// declares, consumed definitionally. The loan roots of its input views
    /// come from the proof's entry construction
    /// (`c_state_with_borrowed_contract_inputs`), never from this transition,
    /// so nothing is lent twice; no call-site transfer record exists for
    /// such a judgment to rebuild from.
    FunctionBoundary,
}

impl ResourceTransitionPurpose {
    fn lends(self) -> bool {
        self == Self::CallSite
    }
}

/// Prepares the resource transition of one contract application; see
/// [`ResourceTransitionPurpose`] for the two routes.
fn prepare_contract_resource_transfer(
    caller_state: &CState,
    callee_state: &CState,
    _interface_name: &str,
    interface: &CFunctionContractInterface,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    preserve_explicit_representation: bool,
    purpose: ResourceTransitionPurpose,
) -> ExecutionResult<Result<CFunctionResourceTransfer, CRuntimeError>> {
    if purpose.lends()
        && caller_state.loan_ledger().is_some() != caller_state.loan_participant().is_some()
    {
        return Ok(Err(CRuntimeError::LoanRefusal(
            LoanRefusal::MissingBacking.diagnostic(LoanRefusalOperation::Plan),
        )));
    }
    // In particular, preparing several pure callback interfaces must not
    // repeatedly enumerate the caller's unrelated resource frame.
    if interface.resource_requires().is_empty() && !preserve_explicit_representation {
        return Ok(Ok(CFunctionResourceTransfer {
            borrowed_inputs: Vec::new(),
            consumed_inputs: Vec::new(),
            canonical_borrowed_owners: Vec::new(),
            callee_resources: ResourceContext::new(),
            caller_resources_after_requirements: caller_state.resources().clone(),
            memory_effects: Vec::new(),
            post_outputs: None,
            candidate_output_views: Vec::new(),
            produced_borrowing_pieces: Vec::new(),
            stable_view_plan: None,
            checked_view_frontier: Vec::new(),
        }));
    }
    let preserve_explicit_representation = preserve_explicit_representation
        && interface
            .composite_resource_definitions()
            .iter()
            .any(CCompositeResourceDefinition::is_recursive);
    let (required_resources, checked_required_resources) =
        match super::assumptions::capture_implicit_reasoning_provenance(|| {
            evaluate_function_resource_context_with_metadata(
                callee_state,
                interface.resource_requires(),
                interface.composite_resource_definitions(),
                assumptions,
                budget,
            )
        })? {
            Ok(resources) => resources,
            Err(error) => return Ok(Err(error)),
        };
    // Role is section semantics, not a decoration on the access mode.  A
    // viewed fact can only be borrowed, while an owned fact may be either a
    // consumed transfer or an entry borrow returned by the contract.  A
    // produced input, or a post-snapshot requirement, is malformed and is
    // rejected before any residual or effect projection is built.
    if checked_required_resources.iter().any(|checked| {
        checked.role == CResourceTransferRole::Produce
            || checked.snapshot == CResourceSnapshot::Post
            || (checked.fact.is_view() && checked.role != CResourceTransferRole::Borrow)
    }) {
        return Ok(Err(CRuntimeError::FunctionContract(
            "resource requirement has an inconsistent transfer role".to_string(),
        )));
    }
    // A view of storage this activation declared, or of read-only storage,
    // is not a caller-supplied borrow. A local array has implicit authority
    // rather than an owned resource fact, so there is nothing to escrow: it
    // keeps the activation-local bounds rule below. A local range the caller
    // holds as a resource fact, whether an explicit owner or a view it was
    // itself lent, is ordinary loan-backed memory and goes through the
    // planner, which also refuses a view whose binding has gone stale.
    //
    // This is the implicit local authority rule (see
    // docs/internals/stable-views.md): while the caller is suspended nothing else can reach its
    // unowned local storage, a callee cannot write through a view, and a
    // view returned from the call still has to pass the provenance routes,
    // so the read is authorized for the call without a ledger transition.
    let intrinsic_read_views = checked_required_resources
        .iter()
        .filter(|requirement| {
            let unsupplied_local = |range: &CMemoryRange| {
                range.base().block.starts_with("local:")
                    && callee_state.memory().has_block(&range.base().block)
                    && caller_state
                        .resources()
                        .directly_supporting_owned_entry(&requirement.fact, assumptions)
                        .is_none()
                    && caller_state
                        .resources()
                        .view_occurrences_for_fact(&requirement.fact, assumptions)
                        .is_empty()
            };
            matches!(
                requirement.fact.resource(),
                CResource::Memory(range)
                    if requirement.fact.is_view()
                        && (unsupplied_local(range)
                            || callee_state.memory().is_read_only_block(&range.base().block))
            )
        })
        .cloned()
        .collect::<Vec<_>>();
    // A composite view whose checked body is empty on this path protects no
    // bytes and holds no token, so there is nothing to lend and nothing a
    // loan could suspend (D6: an empty permission grants no dereference).
    // Demanding backing for it would turn the empty witness of a partial
    // recursive resource into a missing-backing refusal and hide the
    // structural validation that is the real verdict on such a call. Such a
    // requirement is discharged by definitional expansion instead.
    let empty_composite_views = if purpose.lends() {
        checked_required_resources
            .iter()
            .filter(|requirement| {
                requirement.fact.is_view()
                    && matches!(requirement.fact.resource(), CResource::Composite { .. })
                    && expand_all_composite_resource_facts(
                        &ResourceContext::new().unchecked_with_fact(requirement.fact.clone()),
                        interface.composite_resource_definitions(),
                        callee_state.memory(),
                        assumptions,
                    )
                    .is_some_and(|expanded| expanded.facts().is_empty())
            })
            .cloned()
            .collect::<Vec<_>>()
    } else {
        Vec::new()
    };
    // D9: a declared mutable effect is a consequence of the authority the
    // call received and cannot widen it, so the call site compares each
    // effect against every byte this call keeps as a checked view. A planned
    // stable view carries its own range, but neither group above is planned
    // at all -- both are filtered out of `stable_requirements` below -- so
    // their bytes are recorded on the transfer instead. An intrinsic read
    // view is always a plain memory range by the filter that selects it; an
    // empty composite view has an empty checked body and protects no bytes,
    // which is exactly why it needs no backing. The composite views that do
    // reach the planner add their checked frontier pieces below.
    // Neither group is backed by an owned occurrence of the caller's
    // partition, so neither carries a support and both stay on the
    // arithmetic comparison.
    let mut checked_view_frontier = if purpose.lends() {
        intrinsic_read_views
            .iter()
            .chain(empty_composite_views.iter())
            .filter_map(|requirement| Some((requirement.fact.memory_range().cloned()?, None)))
            .collect::<Vec<_>>()
    } else {
        Vec::new()
    };
    // A population's cardinality lives in the tracked population and its
    // transition, not in the resource algebra: the caller holds one
    // representative unit whose quantity is the unit, while `N of p` is
    // discharged definitionally and the count arithmetic is checked by
    // `apply_counted_population_transitions_with_interface`. The stable
    // planner's exclusive reservation asks for one owned entry that directly
    // entails the whole requirement, which no representative can supply for a
    // symbolic or non-unit constant quantity, so such a requirement takes the
    // definitional route. A token population protects no memory, so the
    // ledger has nothing to say about it; a population whose body owns memory
    // is still checked against the active loans after planning.
    let population_quantity_requirements = if purpose.lends() {
        checked_required_resources
            .iter()
            .filter(|requirement| requirement_is_population_quantity(requirement))
            .cloned()
            .collect::<Vec<_>>()
    } else {
        Vec::new()
    };
    // A conditional composite whose guard the assumptions decide false has an
    // empty body on this path: it names no bytes, holds no token, and is
    // entailed by the empty context. That is why the definitional route
    // discharges `owns owned_item(null)` under `if item != 0` with nothing at
    // all, while the planner's exclusive reservation would demand a direct
    // owned entry for it and refuse. This is not weaker than the reservation:
    // only a decided guard collapses the body, and an undecided guard leaves
    // the composite folded, so the expansion is not empty and the requirement
    // keeps its entry. The caller residual is still consumed definitionally
    // below.
    let definitionally_empty_owned = if purpose.lends() {
        checked_required_resources
            .iter()
            .filter(|requirement| {
                requirement.fact.is_own()
                    && matches!(requirement.fact.resource(), CResource::Composite { .. })
                    && expand_all_composite_resource_facts(
                        &ResourceContext::new().unchecked_with_fact(requirement.fact.clone()),
                        interface.composite_resource_definitions(),
                        callee_state.memory(),
                        assumptions,
                    )
                    .is_some_and(|expanded| expanded.facts().is_empty())
            })
            .cloned()
            .collect::<Vec<_>>()
    } else {
        Vec::new()
    };
    let stable_requirements = checked_required_resources
        .iter()
        .filter(|requirement| {
            !intrinsic_read_views.contains(requirement)
                && !empty_composite_views.contains(requirement)
                && !population_quantity_requirements.contains(requirement)
                && !definitionally_empty_owned.contains(requirement)
        })
        .cloned()
        .collect::<Vec<_>>();
    let mut planning_resources = if purpose.lends() {
        candidate_planning_resources(
            caller_state.resources(),
            &stable_requirements,
            interface.composite_resource_definitions(),
            caller_state.memory(),
            assumptions,
        )
    } else {
        caller_state.resources().clone()
    };
    let stable_view_plan = if purpose.lends() {
        let (ledger, caller) = match (
            caller_state.loan_ledger().cloned(),
            caller_state.loan_participant(),
        ) {
            (Some(ledger), Some(caller)) => (ledger, caller),
            _ => {
                let ledger = LoanLedger::new();
                let Ok(caller) = ledger.fresh_participant() else {
                    return Ok(Err(CRuntimeError::FunctionContract(
                        "could not allocate stable-view caller participant".to_string(),
                    )));
                };
                (ledger, caller)
            }
        };
        let Ok(callee) = ledger.fresh_participant() else {
            return Ok(Err(CRuntimeError::FunctionContract(
                "could not allocate stable-view callee participant".to_string(),
            )));
        };
        let composite_backings = if stable_requirements.iter().any(|requirement| {
            requirement.fact.is_view()
                && matches!(requirement.fact.resource(), CResource::Composite { .. })
        }) {
            let mut backings = BTreeMap::new();
            for requirement in stable_requirements.iter().filter(|requirement| {
                requirement.fact.is_view()
                    && matches!(requirement.fact.resource(), CResource::Composite { .. })
            }) {
                // Prefer the caller's own owner for this very composite.
                // Only when there is none does the adapter look for another
                // owned description of the same authority (docs/internals/stable-views.md).
                let mut adapted = Vec::new();
                let mut restored = Vec::new();
                let mut selected = requirement.fact.clone();
                if planning_resources
                    .directly_supporting_owned_entry(&requirement.fact, assumptions)
                    .is_none()
                    // A view the caller already holds is reborrowed from its
                    // own binding, which needs no backing of its own.
                    && planning_resources
                        .view_occurrences_for_fact(&requirement.fact, assumptions)
                        .is_empty()
                {
                    match candidate_composite_view_adapter(
                        &planning_resources,
                        &requirement.fact,
                        interface.composite_resource_definitions(),
                        caller_state,
                        assumptions,
                        budget,
                    )? {
                        Some(adapter) => {
                            planning_resources = adapter.resources;
                            selected = adapter.head;
                            adapted = adapter.adapted;
                            restored = adapter.restored;
                        }
                        None => continue,
                    }
                }
                let Some((support, owned)) = planning_resources
                    .directly_supporting_owned_entry(&selected, assumptions)
                    .map(|(support, owned)| (support, owned.clone()))
                else {
                    continue;
                };
                let owned = &owned;
                // One checked level: primitive children enter the write
                // index, nested composite children become permitted
                // descriptions that projection can open later. The head's
                // escrow protects everything under it, so nothing deeper
                // needs enumerating.
                let singleton = ResourceContext::new().unchecked_with_fact(owned.clone());
                let Some((_, expanded_children, _)) = expand_composite_resource_fact_with_children(
                    &singleton,
                    owned,
                    interface.composite_resource_definitions(),
                    caller_state.memory(),
                    assumptions,
                ) else {
                    return Ok(Err(CRuntimeError::FunctionContract(
                        "could not check the frontier of a composite view".to_string(),
                    )));
                };
                // A viewed piece is a description the head packages (a
                // borrowing composite, step 7): it has no owner here to
                // escrow, so it enters the loan as a permitted description
                // with no byte backing, protected by the hold its head keeps.
                if expanded_children
                    .iter()
                    .any(|fact| matches!(fact.resource(), CResource::Instance(_)))
                {
                    return Ok(Err(CRuntimeError::FunctionContract(
                        "an exclusive instance inside a composite view is unsupported".to_string(),
                    )));
                }
                // The folded head names no bytes of its own, so these checked
                // pieces are the frontier a declared mutable effect has to
                // stay out of. They are recorded before the backing consumes
                // them and only kept once the backing is accepted below. Each
                // piece carries the head's own support: the pieces are that
                // one owned occurrence's bytes, so an effect reserved from a
                // different occurrence is disjoint from them by the partition
                // invariant, exactly as it is from the head.
                let frontier_pieces = expanded_children
                    .iter()
                    .filter_map(|piece| Some((piece.memory_range().cloned()?, Some(support))))
                    .collect::<Vec<_>>();
                let Some(definition) =
                    interface
                        .composite_resource_definitions()
                        .iter()
                        .find(|definition| {
                            matches!(
                                owned.resource(),
                                CResource::Composite { name, .. } if definition.name() == name
                            )
                        })
                else {
                    return Ok(Err(CRuntimeError::FunctionContract(
                        "composite loan definition is missing".to_string(),
                    )));
                };
                // Recovery restores the exact escrowed head, so its facts are
                // re-asserted precisely as folded; that is sound only when
                // everything a fact depends on is stable for the loan.
                if !definition.facts_are_loan_stable() {
                    return Ok(Err(CRuntimeError::FunctionContract(
                        "composite body facts depend on a resource count or an allocation-liveness claim, which a stable loan does not stabilize".to_string(),
                    )));
                }
                let Some(backing) = CompositeLoanBacking::from_checked_adapter(
                    support,
                    owned.clone(),
                    expanded_children,
                    adapted,
                    restored,
                ) else {
                    return Ok(Err(CRuntimeError::FunctionContract(
                        "composite loan frontier is not a checked expansion".to_string(),
                    )));
                };
                checked_view_frontier.extend(frontier_pieces);
                backings.insert(support, backing);
            }
            backings
        } else {
            BTreeMap::new()
        };
        match plan_stable_view_transfer_with_bindings_and_composites(
            &planning_resources,
            &stable_requirements,
            assumptions,
            &ledger,
            caller,
            callee,
            caller_state.loan_view_bindings(),
            &composite_backings,
        ) {
            Ok(plan) => {
                if let Err(error) = plan.recheck_entry(&ledger) {
                    return Ok(Err(CRuntimeError::LoanRefusal(
                        error.diagnostic(LoanRefusalOperation::Entry),
                    )));
                }
                Some(plan)
            }
            Err(error) => {
                // An owned requirement the caller cannot supply is a missing
                // owner, whatever planned it: name the fact, as the ordinary
                // resource transfer does, rather than a loan the call never
                // asked for. A view the planner cannot back is a loan matter.
                if let super::loans::StableViewPlanError::MissingResource(resource) = &error
                    && resource.is_own()
                {
                    return Ok(Err(CRuntimeError::MissingResource {
                        resource: resource.clone(),
                    }));
                }
                if let Some(diagnostic) = error.loan_diagnostic(LoanRefusalOperation::Plan) {
                    return Ok(Err(CRuntimeError::LoanRefusal(diagnostic)));
                }
                return Ok(Err(CRuntimeError::FunctionContract(
                    "stable-view call transition refused".to_string(),
                )));
            }
        }
    } else {
        None
    };
    // Excluding a counted-population requirement from the exclusive
    // reservation costs nothing for a token population, whose units protect
    // no bytes. A population whose body owns memory is a different matter:
    // its units carry write authority over that storage into the callee, so
    // it is checked against the loans this plan and the caller hold, exactly
    // as a direct owned transfer of those bytes would be.
    if let Some(plan) = &stable_view_plan {
        for requirement in &population_quantity_requirements {
            let singleton = ResourceContext::new().unchecked_with_fact(requirement.fact.clone());
            let body = match evaluate_resource_population_body_resources(
                &singleton,
                callee_state,
                interface.composite_resource_definitions(),
                assumptions,
                budget,
                false,
            )? {
                Ok(resources) => resources,
                Err(error) => return Ok(Err(error)),
            };
            let body = expand_all_composite_resource_facts(
                &body,
                interface.composite_resource_definitions(),
                callee_state.memory(),
                assumptions,
            )
            .unwrap_or(body);
            for fact in body.facts().iter().filter(|fact| fact.is_own()) {
                let Some(range) = fact.memory_range() else {
                    continue;
                };
                if let Some(diagnostic) = plan.ledger.memory_access_refusal(
                    range,
                    assumptions,
                    LoanRefusalOperation::Plan,
                ) {
                    return Ok(Err(CRuntimeError::LoanRefusal(diagnostic)));
                }
            }
        }
    }
    let Some(canonical_resources) = expand_all_composite_resource_facts(
        &required_resources,
        interface.composite_resource_definitions(),
        callee_state.memory(),
        assumptions,
    ) else {
        return Ok(Err(CRuntimeError::FunctionContract(format!(
            "could not expand required composite resources before call: {required_resources:?}"
        ))));
    };
    let canonical_resources = expand_decidable_composite_resource_frontier(
        &canonical_resources,
        interface.composite_resource_definitions(),
        callee_state.memory(),
        assumptions,
    );
    let population_body_resources = match evaluate_resource_population_body_resources(
        &required_resources,
        callee_state,
        interface.composite_resource_definitions(),
        assumptions,
        budget,
        false,
    )? {
        Ok(resources) => resources,
        Err(error) => return Ok(Err(error)),
    };
    let required_composite_heads = required_resources
        .facts()
        .iter()
        .filter_map(resource_fact_composite_head)
        .collect::<Vec<_>>();
    let caller_composite_heads = caller_state
        .resources()
        .facts()
        .iter()
        .filter_map(resource_fact_composite_head)
        .collect::<Vec<_>>();
    let has_explicit_representation = caller_state.resources().facts().len()
        != required_resources.facts().len()
        || caller_composite_heads != required_composite_heads;
    let mut callee_resources = if let Some(plan) = &stable_view_plan {
        plan.callee_resources.clone()
    } else if preserve_explicit_representation && has_explicit_representation {
        // Proof execution may have opened exactly the recursive branches needed
        // by the body with `observe` or `unfold`. Independent certification
        // must execute from that same definitionally equivalent form.
        // The transfer checks below still consume every declared requirement,
        // so this cannot weaken the function contract or affect ordinary
        // calls, which always use the canonical boundary.
        caller_state.resources().clone()
    } else {
        canonical_resources
    };
    for empty_view in &empty_composite_views {
        // The head names a resource the callee may state; its checked body is
        // empty, so composing it adds a description and no authority.
        if !callee_resources.satisfies_fact(&empty_view.fact, assumptions) {
            callee_resources = match callee_resources
                .try_compose_with_fact(empty_view.fact.clone(), assumptions)
            {
                Ok(resources) => resources,
                Err(error) => return Ok(Err(resource_context_runtime_error(error))),
            };
        }
    }
    for requirement in &population_quantity_requirements {
        // The plan never saw this requirement, so the callee context has to
        // receive exactly what the canonical boundary would have handed it:
        // the requirement expanded through its definition, the same way
        // `canonical_resources` expands every other required resource.
        let singleton = ResourceContext::new().unchecked_with_fact(requirement.fact.clone());
        let expanded = expand_all_composite_resource_facts(
            &singleton,
            interface.composite_resource_definitions(),
            callee_state.memory(),
            assumptions,
        )
        .map(|expanded| {
            expand_decidable_composite_resource_frontier(
                &expanded,
                interface.composite_resource_definitions(),
                callee_state.memory(),
                assumptions,
            )
        })
        .unwrap_or(singleton);
        for fact in expanded.facts() {
            if callee_resources.satisfies_fact(fact, assumptions) {
                continue;
            }
            callee_resources = match callee_resources
                .try_compose_with_facts_delaying_normalization([fact.clone()], assumptions)
            {
                Ok(resources) => resources,
                Err(error) => return Ok(Err(resource_context_runtime_error(error))),
            };
        }
    }
    for intrinsic_view in &intrinsic_read_views {
        // The activation-local bounds rule, decided before any read is
        // attempted. Implicit local authority covers the storage the block
        // has and nothing past it, so a view running off the end is a
        // resource the caller cannot supply, whoever planned the call.
        // Merely withholding the view would let the verdict become the
        // callee's first read of the cells beyond the block, which names the
        // wrong invariant: the call is refused because the view is not
        // backed, not because the storage happens to be uninitialized.
        if matches!(
            intrinsic_view.fact.resource(),
            CResource::Memory(range)
                if range.base().block.starts_with("local:")
                    && !local_view_range_within_block(range, callee_state.memory())
        ) {
            return Ok(Err(CRuntimeError::MissingResource {
                resource: intrinsic_view.fact.clone(),
            }));
        }
        if !callee_resources.satisfies_fact(&intrinsic_view.fact, assumptions) {
            callee_resources = match callee_resources
                .try_compose_with_fact(intrinsic_view.fact.clone(), assumptions)
            {
                Ok(resources) => resources,
                Err(error) => return Ok(Err(resource_context_runtime_error(error))),
            };
        }
    }
    for body_resource in population_body_resources.facts() {
        // The population owns its body even while that body is absent from
        // the caller's explicit proof context. Contract execution opens the
        // body internally after the required population unit has established
        // authority; surface proofs still need scoped `open` to use it.
        if !callee_resources.satisfies_fact(body_resource, assumptions) {
            callee_resources = match callee_resources
                .try_compose_with_facts_delaying_normalization([body_resource.clone()], assumptions)
            {
                Ok(resources) => resources,
                Err(error) => return Ok(Err(resource_context_runtime_error(error))),
            };
        }
    }
    if preserve_explicit_representation && has_explicit_representation {
        let viewed_composites = caller_state
            .resources()
            .facts()
            .iter()
            .filter(|fact| matches!(fact, CResourceFact::View(CResource::Composite { .. })))
            .cloned()
            .collect::<Vec<_>>();
        for composite in viewed_composites {
            let singleton = ResourceContext::new().unchecked_with_fact(composite.clone());
            if let Some(expanded) = expand_composite_resource_fact(
                &singleton,
                &composite,
                interface.composite_resource_definitions(),
                callee_state.memory(),
                assumptions,
            ) {
                callee_resources =
                    callee_resources.unchecked_with_facts(expanded.facts().iter().cloned());
            }
        }
    }
    // Consumption uses the normalized algebraic context so duplicate token
    // clauses retain their quantity (and diagnostics name the complete
    // requirement).  The provenance-bearing list remains the effect source;
    // normalization is not allowed to erase its role/snapshot metadata.
    let mut required_resource_list = required_resources.facts().to_vec();
    required_resource_list.sort_by_key(resource_fact_transfer_priority);

    let mut return_resources = stable_view_plan
        .as_ref()
        .map(|plan| plan.caller_resources_after_requirements.clone())
        .unwrap_or_else(|| caller_state.resources().clone());
    // The requirements the plan did not reserve are consumed here, off the
    // residual the plan published, by the definitional route. Everything else
    // the plan already removed.
    let population_quantity_resources = population_quantity_requirements
        .iter()
        .map(|requirement| requirement.fact.resource().clone())
        .collect::<BTreeSet<_>>();
    let definitionally_empty_owned_resources = definitionally_empty_owned
        .iter()
        .map(|requirement| requirement.fact.resource().clone())
        .collect::<BTreeSet<_>>();
    for resource in required_resource_list.iter().filter(|resource| {
        stable_view_plan.is_none()
            || (resource.is_own()
                && (population_quantity_resources.contains(resource.resource())
                    || definitionally_empty_owned_resources.contains(resource.resource())))
    }) {
        // A borrowed view of the caller's own stack object needs no resource
        // from the caller, but it still has to name storage that object has.
        // A range running past the block would otherwise let the callee read
        // whatever the caller keeps beyond it: `views a[0..3]` on an
        // `int32 b[2]` used to be discharged by the block merely existing.
        if let CResourceFact::View(CResource::Memory(range)) = resource
            && range.base().block.starts_with("local:")
            && callee_state.memory().has_block(&range.base().block)
            && local_view_range_within_block(range, callee_state.memory())
        {
            continue;
        }
        if let CResource::Composite { name, arguments } | CResource::Token { name, arguments } =
            resource.resource()
            && interface
                .composite_resource_definitions()
                .iter()
                .any(|definition| definition.is_counted_population() && definition.name() == name)
            && !return_resources.satisfies_fact(resource, assumptions)
            && callee_state
                .counted_population(name, arguments)
                .is_some_and(|count| {
                    quantity_condition_holds(
                        assumptions,
                        ConditionTerm::Bitvector32Equal(
                            Box::new(count.clone()),
                            Box::new(Bitvector32Term::Constant(1)),
                        ),
                    )
                })
        {
            let singleton = ResourceContext::new().unchecked_with_fact(resource.clone());
            let body = match evaluate_resource_population_body_resources(
                &singleton,
                callee_state,
                interface.composite_resource_definitions(),
                assumptions,
                budget,
                false,
            )? {
                Ok(resources) => resources,
                Err(error) => return Ok(Err(error)),
            };
            let unfolded = body
                .facts()
                .iter()
                .try_fold(return_resources.clone(), |resources, body_resource| {
                    resources.without_fact(body_resource, assumptions)
                });
            if let Some(unfolded) = unfolded {
                return_resources = unfolded;
                continue;
            }
        }
        let Some(resources) = consume_resource_fact_definitionally(
            &return_resources,
            resource,
            interface.composite_resource_definitions(),
            caller_state.memory(),
            assumptions,
        ) else {
            return Ok(Err(CRuntimeError::MissingResource {
                resource: resource.clone(),
            }));
        };
        return_resources = resources;
    }
    let borrowed_inputs = checked_required_resources
        .iter()
        .filter(|checked| checked.role == CResourceTransferRole::Borrow)
        .cloned()
        .collect();
    let consumed_inputs = checked_required_resources
        .iter()
        .filter(|checked| checked.role == CResourceTransferRole::Consume)
        .cloned()
        .collect();
    let canonical_borrowed_owners = stable_view_plan
        .as_ref()
        .into_iter()
        .flat_map(|plan| {
            plan.transferred_ownership
                .iter()
                .zip(&plan.canonical_transferred_ownership)
        })
        .filter_map(|(checked, canonical)| {
            (checked.role == CResourceTransferRole::Borrow)
                .then(|| {
                    canonical
                        .clone()
                        .map(|canonical| (checked.fact.clone(), canonical))
                })
                .flatten()
        })
        .collect();
    Ok(Ok(CFunctionResourceTransfer {
        borrowed_inputs,
        consumed_inputs,
        canonical_borrowed_owners,
        callee_resources,
        caller_resources_after_requirements: return_resources,
        memory_effects: Vec::new(),
        post_outputs: None,
        candidate_output_views: Vec::new(),
        produced_borrowing_pieces: Vec::new(),
        stable_view_plan,
        checked_view_frontier,
    }))
}

/// Evaluates the first `count` returned resources of a contract as one
/// jointly returned context. A borrowed resource (an `owns` clause) is
/// evaluated at `entry_state`: the callee returns exactly what it was lent,
/// even when the clause's address depends on a field the body writes. Every
/// other returned resource is evaluated at `post_state`, where the result and
/// the exit memory are visible.
pub(super) fn evaluate_function_return_resource_context(
    function: &CFunction,
    entry_state: &CState,
    post_state: &CState,
    count: usize,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ResourceContext, CRuntimeError>> {
    evaluate_contract_return_resource_context(
        function.contract_interface(),
        &[],
        entry_state,
        post_state,
        count,
        assumptions,
        budget,
    )
}

fn evaluate_contract_return_resource_context(
    interface: &CFunctionContractInterface,
    canonical_borrowed_owners: &[(CResourceFact, CResourceFact)],
    entry_state: &CState,
    post_state: &CState,
    count: usize,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ResourceContext, CRuntimeError>> {
    let mut context = ResourceContext::new();
    // `owns` requirements that are returned as entry-snapshot borrows carry
    // caller identity in the checked transition. Re-evaluating an address
    // such as `self->pointer` in the callee entry state can replace that
    // identity with a symbolic parameter spelling, even though the resource
    // being returned is exactly the occurrence that was lent. Consume the
    // already checked owned inputs in their source order instead. Views keep
    // their ordinary evaluation path because their loan provenance is
    // reconstructed separately, and post-snapshot instances carry fresh
    // fields rather than an entry fact.
    let mut canonical_by_checked = BTreeMap::<CResourceFact, VecDeque<CResourceFact>>::new();
    for (checked, canonical) in canonical_borrowed_owners {
        canonical_by_checked
            .entry(checked.clone())
            .or_default()
            .push_back(canonical.clone());
    }
    // An entry-snapshot borrow whose address depends on a cell the contract's
    // own composites hold (`owns pair(node)` supplying the link
    // `owns pair(node->left->left)` loads) is read the way the entry read
    // it: through the clause set opened by its definitions. The opened cells
    // enter as read authority only, computed once for the entry; the
    // evaluated fact is then matched to the owner the transition lent, never
    // replaced.
    let entry_opened_views = if interface
        .resource_ensures()
        .iter()
        .take(count)
        .any(|resource| resource.snapshot() == CResourceSnapshot::Entry)
    {
        opened_composite_read_views(
            entry_state.resources(),
            interface.composite_resource_definitions(),
            entry_state.memory(),
            assumptions,
        )
    } else {
        Vec::new()
    };
    for resource in interface.resource_ensures().iter().take(count) {
        // Snapshot selection is carried by the normalized specification. A
        // named instance is always post-evaluated by lowering, so its
        // identity remains stable while its fields can be fresh.
        let state = match resource.snapshot() {
            CResourceSnapshot::Entry => entry_state,
            CResourceSnapshot::Current | CResourceSnapshot::Post => post_state,
        };
        // A returned borrow is addressed through the cells the contract
        // already holds, including those a folded matched instance publishes
        // for its selected arm (D7). Without that read authority
        // `owns node->right->augmented` could be required at entry and then
        // fail to be evaluated at the very same state on return.
        let supply = state
            .resources()
            .clone()
            .unchecked_with_facts(context.facts().iter().cloned());
        let mut views = instance_arm_views(
            &supply,
            interface.composite_resource_definitions(),
            state,
            assumptions,
        );
        if resource.snapshot() == CResourceSnapshot::Entry {
            views.extend(entry_opened_views.iter().cloned());
        }
        let evaluation_state = state
            .clone()
            .with_resource_context(supply.unchecked_with_facts(views));
        let evaluated = match evaluate_function_resource_spec_with_entry(
            entry_state,
            &evaluation_state,
            resource,
            assumptions,
            budget,
        )? {
            Ok(resource) => resource,
            Err(error) => return Ok(Err(error)),
        };
        let resource = if resource.role() == CResourceTransferRole::Borrow
            && resource.snapshot() == CResourceSnapshot::Entry
            && !resource.is_view()
        {
            canonical_by_checked
                .get_mut(&evaluated)
                .and_then(VecDeque::pop_front)
                .unwrap_or(evaluated)
        } else {
            evaluated
        };
        context = match context.try_compose_with_fact(resource, assumptions) {
            Ok(context) => context,
            Err(error) => return Ok(Err(resource_context_runtime_error(error))),
        };
    }
    Ok(Ok(context))
}

/// The memory a context's owned composites hold, opened through their
/// definitions over `memory`, as read views: the authority a clause set
/// gives to the addresses its own dependent clauses load, offered to an
/// evaluation that reads the entry the way the entry itself did. Nothing is
/// owned twice; a view grants a read and no more.
fn opened_composite_read_views(
    resources: &ResourceContext,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &PureFactContext,
) -> Vec<CResourceFact> {
    if !resources
        .facts()
        .iter()
        .any(|fact| fact.is_own() && matches!(fact.resource(), CResource::Composite { .. }))
    {
        return Vec::new();
    }
    let Some(opened) =
        expand_all_composite_resource_facts(resources, definitions, memory, assumptions)
    else {
        return Vec::new();
    };
    let opened =
        expand_decidable_composite_resource_frontier(&opened, definitions, memory, assumptions);
    opened
        .facts()
        .iter()
        .filter_map(|fact| match fact {
            CResourceFact::Own(resource @ CResource::Memory(_), _) => {
                Some(CResourceFact::View(resource.clone()))
            }
            _ => None,
        })
        .collect()
}

/// The owned facts a call's lend escrowed. They are not in the
/// caller residual for the duration of the call, but recovery composes each
/// one back, so a check on what the caller will hold has to read them.
fn escrowed_owners(transfer: &CFunctionResourceTransfer) -> &[CResourceFact] {
    transfer
        .stable_view_plan
        .as_ref()
        .map(|plan| plan.escrowed_owners())
        .unwrap_or_default()
}

#[allow(clippy::too_many_arguments)]
fn evaluate_function_return_resources(
    caller_resources_after_requirements: &ResourceContext,
    escrowed_owners: &[CResourceFact],
    entry_state: &CState,
    post_state: &CState,
    function: &CFunction,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ContractReturnResources, CRuntimeError>> {
    evaluate_contract_return_resources(
        caller_resources_after_requirements,
        escrowed_owners,
        &[],
        entry_state,
        post_state,
        function.name(),
        function.contract_interface(),
        assumptions,
        budget,
    )
}

#[allow(clippy::too_many_arguments)]
fn evaluate_contract_return_resources(
    caller_resources_after_requirements: &ResourceContext,
    escrowed_owners: &[CResourceFact],
    canonical_borrowed_owners: &[(CResourceFact, CResourceFact)],
    entry_state: &CState,
    post_state: &CState,
    interface_name: &str,
    interface: &CFunctionContractInterface,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ContractReturnResources, CRuntimeError>> {
    let ensured_resources = match crate::instrumentation::measure_operation(
        interface_name,
        "contract resource transition",
        "ensured resource lowering",
        || {
            evaluate_contract_return_resource_context(
                interface,
                canonical_borrowed_owners,
                entry_state,
                post_state,
                interface.resource_ensures().len(),
                assumptions,
                budget,
            )
        },
    )? {
        Ok(resources) => resources,
        Err(error) => return Ok(Err(error)),
    };
    // A composite arrives folded, so composing its head says nothing about
    // what its body covers. Check the body against the destination before the
    // head enters it, or a contract that produces a composite over bytes the
    // destination still owns turns one owner into two.
    if let Some(error) = crate::instrumentation::measure_operation(
        interface_name,
        "contract resource transition",
        "ensured composite frontier check",
        || {
            // A lend empties the escrowed owner out of the residual, and
            // recovery composes it straight back. The destination for this
            // check is what the caller holds across the call, so the escrow
            // belongs in it; without it the stable-view transition would
            // admit exactly the overlap the definitional residual catches.
            let destination = caller_resources_after_requirements
                .clone()
                .unchecked_with_facts(escrowed_owners.iter().cloned());
            produced_composite_frontier_conflict(
                &destination,
                &ensured_resources,
                interface.composite_resource_definitions(),
                post_state.memory(),
                assumptions,
            )
        },
    ) {
        return Ok(Err(error));
    }
    let ensured_views = ensured_resources
        .facts()
        .iter()
        .filter(|fact| fact.is_view())
        .cloned()
        .collect::<Vec<_>>();
    // Every ensured view is composed into the caller and then classified by
    // where its live authority comes from. The blanket deduplication that
    // used to drop an ensured view the caller already satisfied is gone
    // (docs/internals/stable-views.md: "blanket deduplication against a caller owner is no
    // longer a valid way to discharge obligations", closed as step 6's
    // F14(c)). It was a filter against `satisfies_fact`, so an owner the
    // caller happened to hold silently answered a returned view; the
    // provenance routes in `recover_candidate_stable_view_resources` decide
    // that question now, over `candidate_output_views` and the residual
    // alike.
    let (return_resources, inserted_ensured_occurrences) =
        match crate::instrumentation::measure_operation(
            interface_name,
            "contract resource transition",
            "ensured resource composition",
            || {
                caller_resources_after_requirements
                    .clone()
                    .try_compose_with_facts_delaying_normalization_with_occurrences(
                        ensured_resources.facts().iter().cloned(),
                        assumptions,
                    )
            },
        ) {
            Ok(resources) => resources,
            Err(error) => return Ok(Err(resource_context_runtime_error(error))),
        };
    let mut source_ranks = BTreeMap::<CResourceFact, usize>::new();
    let Some(projected_cores_by_support) = crate::instrumentation::measure_operation(
        interface_name,
        "contract resource transition",
        "ensured resource core projection",
        || {
            let _assumptions_id_scope = crate::kernel::PureFactContextIdScope::enter(assumptions);
            ensured_resources
                .facts()
                .iter()
                .filter(|support| support.is_own())
                .map(|support| {
                    let source_rank = source_ranks.entry(support.clone()).or_default();
                    let support_occurrence = ensured_resources
                        .owned_occurrences_for_fact(support)
                        .get(*source_rank)
                        .copied()?;
                    *source_rank += 1;
                    let singleton = ResourceContext::new().unchecked_with_fact(support.clone());
                    let expanded = expand_all_composite_resource_facts(
                        &singleton,
                        interface.composite_resource_definitions(),
                        post_state.memory(),
                        assumptions,
                    )?;
                    let expansion = expanded.facts().to_vec();
                    let projected = expansion
                        .iter()
                        .filter_map(|fact| fact.core_with_assumptions(assumptions))
                        // These duplicable cores are certified projections of
                        // `support`; publishing them needs no proof-aware
                        // search through the caller's existing resources.
                        // Exact duplicates are the only entries worth
                        // suppressing here. Equivalent alternate spellings
                        // remain supported by this occurrence and disappear
                        // with it.
                        .filter(|core| !return_resources.contains_exact_representation(core))
                        .collect::<BTreeSet<_>>()
                        .into_iter()
                        .collect::<Vec<_>>();
                    Some((support.clone(), support_occurrence, expansion, projected))
                })
                .collect::<Option<Vec<_>>>()
        },
    ) else {
        return Ok(Err(CRuntimeError::FunctionContract(format!(
            "could not expand ensured composite resources after call: {ensured_resources:?}"
        ))));
    };
    // The callee has already certified every ensured composite and its
    // instantiated body. Its duplicable cores are therefore observations of
    // certified ownership, not independent persistent caller capabilities.
    // Record their exact support so consuming that ownership removes only
    // its projections through the reverse index.
    let mut destination_occurrences = std::collections::BTreeMap::<
        CResourceFact,
        Vec<crate::kernel::primitives::ResourceOccurrenceId>,
    >::new();
    for (fact, occurrence) in inserted_ensured_occurrences {
        destination_occurrences
            .entry(fact)
            .or_default()
            .push(occurrence);
    }
    let mut destination_source_ranks = std::collections::BTreeMap::<CResourceFact, usize>::new();
    let mut destination_by_source_occurrence = std::collections::BTreeMap::new();
    for (support, source_occurrence, _, _) in &projected_cores_by_support {
        let rank = destination_source_ranks.entry(support.clone()).or_default();
        let Some(destination_occurrence) = destination_occurrences
            .get(support)
            .and_then(|occurrences| occurrences.get(*rank))
            .copied()
        else {
            return Ok(Err(CRuntimeError::FunctionContract(format!(
                "ensured resource support was not preserved after call: {support:?}"
            ))));
        };
        *rank += 1;
        destination_by_source_occurrence.insert(*source_occurrence, destination_occurrence);
    }
    let mut return_resources = return_resources;
    let mut produced_borrowing_pieces = Vec::new();
    for (support, source_occurrence, expansion, projected) in projected_cores_by_support {
        // Only the one-level frontier names the borrows this composite
        // packages; a nested composite's own body is that composite's
        // business (the 4b rule). A counted population is not a struct
        // holding a borrow: its body is population-wide, folded into the
        // family by whoever produces a unit (a verified producer cannot mint
        // one without the body), so its viewed pieces keep the observation
        // reading rather than an escaping loan.
        let is_population = match support.resource() {
            CResource::Composite { name, .. } => {
                support.owned_quantity_term() != Some(&Bitvector32Term::Constant(1))
                    || post_state.observes_population_family(name)
                    || entry_state.observes_population_family(name)
                    || interface
                        .composite_resource_definitions()
                        .iter()
                        .any(|definition| {
                            definition.name() == name && definition.is_counted_population()
                        })
            }
            _ => false,
        };
        if let Some((_, children, _)) = (!is_population)
            .then(|| {
                expand_composite_resource_fact_with_children(
                    &ResourceContext::new().unchecked_with_fact(support.clone()),
                    &support,
                    interface.composite_resource_definitions(),
                    post_state.memory(),
                    assumptions,
                )
            })
            .flatten()
        {
            produced_borrowing_pieces.extend(
                children
                    .into_iter()
                    .filter(|piece| piece.is_view())
                    .map(|piece| (support.clone(), piece)),
            );
        }
        let Some(support_occurrence) = destination_by_source_occurrence
            .get(&source_occurrence)
            .copied()
        else {
            return Ok(Err(CRuntimeError::FunctionContract(format!(
                "ensured resource support was not preserved after call: {support:?}"
            ))));
        };
        return_resources = return_resources
            .unchecked_with_supported_facts_from_occurrence_with_memory(
                support_occurrence,
                &support,
                projected,
                post_state.memory(),
            )
            .with_cached_supported_expansion_for_occurrence(
                support_occurrence,
                &support,
                expansion,
            );
    }
    Ok(Ok(ContractReturnResources {
        return_resources,
        ensured_views,
        produced_borrowing_pieces,
    }))
}

/// The outputs of a contract's return-resource evaluation.
pub(crate) struct ContractReturnResources {
    pub(crate) return_resources: ResourceContext,
    pub(crate) ensured_views: Vec<CResourceFact>,
    pub(crate) produced_borrowing_pieces: Vec<(CResourceFact, CResourceFact)>,
}

/// Checks every produced or ensured composite's body against the context it
/// is about to be composed into.
///
/// A valid resource context denotes a partition: every owned fact is disjoint
/// from every other fact in it, composites included. Inside one component the
/// kernel keeps that by construction, because unfolding consumes the head and
/// folding consumes the pieces. A callee's output crosses that boundary as a
/// folded head whose body was never compared with what the destination holds,
/// so without this check `produces box(p)` beside a caller that still owns
/// `p[0..1]` leaves two owners over the same byte.
///
/// Only the one-level checked frontier is compared. A nested composite child
/// is itself a fact here, not a body to reason inside; that is the same
/// "no reasoning inside composites" rule the composite lend follows.
fn produced_composite_frontier_conflict(
    destination: &ResourceContext,
    ensured: &ResourceContext,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &PureFactContext,
) -> Option<CRuntimeError> {
    for produced in ensured.facts() {
        let CResource::Composite { name, .. } = produced.resource() else {
            continue;
        };
        if !produced.is_own() {
            continue;
        }
        // A counted population's body is population-wide, not per unit. Its
        // units carry nothing of their own, and the ensured context adds the
        // units a contract returns as a borrow to the ones it produces, so a
        // quantity above one is ordinary here. The body cannot collide with
        // what the caller holds: a unit is produced only by a fold that
        // consumes the body out of the producer's context (a verified
        // producer cannot mint one without it, see
        // `mdtests/population_unit_needs_its_body.md`), and a caller reaches
        // the body afterwards only as an observation. An extern contract that
        // claims otherwise is its own trust assumption.
        if definitions
            .iter()
            .any(|definition| definition.name() == name && definition.is_counted_population())
        {
            continue;
        }
        let singleton = ResourceContext::new().unchecked_with_fact(produced.clone());
        // An opaque head — no definition, an instance schema, a matched arm,
        // or a guard this path has not decided — exposes no frontier to
        // compare, and expansion is the only thing that could name one.
        let Some((_, frontier, _)) = expand_composite_resource_fact_with_children(
            &singleton,
            produced,
            definitions,
            memory,
            assumptions,
        ) else {
            continue;
        };
        // A token-only body holds no memory, instance, or nested composite a
        // destination fact could overlap: token units are a count, and counts
        // add rather than collide.
        if !frontier.iter().any(|piece| {
            piece.is_own()
                && matches!(
                    piece.resource(),
                    CResource::Memory(_) | CResource::Instance(_) | CResource::Composite { .. }
                )
        }) {
            continue;
        }
        // The frontier was evaluated for one unit, and an ordinary composite
        // has no population-wide body to install instead: every unit owns the
        // same bytes this one does. Two such units are already two owners of
        // one range, and a symbolic count is not a quantity the check below
        // could compare against the destination at all. Refuse rather than
        // check one unit and call the rest checked.
        if produced
            .owned_quantity_term()
            .and_then(Bitvector32Term::as_const)
            != Some(1)
        {
            return Some(CRuntimeError::FunctionContract(format!(
                "a produced quantity of `{name}` other than one owns memory in its \
                 body, so its units would own the same range more than once"
            )));
        }
        // The pieces are a checked composition, so they are already disjoint
        // from one another: one validity check over the whole frontier
        // decides the composite, and only a refusal pays to name the piece.
        let Some(error) = destination
            .clone()
            .unchecked_with_facts(frontier.iter().cloned())
            .validity_error(assumptions)
        else {
            continue;
        };
        let piece = frontier
            .iter()
            .find(|piece| {
                destination
                    .clone()
                    .unchecked_with_fact((*piece).clone())
                    .validity_error(assumptions)
                    .is_some()
            })
            .unwrap_or(produced);
        let held =
            conflicting_destination_fact(destination, &error).unwrap_or_else(|| piece.clone());
        return Some(CRuntimeError::ProducedCompositeOverlapsHeldResource {
            produced: Box::new(produced.clone()),
            piece: Box::new(piece.clone()),
            held: Box::new(held),
        });
    }
    None
}

/// Names the destination fact a frontier piece collides with, so the refusal
/// can point at both sides rather than at a bare range.
fn conflicting_destination_fact(
    destination: &ResourceContext,
    error: &ResourceContextValidityError,
) -> Option<CResourceFact> {
    match error {
        ResourceContextValidityError::InvalidInstanceAccess(fact)
        | ResourceContextValidityError::DuplicateOwnedResourceFact(fact) => Some(fact.clone()),
        // The two overlapping ranges are reported in index order, so the
        // destination's own range may be either side.
        ResourceContextValidityError::OverlappingOwnedMemoryResources { left, right } => {
            destination
                .facts()
                .iter()
                .find(|held| {
                    held.memory_own_range()
                        .is_some_and(|range| range == left || range == right)
                })
                .cloned()
        }
    }
}

/// Whether a requirement asks for a quantity of a resource population other
/// than the unit.
///
/// Only `CResourceSpec::quantified` builds one, and only over a composite or
/// token term, so this is exactly the `N of p` clause. It is not a claim
/// about one owned entry: the caller holds a representative unit while the
/// declared cardinality lives in the tracked population, so the count is
/// decided by the counted-population transition and the definitional route,
/// never by an exact-entry reservation.
fn requirement_is_population_quantity(requirement: &CCheckedResourceFact) -> bool {
    matches!(
        requirement.fact.resource(),
        CResource::Composite { .. } | CResource::Token { .. }
    ) && requirement.fact.is_own()
        && requirement.fact.owned_quantity_term() != Some(&Bitvector32Term::Constant(1))
}

fn counted_population_quantities(
    resources: &ResourceContext,
    definitions: &[CCompositeResourceDefinition],
    tracked_state: &CState,
    assumptions: &PureFactContext,
) -> BTreeMap<(String, ResourceArguments), Bitvector32Term> {
    let mut quantities = BTreeMap::<(String, ResourceArguments), Bitvector32Term>::new();
    for fact in resources.facts() {
        let (name, arguments) = match fact.resource() {
            CResource::Composite { name, arguments } | CResource::Token { name, arguments } => {
                (name, arguments)
            }
            CResource::Memory(_) | CResource::Instance(_) => continue,
        };
        if name == CResourceFact::ALLOCATION_RESOURCE_NAME {
            continue;
        }
        // A counted population has one population-wide owner whose lifetime
        // follows the first produced and last consumed unit, so its count is
        // tracked. An ordinary composite's body lives inside its own head and
        // contributes no such owner, so it enters the transition only when
        // the state already observes its family.
        let has_declared_body = definitions.iter().any(|definition| {
            definition.name() == name && definition_has_population_wide_body(definition)
        });
        let population_is_observed = tracked_state.observes_population_family(name)
            || tracked_state
                .counted_population_proven_equal(name, arguments, assumptions)
                .is_some();
        if !has_declared_body && !population_is_observed {
            continue;
        }
        let Some(quantity) = fact.owned_quantity_term() else {
            continue;
        };
        quantities
            .entry((name.clone(), arguments.clone()))
            .and_modify(|total| {
                *total = Bitvector32Term::add(total.clone(), quantity.clone());
            })
            .or_insert_with(|| quantity.clone());
    }
    quantities
}

/// Only a counted population has a population-wide body.
///
/// An ordinary composite's body lives inside its head: installing it as owned
/// authority beside the produced head let a caller write the body and still
/// use the head's facts, which verified a false theorem (found on
/// 2026-09-13 while landing stable views). The predicate that also admitted an unconditional,
/// non-recursive composite with a snapshot-independent footprint was retired
/// with the `track_ordinary_populations` parameter at step 8c; every caller
/// had already stopped asking for it.
fn definition_has_population_wide_body(definition: &CCompositeResourceDefinition) -> bool {
    definition.is_counted_population()
}

/// Population quantity relations are decided by exact routes only: syntactic
/// identity, constant folding, an indexed exact fact lookup, and the retained
/// atomic condition checker on the bare condition. No general proposition
/// search runs here; a relation that only follows logically becomes an
/// explicit obligation at the consuming operation.
fn population_quantity_is_zero(quantity: &Bitvector32Term, assumptions: &PureFactContext) -> bool {
    quantity == &Bitvector32Term::Constant(0)
        || quantity_condition_holds(
            assumptions,
            ConditionTerm::Bitvector32Equal(
                Box::new(quantity.clone()),
                Box::new(Bitvector32Term::Constant(0)),
            ),
        )
}

fn population_quantity_is_positive(
    quantity: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    quantity.as_const().is_some_and(|value| value > 0)
        || quantity_condition_holds(
            assumptions,
            ConditionTerm::Bitvector32SignedGreaterThan(
                Box::new(quantity.clone()),
                Box::new(Bitvector32Term::Constant(0)),
            ),
        )
}

fn population_quantities_are_equal(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    left == right
        || quantity_condition_holds(
            assumptions,
            ConditionTerm::Bitvector32Equal(Box::new(left.clone()), Box::new(right.clone())),
        )
}

fn population_body_requires_positive_witness(definition: &CCompositeResourceDefinition) -> bool {
    fn resource_is_duplicable_view(resource: &CResourceSpec) -> bool {
        !resource.is_instance() && resource.is_view()
    }

    !definition.facts().is_empty()
        || definition
            .contains()
            .iter()
            .any(|resource| !resource_is_duplicable_view(resource))
}

#[derive(Default)]
struct CCountedPopulationTransition {
    finalized_body_resources: Vec<CResourceFact>,
    population_facts: Vec<Proposition>,
    postcondition_obligations: Vec<ProofObligation>,
}

fn apply_counted_population_transition_resources(
    mut resources: ResourceContext,
    transition: &CCountedPopulationTransition,
    assumptions: &PureFactContext,
) -> Result<ResourceContext, CRuntimeError> {
    for resource in &transition.finalized_body_resources {
        for representation in [
            Some(resource.clone()),
            resource.core_with_assumptions(assumptions),
        ]
        .into_iter()
        .flatten()
        {
            while resources.facts().contains(&representation) {
                resources = resources
                    .without_exact_representation(&representation)
                    .expect(
                        "an exact finalized population-body representation should be removable",
                    );
            }
        }
    }
    Ok(resources)
}

fn apply_counted_population_transitions(
    caller_state: &CState,
    post_state: &mut CState,
    function: &CFunction,
    argument_values: &[CValue],
    assumptions: &PureFactContext,
    reestablish_invariants: bool,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<CCountedPopulationTransition, CRuntimeError>> {
    apply_counted_population_transitions_with_interface(
        caller_state,
        post_state,
        Some(function),
        function.contract_interface(),
        argument_values,
        assumptions,
        reestablish_invariants,
        budget,
    )
}

fn apply_counted_population_transitions_with_interface(
    caller_state: &CState,
    post_state: &mut CState,
    storage: Option<&CFunction>,
    interface: &CFunctionContractInterface,
    argument_values: &[CValue],
    assumptions: &PureFactContext,
    reestablish_invariants: bool,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<CCountedPopulationTransition, CRuntimeError>> {
    let Some(mut entry_state) =
        bind_c_contract_arguments(caller_state, interface, argument_values, storage)
    else {
        return Ok(Err(CRuntimeError::TypeMismatch));
    };
    // Resource formals belong to this call, just like the C argument views.
    entry_state.resource_bindings = post_state.resource_bindings.clone();
    let required = match evaluate_function_resource_context(
        &entry_state,
        interface.resource_requires(),
        interface.composite_resource_definitions(),
        assumptions,
        budget,
    )? {
        Ok(resources) => resources,
        Err(error) => return Ok(Err(error)),
    };
    let post_contract_state =
        with_contract_interface_argument_views(post_state, interface, argument_values);
    let ensured = match evaluate_function_resource_context(
        &post_contract_state,
        interface.resource_ensures(),
        interface.composite_resource_definitions(),
        assumptions,
        budget,
    )? {
        Ok(resources) => resources,
        Err(error) => return Ok(Err(error)),
    };
    let required_quantities = counted_population_quantities(
        &required,
        interface.composite_resource_definitions(),
        caller_state,
        assumptions,
    );
    let ensured_quantities = counted_population_quantities(
        &ensured,
        interface.composite_resource_definitions(),
        caller_state,
        assumptions,
    );
    let caller_quantities = counted_population_quantities(
        caller_state.resources(),
        interface.composite_resource_definitions(),
        caller_state,
        assumptions,
    );
    let keys = required_quantities
        .keys()
        .chain(ensured_quantities.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut transition = CCountedPopulationTransition::default();
    let mut transition_guaranteed_facts = Vec::new();
    for (name, arguments) in keys {
        let declared_population_definition = interface
            .composite_resource_definitions()
            .iter()
            .find(|definition| definition.name() == name);
        let population_body_definition = declared_population_definition
            .filter(|definition| definition_has_population_wide_body(definition));
        let required_quantity = required_quantities
            .get(&(name.clone(), arguments.clone()))
            .cloned()
            .unwrap_or(Bitvector32Term::Constant(0));
        let ensured_quantity = ensured_quantities
            .get(&(name.clone(), arguments.clone()))
            .cloned()
            .unwrap_or(Bitvector32Term::Constant(0));
        if population_quantities_are_equal(&required_quantity, &ensured_quantity, assumptions) {
            // A resource-neutral contract preserves this exact population.
            // Do not ask general arithmetic reasoning to rediscover
            // `old_count + 0 != 0`; on large proof contexts that turns a
            // constant-time ledger update into an expensive search.
            if caller_state.counted_population(&name, &arguments).is_none() {
                let visible_count = caller_quantities
                    .get(&(name.clone(), arguments.clone()))
                    .cloned()
                    .unwrap_or(required_quantity);
                if population_quantity_is_positive(&visible_count, assumptions) {
                    *post_state =
                        post_state
                            .clone()
                            .with_counted_population(name, arguments, visible_count);
                }
            }
            continue;
        }
        let consumes_entire_population =
            population_quantity_is_zero(&ensured_quantity, assumptions)
                && caller_state
                    .counted_population(&name, &arguments)
                    .is_some_and(|old_count| {
                        population_quantities_are_equal(old_count, &required_quantity, assumptions)
                    });
        let tracked_prior = caller_state.counted_population(&name, &arguments).cloned();
        let visible_prior = caller_quantities
            .get(&(name.clone(), arguments.clone()))
            .cloned();
        let prior_count_for_transition = tracked_prior.clone().or_else(|| visible_prior.clone());
        let new_count = if let Some((required, ensured)) = required_quantity
            .as_const()
            .zip(ensured_quantity.as_const())
        {
            let prior = tracked_prior.clone().or_else(|| visible_prior.clone());
            if let Some(prior) = prior {
                if ensured >= required {
                    Bitvector32Term::add(prior, Bitvector32Term::Constant(ensured - required))
                } else {
                    Bitvector32Term::subtract(prior, Bitvector32Term::Constant(required - ensured))
                }
            } else if required > 0 || ensured > 0 {
                Bitvector32Term::Constant(ensured)
            } else {
                return Ok(Err(CRuntimeError::FunctionContract(format!(
                    "counted population `{name}` is not initialized"
                ))));
            }
        } else {
            let prior_count = match tracked_prior.or(visible_prior) {
                Some(prior_count) => prior_count,
                None if population_quantity_is_zero(&required_quantity, assumptions) => {
                    Bitvector32Term::Constant(0)
                }
                None => {
                    return Ok(Err(CRuntimeError::FunctionContract(format!(
                        "counted population `{name}` is not initialized"
                    ))));
                }
            };
            // Replacing the entire visible population is the common symbolic
            // contract case. Preserve the ensured quantity directly instead
            // of asking later checks to rediscover cancellation.
            if population_quantities_are_equal(&prior_count, &required_quantity, assumptions) {
                ensured_quantity.clone()
            } else {
                Bitvector32Term::add(
                    Bitvector32Term::subtract(prior_count, required_quantity.clone()),
                    ensured_quantity.clone(),
                )
            }
        };
        let population_was_initialized =
            caller_state.counted_population(&name, &arguments).is_some()
                || caller_quantities
                    .get(&(name.clone(), arguments.clone()))
                    .is_some_and(|quantity| population_quantity_is_positive(quantity, assumptions))
                || population_quantity_is_positive(&required_quantity, assumptions);
        let population_ends = consumes_entire_population
            || bitvector_terms_proven_equal_for_memory_resolution(
                &new_count,
                &Bitvector32Term::Constant(0),
                assumptions,
            )
            || quantity_condition_holds(
                assumptions,
                ConditionTerm::Bitvector32Equal(
                    Box::new(new_count.clone()),
                    Box::new(Bitvector32Term::Constant(0)),
                ),
            );
        if population_was_initialized && population_ends {
            *post_state = post_state
                .clone()
                .without_counted_population(&name, &arguments);
            if population_body_definition.is_some() {
                let singleton = ResourceContext::new().unchecked_with_fact(CResourceFact::own(
                    CResource::Composite {
                        name: name.clone(),
                        arguments: arguments.clone(),
                    },
                ));
                let finalized = match evaluate_resource_population_body_resources(
                    &singleton,
                    &entry_state,
                    interface.composite_resource_definitions(),
                    assumptions,
                    budget,
                    true,
                )? {
                    Ok(resources) => resources,
                    Err(error) => return Ok(Err(error)),
                };
                transition
                    .finalized_body_resources
                    .extend(finalized.facts().iter().cloned());
            }
        } else {
            *post_state = post_state.clone().with_counted_population(
                name.clone(),
                arguments.clone(),
                new_count.clone(),
            );
            // A visible ensured unit witnesses nonemptiness. The transition
            // preserves the population cardinality invariant algebraically:
            // entry count >= required units, then both sides change by the
            // same net contract quantity. Only a population with no locally
            // returned unit needs an explicit proof that unseen units remain.
            if population_quantity_is_zero(&ensured_quantity, assumptions)
                && declared_population_definition
                    .is_none_or(population_body_requires_positive_witness)
            {
                transition.postcondition_obligations.push(
                    ProofObligation::verification_condition(Proposition::ConditionIs(
                        ConditionTerm::Bitvector32Equal(
                            Box::new(new_count),
                            Box::new(Bitvector32Term::Constant(0)),
                        ),
                        false,
                    ))
                    .with_context("resource population remains nonempty"),
                );
            } else {
                // Entry count covers every required unit, and the logical
                // count and returned quantity change by the same contract
                // delta. A returned unit therefore witnesses nonemptiness
                // without another arithmetic proof obligation.
                let guaranteed = Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedGreaterEqual(
                        Box::new(new_count.clone()),
                        Box::new(ensured_quantity.clone()),
                    ),
                    true,
                );
                if let (Some(new_count), Some(ensured_count)) =
                    (new_count.as_const(), ensured_quantity.as_const())
                    && (new_count as i32) < (ensured_count as i32)
                {
                    return Ok(Err(CRuntimeError::FunctionContract(format!(
                        "invalid counted population transition for `{name}`: post-count {new_count} is below returned quantity {ensured_count}"
                    ))));
                }
                let residual_is_certified_nonnegative =
                    population_quantity_is_zero(&ensured_quantity, assumptions)
                        && prior_count_for_transition.as_ref().is_some_and(|prior| {
                            new_count
                                == Bitvector32Term::subtract(
                                    prior.clone(),
                                    required_quantity.clone(),
                                )
                                && quantity_condition_holds(
                                    assumptions,
                                    ConditionTerm::Bitvector32SignedGreaterEqual(
                                        Box::new(required_quantity.clone()),
                                        Box::new(Bitvector32Term::Constant(0)),
                                    ),
                                )
                                && quantity_condition_holds(
                                    assumptions,
                                    ConditionTerm::Bitvector32SignedLessEqual(
                                        Box::new(required_quantity.clone()),
                                        Box::new(prior.clone()),
                                    ),
                                )
                        });
                if residual_is_certified_nonnegative
                    || quantity_condition_holds(
                        assumptions,
                        ConditionTerm::Bitvector32SignedGreaterEqual(
                            Box::new(new_count.clone()),
                            Box::new(ensured_quantity.clone()),
                        ),
                    )
                {
                    transition_guaranteed_facts.push(guaranteed);
                } else {
                    transition.postcondition_obligations.push(
                        ProofObligation::verification_condition(guaranteed)
                            .with_context("returned resource quantity fits post-population"),
                    );
                }
            }
        }
    }

    if !reestablish_invariants {
        return Ok(Ok(transition));
    }

    // Re-establish every active counted population's declared invariant at
    // the post-contract snapshot. The transition changes the logical count;
    // a body fact relating that count to C memory is therefore a genuine
    // verification condition, not an automatically assumed consequence.
    let post_contract_state =
        with_contract_interface_argument_views(post_state, interface, argument_values);
    let mut active_populations = Vec::new();
    for population in post_contract_state.counted_populations() {
        if population_quantity_is_zero(&population.count, assumptions) {
            continue;
        }
        let population_body =
            interface
                .composite_resource_definitions()
                .iter()
                .find(|definition| {
                    definition.name() == population.name
                        && definition_has_population_wide_body(definition)
                });
        let Some(population_body) = population_body else {
            continue;
        };
        if !population_body_requires_positive_witness(population_body) {
            continue;
        }
        if !population_quantity_is_positive(&population.count, assumptions) {
            transition.postcondition_obligations.push(
                ProofObligation::verification_condition(Proposition::ConditionIs(
                    ConditionTerm::Bitvector32Equal(
                        Box::new(population.count.clone()),
                        Box::new(Bitvector32Term::Constant(0)),
                    ),
                    false,
                ))
                .with_context("resource population body is active"),
            );
        }
        active_populations.push(CResourceFact::own(CResource::Composite {
            name: population.name.clone(),
            arguments: population.arguments.clone(),
        }));
    }
    let active_populations = ResourceContext::new().unchecked_with_facts(active_populations);
    let Some(population_facts) = evaluate_resource_population_fact_propositions(
        &active_populations,
        interface.composite_resource_definitions(),
        &post_contract_state,
        &PureFactContext::new(),
        true,
    ) else {
        return Ok(Err(CRuntimeError::FunctionContract(
            "could not evaluate resource population postcondition".to_string(),
        )));
    };
    for proposition in population_facts {
        if let Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedGreaterEqual(left, right),
            true,
        ) = &proposition
            && let (Some(left), Some(right)) = (left.as_const(), right.as_const())
            && (left as i32) < (right as i32)
        {
            return Ok(Err(CRuntimeError::FunctionContract(format!(
                "invalid population fact: post-count {left} is below visible quantity {right}"
            ))));
        }
        transition.population_facts.push(proposition.clone());
        // The transition's own algebraic guarantee, then the retained exact
        // routes. Anything else is a genuine verification condition for a
        // Surface tactic, not something for lowering to prove here.
        if !transition_guaranteed_facts.contains(&proposition) {
            add_required_proof_obligation_with_context(
                &mut transition.postcondition_obligations,
                assumptions,
                proposition,
                Some("resource population invariant"),
                None,
            );
        }
    }
    Ok(Ok(transition))
}

fn resource_fact_composite_head(fact: &CResourceFact) -> Option<(bool, &str)> {
    let CResource::Composite { name, .. } = fact.resource() else {
        return None;
    };
    Some((fact.is_own(), name))
}

pub(super) fn prepare_function_contract_entry_state_with_values(
    caller_state: &CState,
    function: &CFunction,
    argument_values: &[CValue],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<CState, CRuntimeError>> {
    let Some(callee_state) = bind_c_function_arguments(caller_state, function, argument_values)
    else {
        return Ok(Err(CRuntimeError::FunctionContract(format!(
            "could not bind contract-entry arguments for {}",
            function.name()
        ))));
    };
    let transfer = match crate::instrumentation::measure_operation(
        function.name(),
        "contract resource transition",
        "contract resource transfer preparation",
        || {
            prepare_contract_resource_transfer(
                caller_state,
                &callee_state,
                function.name(),
                function.contract_interface(),
                assumptions,
                budget,
                true,
                ResourceTransitionPurpose::FunctionBoundary,
            )
        },
    )? {
        Ok(transfer) => transfer,
        Err(error) => return Ok(Err(error)),
    };
    Ok(Ok(callee_state_with_resource_transfer(
        callee_state,
        &transfer,
    )))
}

/// Binds a composite definition's existential witnesses as locals of the
/// body-evaluation state, after its parameters. A witness related to a word
/// by a `where` fact of the shape `word == address(witness) + tag` is bound
/// to that word's recorded origin, so folding and unfolding the same body
/// agree on it; a witness with no recorded origin yet (an unfold whose facts
/// are about to introduce it) is bound to a fresh symbolic pointer chosen
/// deterministically from the variables already in use.
pub(super) fn bind_composite_witnesses(
    definition: &CCompositeResourceDefinition,
    arguments: &[AlgebraicValue],
    state: &mut CState,
    assumptions: &PureFactContext,
) -> Option<Vec<CValue>> {
    let held = state.resources.clone();
    bind_composite_witnesses_with_held(definition, arguments, state, &held, assumptions)
}

/// [`bind_composite_witnesses`] with the held resource facts supplied
/// separately, for callers whose evaluation state carries no resources.
pub(super) fn bind_composite_witnesses_with_held(
    definition: &CCompositeResourceDefinition,
    arguments: &[AlgebraicValue],
    state: &mut CState,
    held: &ResourceContext,
    assumptions: &PureFactContext,
) -> Option<Vec<CValue>> {
    if definition.witnesses().is_empty() {
        return Some(Vec::new());
    }
    let mut values = Vec::new();
    for (index, witness) in definition.witnesses().iter().enumerate() {
        let word = definition
            .facts()
            .iter()
            .find_map(|fact| witness_origin_word(fact, witness.name()))
            .and_then(|word| {
                let mut budget = ExecutionBudget::beside_live_state();
                let paths = super::spec::evaluate_spec_expression_paths_with_loop_entry(
                    state,
                    word,
                    None,
                    assumptions,
                    &mut budget,
                )
                .ok()?;
                let [path] = paths.as_slice() else {
                    return None;
                };
                match &path.value {
                    CValue::UInt64(term) | CValue::Int64(term) => Some(term.clone()),
                    _ => None,
                }
            });
        let origin = word
            .as_ref()
            .and_then(|term| {
                if term.uint64_as_const() == Some(0) {
                    return Some(Pointer::null());
                }
                let mut used = super::eval::pointer_tags::UsedFacts::new();
                super::eval::pointer_tags::tagged_address_form(term, assumptions, &mut used)
                    .map(|form| form.pointer)
            })
            // A body that contains a composite resource under the witness
            // names it through the resource context: when exactly one held
            // fact of that composite exists, its argument is the witness a
            // fold consumes. This is the fold's own obligation read back,
            // not a search.
            .or_else(|| {
                held_child_witness(definition, witness.name(), arguments, held, assumptions)
            });
        // A witness with no recorded origin is named by the content of the
        // instance that introduces it: the definition, the witness position,
        // the argument values, and the word's own value term. The word term
        // survives materializing the body's cells, which store that same
        // symbolic load, and changes when the word is stored, so every site
        // that instantiates the same body at the same word names the same
        // pointer while a later store names another.
        let pointer = origin.unwrap_or_else(|| {
            use std::hash::{Hash, Hasher};
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            definition.name().hash(&mut hasher);
            index.hash(&mut hasher);
            arguments.hash(&mut hasher);
            // The canonical form names a load by its cell rather than by
            // the snapshot it was read from, so the key is the same before
            // and after the body's cells are materialized.
            word.as_ref()
                .map(super::eval::canonical_term)
                .hash(&mut hasher);
            Pointer::symbolic(Variable(4_000_000_000 + hasher.finish() % 4_000_000_000))
        });
        let value = CValue::typed_pointer(pointer, witness.c_type());
        state
            .locals
            .set_typed(witness.name().to_string(), value.clone(), witness.c_type());
        values.push(value);
    }
    Some(values)
}

/// The unique held composite fact that a `contains name(witness)` clause of
/// the body would consume, if the body has such a clause and exactly one
/// held fact of that composite exists.
fn held_child_witness(
    definition: &CCompositeResourceDefinition,
    witness: &str,
    arguments: &[AlgebraicValue],
    resources: &ResourceContext,
    assumptions: &PureFactContext,
) -> Option<Pointer> {
    // The body's own instance is never its own child.
    let own_pointers = arguments
        .iter()
        .filter_map(|argument| match argument {
            AlgebraicValue::C(CValue::Pointer(pointer)) => Some(pointer.pointer().clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    let child_name = definition.contains().iter().find_map(|spec| {
        let arguments = spec.declared_arguments()?;
        (spec.family() == ResourceFamily::Composite
            && matches!(arguments, [CExpression::Variable(argument)] if argument == witness))
        .then(|| spec.declared_name().expect("composite spec has a name"))
    })?;
    let mut candidates = resources
        .facts()
        .iter()
        .filter_map(|fact| match fact.resource() {
            CResource::Composite { name, arguments } if name == child_name => {
                match arguments.as_ref() {
                    [AlgebraicValue::C(CValue::Pointer(pointer))] => {
                        Some(pointer.pointer().clone())
                    }
                    _ => None,
                }
            }
            _ => None,
        })
        // A candidate in the block of one of the body's own pointers must be
        // proven a different pointer.
        .filter(|pointer| {
            own_pointers.iter().all(|own| {
                own.block != pointer.block
                    || assumptions
                        .decide(&ConditionTerm::pointer_equal(pointer.clone(), own.clone()))
                        == Some(false)
            })
        });
    let first = candidates.next()?;
    candidates.all(|other| other == first).then_some(first)
}

/// The word a `where` fact relates `witness` to: for `E == address(witness)`
/// or `E == address(witness) + t` (either operand order, under `and`), the
/// expression `E`.
fn witness_origin_word<'a>(fact: &'a SpecProposition, witness: &str) -> Option<&'a SpecExpression> {
    fn mentions_witness_address(expression: &SpecExpression, witness: &str) -> bool {
        match expression {
            SpecExpression::CExpression(CExpression::Cast {
                expression,
                target_type: CType::UInt64 | CType::Int64,
                ..
            }) => matches!(expression.as_ref(), CExpression::Variable(name) if name == witness),
            SpecExpression::Add(left, right) => {
                mentions_witness_address(left, witness) || mentions_witness_address(right, witness)
            }
            _ => false,
        }
    }
    match fact {
        SpecProposition::And(left, right) => {
            witness_origin_word(left, witness).or_else(|| witness_origin_word(right, witness))
        }
        SpecProposition::Comparison {
            left,
            operator: CComparisonOperator::Equal,
            right,
        } => {
            if mentions_witness_address(right, witness) {
                Some(left)
            } else if mentions_witness_address(left, witness) {
                Some(right)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Why a fold or unfold was refused. Most refusals are one fixed sentence;
/// the body-fact refusal names which fact of which arm the fold could not
/// establish, since "the body facts" of a five-fact arm sends the author to
/// read all five. The static sentence is still available to callers whose
/// own error is a static string.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResourceRewriteRefusal {
    Message(&'static str),
    /// `fold` could not establish body fact `index` (zero-based, in
    /// declaration order) of the `count` facts in `arm`, or of the
    /// definition's own facts when `arm` is `None`.
    BodyFactNotEstablished {
        arm: Option<String>,
        index: usize,
        count: usize,
    },
}

impl ResourceRewriteRefusal {
    pub fn describe(&self) -> String {
        match self {
            ResourceRewriteRefusal::Message(message) => (*message).to_string(),
            ResourceRewriteRefusal::BodyFactNotEstablished { arm, index, count } => {
                let place = match arm {
                    Some(arm) => format!("of arm `{arm}`"),
                    None => "of the resource body".to_string(),
                };
                format!(
                    "fold requires the instance body facts for the proposed fields: fact {} of {count} {place} is not established",
                    index + 1
                )
            }
        }
    }
}

impl From<&'static str> for ResourceRewriteRefusal {
    fn from(message: &'static str) -> Self {
        ResourceRewriteRefusal::Message(message)
    }
}

impl From<ResourceRewriteRefusal> for &'static str {
    fn from(refusal: ResourceRewriteRefusal) -> Self {
        match refusal {
            ResourceRewriteRefusal::Message(message) => message,
            ResourceRewriteRefusal::BodyFactNotEstablished { .. } => {
                "fold requires the instance body facts for the proposed fields"
            }
        }
    }
}

/// A declaration-level consequence of a selected resource body. This is not
/// a fact-store delta: a clause remains here when its proposition was already
/// known, so presentation can retain its exact binder and source ordinal.
#[derive(Clone, Debug)]
pub(crate) struct ResourceBodyClauseRecord {
    pub(crate) arm: Option<String>,
    pub(crate) ordinal: usize,
    pub(crate) proposition: Proposition,
    pub(crate) introductions: LoweringIntroductions,
}

#[derive(Clone, Debug)]
pub(crate) struct ResourceInstanceRewriteResult {
    pub(crate) state: CState,
    pub(crate) semantic_facts: Vec<Proposition>,
    pub(crate) body_clauses: Vec<ResourceBodyClauseRecord>,
}

/// Whether an undischarged proposition only says that an arithmetic
/// evaluation does not hit undefined behavior (for example, `x + 2` cannot
/// overflow). Unfold exposes such conditions alongside the body fact instead
/// of refusing; anything else keeps the generic conditional-proof
/// diagnostic.
fn is_pure_undefined_behavior_condition(proposition: &Proposition) -> bool {
    let Proposition::ConditionIs(condition, false) = proposition else {
        return false;
    };
    matches!(
        condition,
        ConditionTerm::Bitvector32SignedAddOverflows(..)
            | ConditionTerm::Bitvector32SignedSubtractOverflows(..)
            | ConditionTerm::Bitvector32SignedMultiplyOverflows(..)
            | ConditionTerm::Bitvector32SignedDivideOverflows(..)
            | ConditionTerm::Bitvector32SignedShiftLeftOverflows(..)
            | ConditionTerm::Bitvector64SignedAddOverflows(..)
            | ConditionTerm::Bitvector64SignedSubtractOverflows(..)
            | ConditionTerm::Bitvector64SignedMultiplyOverflows(..)
            | ConditionTerm::Bitvector64SignedDivideOverflows(..)
            | ConditionTerm::Bitvector64SignedShiftLeftOverflows(..)
    )
}

/// Lower one selected body in source order. A body clause is available to a
/// later clause only after the selected resource justified it (unfold/match),
/// or after the fold's existing facts established it. Routing facts for a
/// conditional lowering must be stated in this exact accumulated context;
/// other paths being impossible is not itself evidence for a survivor.
#[allow(clippy::too_many_arguments)]
fn lower_selected_resource_body_clauses(
    evaluation: &CState,
    source: &[SpecProposition],
    arm: Option<&str>,
    integer_bindings: &BTreeMap<Variable, IntegerTerm>,
    algebraic_bindings: &BTreeMap<String, AlgebraicTerm>,
    body_assumptions: &PureFactContext,
    established_assumptions: Option<&PureFactContext>,
    budget: &mut ExecutionBudget,
) -> Result<(Vec<ResourceBodyClauseRecord>, Vec<Proposition>), ResourceRewriteRefusal> {
    let c_replacements = BTreeMap::new();
    let algebraic_replacements = BTreeMap::new();
    let mut rewrite = crate::kernel::proof::term_rewrite::TermRewrite::for_checked_typed_variables(
        &c_replacements,
        integer_bindings,
        &algebraic_replacements,
    );
    rewrite.enable_registered_load_resolution();
    rewrite
        .reserve_spec_proposition_sources(source.iter())
        .map_err(|_| "resource match Integer binding substitution exceeded its checked scope")?;
    let mut context = body_assumptions.clone();
    let mut records = Vec::with_capacity(source.len());
    let mut retained_conditions = Vec::new();
    for (ordinal, clause) in source.iter().enumerate() {
        crate::instrumentation::record_deterministic_work(1);
        let clause = rewrite.spec_proposition(clause).map_err(
            |_| "resource match Integer binding substitution exceeded its checked scope",
        )?;
        let paths = crate::kernel::spec::lower_spec_proposition_at_state_with_algebraic_bindings(
            evaluation,
            &clause,
            None,
            &context,
            algebraic_bindings,
            budget,
        )
        .map_err(|_| "could not evaluate instance body fact")?;
        let path = crate::kernel::api::exactly_selected_spec_proposition_path(&paths, &context)
            .ok_or("instance body fact needs an unsupported conditional proof")?;
        // An undischarged pure undefined-behavior condition (unchecked
        // arithmetic) is exposed alongside the body fact instead of
        // refusing the rewrite: the author asserted the C meaning, which
        // includes definedness, and every later use re-checks it. Anything
        // else still refuses as before.
        let retained_start = retained_conditions.len();
        for fact in &path.facts {
            if required_obligation_is_exactly_discharged(&context, fact.proposition()) {
                continue;
            }
            if is_pure_undefined_behavior_condition(fact.proposition()) {
                retained_conditions.push(fact.proposition().clone());
                continue;
            }
            return Err("instance body fact needs an unsupported conditional proof".into());
        }
        for goal in &path.obligations {
            if required_obligation_is_exactly_discharged(&context, goal.proposition())
                || quantified_resource_fact_memory_obligation_is_discharged(
                    &context,
                    goal.proposition(),
                )
            {
                continue;
            }
            if is_pure_undefined_behavior_condition(goal.proposition()) {
                retained_conditions.push(goal.proposition().clone());
                continue;
            }
            return Err("instance body fact needs an unsupported conditional proof".into());
        }
        for condition in &retained_conditions[retained_start..] {
            context = context.assume_proposition(condition.clone());
        }
        if let Some(established) = established_assumptions
            && !resource_body_fact_is_established(established, &path.proposition)
        {
            return Err(ResourceRewriteRefusal::BodyFactNotEstablished {
                arm: arm.map(str::to_owned),
                index: ordinal,
                count: source.len(),
            });
        }
        let record = ResourceBodyClauseRecord {
            arm: arm.map(str::to_owned),
            ordinal,
            proposition: path.proposition.clone(),
            introductions: path.introductions.clone(),
        };
        context = context.assume_proposition(path.proposition.clone());
        records.push(record);
    }
    Ok((records, retained_conditions))
}

/// A fold body fact may name a memory load from before a disjoint call while
/// the selected body is lowered against the post-call frame. Exact discharge
/// remains the normal route; the checked pointer-load transport is the
/// narrowly-scoped fallback for this explicit resource clause. This keeps
/// call/frame transport out of the general fact path while still allowing a
/// resource fold to reuse a load whose stored pointer value the checked
/// memory derivation proves unchanged.
fn resource_body_fact_is_established(
    established: &PureFactContext,
    proposition: &Proposition,
) -> bool {
    if required_obligation_is_exactly_discharged(established, proposition) {
        return true;
    }
    matches!(
        proposition,
        Proposition::ConditionIs(
            ConditionTerm::PointerOffsetEqual(left, right),
            true,
        ) if crate::kernel::memory_provenance::pointer_load_offset_proven_equal(
            left,
            right,
            established,
        )
    )
}

/// Exchange one exclusive instance for its immediate memory body, or back.
/// Memory-only bodies need no open token, including guarded/matched bodies.
/// Recursive children require explicit independent child selections.
#[cfg(test)]
pub(crate) fn rewrite_resource_instance(
    state: &CState,
    instance: &ResourceInstance,
    definition: &CCompositeResourceDefinition,
    assumptions: &PureFactContext,
    unfold: bool,
) -> Result<(CState, Vec<Proposition>), ResourceRewriteRefusal> {
    let result = rewrite_resource_instance_selecting_children(
        state,
        instance,
        definition,
        std::slice::from_ref(definition),
        assumptions,
        unfold,
        None,
    )?;
    Ok((result.state, result.semantic_facts))
}

/// The composite definition a matched arm's child names. A child of the
/// parent's own family resolves to the definition already in hand; any other
/// declared resource is looked up in the registered definitions, so the
/// child's own parameters and fields decide what the rewrite checks.
pub(in crate::kernel) fn child_composite_definition<'a>(
    definition: &'a CCompositeResourceDefinition,
    definitions: &'a [CCompositeResourceDefinition],
    child: &CResourceChildSpec,
) -> Result<&'a CCompositeResourceDefinition, &'static str> {
    if child.resource == definition.name() {
        return Ok(definition);
    }
    definitions
        .binary_search_by(|candidate| candidate.name().cmp(&child.resource))
        .ok()
        .map(|index| &definitions[index])
        .ok_or("resource match child has no registered definition")
}

/// The order that decides which of two equal spellings an arm is instantiated
/// at. A block the program allocated or was handed is preferred over a
/// symbolic one, and two symbolic blocks are ordered by their identities,
/// which are minted in creation order: a binding introduced at the current
/// frontier is newer than the havocked local or parameter a proof equates it
/// with. The order is total and the choice is always the smaller element, so
/// two spellings collapse to the same one whichever side the query starts
/// from, and a spelling the program already uses is never traded away for a
/// proof name.
fn pointer_spelling_rank(pointer: &Pointer) -> (bool, &Pointer) {
    (matches!(pointer.block, PointerBlock::Symbolic(_)), pointer)
}

/// The spelling a matched arm's pointer binding denotes.
///
/// A binding introduced by a proof `match` is a fresh symbolic pointer: it
/// names the node the model says the arm holds, and no C statement is written
/// through it. When an exact pointer equality identifies it with an older
/// pointer -- the local an ascending walk reassigns, a parameter, a witness --
/// the two are one address, and the program reads and writes that address
/// under its own spelling. Instantiating the arm's clauses at the binding's
/// symbolic spelling therefore owns, names, and requires cells the C can never
/// reach: the read is refused with `missing resource fact views
/// symbolic-pointer:...` while ownership of that very cell is held one
/// provable equality away.
///
/// Declared resource identity already respects proved equality of a
/// resource's arguments -- ownership of `list(node->next)` is ownership of
/// `list(tail)` once `node->next == tail` is proved. This is that rule for the
/// ownership a matched arm introduces *through a binding*: the arm's clauses
/// are instantiated at a provably equal pointer, so the body they state is the
/// same body, and every cell, fact, and child argument in it lands on the
/// address the program names. A fold requires the body at the same spelling,
/// which is what lets a walk hand its instance back.
///
/// Soundness rests on the equality being exact and on it being a genuine
/// cross-block one. `exact_pointer_aliases` reads the index of assumed
/// `PointerEqual` facts: never a derived, heuristic, or disjunctive
/// conclusion, and never a `!=`. An equality between two offsets of one block
/// is not a `PointerEqual` at all -- `ConditionTerm::pointer_equal` folds it
/// to a `PointerOffsetEqual` -- so an entry can only ever exchange two
/// spellings of one address, at the offset the fact states and no other. Which
/// equal spelling is chosen changes nothing logically, since they are all the
/// same address; `pointer_spelling_rank` fixes it so that the choice is
/// deterministic, directed at the older spelling, and stable in the
/// certificate. Boundedness: one keyed lookup per pointer binding, one hop, no
/// transitive closure and no fact-set scan.
pub(crate) fn arm_binding_program_spelling(
    value: &CValue,
    assumptions: &PureFactContext,
) -> Option<CValue> {
    let CValue::Pointer(value_pointer) = value else {
        return None;
    };
    let pointer = value_pointer.pointer();
    if !matches!(pointer.block, PointerBlock::Symbolic(_)) {
        return None;
    }
    crate::instrumentation::record_deterministic_work(1);
    let spelling = assumptions
        .exact_pointer_aliases(pointer)
        .filter(|alias| pointer_spelling_rank(alias) < pointer_spelling_rank(pointer))
        .min_by_key(|alias| pointer_spelling_rank(alias))?;
    let mut aliased = value_pointer.clone();
    aliased.replace_pointer(spelling.clone());
    Some(CValue::Pointer(aliased))
}

pub(crate) fn rewrite_resource_instance_selecting_children(
    state: &CState,
    instance: &ResourceInstance,
    definition: &CCompositeResourceDefinition,
    definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
    unfold: bool,
    selected_children: Option<&[(String, Variable)]>,
) -> Result<ResourceInstanceRewriteResult, ResourceRewriteRefusal> {
    if definition.name() != instance.name()
        || definition.instance_schema.as_ref() != Some(instance.schema())
        || definition.recursive
        || definition.counted_population
        || !definition.witnesses.is_empty()
        || definition.parameters.len() != instance.arguments.len()
        || instance
            .arguments
            .iter()
            .zip(&definition.parameters)
            .any(|(argument, parameter)| {
                argument
                    .as_c_value()
                    .is_none_or(|value| value.c_type() != parameter.c_type())
            })
        || definition
            .contains
            .iter()
            .any(|body| body.family() != ResourceFamily::Memory || body.is_view())
    {
        return Err(
            "instance fold/unfold requires a nonrecursive, witness-free memory body".into(),
        );
    }
    let folded_instance = instance.clone();
    let folded = CResourceFact::own(CResource::Instance(folded_instance.clone()));
    if unfold {
        if state.resources.owned_instance(instance.identity) != Some(instance) {
            return Err("instance is not exclusively owned in folded form".into());
        }
    } else if state.resources.owned_instance(instance.identity).is_some() {
        return Err("fold result identity is already in use".into());
    }
    let mut evaluation = instance_body_evaluation(state, instance, definition)?;
    let mut budget = ExecutionBudget::beside_live_state();
    let mut algebraic_bindings = BTreeMap::new();
    let mut integer_bindings = BTreeMap::new();
    let mut constructor_fields = Vec::new();
    // D7 in reverse, at the point of the fold or unfold and against the
    // premises standing there. A loop body that has moved its cursor knows
    // what a child it unfolded earlier is only now, and the arm this rewrite
    // needs is the one those premises leave (A26, gap 57b). The work is this
    // one instance's own arms.
    let instance_refutations = if definition.matched.is_some() {
        instance_arm_model_facts(instance, definitions, state, assumptions)
    } else {
        Vec::new()
    };
    let selected = if definition.matched.is_some() {
        let selection_assumptions = instance_refutations
            .iter()
            .cloned()
            .fold(assumptions.clone(), PureFactContext::assume_proposition);
        let (arm, constructor) =
            selected_instance_match_arm(instance, definition, definitions, &selection_assumptions)?;
        let AlgebraicTermNode::Constructor { fields, .. } = constructor.node else {
            unreachable!()
        };
        constructor_fields = fields.clone();
        for (index, value) in fields.iter().enumerate() {
            let name = arm
                .bindings
                .get(index)
                .ok_or("resource match binding count mismatch")?;
            let binding_type = arm
                .binding_types
                .get(index)
                .ok_or("resource match binding type count mismatch")?;
            let binding_variable = arm
                .binding_variables
                .get(index)
                .ok_or("resource match Integer binding identity count mismatch")?;
            match (binding_type, binding_variable, value) {
                (AlgebraicValueType::C(_), None, AlgebraicValue::C(value)) => {
                    let ty = value.c_type();
                    // A pointer payload an exact equality identifies with a C
                    // pointer denotes that pointer, so the arm's cells are
                    // owned, named, and required at the spelling the C
                    // statements read (see `arm_binding_program_spelling`).
                    let value = arm_binding_program_spelling(value, assumptions)
                        .unwrap_or_else(|| value.clone());
                    evaluation.locals.set_typed(name.clone(), value, ty);
                }
                (AlgebraicValueType::Integer, Some(variable), AlgebraicValue::Integer(value)) => {
                    if integer_bindings.insert(*variable, value.clone()).is_some() {
                        return Err("resource match Integer bindings reuse an identity".into());
                    }
                }
                (AlgebraicValueType::Algebraic { .. }, None, AlgebraicValue::Algebraic(value)) => {
                    algebraic_bindings.insert(name.clone(), value.clone());
                }
                _ => return Err("resource match constructor binding type mismatch".into()),
            }
        }
        Some(arm)
    } else {
        None
    };
    let active = evaluate_composite_resource_body_condition(
        definition,
        &evaluation,
        assumptions,
        &mut budget,
    )
    .ok_or("instance fold/unfold requires a proved body guard case")?;
    let explicit_children = selected_children.map(|children| {
        children
            .iter()
            .map(|(name, identity)| (name.as_str(), *identity))
            .collect::<BTreeMap<_, _>>()
    });
    if explicit_children.is_none() && selected.is_some_and(|arm| !arm.children.is_empty()) {
        return Err("recursive children require explicit independent child selections".into());
    }
    if let Some(children) = &explicit_children {
        let supplied = selected_children.unwrap();
        let expected = selected.map_or(&[][..], |arm| arm.children.as_slice());
        let identities = supplied
            .iter()
            .map(|(_, identity)| *identity)
            .collect::<BTreeSet<_>>();
        if children.len() != supplied.len()
            || identities.len() != supplied.len()
            || identities.contains(&instance.identity)
            || children.len() != expected.len()
            || expected
                .iter()
                .any(|child| !children.contains_key(child.name.as_str()))
        {
            return Err("child selection must name every selected arm child exactly once".into());
        }
    }
    let mut body = evaluate_function_resource_context_with_normalization(
        &evaluation,
        if active {
            selected.map_or(&definition.contains, |arm| &arm.contains)
        } else {
            &[]
        },
        // A resource body is rewritten against its own declared memory only;
        // expanding a contained composite here would hand the body read
        // authority it has not opened.
        &[],
        assumptions,
        &mut budget,
        false,
    )
    .map_err(|_| "instance body evaluation exceeded its budget")?
    .map(|(context, _)| context)
    .map_err(|_| "could not evaluate instance memory body")?;
    // Only the immediate declared memory justifies child-argument loads, not
    // the ambient frame or a child that has not been constructed. On fold,
    // check and consume that memory before allowing it in this scratch view.
    let mut next = state.clone();
    if !unfold {
        for fact in body.facts() {
            next.resources = next
                .resources
                .without_fact_incrementally(fact, assumptions)
                .ok_or("fold requires ownership of the complete instance body")?;
        }
    }
    let mut child_evaluation = evaluation.clone();
    child_evaluation.resources = body.clone();
    let child_assumptions = assumptions.clone().require_owned_expression_loads();
    let mut resource_bindings = BTreeMap::from([(Variable(u64::MAX), instance.identity)]);
    let mut introduced_children: Vec<ResourceInstance> = Vec::new();
    for child in selected.into_iter().flat_map(|arm| &arm.children) {
        crate::instrumentation::record_deterministic_work(1);
        // The child's own definition supplies the parameter types its
        // arguments are coerced to and the schema its fields must satisfy.
        let child_definition = child_composite_definition(definition, definitions, child)?;
        let child_schema = if child_definition.name() == definition.name() {
            instance.schema.clone()
        } else {
            child_definition
                .instance_schema
                .clone()
                .ok_or("resource match child requires a field-bearing definition")?
        };
        let arguments = child
            .arguments
            .iter()
            .zip(&child_definition.parameters)
            .map(|(argument, parameter)| {
                let paths = evaluate_c_expression_paths(
                    &child_evaluation,
                    argument,
                    &child_assumptions,
                    &mut budget,
                )
                .map_err(|_| "recursive child argument evaluation exceeded its budget")?;
                // A child argument is a prerequisite of the rewrite, not a
                // proof site: it has no obligation vector to receive an
                // unmet condition. Restrict it to the retained exact routes
                // and refuse the rewrite otherwise, which is the
                // conservative equivalent of emitting the obligation.
                if paths.len() != 1
                    || paths[0].facts.iter().any(|fact| {
                        !required_obligation_is_exactly_discharged(
                            &child_assumptions,
                            fact.proposition(),
                        )
                    })
                    || paths[0].obligations.iter().any(|goal| {
                        !required_obligation_is_exactly_discharged(
                            &child_assumptions,
                            goal.proposition(),
                        )
                    })
                {
                    return Err("recursive child argument requires a proved, readable expression");
                }
                match &paths[0].outcome {
                    CExpressionOutcome::Value(value) => {
                        coerce_c_function_argument_without_obligations(value, parameter)
                            .map(AlgebraicValue::C)
                            .ok_or("recursive child argument type mismatch")
                    }
                    _ => Err("could not evaluate recursive child argument"),
                }
            })
            .collect::<Result<ResourceArguments, _>>()?;
        let fields = child
            .field_bindings
            .iter()
            .map(|index| {
                constructor_fields
                    .get(*index)
                    .cloned()
                    .ok_or("invalid child field binding")
            })
            .collect::<Result<ResourceArguments, _>>()?;
        let identity =
            explicit_children.as_ref().expect("checked child selection")[child.name.as_str()];
        if unfold && state.resources.owned_instance(identity).is_some() {
            return Err("unfold child result identity is already in use".into());
        }
        let mut child_instance = ResourceInstance::new(
            identity,
            child_definition.name().to_string(),
            arguments,
            child_schema,
            fields,
        )
        .ok_or("recursive child fields or arguments have invalid types")?;
        if child_instance.arguments.len() != child_definition.parameters.len()
            || child_instance
                .arguments
                .iter()
                .zip(&child_definition.parameters)
                .any(|(argument, parameter)| {
                    argument
                        .as_c_value()
                        .is_none_or(|value| value.c_type() != parameter.c_type())
                })
        {
            return Err("recursive child arguments have invalid types".into());
        }
        if !unfold {
            let actual = state
                .resources
                .owned_instance(identity)
                .ok_or("fold requires an owned, folded child")?;
            if actual.name != child_instance.name
                || actual.schema != child_instance.schema
                || actual.arguments.len() != child_instance.arguments.len()
                || actual.fields.len() != child_instance.fields.len()
                || !actual
                    .arguments
                    .iter()
                    .zip(child_instance.arguments.iter())
                    .chain(actual.fields.iter().zip(child_instance.fields.iter()))
                    .all(|(a, b)| crate::kernel::resource_arguments_proven_equal(a, b, assumptions))
            {
                return Err("selected child does not satisfy the proposed parent model".into());
            }
            child_instance = actual.clone();
        }
        resource_bindings.insert(child.binding, identity);
        introduced_children.push(child_instance.clone());
        body = body
            .try_compose_into_valid_context_delaying_normalization(
                [CResourceFact::own(CResource::Instance(
                    child_instance.clone(),
                ))],
                assumptions,
            )
            .map_err(|_| "child ownership is duplicated")?;
    }
    if unfold {
        next.resources = next
            .resources
            .without_fact_delaying_normalization(&folded, assumptions)
            .ok_or("instance ownership is missing")?
            .try_compose_into_valid_context_delaying_normalization(
                body.facts().iter().cloned(),
                assumptions,
            )
            .map_err(|_| "instance body overlaps existing ownership")?;
    } else {
        // Immediate memory was consumed before evaluating child arguments.
        for fact in body
            .facts()
            .iter()
            .filter(|fact| fact.memory_range().is_none())
        {
            next.resources = next
                .resources
                .without_fact_incrementally(fact, assumptions)
                .ok_or("fold requires ownership of the complete instance body")?;
        }
        next.resources = next
            .resources
            .try_compose_into_valid_context_delaying_normalization([folded.clone()], assumptions)
            .map_err(|_| "fold would duplicate instance ownership")?;
    }
    evaluation.resources = if unfold {
        next.resources.clone()
    } else {
        state.resources.clone()
    };
    evaluation.resource_bindings = Some(std::sync::Arc::new(resource_bindings));
    let mut facts = body.observable_facts_assuming_valid(assumptions);
    for fact in body.facts() {
        let Some(range) = fact.memory_range() else {
            continue;
        };
        let width = range.element_width();
        facts.push(Proposition::CMemoryLoadable {
            memory: state.memory.clone(),
            base: range
                .base()
                .offset_by_elements(range.start().clone(), width),
            bytes: Bitvector32Term::multiply(
                Bitvector32Term::subtract(range.end().clone(), range.start().clone()),
                Bitvector32Term::Constant(width),
            ),
        });
    }
    facts.push(Proposition::CResourceComposition(body));
    let mut body_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads();
    for fact in &facts {
        body_assumptions = body_assumptions.assume_proposition(fact.clone());
    }
    let facts_to_rewrite = selected.map_or(&definition.facts, |arm| &arm.facts);
    let (body_clauses, retained_conditions) = if active {
        lower_selected_resource_body_clauses(
            &evaluation,
            facts_to_rewrite,
            selected.map(|arm| arm.variant.as_str()),
            &integer_bindings,
            &algebraic_bindings,
            &body_assumptions,
            (!unfold).then_some(assumptions),
            &mut budget,
        )?
    } else {
        (Vec::new(), Vec::new())
    };
    facts.extend(body_clauses.iter().map(|clause| clause.proposition.clone()));
    facts.extend(retained_conditions);
    if unfold {
        // The arm this unfold opened is the one the premises standing here
        // leave, so the model fact that forced it is published with the
        // body's own facts: the path, and every later step, then names the
        // constructor this rewrite used.
        facts.extend(instance_refutations);
        // A child instance is born here, so this is where the premises the
        // proof already carries first say something about its model: a guard
        // that refutes one of the child's arms (D7 in reverse) publishes the
        // model fact that refutation forces. A descending loop learns
        // `left.model != Empty` from `root->left != 0`, and the walk that
        // stops learns `left.model == Empty` from `root->left == 0`.
        for child in &introduced_children {
            facts.extend(instance_arm_model_facts(
                child,
                definitions,
                &next,
                assumptions,
            ));
        }
    }
    let mut seen = BTreeSet::new();
    let semantic_facts = if unfold {
        facts
            .into_iter()
            .filter(|fact| !assumptions.states_required_goal(fact) && seen.insert(fact.clone()))
            .collect()
    } else {
        Vec::new()
    };
    Ok(ResourceInstanceRewriteResult {
        state: next,
        semantic_facts,
        body_clauses,
    })
}

fn quantified_resource_fact_memory_obligation_is_discharged(
    assumptions: &PureFactContext,
    proposition: &Proposition,
) -> bool {
    let Proposition::ForAll { body, .. } = proposition else {
        return false;
    };
    let Proposition::Implies(antecedent, consequent) = body.as_ref() else {
        return false;
    };
    fn assume_conjuncts(
        assumptions: PureFactContext,
        proposition: &Proposition,
    ) -> PureFactContext {
        if let Proposition::And(left, right) = proposition {
            let assumptions = assume_conjuncts(assumptions, left);
            assume_conjuncts(assumptions, right)
        } else {
            assumptions.assume_proposition(proposition.clone())
        }
    }
    assume_conjuncts(assumptions.clone(), antecedent).proves_atomic_memory_or_resource(consequent)
}

/// The facts a constructor case exposes for the exact folded resource field
/// the proof matched.
///
/// This is the read-only half of an instance unfold: it binds the selected
/// arm's constructor payloads and evaluates that arm's facts against its own
/// immediate memory body, but it neither publishes the body's ownership nor
/// changes `state`.  The projection identifies one held instance directly;
/// no ambient resource or premise scan is needed.  Any mismatch or unsupported
/// body shape fails closed by publishing no facts.
pub(in crate::kernel) fn matched_resource_instance_case_clauses(
    state: &CState,
    projection: &ResourceFieldProjection,
    model: &AlgebraicTerm,
    constructor: &AlgebraicTerm,
    definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
) -> Vec<ResourceBodyClauseRecord> {
    if projection.at_entry {
        return Vec::new();
    }
    if !projection.children.is_empty() {
        return Vec::new();
    }
    let Some(instance) = state.owned_resource_instance(projection.identity) else {
        return Vec::new();
    };
    let Ok(definition_index) =
        definitions.binary_search_by(|definition| definition.name().cmp(instance.name()))
    else {
        return Vec::new();
    };
    let definition = &definitions[definition_index];
    let Some(matched) = definition.matched.as_ref() else {
        return Vec::new();
    };
    if projection.field_index != matched.field_index
        || !matches!(
            instance.fields().get(projection.field_index),
            Some(AlgebraicValue::Algebraic(field_model)) if field_model == model
        )
    {
        return Vec::new();
    }
    let Ok((arm, selected_constructor)) =
        selected_instance_match_arm(instance, definition, definitions, assumptions)
    else {
        return Vec::new();
    };
    // A matched child has its own folded instance and field scope. Publishing
    // facts about it without performing the explicit child-selection rewrite
    // would conflate the parent's proof match with an ownership unfold. Keep
    // this read-only publication to flat arms; recursive arms still acquire
    // their facts through `unfold(parent) as { ... }`.
    if !arm.children.is_empty() {
        return Vec::new();
    }
    if &selected_constructor != constructor {
        return Vec::new();
    }
    let AlgebraicTermNode::Constructor { fields, .. } = &constructor.node else {
        return Vec::new();
    };
    if fields.len() != arm.bindings.len()
        || fields.len() != arm.binding_types.len()
        || fields.len() != arm.binding_variables.len()
    {
        return Vec::new();
    }

    let Ok(mut evaluation) = instance_body_evaluation(state, instance, definition) else {
        return Vec::new();
    };
    let mut integer_bindings = BTreeMap::new();
    let mut algebraic_bindings = BTreeMap::new();
    for (index, value) in fields.iter().enumerate() {
        let name = &arm.bindings[index];
        match (
            &arm.binding_types[index],
            arm.binding_variables[index],
            value,
        ) {
            (AlgebraicValueType::C(_), None, AlgebraicValue::C(value)) => {
                let ty = value.c_type();
                let value = arm_binding_program_spelling(value, assumptions)
                    .unwrap_or_else(|| value.clone());
                evaluation.locals.set_typed(name.clone(), value, ty);
            }
            (AlgebraicValueType::Integer, Some(variable), AlgebraicValue::Integer(value)) => {
                if integer_bindings.insert(variable, value.clone()).is_some() {
                    return Vec::new();
                }
            }
            (AlgebraicValueType::Algebraic { .. }, None, AlgebraicValue::Algebraic(value)) => {
                algebraic_bindings.insert(name.clone(), value.clone());
            }
            _ => return Vec::new(),
        }
    }

    let mut budget = ExecutionBudget::beside_live_state();
    let Some(active) = evaluate_composite_resource_body_condition(
        definition,
        &evaluation,
        assumptions,
        &mut budget,
    ) else {
        return Vec::new();
    };
    if !active {
        return Vec::new();
    }
    let Ok(Ok((body_resources, _))) = evaluate_function_resource_context_with_normalization(
        &evaluation,
        &arm.contains,
        &[],
        assumptions,
        &mut budget,
        false,
    ) else {
        return Vec::new();
    };
    evaluation.resources = body_resources.clone();
    let mut supporting_facts = body_resources.observable_facts_assuming_valid(assumptions);
    for fact in body_resources.facts() {
        let Some(range) = fact.memory_range() else {
            continue;
        };
        let width = range.element_width();
        supporting_facts.push(Proposition::CMemoryLoadable {
            memory: state.memory.clone(),
            base: range
                .base()
                .offset_by_elements(range.start().clone(), width),
            bytes: Bitvector32Term::multiply(
                Bitvector32Term::subtract(range.end().clone(), range.start().clone()),
                Bitvector32Term::Constant(width),
            ),
        });
    }
    supporting_facts.push(Proposition::CResourceComposition(body_resources));
    let mut body_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads();
    for fact in supporting_facts {
        body_assumptions = body_assumptions.assume_proposition(fact);
    }

    lower_selected_resource_body_clauses(
        &evaluation,
        &arm.facts,
        Some(&arm.variant),
        &integer_bindings,
        &algebraic_bindings,
        &body_assumptions,
        None,
        &mut budget,
    )
    .map(|(records, _retained)| records)
    .unwrap_or_default()
}

pub(in crate::kernel) fn selected_instance_match_arm<'a>(
    instance: &ResourceInstance,
    definition: &'a CCompositeResourceDefinition,
    definitions: &'a [CCompositeResourceDefinition],
    assumptions: &PureFactContext,
) -> Result<(&'a CResourceMatchArm, AlgebraicTerm), &'static str> {
    let body = definition
        .matched
        .as_ref()
        .ok_or("missing resource match body")?;
    if definition.condition.is_some()
        || !definition.contains.is_empty()
        || !definition.facts.is_empty()
        || !body.algebraic_type.has_consistent_root_schema()
        || body.algebraic_type.rigid
        || instance
            .schema()
            .fields()
            .get(body.field_index)
            .map(|(_, ty)| ty)
            != Some(&ResourceFieldType::Algebraic(body.algebraic_type.clone()))
        || body.arms.len() != body.algebraic_type.variants.len()
    {
        return Err("invalid resource match schema");
    }
    let mut variants = BTreeSet::new();
    let schema_variants = body
        .algebraic_type
        .variants
        .iter()
        .map(|variant| (variant.name.as_str(), &variant.fields))
        .collect::<BTreeMap<_, _>>();
    let reserved = definition
        .parameters
        .iter()
        .map(|parameter| parameter.name())
        .chain(
            instance
                .schema()
                .fields()
                .iter()
                .map(|(name, _)| name.as_str()),
        )
        .collect::<BTreeSet<_>>();
    for arm in &body.arms {
        let mut names = BTreeSet::new();
        if !variants.insert(&arm.variant)
            || schema_variants
                .get(arm.variant.as_str())
                .is_none_or(|fields| {
                    **fields != arm.binding_types
                        || fields.len() != arm.bindings.len()
                        || arm.binding_variables.len() != arm.bindings.len()
                })
            || arm.bindings.iter().any(|name| {
                name.is_empty() || !names.insert(name) || reserved.contains(name.as_str())
            })
            || arm.binding_variables.iter().zip(&arm.binding_types).any(
                |(variable, binding_type)| match binding_type {
                    AlgebraicValueType::Integer => variable.is_none(),
                    _ => variable.is_some(),
                },
            )
            || arm
                .contains
                .iter()
                .any(|resource| resource.family() != ResourceFamily::Memory || resource.is_view())
        {
            return Err("invalid resource match arm");
        }
        let mut integer_binding_variables = BTreeSet::new();
        for (variable, binding_type) in arm.binding_variables.iter().zip(&arm.binding_types) {
            if binding_type == &AlgebraicValueType::Integer
                && !integer_binding_variables.insert(variable.expect("checked above"))
            {
                return Err("resource match Integer bindings reuse an identity");
            }
        }
        let mut child_names = BTreeSet::new();
        let mut child_bindings = BTreeSet::new();
        for child in &arm.children {
            // A child is checked against its own definition, which is the
            // parent's for a directly recursive child and another declared
            // resource otherwise.
            let child_definition = child_composite_definition(definition, definitions, child)?;
            let child_schema = if child_definition.name() == definition.name() {
                instance.schema()
            } else {
                child_definition
                    .instance_schema
                    .as_ref()
                    .ok_or("resource match child requires a field-bearing definition")?
            };
            if child.name.is_empty()
                || reserved.contains(child.name.as_str())
                || names.contains(&child.name)
                || !child_names.insert(&child.name)
                || child.binding == Variable(u64::MAX)
                || !child_bindings.insert(child.binding)
                || child.arguments.len() != child_definition.parameters.len()
                || child.field_bindings.len() != child_schema.fields().len()
            {
                return Err("invalid recursive child schema");
            }
            for ((_, field_type), index) in child_schema.fields().iter().zip(&child.field_bindings)
            {
                let expected = match field_type {
                    ResourceFieldType::Integer => AlgebraicValueType::Integer,
                    ResourceFieldType::C(ty) => AlgebraicValueType::C(*ty),
                    ResourceFieldType::Algebraic(ty) => ty.value_type(),
                };
                if arm.binding_types.get(*index) != Some(&expected) {
                    return Err(
                        "recursive child fields must be immediate constructor bindings of the declared type",
                    );
                }
            }
            // In particular, a same-family child's model is bound to a field
            // of this constructor, never to the whole parent model. A child of
            // another family has no such field; its own matched field is
            // already checked above, against its own declared type.
            if child_definition.name() == definition.name()
                && arm
                    .binding_types
                    .get(child.field_bindings[body.field_index])
                    != Some(&body.algebraic_type.value_type())
            {
                return Err("recursive child model must be a proper submodel");
            }
        }
    }
    let Some(AlgebraicValue::Algebraic(model)) = instance.fields().get(body.field_index) else {
        return Err("resource match field is not algebraic");
    };
    // Fold and unfold bind the arm's fields, so they need the constructor
    // itself: an arm merely entailed by the premises (D7) grants reading, not
    // the values a rewrite would substitute.
    let Some(ResourceModelArmSelection::Constructor(constructor)) =
        select_resource_model_arm(model, assumptions)
    else {
        return Err("resource match requires constructor evidence for the instance field");
    };
    let AlgebraicTermNode::Constructor { variant, .. } = &constructor.node else {
        unreachable!()
    };
    let arm = body
        .arms
        .iter()
        .find(|arm| &arm.variant == variant)
        .ok_or("unknown resource match constructor")?;
    Ok((arm, constructor))
}

/// Which arm of a matched resource model one section's premises select.
///
/// `Constructor` carries the model's own constructor application, so the arm's
/// bindings have values. `Variant` names the arm without naming its fields:
/// the premises rule out every other variant, or witness this one, but no
/// premise says what it holds.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResourceModelArmSelection {
    Constructor(AlgebraicTerm),
    Variant(String),
}

impl ResourceModelArmSelection {
    pub fn variant(&self) -> &str {
        match self {
            Self::Constructor(constructor) => match &constructor.node {
                AlgebraicTermNode::Constructor { variant, .. } => variant,
                _ => unreachable!("a selected constructor term is a constructor application"),
            },
            Self::Variant(variant) => variant,
        }
    }
}

/// What one frontier's premises say about a matched resource model: the arm
/// they select, the arms they leave possible, or nothing.
///
/// `Possible` carries two or more variants, so a caller never has to ask a
/// second question to tell "one arm" from "several": `Selected` is the answer
/// that grants an arm's own cells and facts, `Possible` the answer that grants
/// only what every survivor agrees on, and `Open` the answer that grants
/// nothing and keeps the instance folded.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResourceModelArmDecision {
    Selected(ResourceModelArmSelection),
    Possible(Vec<String>),
    Open,
}

/// The one arm decision in Click: premises plus constructor exhaustiveness
/// against one matched model value.
///
/// Every frontier that decides a matched instance's arms reaches this
/// function, through [`publish_instance_arms`] for a whole context or through
/// [`select_resource_model_arm`] for one model. Contract lowering asks it for
/// a `requires`-selected arm; a loop head asks the same question with its
/// invariants playing the part of the requirements, and a fold or unfold asks
/// it through [`selected_instance_match_arm`], which needs the stronger
/// `Constructor` answer because it binds the arm's fields.
///
/// The answer is decided, never searched: a constructor premise answers
/// outright, an existential premise witnesses one variant, and disequalities
/// against field-free constructors rule variants out. One variant left is
/// `Selected`; two or more, with at least one ruled out, is `Possible`; any
/// other state of evidence is `Open`. A context that has ruled out every
/// declared variant is inconsistent and not this decision's business to
/// exploit, so it is `Open` too.
///
/// Cost is the number of premises about this exact value plus the declared
/// variants of its type. Unrelated premises are never visited.
pub fn decide_resource_model_arm(
    model: &AlgebraicTerm,
    assumptions: &PureFactContext,
) -> ResourceModelArmDecision {
    if let Some(constructor) = assumptions.known_algebraic_constructor(model) {
        return ResourceModelArmDecision::Selected(ResourceModelArmSelection::Constructor(
            constructor,
        ));
    }
    let AlgebraicTermNode::Variable(variable) = &model.node else {
        return ResourceModelArmDecision::Open;
    };
    let declared = model
        .algebraic_type
        .variants
        .iter()
        .map(|variant| variant.name.as_str())
        .collect::<BTreeSet<_>>();
    if declared.is_empty() {
        return ResourceModelArmDecision::Open;
    }
    let mut witnessed = BTreeMap::new();
    let mut excluded = BTreeMap::new();
    for (premise, evidence) in assumptions.algebraic_variant_evidence(*variable) {
        if !declared.contains(evidence.variant.as_str()) {
            continue;
        }
        match evidence.kind {
            AlgebraicVariantEvidenceKind::Witnessed => {
                witnessed.insert(evidence.variant.as_str(), premise);
            }
            AlgebraicVariantEvidenceKind::Excluded => {
                excluded.insert(evidence.variant.as_str(), premise);
            }
        }
    }
    // A witness names its arm directly. Two witnesses would need the context
    // to be inconsistent, which is not this decision's business to exploit.
    // Cite what decided the arm, so an expansion of the selected arm names the
    // premises a reader would look for.
    if let [(variant, premise)] = witnessed.iter().collect::<Vec<_>>().as_slice() {
        super::assumptions::record_reasoning_provenance(assumptions, premise);
        return ResourceModelArmDecision::Selected(ResourceModelArmSelection::Variant(
            (**variant).to_owned(),
        ));
    }
    if !witnessed.is_empty() {
        return ResourceModelArmDecision::Open;
    }
    let excluded_variants = excluded.keys().copied().collect::<BTreeSet<_>>();
    let possible = declared
        .difference(&excluded_variants)
        .copied()
        .collect::<Vec<_>>();
    let decision = match possible.as_slice() {
        [] => return ResourceModelArmDecision::Open,
        [only] => ResourceModelArmDecision::Selected(ResourceModelArmSelection::Variant(
            (*only).to_owned(),
        )),
        _ if excluded.is_empty() => return ResourceModelArmDecision::Open,
        several => ResourceModelArmDecision::Possible(
            several
                .iter()
                .map(|variant| (*variant).to_owned())
                .collect(),
        ),
    };
    for premise in excluded.values() {
        super::assumptions::record_reasoning_provenance(assumptions, premise);
    }
    decision
}

/// The arm one frontier's premises select, when they select exactly one.
///
/// A thin reading of [`decide_resource_model_arm`]: the callers that can only
/// act on a decided arm — a fold, an unfold, a termination measure — ask this
/// one instead of matching the three-way answer.
pub fn select_resource_model_arm(
    model: &AlgebraicTerm,
    assumptions: &PureFactContext,
) -> Option<ResourceModelArmSelection> {
    match decide_resource_model_arm(model, assumptions) {
        ResourceModelArmDecision::Selected(selection) => Some(selection),
        ResourceModelArmDecision::Possible(_) | ResourceModelArmDecision::Open => None,
    }
}

fn instance_body_evaluation(
    state: &CState,
    instance: &ResourceInstance,
    definition: &CCompositeResourceDefinition,
) -> Result<CState, &'static str> {
    let mut evaluation = state.clone();
    {
        // A local interpretation of proposed fields, never ownership or a
        // persistent open handle. Guards may refer to these fields as well.
        evaluation.instance_field_scope = evaluation
            .instance_field_scope
            .unchecked_with_fact(CResourceFact::own(CResource::Instance(instance.clone())));
    }
    if definition.matched.is_some() {
        // An arm's C names are lexical parameters and constructor bindings,
        // never incidental locals of the function currently opening it.
        evaluation.locals = CLocalEnvironment::default();
    }
    evaluation.resource_bindings = Some(std::sync::Arc::new(BTreeMap::from([(
        Variable(u64::MAX),
        instance.identity,
    )])));
    for (parameter, value) in definition.parameters.iter().zip(instance.arguments.iter()) {
        let value = value
            .as_c_value()
            .ok_or("resource argument is not a C value")?;
        if value.c_type() != parameter.c_type() {
            return Err("resource argument type mismatch");
        }
        evaluation.locals.set_typed(
            parameter.name().to_owned(),
            value.clone(),
            parameter.c_type(),
        );
    }
    Ok(evaluation)
}

pub(in crate::kernel) fn instance_body_guard_case(
    state: &CState,
    instance: &ResourceInstance,
    definition: &CCompositeResourceDefinition,
    assumptions: &PureFactContext,
) -> Option<bool> {
    let evaluation = instance_body_evaluation(state, instance, definition).ok()?;
    evaluate_composite_resource_body_condition(
        definition,
        &evaluation,
        assumptions,
        &mut ExecutionBudget::beside_live_state(),
    )
}

pub(super) fn expand_composite_resource_fact(
    context: &ResourceContext,
    composite: &CResourceFact,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &PureFactContext,
) -> Option<ResourceContext> {
    expand_composite_resource_fact_with_children(
        context,
        composite,
        definitions,
        memory,
        assumptions,
    )
    .map(|(expanded, _, _)| expanded)
}

/// The kernel's own one-level expansion of a viewed composite, packaged as
/// the evidence `LoanLedger::project` re-checks a child projection against.
/// The expansion runs over the head alone, so the admissible children come
/// from the definition and the current memory, never from the caller's
/// ambient resource context or its own list of exposed facts (D2 law 10).
pub(crate) fn checked_composite_projection_evidence(
    viewed: &CResourceFact,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &PureFactContext,
) -> Option<CompositeProjectionEvidence> {
    let head = ResourceContext::new().unchecked_with_fact(viewed.clone());
    let (_, children, _) = expand_composite_resource_fact_with_children(
        &head,
        viewed,
        definitions,
        memory,
        assumptions,
    )?;
    CompositeProjectionEvidence::from_checked_expansion(viewed.clone(), children)
}

pub(super) fn expand_composite_resource_fact_with_children(
    context: &ResourceContext,
    composite: &CResourceFact,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &PureFactContext,
) -> Option<(ResourceContext, Vec<CResourceFact>, Vec<CResourceFact>)> {
    let CResource::Composite { name, arguments } = composite.resource() else {
        return None;
    };
    let definition = definitions
        .iter()
        .find(|definition| definition.name() == name)?;
    if definition.instance_schema.is_some() || definition.matched.is_some() {
        return None;
    }
    if definition.parameters().len() != arguments.len() {
        return None;
    }
    // A viewed composite carries its loan dependency on the folded
    // occurrence.  Expansion must transfer that exact bundle to only the
    // newly inserted child occurrences; equal children in the ambient frame
    // are not eligible destinations.
    let borrowed_parent = if composite.is_view() {
        let occurrences = context.occurrences_for_fact(composite);
        let mut selected = None;
        let mut saw_unbound = false;
        for occurrence in occurrences {
            let Some(dependency) = context.loan_dependency(occurrence) else {
                saw_unbound = true;
                continue;
            };
            if selected
                .as_ref()
                .is_some_and(|(_, existing)| existing != dependency)
            {
                return None;
            }
            selected = Some((occurrence, dependency.clone()));
        }
        if saw_unbound && selected.is_some() {
            return None;
        }
        selected
    } else {
        None
    };
    let expansion_base = borrowed_parent
        .as_ref()
        .map(|(occurrence, _)| {
            context
                .clone()
                .without_exact_representation_for_occurrence(*occurrence)
        })
        .unwrap_or_else(|| context.clone().without_exact_representation(composite))?;
    let mut state = CState::new()
        .with_memory(memory.clone())
        .with_resource_context(expansion_base.clone());
    for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
        let argument = argument.as_c_value()?;
        if parameter.c_type() != argument.c_type() {
            return None;
        }
        state.locals.set_typed(
            parameter.name().to_string(),
            argument.clone(),
            parameter.c_type(),
        );
    }
    bind_composite_witnesses(definition, arguments, &mut state, assumptions)?;
    let mut budget = ExecutionBudget::beside_live_state();
    let evaluation_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads();
    let mut child_facts = Vec::new();
    let Some(body_active) = evaluate_composite_resource_body_condition(
        definition,
        &state,
        &evaluation_assumptions,
        &mut budget,
    ) else {
        // A guarded folded resource remains opaque until the current path
        // decides its condition.
        return Some((context.clone(), Vec::new(), Vec::new()));
    };
    for contained in if body_active {
        definition.contains()
    } else {
        &[]
    } {
        let child_result = evaluate_function_resource_spec(
            &state,
            contained,
            &evaluation_assumptions,
            &mut budget,
        );
        let Ok(Ok(child)) = child_result else {
            return None;
        };
        state.resources = state.resources.clone().unchecked_with_fact(child.clone());
        child_facts.push(child);
    }
    let raw_children = if composite.is_own() {
        child_facts.clone()
    } else {
        child_facts
            .iter()
            .map(|fact| CResourceFact::View(fact.resource().clone()))
            .collect()
    };
    let children = ResourceContext::new()
        .try_compose_with_facts(child_facts, assumptions)
        .ok()?;
    let children = if composite.is_own() {
        children.facts().to_vec()
    } else {
        children
            .facts()
            .iter()
            .map(|fact| CResourceFact::View(fact.resource().clone()))
            .collect()
    };
    let mut expanded = expansion_base.clone();
    let missing = children
        .iter()
        .filter(|child| {
            !expanded.facts().contains(child)
                && !resource_context_contains_exact_owned_fact(&expanded, child, assumptions)
        })
        .cloned()
        .collect::<Vec<_>>();
    let (expanded_context, inserted) = expanded
        .try_compose_certified_group_into_valid_context_delaying_normalization_with_occurrences(
            missing,
            assumptions,
        )
        .ok()?;
    expanded = expanded_context;
    if let Some((_, binding)) = borrowed_parent {
        let mut transferred_views = BTreeSet::new();
        for (child, occurrence) in inserted {
            if !child.is_view() {
                continue;
            }
            transferred_views.insert(child.clone());
            expanded = expanded.with_loan_dependency(
                occurrence,
                crate::kernel::loans::LoanViewBinding {
                    viewed: child,
                    ..binding.clone()
                },
            );
        }
        if children
            .iter()
            .filter(|child| child.is_view())
            .any(|child| {
                if transferred_views.contains(child) {
                    return false;
                }
                let expected = crate::kernel::loans::LoanViewBinding {
                    viewed: child.clone(),
                    ..binding.clone()
                };
                !expanded
                    .view_occurrences_for_fact(child, assumptions)
                    .iter()
                    .any(|occurrence| expanded.loan_dependency(*occurrence) == Some(&expected))
            })
        {
            // Reusing an equal ambient child would lose the source occurrence
            // relation.  The checked expansion has no destination ID to bind.
            return None;
        }
    }
    Some((expanded, children, raw_children))
}

fn resource_context_contains_exact_owned_fact(
    context: &ResourceContext,
    required: &CResourceFact,
    assumptions: &PureFactContext,
) -> bool {
    if !required.is_own() {
        return false;
    }
    if let CResourceFact::Own(CResource::Memory(required_range), _) = required {
        let exact_parts = context
            .facts()
            .iter()
            .filter(|available| {
                available.memory_own_range().is_some_and(|available_range| {
                    memory_range_covers(required_range, available_range, assumptions)
                })
            })
            .cloned()
            .collect::<Vec<_>>();
        let exact_parts = ResourceContext::new().unchecked_with_facts(exact_parts);
        return exact_parts.validity_error(assumptions).is_none()
            && exact_parts.satisfies_fact(required, assumptions);
    }
    context.facts().iter().any(|available| {
        if !available.is_own() || available.family() != required.family() {
            return false;
        }
        ResourceContext::new()
            .unchecked_with_fact(available.clone())
            .without_fact_delaying_normalization(required, assumptions)
            .is_some_and(|remaining| remaining.is_empty())
    })
}

/// The proposition asserting the opposite of `proposition`, without adding a
/// logical rule: a bare condition flips its value, a negation drops, and
/// anything else is wrapped in one `Not`.
fn negated_contract_proposition(proposition: &Proposition) -> Proposition {
    match proposition {
        Proposition::ConditionIs(condition, value) => {
            Proposition::ConditionIs(condition.clone(), !value)
        }
        Proposition::Not(body) => body.as_ref().clone(),
        proposition => Proposition::Not(Box::new(proposition.clone())),
    }
}

/// Decide one lowered contract guard by the retained exact routes only:
/// `Some(true)` when the guard holds, `Some(false)` when its opposite does,
/// and `None` when neither is decided.
///
/// `None` is not "false". It is the answer that leaves the choice to the
/// consumer — which refuses the refinement, keeps both specification paths,
/// or emits an obligation — instead of letting a general proof search inside
/// the kernel settle a contract branch.
fn guard_value_by_exact_routes(assumptions: &PureFactContext, guard: &Proposition) -> Option<bool> {
    if required_obligation_is_exactly_discharged(assumptions, guard) {
        return Some(true);
    }
    required_obligation_is_exactly_discharged(assumptions, &negated_contract_proposition(guard))
        .then_some(false)
}

/// Decide one guard: `Some(true)`, `Some(false)`, or `None` for undecided.
///
/// Package 10(b) removed the general-prover leg, so every answer now comes
/// from the exact fact index, the frozen condition checker on a bare
/// condition, or the frozen atomic memory/resource checkers. An undecided
/// guard travels to the caller, which keeps both specification paths or
/// refuses the operation.
///
/// `resource_guard_conjunction` is the reaching fixture for a guard that is
/// not a bare condition. The obligation check below has no reaching fixture:
/// a guard is the condition of a resource body, and a resource condition must
/// be load-free, so the lowered guard path carries no obligation.
pub(super) fn evaluate_guarded_contract_condition(
    condition: &SpecProposition,
    state: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> Option<bool> {
    let paths = lower_spec_proposition_at_state_with_loop_entry(
        state,
        condition,
        None,
        assumptions,
        budget,
    )
    .ok()?;
    let [path] = paths.as_slice() else {
        return None;
    };
    if !path.obligations.iter().all(|obligation| {
        required_obligation_is_exactly_discharged(assumptions, obligation.proposition())
    }) {
        return None;
    }
    let proves_body_condition = |proposition: &Proposition| match proposition {
        Proposition::ConditionIs(condition, value) => {
            assumptions.proves_condition_exact_or_snapshot(condition, *value)
                || assumptions.decide(condition) == Some(*value)
        }
        Proposition::Not(body) => match body.as_ref() {
            Proposition::ConditionIs(condition, value) => {
                assumptions.proves_condition_exact_or_snapshot(condition, !*value)
                    || assumptions.decide(condition) == Some(!*value)
            }
            _ => false,
        },
        // No general prover leg. A guard this does not decide is undecided,
        // and the caller keeps both specification paths or refuses the
        // operation rather than having the kernel search for a proof.
        _ => required_obligation_is_exactly_discharged(assumptions, proposition),
    };
    if proves_body_condition(&path.proposition) {
        super::assumptions::record_reasoning_provenance(assumptions, &path.proposition);
        return Some(true);
    }
    let false_proposition = negated_contract_proposition(&path.proposition);
    if proves_body_condition(&false_proposition) {
        super::assumptions::record_reasoning_provenance(assumptions, &false_proposition);
        Some(false)
    } else {
        None
    }
}

fn evaluate_composite_resource_body_condition(
    definition: &CCompositeResourceDefinition,
    state: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> Option<bool> {
    definition.condition().map_or(Some(true), |condition| {
        evaluate_guarded_contract_condition(condition, state, assumptions, budget)
    })
}

pub(super) fn expand_all_composite_resource_facts(
    context: &ResourceContext,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &PureFactContext,
) -> Option<ResourceContext> {
    let mut cached = context.clone();
    let supports = context
        .facts()
        .iter()
        .filter(|fact| matches!(fact.resource(), CResource::Composite { .. }))
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .flat_map(|support| {
            context
                .cached_supported_expansions(&support)
                .into_iter()
                .map(move |(occurrence, expansion)| (support.clone(), occurrence, expansion))
        })
        .collect::<Vec<_>>();
    for (support, support_occurrence, expansion) in supports {
        if expansion.as_slice() == [support.clone()] {
            continue;
        }
        cached = cached.without_exact_representation_for_occurrence(support_occurrence)?;
        let missing = expansion
            .into_iter()
            .filter(|fact| {
                !cached.facts().contains(fact)
                    && !resource_context_contains_exact_owned_fact(&cached, fact, assumptions)
            })
            .collect::<Vec<_>>();
        cached = cached
            .try_compose_certified_group_into_valid_context_delaying_normalization(
                missing,
                assumptions,
            )
            .ok()?;
    }
    expand_composite_resource_context(&cached, definitions, memory, assumptions)
        .map(|(resources, _)| resources)
}

/// Expands each owned composite of `context` exactly one level, in place of
/// its head, and leaves every child composite folded. This is the frontier
/// boundary the composite lend and `project` use: the kernel does not reason
/// inside a folded composite beyond its one-level frontier, so a frame check
/// that consults ownership sees exactly what a lend would. `None` when no
/// head expanded. Work is charged per head, never per nested level.
pub(super) fn expand_owned_composite_resource_facts_one_level(
    context: &ResourceContext,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &PureFactContext,
) -> Option<ResourceContext> {
    let heads = context
        .facts()
        .iter()
        .filter(|fact| fact.is_own() && matches!(fact.resource(), CResource::Composite { .. }))
        .cloned()
        .collect::<Vec<_>>();
    let mut expanded = context.clone();
    let mut changed = false;
    for head in heads {
        crate::instrumentation::record_deterministic_work(1);
        if !expanded.facts().contains(&head) {
            continue;
        }
        let Some(next) =
            expand_composite_resource_fact(&expanded, &head, definitions, memory, assumptions)
        else {
            continue;
        };
        if next != expanded {
            expanded = next;
            changed = true;
        }
    }
    changed.then_some(expanded)
}

/// Continues through recursive composites only while their guards are
/// decidable in the current contract path. Unknown branches remain folded.
fn expand_decidable_composite_resource_frontier(
    context: &ResourceContext,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &PureFactContext,
) -> ResourceContext {
    let mut expanded = context.clone();
    let mut seen = BTreeSet::new();
    let mut pending = VecDeque::from(
        context
            .facts()
            .iter()
            .filter(|fact| matches!(fact.resource(), CResource::Composite { .. }))
            .cloned()
            .collect::<Vec<_>>(),
    );
    while let Some(composite) = pending.pop_front() {
        if !seen.insert(composite.clone()) || !expanded.facts().contains(&composite) {
            continue;
        }
        let Some(next) =
            expand_composite_resource_fact(&expanded, &composite, definitions, memory, assumptions)
        else {
            continue;
        };
        if next == expanded {
            continue;
        }
        for child in next.facts().iter().filter(|fact| {
            matches!(fact.resource(), CResource::Composite { .. }) && !seen.contains(*fact)
        }) {
            pending.push_back(child.clone());
        }
        expanded = next;
    }
    expanded
}

/// Expands only the folded branches needed to expose `target`, leaving
/// unrelated and deeper recursive resources folded.
pub(super) fn expose_composite_resource_fact(
    context: &ResourceContext,
    target: &CResourceFact,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &PureFactContext,
) -> Option<ResourceContext> {
    // Exposure unfolds composites until the target is held. A memory target
    // is looked up by structure at every context first: the indexed answer
    // for a cell an unfolded body names outright. Only when no unfolding
    // holds it by structure does each context, in the same order, answer
    // with the reasoning the resource algebra applies.
    let structural = target.memory_range().is_some();
    // A token or composite target that the starting context already holds
    // needs no unfolding, and the starting context is the first one the
    // search below would accept. Answering from the index first keeps
    // exposing each of a context's members from re-expanding every composite
    // it still holds, which made exposing all of them quadratic.
    if !structural && context.satisfies_fact(target, assumptions) {
        return Some(context.clone());
    }
    let mut visited = Vec::new();
    let mut seen = BTreeSet::new();
    let mut pending = VecDeque::from([context.clone()]);
    while let Some(context) = pending.pop_front() {
        if !seen.insert(context.clone()) {
            continue;
        }
        if structural && context.satisfies_memory_fact_structurally(target) {
            return Some(context);
        }
        // The composite whose pointer argument is the target's base by
        // structure is unfolded first: when any composite holds the cell,
        // it is that one.
        let mut composites = context
            .facts()
            .iter()
            .filter(|fact| matches!(fact.resource(), CResource::Composite { .. }))
            .cloned()
            .collect::<Vec<_>>();
        if let Some(required) = target.memory_range() {
            composites
                .sort_by_key(|composite| !composite_names_pointer_base(composite, required.base()));
        }
        for composite in &composites {
            let expanded = expand_composite_resource_fact(
                &context,
                composite,
                definitions,
                memory,
                assumptions,
            )?;
            if expanded == context {
                continue;
            }
            if structural && expanded.satisfies_memory_fact_structurally(target) {
                return Some(expanded);
            }
            pending.push_back(expanded);
        }
        visited.push(context);
    }
    visited
        .into_iter()
        .find(|context| context.satisfies_fact(target, assumptions))
}

/// Whether a composite fact names the base of `pointer` among its pointer
/// arguments by structure: the same pointer, or one that `pointer` is a
/// constant offset from.
fn composite_names_pointer_base(composite: &CResourceFact, pointer: &Pointer) -> bool {
    let CResource::Composite { arguments, .. } = composite.resource() else {
        return false;
    };
    arguments.iter().any(|argument| {
        let AlgebraicValue::C(CValue::Pointer(argument)) = argument else {
            return false;
        };
        argument.pointer() == pointer
            || pointer
                .element_index_from_base_with_width(argument.pointer(), 1)
                .is_some()
    })
}

fn expand_composite_resource_context(
    context: &ResourceContext,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &PureFactContext,
) -> Option<(ResourceContext, Vec<CResourceFact>)> {
    let mut expanded = context.clone();
    let mut composites = Vec::new();
    let roots = context
        .facts()
        .iter()
        .filter(|fact| matches!(fact.resource(), CResource::Composite { .. }))
        .cloned()
        .collect::<Vec<_>>();
    for root in roots {
        expanded = expand_composite_resource_tree(
            &expanded,
            &root,
            definitions,
            memory,
            assumptions,
            &[],
            &mut composites,
        )?;
    }
    Some((expanded, composites))
}

fn expand_composite_resource_tree(
    context: &ResourceContext,
    composite: &CResourceFact,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &PureFactContext,
    ancestors: &[String],
    composites: &mut Vec<CResourceFact>,
) -> Option<ResourceContext> {
    if !context.facts().contains(composite) {
        return Some(context.clone());
    }
    let CResource::Composite { name, .. } = composite.resource() else {
        return Some(context.clone());
    };
    let definition = definitions
        .iter()
        .find(|definition| definition.name() == name)?;
    if definition.is_recursive() && ancestors.iter().any(|ancestor| ancestor == name) {
        return Some(context.clone());
    }
    let (mut expanded, children, _) = expand_composite_resource_fact_with_children(
        context,
        composite,
        definitions,
        memory,
        assumptions,
    )?;
    if expanded.facts().contains(composite) {
        return Some(expanded);
    }
    composites.push(composite.clone());
    let mut child_ancestors = ancestors.to_vec();
    child_ancestors.push(name.clone());
    for child in children {
        if matches!(child.resource(), CResource::Composite { .. }) {
            expanded = expand_composite_resource_tree(
                &expanded,
                &child,
                definitions,
                memory,
                assumptions,
                &child_ancestors,
                composites,
            )?;
        }
    }
    Some(expanded)
}

pub(super) fn expand_all_composite_resource_facts_and_propositions(
    context: &ResourceContext,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &PureFactContext,
) -> Option<(ResourceContext, Vec<Proposition>)> {
    let (expanded, composites) =
        expand_composite_resource_context(context, definitions, memory, assumptions)?;
    let mut propositions = Vec::new();
    for composite in composites {
        propositions.extend(evaluate_composite_resource_relation_propositions(
            &composite,
            definitions,
            memory,
            assumptions,
        )?);
        let fact_assumptions = assumptions_with_propositions(assumptions, &propositions);
        propositions.extend(evaluate_composite_resource_fact_propositions(
            &composite,
            definitions,
            memory,
            &expanded,
            &fact_assumptions,
        )?);
    }
    Some((expanded, propositions))
}

pub(super) fn evaluate_resource_population_fact_propositions(
    context: &ResourceContext,
    definitions: &[CCompositeResourceDefinition],
    state: &CState,
    assumptions: &PureFactContext,
    include_ordinary: bool,
) -> Option<Vec<Proposition>> {
    let mut populations = BTreeMap::<(String, ResourceArguments), Bitvector32Term>::new();
    for fact in context.facts() {
        let (name, arguments) = match fact.resource() {
            CResource::Composite { name, arguments } | CResource::Token { name, arguments } => {
                (name, arguments)
            }
            CResource::Memory(_) | CResource::Instance(_) => continue,
        };
        let Some(quantity) = fact.owned_quantity_term() else {
            continue;
        };
        populations
            .entry((name.clone(), arguments.clone()))
            .and_modify(|total| {
                *total = Bitvector32Term::add(total.clone(), quantity.clone());
            })
            .or_insert_with(|| quantity.clone());
    }
    let mut propositions = Vec::new();
    for ((name, arguments), visible_quantity) in populations {
        let Some(definition) = definitions
            .iter()
            .find(|definition| definition.name() == name)
        else {
            continue;
        };
        if definition.parameters().len() != arguments.len() {
            return None;
        }
        let population_count = state.counted_population(&name, &arguments);
        if let Some(population_count) = population_count {
            propositions.push(Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedGreaterEqual(
                    Box::new(population_count.clone()),
                    Box::new(visible_quantity),
                ),
                true,
            ));
        }
        // Resource expansion checks ownership relations, but a composite's
        // declared pure facts must also be checked from the kernel-side body
        // state. Ordinary resources do not need a population ledger merely
        // to validate those facts; this is deliberately independent of the
        // population-wide accounting policy below. A body with no facts has
        // no additional proposition to validate here.
        let check_declared_facts = definition.is_counted_population()
            || include_ordinary
            || !definition.facts().is_empty();
        if !check_declared_facts {
            continue;
        }
        let body_active = match population_count {
            Some(_) => {
                let mut population_state = state.clone();
                for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
                    let argument = argument.as_c_value()?;
                    if parameter.c_type() != argument.c_type() {
                        return None;
                    }
                    population_state.locals.set_typed(
                        parameter.name().to_string(),
                        argument.clone(),
                        parameter.c_type(),
                    );
                }
                bind_composite_witnesses(
                    definition,
                    &arguments,
                    &mut population_state,
                    assumptions,
                )?;
                let mut budget = ExecutionBudget::beside_live_state();
                let evaluation_assumptions = assumptions
                    .clone()
                    .allow_symbolic_contract_loads()
                    .prefer_symbolic_external_loads();
                evaluate_composite_resource_body_condition(
                    definition,
                    &population_state,
                    &evaluation_assumptions,
                    &mut budget,
                )?
            }
            None if !definition.is_counted_population() && !include_ordinary => {
                let mut population_state = state.clone();
                for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
                    let argument = argument.as_c_value()?;
                    if parameter.c_type() != argument.c_type() {
                        return None;
                    }
                    population_state.locals.set_typed(
                        parameter.name().to_string(),
                        argument.clone(),
                        parameter.c_type(),
                    );
                }
                bind_composite_witnesses(
                    definition,
                    &arguments,
                    &mut population_state,
                    assumptions,
                )?;
                let mut budget = ExecutionBudget::beside_live_state();
                let evaluation_assumptions = assumptions
                    .clone()
                    .allow_symbolic_contract_loads()
                    .prefer_symbolic_external_loads();
                match evaluate_composite_resource_body_condition(
                    definition,
                    &population_state,
                    &evaluation_assumptions,
                    &mut budget,
                ) {
                    Some(active) => active,
                    None => continue,
                }
            }
            None => return None,
        };
        if population_count.is_none() && (definition.is_counted_population() || include_ordinary) {
            return None;
        }
        let mut population_state = state.clone();
        for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
            let argument = argument.as_c_value()?;
            if parameter.c_type() != argument.c_type() {
                return None;
            }
            population_state.locals.set_typed(
                parameter.name().to_string(),
                argument.clone(),
                parameter.c_type(),
            );
        }
        bind_composite_witnesses(definition, &arguments, &mut population_state, assumptions)?;
        let mut budget = ExecutionBudget::beside_live_state();
        let evaluation_assumptions = assumptions
            .clone()
            .allow_symbolic_contract_loads()
            .prefer_symbolic_external_loads();
        if !body_active {
            continue;
        }
        // Definition facts are justified by the population body, even while
        // that body is opaque in the surface proof context. Expose the body
        // only in this kernel-local state so heap-dependent invariants can
        // discharge their own loadability obligations.
        for contained in definition.contains() {
            let body_resource = evaluate_function_resource_spec(
                &population_state,
                contained,
                &evaluation_assumptions,
                &mut budget,
            )
            .ok()?
            .ok()?;
            if !population_state
                .resources
                .satisfies_fact(&body_resource, &evaluation_assumptions)
            {
                population_state.resources = population_state
                    .resources
                    .try_compose_with_facts_delaying_normalization(
                        [body_resource],
                        &evaluation_assumptions,
                    )
                    .ok()?;
            }
        }
        let mut fact_assumptions = assumptions.clone();
        let mut pending = definition.facts().iter().collect::<Vec<_>>();
        while !pending.is_empty() {
            let mut next_pending = Vec::new();
            let mut made_progress = false;
            for population_fact in pending {
                let evaluation_assumptions = fact_assumptions
                    .clone()
                    .allow_symbolic_contract_loads()
                    .prefer_symbolic_external_loads();
                // Resource-definition loadability facts are symbolic summaries;
                // their owning range supplies the concrete validity check when
                // the resource is used. Do not turn an unconstrained summary
                // endpoint into a failed definition during population setup.
                let Ok(paths) = lower_spec_proposition_at_state_without_range_guards(
                    &population_state,
                    population_fact,
                    None,
                    &evaluation_assumptions,
                    &mut budget,
                ) else {
                    return None;
                };
                let [path] = paths.as_slice() else {
                    next_pending.push(population_fact);
                    continue;
                };
                if !path.obligations.iter().all(|obligation| {
                    if required_obligation_is_exactly_discharged(
                        &fact_assumptions,
                        obligation.proposition(),
                    ) {
                        return true;
                    }
                    let Proposition::CMemoryLoadable {
                        memory: obligation_memory,
                        base,
                        bytes,
                    } = obligation.proposition()
                    else {
                        return false;
                    };
                    memory_snapshots_proven_equal_at_pointer(
                        obligation_memory,
                        population_state.memory(),
                        base,
                        &fact_assumptions,
                    ) && bytes.as_const().is_some_and(|bytes| {
                        resource_context_has_read(
                            population_state.resources(),
                            base,
                            bytes,
                            &fact_assumptions,
                        )
                    })
                }) {
                    next_pending.push(population_fact);
                    continue;
                }
                for obligation in &path.obligations {
                    fact_assumptions =
                        fact_assumptions.assume_proposition(obligation.proposition().clone());
                }
                for path_fact in &path.facts {
                    let proposition = path_fact.proposition().clone();
                    if !propositions.contains(&proposition) {
                        propositions.push(proposition.clone());
                    }
                    fact_assumptions = fact_assumptions.assume_proposition(proposition);
                }
                if !propositions.contains(&path.proposition) {
                    propositions.push(path.proposition.clone());
                }
                fact_assumptions = fact_assumptions.assume_proposition(path.proposition.clone());
                made_progress = true;
            }
            if !made_progress {
                return None;
            }
            pending = next_pending;
        }
    }
    Some(propositions)
}

pub(super) fn evaluate_composite_resource_relation_propositions(
    composite: &CResourceFact,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &PureFactContext,
) -> Option<Vec<Proposition>> {
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
        if parameter.c_type() != argument.c_type() {
            return None;
        }
        state.locals.set_typed(
            parameter.name().to_string(),
            argument.clone(),
            parameter.c_type(),
        );
    }
    bind_composite_witnesses(definition, arguments, &mut state, assumptions)?;
    let mut budget = ExecutionBudget::beside_live_state();
    let evaluation_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads();
    let mut child_facts = Vec::new();
    let mut children = Vec::new();
    let body_active = evaluate_composite_resource_body_condition(
        definition,
        &state,
        &evaluation_assumptions,
        &mut budget,
    )?;
    for contained in if body_active {
        definition.contains()
    } else {
        &[]
    } {
        let child_result = evaluate_function_resource_spec(
            &state,
            contained,
            &evaluation_assumptions,
            &mut budget,
        );
        let Ok(Ok(child)) = child_result else {
            return None;
        };
        state.resources = state.resources.clone().unchecked_with_fact(child.clone());
        if composite.is_own()
            && let Some(owned_child) = child.owned_resource()
        {
            children.push(owned_child.clone());
        }
        child_facts.push(child);
    }
    let mut propositions = Vec::new();
    if composite.is_own() {
        // The child context is the compact authority for ownership-derived
        // separation. Publishing one carrier lets certification answer
        // member-pair queries on demand instead of materializing O(N^2)
        // `CResourceSeparate` propositions.
        let child_context = ResourceContext::new()
            .try_compose_with_facts(child_facts, assumptions)
            .ok()?;
        propositions.push(Proposition::CResourceComposition(child_context));
    }
    for child in &children {
        propositions.push(Proposition::CResourceContains {
            parent: composite.resource().clone(),
            child: child.clone(),
        });
    }
    Some(propositions)
}

pub(super) fn evaluate_composite_resource_loadable_propositions(
    composite: &CResourceFact,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &PureFactContext,
) -> Option<Vec<Proposition>> {
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
        if parameter.c_type() != argument.c_type() {
            return None;
        }
        state.locals.set_typed(
            parameter.name().to_string(),
            argument.clone(),
            parameter.c_type(),
        );
    }
    bind_composite_witnesses(definition, arguments, &mut state, assumptions)?;
    let mut budget = ExecutionBudget::beside_live_state();
    let evaluation_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads();
    if !evaluate_composite_resource_body_condition(
        definition,
        &state,
        &evaluation_assumptions,
        &mut budget,
    )? {
        return Some(Vec::new());
    }

    let mut propositions = Vec::new();
    for resource in definition.contains() {
        let Some(segment) = resource.memory_segment() else {
            continue;
        };
        let evaluated = match evaluate_function_resource_spec(
            &state,
            resource,
            &evaluation_assumptions,
            &mut budget,
        )
        .ok()?
        {
            Ok(resource) => resource,
            Err(_) => return None,
        };
        let range = evaluated.memory_range()?;
        let element_width = segment.element_width();
        propositions.push(Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: range
                .base()
                .offset_by_elements(range.start().clone(), element_width),
            bytes: Bitvector32Term::multiply(
                Bitvector32Term::subtract(range.end().clone(), range.start().clone()),
                Bitvector32Term::Constant(element_width),
            ),
        });
    }
    Some(propositions)
}

pub(super) fn evaluate_composite_resource_fact_propositions(
    composite: &CResourceFact,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    resources: &ResourceContext,
    assumptions: &PureFactContext,
) -> Option<Vec<Proposition>> {
    let CResource::Composite { name, arguments } = composite.resource() else {
        return None;
    };
    let definition = definitions
        .iter()
        .find(|definition| definition.name() == name)?;
    if definition.parameters().len() != arguments.len() {
        return None;
    }
    let mut state = CState::new()
        .with_memory(memory.clone())
        .with_resource_context(resources.clone());
    for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
        let argument = argument.as_c_value()?;
        if parameter.c_type() != argument.c_type() {
            return None;
        }
        state.locals.set_typed(
            parameter.name().to_string(),
            argument.clone(),
            parameter.c_type(),
        );
    }
    bind_composite_witnesses(definition, arguments, &mut state, assumptions)?;
    let mut result = Vec::new();
    let mut budget = ExecutionBudget::beside_live_state();
    let mut fact_assumptions = assumptions.clone();
    let evaluation_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads();
    if !evaluate_composite_resource_body_condition(
        definition,
        &state,
        &evaluation_assumptions,
        &mut budget,
    )? {
        return Some(result);
    }
    let mut pending = definition.facts().iter().collect::<Vec<_>>();
    while !pending.is_empty() {
        let mut next_pending = Vec::new();
        let mut made_progress = false;
        for fact in pending {
            let evaluation_assumptions = fact_assumptions
                .clone()
                .allow_symbolic_contract_loads()
                .prefer_symbolic_external_loads();
            // Resource-definition loadability facts are symbolic summaries;
            // their owning range supplies the concrete validity check when
            // the resource is used. Do not turn an unconstrained summary
            // endpoint into a failed definition during population setup.
            let Ok(paths) = lower_spec_proposition_at_state_without_range_guards(
                &state,
                fact,
                None,
                &evaluation_assumptions,
                &mut budget,
            ) else {
                return None;
            };
            let [path] = paths.as_slice() else {
                next_pending.push(fact);
                continue;
            };
            if !path.obligations.iter().all(|obligation| {
                if required_obligation_is_exactly_discharged(
                    &fact_assumptions,
                    obligation.proposition(),
                ) {
                    return true;
                }
                let Proposition::CMemoryLoadable {
                    memory: obligation_memory,
                    base,
                    bytes,
                } = obligation.proposition()
                else {
                    return false;
                };
                memory_snapshots_proven_equal_at_pointer(
                    obligation_memory,
                    memory,
                    base,
                    &fact_assumptions,
                ) && bytes.as_const().is_some_and(|bytes| {
                    resource_context_has_read(resources, base, bytes, &fact_assumptions)
                })
            }) {
                next_pending.push(fact);
                continue;
            }
            for obligation in &path.obligations {
                fact_assumptions =
                    fact_assumptions.assume_proposition(obligation.proposition().clone());
            }
            for path_fact in &path.facts {
                let proposition = path_fact.proposition().clone();
                if !result.contains(&proposition) {
                    result.push(proposition.clone());
                }
                fact_assumptions = fact_assumptions.assume_proposition(proposition);
            }
            if !result.contains(&path.proposition) {
                result.push(path.proposition.clone());
            }
            fact_assumptions = fact_assumptions.assume_proposition(path.proposition.clone());
            made_progress = true;
        }
        if !made_progress {
            return None;
        }
        pending = next_pending;
    }
    Some(result)
}

/// Whether a body outcome establishes every resource the contract returns,
/// by the rule contract certification applies to a `produces` claim: each
/// returned resource, read as one jointly returned context, is satisfied by
/// the body's returned context definitionally, so a composite whose pieces
/// and facts the body holds counts as returned, and a duplicable body such
/// as a view yields any quantity, while a consumed cell the body no longer
/// holds does not.
pub(super) fn function_return_resources_definitionally_established(
    caller_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    outcome: &CFunctionOutcome,
    assumptions: &PureFactContext,
) -> bool {
    let CFunctionOutcome::Return {
        value,
        state: return_state,
    } = outcome
    else {
        return false;
    };
    let Some(argument_values) = arguments
        .iter()
        .map(|argument| match argument {
            CExpression::Value(value) => Some(value.clone()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()
    else {
        return false;
    };
    let Some(callee_state) = bind_c_function_arguments(caller_state, function, &argument_values)
    else {
        return false;
    };
    let exit_memory = function_exit_memory(caller_state, return_state, value, function);
    let mut claim_return_state = return_state.clone();
    claim_return_state.set_memory(exit_memory.clone());
    let definitions = function.composite_resource_definitions();
    let Some(post_resources) = expand_all_composite_resource_facts(
        claim_return_state.resources(),
        definitions,
        claim_return_state.memory(),
        assumptions,
    ) else {
        return false;
    };
    let Ok(post_resource_facts) = post_resources.observable_facts(assumptions) else {
        return false;
    };
    let assumptions = assumptions_with_propositions(assumptions, &post_resource_facts);
    let mut post_state = callee_state.with_memory(exit_memory);
    post_state.resources = post_resources;
    post_state.counted_populations = return_state.counted_populations.clone();
    if function.return_type() != CType::Void {
        post_state
            .locals
            .set_typed("result".to_string(), value.clone(), function.return_type());
    }
    let mut budget = ExecutionBudget::beside_live_state();
    let entry_resource_state =
        with_contract_argument_views(caller_state, function, &argument_values);
    let Ok(Ok(expected)) = evaluate_function_return_resource_context(
        function,
        &entry_resource_state,
        &post_state,
        function.resource_ensures().len(),
        &assumptions,
        &mut budget,
    ) else {
        return false;
    };
    expected.facts().iter().all(|fact| {
        resource_context_satisfies_definitional_fact(
            claim_return_state.resources(),
            fact,
            definitions,
            claim_return_state.memory(),
            &assumptions,
        )
    })
}

pub(super) fn resource_context_satisfies_definitional_fact(
    available: &ResourceContext,
    required: &CResourceFact,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &PureFactContext,
) -> bool {
    if available.satisfies_fact(required, assumptions) {
        return true;
    }
    let Some(available) =
        expand_all_composite_resource_facts(available, definitions, memory, assumptions)
    else {
        return false;
    };
    let required_context = ResourceContext::new().unchecked_with_fact(required.clone());
    let Some(required) =
        expand_all_composite_resource_facts(&required_context, definitions, memory, assumptions)
    else {
        return false;
    };
    required
        .facts()
        .iter()
        .all(|fact| available.satisfies_fact(fact, assumptions))
}

/// True when every element of a constant-bounded memory range is concretely
/// loadable, so a view of it is represented by the materialized cells rather
/// than a resource fact.
fn view_range_concretely_loadable(memory: &CMemory, range: &CMemoryRange) -> bool {
    let (Some(start), Some(end)) = (range.start().as_const(), range.end().as_const()) else {
        return false;
    };
    if end <= start || end - start > 64 {
        return false;
    }
    let width = match &range.base().offset {
        PointerOffsetTerm::Int32Scaled { byte_width, .. } => {
            u32::try_from(*byte_width).unwrap_or(4)
        }
        _ => 4,
    };
    (start..end).all(|index| {
        let pointer = Pointer {
            block: range.base().block.clone(),
            offset: PointerOffsetTerm::add(
                range.base().offset.clone(),
                PointerOffsetTerm::scale_int32(Bitvector32Term::Constant(index), i64::from(width)),
            ),
        };
        memory.is_loadable_concretely(&pointer, width)
    })
}

fn consume_resource_fact_definitionally(
    available: &ResourceContext,
    required: &CResourceFact,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &PureFactContext,
) -> Option<ResourceContext> {
    fn consume(
        available: &ResourceContext,
        required: &CResourceFact,
        definitions: &[CCompositeResourceDefinition],
        memory: &CMemory,
        assumptions: &PureFactContext,
        seen: &mut BTreeSet<(ResourceContext, CResourceFact)>,
    ) -> Option<ResourceContext> {
        if !seen.insert((available.clone(), required.clone())) {
            return None;
        }
        // A view of memory the caller has concretely materialized is freely
        // satisfiable: read access is represented by the materialized cells,
        // mirroring the local-block view rule at call transfer.
        if let CResourceFact::View(CResource::Memory(range)) = required
            && view_range_concretely_loadable(memory, range)
        {
            return Some(available.clone());
        }
        let direct_remaining = crate::instrumentation::measure_operation(
            "kernel",
            "resource containment",
            "resource containment: direct consumption",
            || {
                available
                    .clone()
                    .without_fact_delaying_normalization(required, assumptions)
            },
        );
        if let Some(remaining) = direct_remaining {
            return Some(remaining);
        }
        let normalized = crate::instrumentation::measure_operation(
            "kernel",
            "resource containment",
            "resource containment: normalization",
            || available.clone().normalized(assumptions),
        );
        if &normalized != available
            && let Some(remaining) =
                normalized.without_fact_delaying_normalization(required, assumptions)
        {
            return Some(remaining);
        }

        let required_context = ResourceContext::new().unchecked_with_fact(required.clone());
        if let Some(expanded_required) = crate::instrumentation::measure_operation(
            "kernel",
            "resource containment",
            "resource containment: expand required",
            || {
                expand_composite_resource_fact(
                    &required_context,
                    required,
                    definitions,
                    memory,
                    assumptions,
                )
            },
        ) {
            let mut remaining = available.clone();
            for child in expanded_required.facts() {
                remaining = consume(&remaining, child, definitions, memory, assumptions, seen)?;
            }
            return Some(remaining);
        }

        for composite in available
            .facts()
            .iter()
            .filter(|fact| matches!(fact.resource(), CResource::Composite { .. }))
        {
            let Some(expanded_available) = crate::instrumentation::measure_operation(
                "kernel",
                "resource containment",
                "resource containment: expand available",
                || {
                    expand_composite_resource_fact(
                        available,
                        composite,
                        definitions,
                        memory,
                        assumptions,
                    )
                },
            ) else {
                continue;
            };
            if let Some(remaining) = consume(
                &expanded_available,
                required,
                definitions,
                memory,
                assumptions,
                seen,
            ) {
                return Some(remaining);
            }
        }
        None
    }

    consume(
        available,
        required,
        definitions,
        memory,
        assumptions,
        &mut BTreeSet::new(),
    )
}

pub(super) fn resource_context_definitionally_contains(
    available: &ResourceContext,
    required: &ResourceContext,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &PureFactContext,
) -> bool {
    let mut remaining = available.clone();
    let mut required = required.facts().to_vec();
    required.sort_by_key(resource_fact_transfer_priority);
    for fact in &required {
        let Some(next) = consume_resource_fact_definitionally(
            &remaining,
            fact,
            definitions,
            memory,
            assumptions,
        ) else {
            return false;
        };
        remaining = next;
    }
    true
}

pub(super) fn resource_contexts_definitionally_equivalent_by_consumption(
    left: &ResourceContext,
    right: &ResourceContext,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &PureFactContext,
) -> bool {
    resource_context_definitionally_contains(left, right, definitions, memory, assumptions)
        && resource_context_definitionally_contains(right, left, definitions, memory, assumptions)
}

pub(crate) fn evaluate_function_resource_context(
    state: &CState,
    resources: &[CResourceSpec],
    definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ResourceContext, CRuntimeError>> {
    evaluate_function_resource_context_with_metadata(
        state,
        resources,
        definitions,
        assumptions,
        budget,
    )
    .map(|result| result.map(|(context, _)| context))
}

/// Evaluate a resource section once and retain the source metadata alongside
/// each checked fact.  The ordinary context API below is a compatibility view
/// for callers that only need algebraic containment; transition/effect code
/// must use this provenance-bearing result.
pub(crate) fn evaluate_function_resource_context_with_metadata(
    state: &CState,
    resources: &[CResourceSpec],
    definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<(ResourceContext, Vec<CCheckedResourceFact>), CRuntimeError>> {
    evaluate_function_resource_context_with_normalization(
        state,
        resources,
        definitions,
        assumptions,
        budget,
        true,
    )
}

fn evaluate_function_resource_context_with_normalization(
    state: &CState,
    resources: &[CResourceSpec],
    definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    normalize: bool,
) -> ExecutionResult<Result<(ResourceContext, Vec<CCheckedResourceFact>), CRuntimeError>> {
    let evaluated = match evaluate_resource_clauses_against_whole_section(
        state,
        resources,
        definitions,
        assumptions,
        budget,
    )? {
        Ok(evaluated) => evaluated,
        Err(error) => return Ok(Err(error)),
    };
    let mut context = ResourceContext::new();
    let checked = evaluated;
    for resource in &checked {
        // Instance rewrites retain the declared memory pieces so folding does
        // not need to normalize an ambient block just to consume those pieces.
        let composed = if normalize {
            context.try_compose_with_fact(resource.fact.clone(), assumptions)
        } else {
            context.try_compose_into_valid_context_delaying_normalization(
                [resource.fact.clone()],
                assumptions,
            )
        };
        context = match composed {
            Ok(context) => context,
            Err(error) => return Ok(Err(resource_context_runtime_error(error))),
        };
    }
    Ok(Ok((context, checked)))
}

/// Evaluates one contract section's resource clauses against the loadability
/// the whole section supplies, and returns their resources in source order.
///
/// A base load in one clause may read a cell any other clause of the same
/// section owns or views, including a cell inside a folded composite, exactly
/// as a `requires` clause may. The first pass walks the clauses in source
/// order. If it leaves clauses unevaluated, the successful portion is expanded
/// once and the missing-resource edges recorded by each failed clause drive an
/// indexed event queue. A newly supplied memory fact therefore wakes only its
/// dependent clauses; no fixed-point round rescans all pending clauses.
///
/// Each clause contributes its resource exactly once: a clause that evaluates
/// is never revisited, and the caller composes the results once, in source
/// order. Retrying a clause that has not yet produced a resource cannot
/// double-count authority.
///
/// Clauses that no order evaluates are refused by name. That is the honest
/// verdict for a dependency cycle between two clauses and for two clauses that
/// are independently unevaluable; either way the user needs both positions.
fn evaluate_resource_clauses_against_whole_section(
    state: &CState,
    resources: &[CResourceSpec],
    definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<Vec<CCheckedResourceFact>, CRuntimeError>> {
    let mut evaluated: Vec<Option<CResourceFact>> = vec![None; resources.len()];
    let mut supplied: Vec<CResourceFact> = Vec::new();
    let mut failures: Vec<Option<CRuntimeError>> = vec![None; resources.len()];
    let mut dependencies: Vec<Vec<CResourceFact>> = vec![Vec::new(); resources.len()];
    let mut waiters = ResourceClauseWaiterIndex::default();
    for (index, resource) in resources.iter().enumerate() {
        let evaluation_state = state.clone().with_resource_context(
            state
                .resources()
                .clone()
                .unchecked_with_facts(supplied.iter().cloned()),
        );
        let (outcome, missing) = evaluate_resource_clause_with_dependencies(
            &evaluation_state,
            resource,
            assumptions,
            budget,
        )?;
        match outcome {
            Ok(resource) => {
                supplied.push(resource.clone());
                evaluated[index] = Some(resource);
            }
            Err(error) => {
                failures[index] = Some(error);
                resource_clause_register_waiters(index, missing, &mut dependencies, &mut waiters);
            }
        }
    }
    let mut section_supply =
        resource_clause_section_supply(state, &supplied, definitions, assumptions);
    let mut pending = VecDeque::new();
    let mut queued = vec![false; resources.len()];
    for index in 0..resources.len() {
        if evaluated[index].is_none()
            && dependencies[index]
                .iter()
                .any(|dependency| section_supply.satisfies_fact(dependency, assumptions))
        {
            queued[index] = true;
            pending.push_back(index);
        }
    }
    while let Some(index) = pending.pop_front() {
        queued[index] = false;
        if evaluated[index].is_some() {
            continue;
        }
        resource_clause_unregister_waiters(index, &mut dependencies, &mut waiters);
        let evaluation_state = state.clone().with_resource_context(section_supply.clone());
        let (outcome, missing) = evaluate_resource_clause_with_dependencies(
            &evaluation_state,
            &resources[index],
            assumptions,
            budget,
        )?;
        match outcome {
            Ok(resource) => {
                let (next_supply, newly_supplied) = resource_clause_supply_with_fact(
                    section_supply,
                    resource.clone(),
                    definitions,
                    state.memory(),
                    assumptions,
                );
                section_supply = next_supply;
                supplied.push(resource.clone());
                evaluated[index] = Some(resource);
                failures[index] = None;
                for fact in newly_supplied {
                    resource_clause_enqueue_waiters(
                        &fact,
                        assumptions,
                        &section_supply,
                        &evaluated,
                        &mut queued,
                        &mut pending,
                        &dependencies,
                        &waiters,
                    );
                }
            }
            Err(error) => {
                failures[index] = Some(error);
                resource_clause_register_waiters(index, missing, &mut dependencies, &mut waiters);
            }
        }
    }
    // A clause refused for its own shape is reported at its own position: no
    // other clause's authority was ever going to repair it, so naming a pair
    // would send the user to a clause that is fine.
    let unresolved = evaluated
        .iter()
        .enumerate()
        .filter_map(|(index, resource)| resource.is_none().then_some(index))
        .collect::<Vec<_>>();
    let refused = unresolved
        .iter()
        .copied()
        .filter(|index| {
            let error = failures[*index].as_ref();
            let awaits = !dependencies[*index].is_empty()
                || error.is_some_and(resource_clause_failure_awaits_supply);
            !awaits
        })
        .min_by_key(|index| resource_clause_position(resources, *index));
    if let Some(index) = refused.or_else(|| {
        unresolved
            .iter()
            .copied()
            .min_by_key(|index| resource_clause_position(resources, *index))
    }) {
        let error = failures[index]
            .take()
            .unwrap_or_else(|| CRuntimeError::FunctionContract("unevaluated".to_string()));
        let cycle = refused
            .is_none()
            .then(|| {
                let source_index = resource_clause_position(resources, index).0;
                unresolved
                    .iter()
                    .copied()
                    .filter(|other| {
                        *other != index
                            && resource_clause_position(resources, *other).0 != source_index
                    })
                    .min_by_key(|other| resource_clause_position(resources, *other))
                    .map(|other| (index, other))
            })
            .flatten();
        return Ok(Err(match cycle {
            Some((index, other)) => {
                resource_clause_cycle_runtime_error(error, index, other, resources)
            }
            None => resource_clause_runtime_error(error, index, resources),
        }));
    }
    Ok(Ok(evaluated
        .into_iter()
        .enumerate()
        .filter_map(|(index, fact)| {
            fact.map(|fact| CCheckedResourceFact {
                fact,
                role: resources[index].role(),
                snapshot: resources[index].snapshot(),
                clause_position: resources[index].clause_position(),
            })
        })
        .collect()))
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum ResourceClauseDependencyKey {
    Fact(CResourceFact),
    MemoryBase(Pointer),
    MemoryBlock(PointerBlock),
}

/// A sparse segment-tree coordinate space for a concrete memory block.
///
/// The range bounds are normalized to the block's physical byte coordinate,
/// using the pointer base's proven constant byte offset and checked element
/// widths.  Keeping the base out of the key is what lets a clause based at
/// `p + 2` wake a clause based at `p`, while refusing to compare symbolic
/// pointer offsets.  A non-concrete base or bound uses the bounded block/base
/// fallback below instead.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ResourceClauseIntervalSpace {
    block: PointerBlock,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ResourceClauseIntervalNode {
    space: ResourceClauseIntervalSpace,
    /// `level` is the base-2 logarithm of the node's byte span.  The root
    /// is level 32 and the leaves are level 0; no node represents individual
    /// cells outside this fixed-depth index.
    level: u8,
    start: u32,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ResourceClauseIntervalWaiter {
    clause: usize,
    dependency: usize,
}

#[derive(Default)]
struct ResourceClauseIntervalIndex {
    exact: BTreeMap<ResourceClauseIntervalNode, BTreeSet<ResourceClauseIntervalWaiter>>,
    /// Subtree aggregates are used only when a query fully covers a node.
    /// Partial queries follow their two boundary paths, so a tiny supplied
    /// range never reads the root aggregate and never wakes every waiter in a
    /// block.  Each update touches at most 33 ancestors per canonical range
    /// node, independent of the number of memory cells in that range.
    subtree: BTreeMap<ResourceClauseIntervalNode, BTreeSet<ResourceClauseIntervalWaiter>>,
}

#[derive(Default)]
struct ResourceClauseWaiterIndex {
    coarse: BTreeMap<ResourceClauseDependencyKey, BTreeSet<usize>>,
    /// Concrete waiters also have a block-local fallback entry.  It is used
    /// only when the *supplied* memory fact cannot be normalized to a
    /// concrete interval: a symbolic event has no interval key to query, but
    /// its explicit block is still a sound conservative candidate boundary.
    /// Store the dependency index as well as the clause so register/remove
    /// stay symmetric when one clause waits on multiple ranges in a block.
    concrete_block_fallback: BTreeMap<PointerBlock, BTreeSet<ResourceClauseIntervalWaiter>>,
    intervals: ResourceClauseIntervalIndex,
}

/// Returns a concrete, block-relative byte interval when the base and both
/// bounds have a checked signed integer interpretation.  The interval index
/// is deliberately conservative: ranges that cannot be normalized into the
/// fixed 32-bit coordinate universe remain on the symbolic block/base path.
fn resource_clause_concrete_memory_interval(
    range: &CMemoryRange,
) -> Option<(ResourceClauseIntervalSpace, i64, i64)> {
    let (start, end) = crate::kernel::primitives::concrete_memory_range_bounds(range)?;
    if start >= end {
        return None;
    }
    Some((
        ResourceClauseIntervalSpace {
            block: range.base().block.clone(),
        },
        start,
        end,
    ))
}

fn resource_clause_biased_coordinate(value: i64) -> Option<u64> {
    (i64::from(i32::MIN)..=i64::from(i32::MAX))
        .contains(&value)
        .then_some((value - i64::from(i32::MIN)) as u64)
}

fn resource_clause_interval_node_start(coordinate: u64, level: u8) -> u32 {
    if level >= 32 {
        0
    } else {
        ((coordinate >> level) << level) as u32
    }
}

fn resource_clause_interval_node(
    space: &ResourceClauseIntervalSpace,
    level: u8,
    start: u32,
) -> ResourceClauseIntervalNode {
    ResourceClauseIntervalNode {
        space: space.clone(),
        level,
        start,
    }
}

/// Canonical segment-tree decomposition of `[start, end)`.  A range is
/// represented by O(32) aligned nodes, rather than by its cells.
fn resource_clause_interval_nodes(
    space: &ResourceClauseIntervalSpace,
    start: i64,
    end: i64,
) -> Option<Vec<ResourceClauseIntervalNode>> {
    let mut start = resource_clause_biased_coordinate(start)?;
    let end = resource_clause_biased_coordinate(end)?;
    if start >= end {
        return None;
    }
    let mut nodes = Vec::new();
    while start < end {
        let alignment = if start == 0 {
            32
        } else {
            start.trailing_zeros().min(32)
        };
        let remaining = end - start;
        let magnitude = 63 - remaining.leading_zeros();
        let level = alignment.min(magnitude).min(32) as u8;
        let node_start = resource_clause_interval_node_start(start, level);
        nodes.push(resource_clause_interval_node(space, level, node_start));
        start += 1u64 << level;
    }
    Some(nodes)
}

fn resource_clause_interval_node_ancestors(
    node: &ResourceClauseIntervalNode,
) -> Vec<ResourceClauseIntervalNode> {
    (node.level..=32)
        .map(|level| {
            resource_clause_interval_node(
                &node.space,
                level,
                resource_clause_interval_node_start(u64::from(node.start), level),
            )
        })
        .collect()
}

fn resource_clause_interval_node_bounds(node: &ResourceClauseIntervalNode) -> (u64, u64) {
    let start = u64::from(node.start);
    (start, start + (1u64 << node.level))
}

impl ResourceClauseIntervalIndex {
    fn insert(
        &mut self,
        waiter: ResourceClauseIntervalWaiter,
        space: &ResourceClauseIntervalSpace,
        start: i64,
        end: i64,
    ) {
        let Some(nodes) = resource_clause_interval_nodes(space, start, end) else {
            return;
        };
        for node in nodes {
            self.exact
                .entry(node.clone())
                .or_default()
                .insert(waiter.clone());
            for ancestor in resource_clause_interval_node_ancestors(&node) {
                self.subtree
                    .entry(ancestor)
                    .or_default()
                    .insert(waiter.clone());
            }
        }
    }

    fn remove(
        &mut self,
        waiter: &ResourceClauseIntervalWaiter,
        space: &ResourceClauseIntervalSpace,
        start: i64,
        end: i64,
    ) {
        let Some(nodes) = resource_clause_interval_nodes(space, start, end) else {
            return;
        };
        for node in nodes {
            let remove_exact = self.exact.get_mut(&node).is_some_and(|waiters| {
                waiters.remove(waiter);
                waiters.is_empty()
            });
            if remove_exact {
                self.exact.remove(&node);
            }
            for ancestor in resource_clause_interval_node_ancestors(&node) {
                let remove_subtree = self.subtree.get_mut(&ancestor).is_some_and(|waiters| {
                    waiters.remove(waiter);
                    waiters.is_empty()
                });
                if remove_subtree {
                    self.subtree.remove(&ancestor);
                }
            }
        }
    }

    fn add_candidates(
        waiters: &BTreeSet<ResourceClauseIntervalWaiter>,
        candidates: &mut BTreeSet<usize>,
    ) {
        candidates.extend(waiters.iter().map(|waiter| waiter.clause));
    }

    fn query_node(
        &self,
        node: &ResourceClauseIntervalNode,
        query_start: u64,
        query_end: u64,
        candidates: &mut BTreeSet<usize>,
    ) {
        let (node_start, node_end) = resource_clause_interval_node_bounds(node);
        if node_end <= query_start || query_end <= node_start {
            return;
        }
        if let Some(waiters) = self.exact.get(node) {
            Self::add_candidates(waiters, candidates);
        }
        if query_start <= node_start && node_end <= query_end {
            if let Some(waiters) = self.subtree.get(node) {
                Self::add_candidates(waiters, candidates);
            }
            return;
        }
        if node.level == 0 {
            return;
        }
        let child_level = node.level - 1;
        let left = resource_clause_interval_node(&node.space, child_level, node.start);
        let right_start = (u64::from(node.start) + (1u64 << child_level)) as u32;
        let right = resource_clause_interval_node(&node.space, child_level, right_start);
        self.query_node(&left, query_start, query_end, candidates);
        self.query_node(&right, query_start, query_end, candidates);
    }

    fn candidates_for_fact(&self, fact: &CResourceFact) -> BTreeSet<usize> {
        let mut candidates = BTreeSet::new();
        let Some(range) = fact.memory_range() else {
            return candidates;
        };
        let Some((space, start, end)) = resource_clause_concrete_memory_interval(range) else {
            return candidates;
        };
        let Some(query_start) = resource_clause_biased_coordinate(start) else {
            return candidates;
        };
        let Some(query_end) = resource_clause_biased_coordinate(end) else {
            return candidates;
        };
        let root = resource_clause_interval_node(&space, 32, 0);
        self.query_node(&root, query_start, query_end, &mut candidates);
        candidates
    }
}

fn resource_clause_coarse_keys(fact: &CResourceFact) -> Vec<ResourceClauseDependencyKey> {
    let mut keys = vec![ResourceClauseDependencyKey::Fact(fact.clone())];
    if let Some(range) = fact.memory_range() {
        keys.push(ResourceClauseDependencyKey::MemoryBase(
            range.base().clone(),
        ));
        keys.push(ResourceClauseDependencyKey::MemoryBlock(
            range.base().block.clone(),
        ));
    }
    keys
}

impl ResourceClauseWaiterIndex {
    fn register(&mut self, clause: usize, dependencies: &[CResourceFact]) {
        for (dependency_index, dependency) in dependencies.iter().enumerate() {
            if let Some((space, start, end)) = dependency
                .memory_range()
                .and_then(resource_clause_concrete_memory_interval)
            {
                let waiter = ResourceClauseIntervalWaiter {
                    clause,
                    dependency: dependency_index,
                };
                self.coarse
                    .entry(ResourceClauseDependencyKey::Fact(dependency.clone()))
                    .or_default()
                    .insert(clause);
                self.concrete_block_fallback
                    .entry(space.block.clone())
                    .or_default()
                    .insert(waiter.clone());
                self.intervals.insert(waiter, &space, start, end);
            } else {
                for key in resource_clause_coarse_keys(dependency) {
                    self.coarse.entry(key).or_default().insert(clause);
                }
            }
        }
    }

    fn unregister(&mut self, clause: usize, dependencies: &[CResourceFact]) {
        for (dependency_index, dependency) in dependencies.iter().enumerate() {
            if let Some((space, start, end)) = dependency
                .memory_range()
                .and_then(resource_clause_concrete_memory_interval)
            {
                let waiter = ResourceClauseIntervalWaiter {
                    clause,
                    dependency: dependency_index,
                };
                let key = ResourceClauseDependencyKey::Fact(dependency.clone());
                let remove_key = self.coarse.get_mut(&key).is_some_and(|clauses| {
                    clauses.remove(&clause);
                    clauses.is_empty()
                });
                if remove_key {
                    self.coarse.remove(&key);
                }
                let remove_block = self
                    .concrete_block_fallback
                    .get_mut(&space.block)
                    .is_some_and(|waiters| {
                        waiters.remove(&waiter);
                        waiters.is_empty()
                    });
                if remove_block {
                    self.concrete_block_fallback.remove(&space.block);
                }
                self.intervals.remove(&waiter, &space, start, end);
            } else {
                for key in resource_clause_coarse_keys(dependency) {
                    let remove_key = self.coarse.get_mut(&key).is_some_and(|clauses| {
                        clauses.remove(&clause);
                        clauses.is_empty()
                    });
                    if remove_key {
                        self.coarse.remove(&key);
                    }
                }
            }
        }
    }

    fn candidates_for_supplied(&self, supplied: &CResourceFact) -> BTreeSet<usize> {
        let mut candidates = self.intervals.candidates_for_fact(supplied);
        // Concrete supplied facts use only exact/interval events.  The
        // fallback below is deliberately reserved for symbolic or otherwise
        // un-normalizable supplied memory: scanning concrete waiters in one
        // explicit symbolic block event is conservative and bounded by that
        // event's block-local waiter set, while concrete same-block events
        // retain their interval-sensitive work curve.
        if supplied
            .memory_range()
            .and_then(resource_clause_concrete_memory_interval)
            .is_none()
            && let Some(range) = supplied.memory_range()
            && let Some(waiters) = self.concrete_block_fallback.get(&range.base().block)
        {
            ResourceClauseIntervalIndex::add_candidates(waiters, &mut candidates);
        }
        for key in resource_clause_coarse_keys(supplied) {
            if let Some(clauses) = self.coarse.get(&key) {
                candidates.extend(clauses.iter().copied());
            }
        }
        candidates
    }
}

fn resource_clause_register_waiters(
    index: usize,
    missing: Vec<CResourceFact>,
    dependencies: &mut [Vec<CResourceFact>],
    waiters: &mut ResourceClauseWaiterIndex,
) {
    let mut unique = Vec::new();
    for dependency in missing {
        if unique.contains(&dependency) {
            continue;
        }
        unique.push(dependency.clone());
    }
    waiters.register(index, &unique);
    dependencies[index] = unique;
}

fn resource_clause_unregister_waiters(
    index: usize,
    dependencies: &mut [Vec<CResourceFact>],
    waiters: &mut ResourceClauseWaiterIndex,
) {
    let previous = std::mem::take(&mut dependencies[index]);
    waiters.unregister(index, &previous);
}

fn resource_clause_enqueue_waiters(
    supplied: &CResourceFact,
    assumptions: &PureFactContext,
    section_supply: &ResourceContext,
    evaluated: &[Option<CResourceFact>],
    queued: &mut [bool],
    pending: &mut VecDeque<usize>,
    dependencies: &[Vec<CResourceFact>],
    waiters: &ResourceClauseWaiterIndex,
) {
    let candidates = waiters.candidates_for_supplied(supplied);
    for index in candidates {
        if evaluated[index].is_none()
            && !queued[index]
            && dependencies[index]
                .iter()
                .any(|dependency| section_supply.satisfies_fact(dependency, assumptions))
        {
            queued[index] = true;
            pending.push_back(index);
        }
    }
}

#[cfg(test)]
mod resource_clause_worklist_tests {
    use super::*;

    #[test]
    fn adjacent_supply_wakes_wide_memory_waiter() {
        let base = Pointer {
            block: PointerBlock::Concrete("resource-clause-adjacent".to_string()),
            offset: PointerOffsetTerm::Constant(0),
        };
        let wide = CResourceFact::view_memory(CMemoryRange::new(
            base.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(2),
        ));
        let left = CResourceFact::view_memory(CMemoryRange::new(
            base.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        ));
        let right = CResourceFact::view_memory(CMemoryRange::new(
            base,
            Bitvector32Term::Constant(1),
            Bitvector32Term::Constant(2),
        ));
        let assumptions = PureFactContext::new();
        let mut dependencies = vec![Vec::new()];
        let mut waiters = ResourceClauseWaiterIndex::default();
        resource_clause_register_waiters(0, vec![wide.clone()], &mut dependencies, &mut waiters);
        let evaluated = vec![None];
        let mut queued = vec![false];
        let mut pending = VecDeque::new();
        let section_supply = ResourceContext::new().unchecked_with_fact(left.clone());

        assert!(!section_supply.satisfies_fact(&wide, &assumptions));
        resource_clause_enqueue_waiters(
            &left,
            &assumptions,
            &section_supply,
            &evaluated,
            &mut queued,
            &mut pending,
            &dependencies,
            &waiters,
        );
        assert!(pending.is_empty());

        let section_supply = section_supply.unchecked_with_fact(right.clone());
        assert!(section_supply.satisfies_fact(&wide, &assumptions));
        resource_clause_enqueue_waiters(
            &right,
            &assumptions,
            &section_supply,
            &evaluated,
            &mut queued,
            &mut pending,
            &dependencies,
            &waiters,
        );
        assert_eq!(pending, VecDeque::from([0]));
    }

    /// Same-block disjoint ranges have one real dependency edge apiece.  The
    /// interval index must visit those edges, not every waiter sharing the
    /// block key.  The exact candidate count is the regression: the old
    /// `MemoryBlock` index would produce `size * size` visits here.
    #[test]
    fn same_block_disjoint_waiters_use_interval_candidates() {
        let base = Pointer {
            block: PointerBlock::Concrete("resource-clause-disjoint".to_string()),
            offset: PointerOffsetTerm::Constant(0),
        };
        let samples = [4_usize, 8, 16, 32]
            .into_iter()
            .map(|size| {
                let mut dependencies = vec![Vec::new(); size];
                let mut waiters = ResourceClauseWaiterIndex::default();
                for index in 0..size {
                    let start = (index * 2) as u32;
                    let dependency = CResourceFact::view_memory(CMemoryRange::new(
                        base.clone(),
                        Bitvector32Term::Constant(start),
                        Bitvector32Term::Constant(start + 1),
                    ));
                    resource_clause_register_waiters(
                        index,
                        vec![dependency],
                        &mut dependencies,
                        &mut waiters,
                    );
                }
                let mut candidate_visits = 0;
                for index in 0..size {
                    let start = (index * 2) as u32;
                    let supplied = CResourceFact::view_memory(CMemoryRange::new(
                        base.clone(),
                        Bitvector32Term::Constant(start),
                        Bitvector32Term::Constant(start + 1),
                    ));
                    let candidates = waiters.candidates_for_supplied(&supplied);
                    candidate_visits += candidates.len();
                    assert_eq!(
                        candidates.into_iter().collect::<Vec<_>>(),
                        vec![index],
                        "a disjoint supplied range woke unrelated same-block waiters: size={size} index={index}"
                    );
                }
                (size, candidate_visits)
            })
            .collect::<Vec<_>>();
        assert_eq!(
            samples,
            vec![(4, 4), (8, 8), (16, 16), (32, 32)],
            "same-block interval candidate work should follow actual dependency edges"
        );
    }

    #[test]
    fn comparable_constant_bases_share_interval_space() {
        let block = PointerBlock::Concrete("resource-clause-base-aware".to_string());
        let dependency_base = Pointer {
            block: block.clone(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let supplied_base = Pointer {
            block,
            offset: PointerOffsetTerm::Constant(8),
        };
        let dependency = CResourceFact::view_memory(CMemoryRange::new(
            dependency_base,
            Bitvector32Term::Constant(2),
            Bitvector32Term::Constant(3),
        ));
        let supplied = CResourceFact::view_memory(CMemoryRange::new(
            supplied_base,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        ));
        let mut dependencies = vec![Vec::new()];
        let mut waiters = ResourceClauseWaiterIndex::default();
        resource_clause_register_waiters(0, vec![dependency], &mut dependencies, &mut waiters);
        assert_eq!(
            waiters.candidates_for_supplied(&supplied),
            BTreeSet::from([0])
        );
    }

    #[test]
    fn concrete_memory_waiters_share_physical_byte_space_across_widths() {
        let base = Pointer {
            block: PointerBlock::Concrete("resource-clause-byte-space".to_string()),
            offset: PointerOffsetTerm::Constant(0),
        };
        let dependency = CResourceFact::view_memory(CMemoryRange::new_with_element_width(
            base.clone(),
            Bitvector32Term::Constant(8),
            Bitvector32Term::Constant(12),
            1,
        ));
        let supplied = CResourceFact::view_memory(CMemoryRange::new_with_element_width(
            base,
            Bitvector32Term::Constant(2),
            Bitvector32Term::Constant(3),
            4,
        ));
        let mut dependencies = vec![Vec::new()];
        let mut waiters = ResourceClauseWaiterIndex::default();
        resource_clause_register_waiters(0, vec![dependency], &mut dependencies, &mut waiters);
        assert_eq!(
            waiters.candidates_for_supplied(&supplied),
            BTreeSet::from([0])
        );
    }

    #[test]
    fn symbolic_memory_waiters_keep_conservative_block_fallback() {
        let base = Pointer {
            block: PointerBlock::Concrete("resource-clause-symbolic".to_string()),
            offset: PointerOffsetTerm::Constant(0),
        };
        let dependency = CResourceFact::view_memory(CMemoryRange::new(
            base.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Variable(Variable(9_901)),
        ));
        let supplied = CResourceFact::view_memory(CMemoryRange::new(
            base,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        ));
        let mut dependencies = vec![Vec::new()];
        let mut waiters = ResourceClauseWaiterIndex::default();
        resource_clause_register_waiters(0, vec![dependency], &mut dependencies, &mut waiters);
        assert_eq!(
            waiters.candidates_for_supplied(&supplied),
            BTreeSet::from([0])
        );
    }

    #[test]
    fn concrete_waiter_block_fallback_registers_and_unregisters_symmetrically() {
        let base = Pointer {
            block: PointerBlock::Concrete("resource-clause-fallback-lifetime".to_string()),
            offset: PointerOffsetTerm::Constant(0),
        };
        let dependency = CResourceFact::view_memory(CMemoryRange::new(
            base.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        ));
        let symbolic_supplied = CResourceFact::view_memory(CMemoryRange::new(
            base,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Variable(Variable(9_902)),
        ));
        let mut dependencies = vec![Vec::new()];
        let mut waiters = ResourceClauseWaiterIndex::default();
        resource_clause_register_waiters(0, vec![dependency], &mut dependencies, &mut waiters);
        assert_eq!(
            waiters.candidates_for_supplied(&symbolic_supplied),
            BTreeSet::from([0])
        );
        resource_clause_unregister_waiters(0, &mut dependencies, &mut waiters);
        assert!(
            waiters
                .candidates_for_supplied(&symbolic_supplied)
                .is_empty()
        );
    }
}

fn evaluate_resource_clause_with_dependencies(
    state: &CState,
    resource: &CResourceSpec,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<(Result<CResourceFact, CRuntimeError>, Vec<CResourceFact>)> {
    #[cfg(test)]
    record_resource_clause_attempt();
    let (result, dependencies) = capture_resource_dependencies(|| {
        evaluate_function_resource_spec(state, resource, assumptions, budget)
    });
    result.map(|result| (result, dependencies))
}

/// The read authority a section's already-evaluated clauses supply to the
/// clauses that still need one.
///
/// Expansion adds views, never ownership: a folded composite's cells become
/// readable so a later clause's base load denotes, while every owned resource
/// stays exactly where the clause set put it. This state is a scratch
/// evaluation frame and is never the section's result.
fn resource_clause_section_supply(
    state: &CState,
    supplied: &[CResourceFact],
    definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
) -> ResourceContext {
    let base = state
        .resources()
        .clone()
        .unchecked_with_facts(supplied.iter().cloned());
    if definitions.is_empty() {
        return base;
    }
    // A matched instance supplies the cells of the arm this section's
    // premises select, and nothing when they select none (D7). The arm stays
    // folded either way: only its read authority is published here.
    let mut views = instance_arm_views(&base, definitions, state, assumptions);
    let Some(expanded) =
        expand_all_composite_resource_facts(&base, definitions, state.memory(), assumptions)
    else {
        return base.unchecked_with_facts(views);
    };
    views.extend(
        expanded
            .facts()
            .iter()
            .filter_map(|fact| match fact.resource() {
                CResource::Memory(range) => Some(CResourceFact::view_memory(range.clone())),
                _ => None,
            }),
    );
    base.unchecked_with_facts(views)
}

/// What one frontier's premises decide about the folded matched instances a
/// context holds: the single publication point of decision D7.
///
/// `model_facts` are the negative `model != Variant` conclusions of every
/// refuted field-free arm, plus the positive `model == Variant` when
/// refutation leaves exactly one field-free arm. `views` are the cells the
/// decided arm owns, or the cells every surviving arm agrees on. `arm_facts`
/// are the decided arm's own facts that name no constructor binding.
#[derive(Clone, Debug, Default)]
pub(crate) struct ArmPublication {
    pub model_facts: Vec<Proposition>,
    pub views: Vec<CResourceFact>,
    pub arm_facts: Vec<Proposition>,
}

/// Decides the arms of every folded matched instance `context` holds, from the
/// premises in `assumptions` plus the arms' own binding-free facts.
///
/// This is decision D7, and it is decided in exactly one place. Every frontier
/// a proof passes through — contract entry lowering, contract return, a loop
/// head, a loop back edge, a loop exit, a guard conjunct, an `unfold`, a
/// frontier case split — calls this with its own premises and consumes the
/// same publication, so a refutation that fires at one of them fires at all of
/// them. `docs/concepts/resources.md` lists the sites; wiring a mechanism to
/// one site alone is what this function exists to prevent.
///
/// The order inside is the decision's own: refutation first, because a refuted
/// arm is evidence the selection reads, then read authority and the arm's own
/// facts under the premises refutation just established. That is why a guard
/// conjunct that rules out an ascending frame's `Top` arm can read the cell
/// its two surviving arms agree on.
///
/// Bounded exactly as its parts are: one pass over the instances this context
/// holds, and per instance one evaluation of its own body and one of each of
/// its own arms. Nothing project-wide or path-wide is scanned.
pub(crate) fn publish_instance_arms(
    context: &ResourceContext,
    definitions: &[CCompositeResourceDefinition],
    state: &CState,
    assumptions: &PureFactContext,
) -> ArmPublication {
    if definitions.is_empty() {
        return ArmPublication::default();
    }
    let instances = context
        .facts()
        .iter()
        .filter_map(|fact| match fact.resource() {
            CResource::Instance(instance) => Some(instance),
            _ => None,
        })
        .collect::<Vec<_>>();
    let mut published = ArmPublication::default();
    for instance in &instances {
        published.model_facts.extend(instance_arm_model_facts(
            instance,
            definitions,
            state,
            assumptions,
        ));
    }
    let decided = published
        .model_facts
        .iter()
        .cloned()
        .fold(assumptions.clone(), PureFactContext::assume_proposition);
    for instance in &instances {
        published.views.extend(instance_arm_read_authority(
            instance,
            definitions,
            state,
            &decided,
        ));
        published.arm_facts.extend(decided_instance_arm_facts(
            instance,
            definitions,
            state,
            &decided,
        ));
    }
    published
}

/// The read-authority half of [`publish_instance_arms`], for the point inside
/// a frontier where a section's own clauses are being evaluated one at a time.
///
/// A frontier's publication is taken once, on the finished state, and it is
/// what decides models there. While a section is still being evaluated its
/// clauses need only to be addressable, so this publishes the cells the
/// premises already decide and re-decides nothing: refuting every arm of every
/// held instance again per clause would cost the arms of the section rather
/// than the arms of the frontier.
fn instance_arm_views(
    context: &ResourceContext,
    definitions: &[CCompositeResourceDefinition],
    state: &CState,
    assumptions: &PureFactContext,
) -> Vec<CResourceFact> {
    if definitions.is_empty() {
        return Vec::new();
    }
    context
        .facts()
        .iter()
        .filter_map(|fact| match fact.resource() {
            CResource::Instance(instance) => Some(instance),
            _ => None,
        })
        .flat_map(|instance| instance_arm_read_authority(instance, definitions, state, assumptions))
        .collect()
}

/// The cells owned by the match arm this frontier's premises select for
/// `instance`, or by every arm they leave possible, as views.
///
/// This is the read-authority half of decision D7. The decision is
/// [`decide_resource_model_arm`]; what it decides is published as read
/// authority only, so a contract clause or requirement may read a cell a
/// folded matched instance owns exactly as it may read one a folded
/// `if`-bodied composite owns. Ownership is untouched: only an explicit
/// `unfold` moves the arm's cells into the proof state.
///
/// When the premises select no single arm they may still have refuted some,
/// and the arms they leave possible can agree about a cell. `parent != 0`
/// refutes an ascending frame's `Top` arm, and the `Left` and `Right` arms
/// both own `parent->rb_right`, so that cell is readable however the model
/// turns out. What is published is then the intersection of the possible arms'
/// own memory clauses: a cell one possible arm does not own is never
/// published, and an arm whose clauses cannot be evaluated here makes the
/// intersection empty rather than being skipped.
///
/// Cost is the selected arm's own clauses, or one evaluation of each possible
/// arm's clauses. An instance whose model carries no variant evidence at all,
/// or whose arms name a constructor binding in a memory clause, publishes
/// nothing.
fn instance_arm_read_authority(
    instance: &ResourceInstance,
    definitions: &[CCompositeResourceDefinition],
    state: &CState,
    assumptions: &PureFactContext,
) -> Vec<CResourceFact> {
    let Some(definition) = definitions
        .iter()
        .find(|definition| definition.name() == instance.name())
    else {
        return Vec::new();
    };
    let Some(body) = definition.matched.as_ref() else {
        return Vec::new();
    };
    let Some(AlgebraicValue::Algebraic(model)) = instance.fields().get(body.field_index) else {
        return Vec::new();
    };
    let variants = match decide_resource_model_arm(model, assumptions) {
        ResourceModelArmDecision::Selected(selection) => vec![selection.variant().to_owned()],
        ResourceModelArmDecision::Possible(variants) => variants,
        ResourceModelArmDecision::Open => Vec::new(),
    };
    if variants.is_empty() {
        return Vec::new();
    }
    let Ok(evaluation) = instance_body_evaluation(state, instance, definition) else {
        return Vec::new();
    };
    let mut common: Option<Vec<CResourceFact>> = None;
    for variant in &variants {
        let Some(arm) = body.arms.iter().find(|arm| &arm.variant == variant) else {
            return Vec::new();
        };
        let Some(views) = instance_arm_memory_views(&evaluation, arm, assumptions) else {
            return Vec::new();
        };
        common = Some(match common {
            // Order follows the first arm's clauses, so one possible arm and a
            // selected arm publish the same list in the same order.
            Some(common) => common
                .into_iter()
                .filter(|fact| views.contains(fact))
                .collect(),
            None => views,
        });
        if common.as_ref().is_some_and(Vec::is_empty) {
            return Vec::new();
        }
    }
    common.unwrap_or_default()
}

/// The cells one arm's own memory clauses own at `evaluation`, as views, or
/// `None` when those clauses cannot be evaluated there.
fn instance_arm_memory_views(
    evaluation: &CState,
    arm: &CResourceMatchArm,
    assumptions: &PureFactContext,
) -> Option<Vec<CResourceFact>> {
    crate::instrumentation::record_deterministic_work(1);
    let evaluation_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads();
    let mut budget = ExecutionBudget::beside_live_state();
    let Ok(Ok(body_resources)) = evaluate_function_resource_context_with_normalization(
        evaluation,
        &arm.contains,
        &[],
        &evaluation_assumptions,
        &mut budget,
        false,
    ) else {
        return None;
    };
    Some(
        body_resources
            .0
            .facts()
            .iter()
            .filter_map(|fact| match fact.resource() {
                CResource::Memory(range) => Some(CResourceFact::view_memory(range.clone())),
                _ => None,
            })
            .collect(),
    )
}

/// The negation of one already-lowered body fact, in the shape the exact
/// checkers decide.
///
/// A resource body fact lowers to a bare condition in every case this rule
/// acts on, and a bare condition's negation is the same condition at the
/// other truth value; nothing else is turned inside out here.
fn refutation_of_body_fact(proposition: &Proposition) -> Option<Proposition> {
    match proposition {
        Proposition::ConditionIs(condition, value) => {
            Some(Proposition::ConditionIs(condition.clone(), !value))
        }
        _ => None,
    }
}

/// The model facts a context's premises force on the folded matched instances
/// it holds by refuting arms: decision D7 applied to refutation.
///
/// An owned folded instance's body holds wherever the instance is held, so a
/// premise that refutes an arm's own binding-free fact refutes the arm.
/// `root->left != 0` against `tree_at`'s `HeapTree::Empty` arm `fact p == 0`
/// says the child instance's model is not `HeapTree::Empty`; `root->left == 0`
/// against the `Node` arm's `fact p != 0` says it is not a `Node`.
///
/// Two conclusions are published, both as ordinary propositions:
///
/// - `model != Variant` for each refuted arm whose constructor is field-free.
///   That is exactly the `Excluded` evidence [`select_resource_model_arm`]
///   reads, so on a two-constructor model the surviving arm is then selected.
///   An arm with fields has no negative to state, for the same reason
///   `model != Some(3)` leaves `Some` possible.
/// - `model == Variant` when refutation leaves exactly one arm and that arm's
///   constructor is field-free, because then the model has only one value
///   left. This is what gives `unfold` and proof `match` a constructor after
///   a guard has excluded every other arm.
///
/// Only a fact that names no binding of its own arm takes part: a binding is
/// an unknown of the arm, so a fact about one says nothing until the arm is
/// selected. The arm's own `owns` clauses are evaluated first, exactly as arm
/// selection evaluates the selected arm's cells, so a binding-free fact that
/// reads a cell the arm owns has the authority to read it.
///
/// This is a decision, never a search: each held instance's arms are visited
/// once, each arm's own clauses are evaluated once, and the refutation is the
/// exact-fact check. An instance whose model already carries a constructor is
/// skipped. Nothing outside the instances held and their own arms is visited.
///
/// [`publish_instance_arms`] calls this for every instance a frontier's
/// context holds; the two frontiers that are about one instance — the `unfold`
/// that opens it and the case split that eliminates its constructor — call it
/// directly for that instance alone.
pub(in crate::kernel) fn instance_arm_model_facts(
    instance: &ResourceInstance,
    definitions: &[CCompositeResourceDefinition],
    state: &CState,
    assumptions: &PureFactContext,
) -> Vec<Proposition> {
    let Some(definition) = definitions
        .iter()
        .find(|definition| definition.name() == instance.name())
    else {
        return Vec::new();
    };
    let Some(body) = definition.matched.as_ref() else {
        return Vec::new();
    };
    let Some(AlgebraicValue::Algebraic(model)) = instance.fields().get(body.field_index) else {
        return Vec::new();
    };
    // A model that already carries a constructor needs no exclusion, and only
    // a symbolic value has variant evidence at all.
    if !matches!(model.node, AlgebraicTermNode::Variable(_)) {
        return Vec::new();
    }
    // The positive conclusion needs the arms to be the declared variants
    // exactly once each; the negative one does not, but one gate keeps the
    // two readings of "every other arm" the same.
    let variants = model
        .algebraic_type
        .variants
        .iter()
        .map(|variant| variant.name.as_str())
        .collect::<BTreeSet<_>>();
    if variants.len() != body.arms.len()
        || body
            .arms
            .iter()
            .any(|arm| !variants.contains(arm.variant.as_str()))
    {
        return Vec::new();
    }
    let Ok(evaluation) = instance_body_evaluation(state, instance, definition) else {
        return Vec::new();
    };
    let evaluation_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads();
    let constructor = |arm: &CResourceMatchArm| {
        let term = AlgebraicTerm {
            algebraic_type: model.algebraic_type.clone(),
            node: AlgebraicTermNode::Constructor {
                variant: arm.variant.clone(),
                fields: Vec::new(),
            },
        };
        (arm.bindings.is_empty() && term.is_well_formed()).then_some(term)
    };
    let mut published = Vec::new();
    let mut surviving = Vec::new();
    for arm in &body.arms {
        crate::instrumentation::record_deterministic_work(1);
        if !arm_is_refuted_by_a_binding_free_fact(
            &evaluation,
            arm,
            &evaluation_assumptions,
            assumptions,
        ) && !arm_is_refuted_by_a_predicate_fact(
            &evaluation,
            model,
            arm,
            &evaluation_assumptions,
            assumptions,
        ) {
            surviving.push(arm);
            continue;
        }
        let Some(excluded) = constructor(arm) else {
            continue;
        };
        let negation = Proposition::Not(Box::new(Proposition::Equal(
            Term::Algebraic(model.clone()),
            Term::Algebraic(excluded),
        )));
        if !required_obligation_is_exactly_discharged(assumptions, &negation) {
            published.push(negation);
        }
    }
    if let [survivor] = surviving.as_slice()
        && let Some(selected) = constructor(survivor)
    {
        published.push(Proposition::Equal(
            Term::Algebraic(model.clone()),
            Term::Algebraic(selected),
        ));
    }
    published
}

/// Whether a premise fixing a pure predicate's value at this instance's model
/// refutes `arm`.
///
/// This is package A21's rule, and the second half of D7 in reverse. A
/// premise such as an ascent's `invariant ctx_node_is(c.model, parent) == 1`
/// says what one declared function returns at a model this section cannot
/// otherwise name. Evaluating that function's declared body at one arm's
/// constructor answers what it would return if the model were that arm; when
/// the answer contradicts the premise, the model is not that arm.
///
/// The arm's bindings are symbolic and its own body facts are premises of the
/// evaluation, because an owned folded instance's body holds wherever the
/// instance is held: were the model `Context::Left(identity, ..)`, the arm's
/// `fact identity != 0` would hold of that `identity`. So an exit whose guard
/// failed with `parent == 0` refutes the `Left` frame — the frame's node is
/// not null and `parent` is — while the loop head refutes `Context::Top`,
/// whose value is `1` only at a null `parent`.
///
/// Both halves are exact. The predicate's value at the arm is one evaluation
/// of a declared body, never a search, and the contradiction is the exact
/// obligation check against the arm's own premises. Nothing is concluded from
/// a body this kernel cannot evaluate, from an arm whose bindings or clauses
/// it cannot bind, or from a premise of any other shape.
///
/// Cost is the premises about this exact model times this arm's own clauses
/// and one traversal of each named function's declared body. Nothing outside
/// the arm and those premises is visited.
fn arm_is_refuted_by_a_predicate_fact(
    evaluation: &CState,
    model: &AlgebraicTerm,
    arm: &CResourceMatchArm,
    evaluation_assumptions: &PureFactContext,
    assumptions: &PureFactContext,
) -> bool {
    let AlgebraicTermNode::Variable(variable) = &model.node else {
        return false;
    };
    let premises = assumptions
        .algebraic_predicate_facts(*variable)
        .cloned()
        .collect::<Vec<_>>();
    if premises.is_empty() {
        return false;
    }
    let Some(schema) = model
        .algebraic_type
        .variants
        .iter()
        .find(|variant| variant.name == arm.variant)
    else {
        return false;
    };
    if schema.fields.len() != arm.bindings.len() {
        return false;
    }
    let Some(bindings) = symbolic_arm_binding_values(&model.algebraic_type, schema) else {
        return false;
    };
    let constructor = AlgebraicTerm {
        algebraic_type: model.algebraic_type.clone(),
        node: AlgebraicTermNode::Constructor {
            variant: arm.variant.clone(),
            fields: bindings.clone(),
        },
    };
    if !constructor.is_well_formed() {
        return false;
    }
    let Some(arm_assumptions) = arm_premises_at_symbolic_bindings(
        evaluation,
        arm,
        &bindings,
        evaluation_assumptions,
        assumptions,
    ) else {
        return false;
    };
    let mut budget = ExecutionBudget::beside_live_state();
    premises.iter().any(|premise| {
        crate::instrumentation::record_deterministic_work(1);
        predicate_fact_refutes_constructor(
            premise,
            variable,
            &constructor,
            &arm_assumptions,
            &mut budget,
        )
    })
}

/// Whether one predicate premise, read at `constructor` in place of the
/// symbolic model it speaks about, contradicts itself.
fn predicate_fact_refutes_constructor(
    premise: &Proposition,
    variable: &Variable,
    constructor: &AlgebraicTerm,
    arm_assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> bool {
    let Some(fact) = crate::kernel::assumptions::algebraic_predicate_fact(premise) else {
        return false;
    };
    let position = fact.arguments.iter().position(|argument| {
        matches!(
            argument,
            PureFunctionArgument::Algebraic(AlgebraicTerm {
                node: AlgebraicTermNode::Variable(named),
                ..
            }) if named == variable
        )
    });
    let Some(position) = position else {
        return false;
    };
    let Some(arguments) = crate::kernel::pure_functions::arguments_with_algebraic_substitution(
        fact.arguments,
        position,
        constructor.clone(),
    ) else {
        return false;
    };
    let Some(value) = crate::kernel::pure_functions::evaluate_registered_pure_function(
        fact.name,
        &arguments,
        arm_assumptions,
        budget,
    ) else {
        return false;
    };
    let Some(value) = crate::kernel::spec::c_value_bitvector_term(&value) else {
        return false;
    };
    let condition = if fact.wide {
        ConditionTerm::int64_equal(value, fact.constant.clone())
    } else {
        ConditionTerm::equal(value, fact.constant.clone())
    };
    // The premise fixes the application's value; the arm is refuted when the
    // body's value at this constructor cannot be that one.
    let refutation = Proposition::ConditionIs(condition, !fact.equal);
    if required_obligation_is_exactly_discharged(arm_assumptions, &refutation) {
        super::assumptions::record_reasoning_provenance(arm_assumptions, premise);
        return true;
    }
    false
}

/// Fresh symbolic values for one constructor's fields, in a variable band no
/// generator of the verification reaches.
///
/// The values stand for the unknowns an arm would bind. They must be
/// unconstrained: a value the surrounding premises already speak about would
/// let an unrelated fact decide the predicate. Generators mint from zero (the
/// Surface's execution variables), from a million (the kernel's evaluation
/// variables) and from three million two hundred thousand (quantifier
/// binders), so this band is reserved and never reached. None of these values
/// leaves the refutation: what it publishes names constructors without
/// fields.
///
/// An arm binding a mathematical `Integer` answers `None`, because binding
/// one needs the identity rewrite that only a selected constructor supplies.
fn symbolic_arm_binding_values(
    algebraic_type: &AlgebraicType,
    variant: &AlgebraicVariantType,
) -> Option<Vec<AlgebraicValue>> {
    variant
        .fields
        .iter()
        .map(|value_type| {
            crate::instrumentation::record_deterministic_work(1);
            let variable = next_arm_refutation_variable();
            match value_type {
                AlgebraicValueType::C(c_type) => {
                    Some(AlgebraicValue::C(symbolic_call_result(*c_type, variable)))
                }
                AlgebraicValueType::Integer => None,
                AlgebraicValueType::Algebraic { .. } | AlgebraicValueType::Parameter(_) => {
                    algebraic_type
                        .resolve_nested_type(value_type)
                        .map(|nested_type| {
                            AlgebraicValue::Algebraic(AlgebraicTerm {
                                algebraic_type: nested_type,
                                node: AlgebraicTermNode::Variable(variable),
                            })
                        })
                }
            }
        })
        .collect()
}

/// The first identity of the reserved arm-refutation band.
const ARM_REFUTATION_VARIABLE_BASE: u64 = 1 << 56;

thread_local! {
    static NEXT_ARM_REFUTATION_VARIABLE: std::cell::Cell<u64> =
        const { std::cell::Cell::new(ARM_REFUTATION_VARIABLE_BASE) };
}

fn next_arm_refutation_variable() -> Variable {
    NEXT_ARM_REFUTATION_VARIABLE.with(|next| {
        let variable = next.get();
        next.set(variable.wrapping_add(1).max(ARM_REFUTATION_VARIABLE_BASE));
        Variable(variable)
    })
}

/// The premises that hold of one arm's symbolic bindings: the ambient
/// premises, the cells the arm owns, and the arm's own body facts read at
/// those bindings.
///
/// This is the same evaluation [`arm_binding_free_facts`] performs, with the
/// arm's bindings bound instead of excluded, so a fact about a binding takes
/// part. A fact that cannot be lowered here contributes nothing; a clause
/// vector that cannot be evaluated refuses the whole context, because a fact
/// reading a cell the arm owns needs that authority.
fn arm_premises_at_symbolic_bindings(
    evaluation: &CState,
    arm: &CResourceMatchArm,
    bindings: &[AlgebraicValue],
    evaluation_assumptions: &PureFactContext,
    assumptions: &PureFactContext,
) -> Option<PureFactContext> {
    let mut body_state = evaluation.clone();
    let mut algebraic_bindings = BTreeMap::new();
    for (name, value) in arm.bindings.iter().zip(bindings) {
        crate::instrumentation::record_deterministic_work(1);
        match value {
            AlgebraicValue::C(value) => {
                let c_type = value.c_type();
                body_state
                    .locals
                    .set_typed(name.clone(), value.clone(), c_type);
            }
            AlgebraicValue::Algebraic(value) => {
                algebraic_bindings.insert(name.clone(), value.clone());
            }
            AlgebraicValue::Integer(_) => return None,
        }
    }
    let mut budget = ExecutionBudget::beside_live_state();
    let Ok(Ok(body_resources)) = evaluate_function_resource_context_with_normalization(
        &body_state,
        &arm.contains,
        &[],
        evaluation_assumptions,
        &mut budget,
        false,
    ) else {
        return None;
    };
    let body_state = body_state.with_resource_context(body_resources.0);
    let mut body_assumptions =
        evaluation_assumptions
            .clone()
            .assume_proposition(Proposition::CResourceComposition(
                body_state.resources().clone(),
            ));
    let mut arm_assumptions = assumptions.clone();
    for fact in &arm.facts {
        crate::instrumentation::record_deterministic_work(1);
        let Ok(paths) =
            crate::kernel::spec::lower_spec_proposition_at_state_with_algebraic_bindings(
                &body_state,
                fact,
                None,
                &body_assumptions,
                &algebraic_bindings,
                &mut budget,
            )
        else {
            continue;
        };
        let [path] = paths.as_slice() else {
            continue;
        };
        if !path.facts.is_empty() || !path.obligations.is_empty() {
            continue;
        }
        body_assumptions = body_assumptions.assume_proposition(path.proposition.clone());
        arm_assumptions = arm_assumptions.assume_proposition(path.proposition.clone());
    }
    Some(arm_assumptions)
}

/// Whether `assumptions` refutes one of `arm`'s own facts that names no
/// binding of the arm.
///
/// A fact naming a binding says nothing before the arm is selected: the
/// binding is an unknown the constructor would supply. A budget or evaluation
/// failure is not a refutation: the arm simply publishes nothing.
fn arm_is_refuted_by_a_binding_free_fact(
    evaluation: &CState,
    arm: &CResourceMatchArm,
    evaluation_assumptions: &PureFactContext,
    assumptions: &PureFactContext,
) -> bool {
    arm_binding_free_facts(evaluation, arm, evaluation_assumptions)
        .iter()
        .any(|fact| {
            refutation_of_body_fact(fact).is_some_and(|negation| {
                required_obligation_is_exactly_discharged(assumptions, &negation)
            })
        })
}

/// One arm's own facts that name no binding of the arm, lowered against the
/// instance's body in `evaluation`.
///
/// Facts are restricted to the comparison shape for the same reason arm
/// selection restricts its guards: a comparison of C expressions is what a
/// path condition decides. The arm's `owns` clauses are evaluated first,
/// exactly as arm selection evaluates the selected arm's cells, so a fact that
/// reads a cell the arm owns has the authority to read it. A fact that needs a
/// conditional proof, or that the budget cannot lower, contributes nothing.
///
/// Cost is this arm's own clauses. Nothing outside the arm is visited.
fn arm_binding_free_facts(
    evaluation: &CState,
    arm: &CResourceMatchArm,
    evaluation_assumptions: &PureFactContext,
) -> Vec<Proposition> {
    let bound = arm.bindings.iter().cloned().collect::<BTreeSet<_>>();
    let binding_free = arm
        .facts
        .iter()
        .filter(|fact| !spec_proposition_mentions_any_name(fact, &bound))
        .collect::<Vec<_>>();
    if binding_free.is_empty() {
        return Vec::new();
    }
    let mut budget = ExecutionBudget::beside_live_state();
    let Ok(Ok(body_resources)) = evaluate_function_resource_context_with_normalization(
        evaluation,
        &arm.contains,
        &[],
        evaluation_assumptions,
        &mut budget,
        false,
    ) else {
        return Vec::new();
    };
    let body_state = evaluation.clone().with_resource_context(body_resources.0);
    let body_assumptions =
        evaluation_assumptions
            .clone()
            .assume_proposition(Proposition::CResourceComposition(
                body_state.resources().clone(),
            ));
    let bindings = BTreeMap::new();
    binding_free
        .into_iter()
        .filter_map(|fact| {
            crate::instrumentation::record_deterministic_work(1);
            let paths =
                crate::kernel::spec::lower_spec_proposition_at_state_with_algebraic_bindings(
                    &body_state,
                    fact,
                    None,
                    &body_assumptions,
                    &bindings,
                    &mut budget,
                )
                .ok()?;
            let [path] = paths.as_slice() else {
                return None;
            };
            (path.facts.is_empty() && path.obligations.is_empty()).then(|| path.proposition.clone())
        })
        .collect()
}

/// The facts of the arm a frontier's premises decide for one folded matched
/// instance, restricted to the facts that name no constructor binding.
///
/// This is the last part of decision D7: the read authority says which cells
/// the arm owns, and this says what the arm states about them. `consumes t:
/// tree_at(root); requires t.model != HeapTree::Empty;` selects the `Node`
/// arm, whose `fact p != 0` is then an entry premise, so a walk that starts
/// with `if (root == 0)` decides the guard instead of needing an infeasible
/// `branch`.
///
/// A fact naming a binding stays unpublished: the binding is an unknown of the
/// arm, and only an `unfold` or a proof `match` names it. Cost is the decided
/// arm's own clauses.
fn decided_instance_arm_facts(
    instance: &ResourceInstance,
    definitions: &[CCompositeResourceDefinition],
    state: &CState,
    assumptions: &PureFactContext,
) -> Vec<Proposition> {
    let Some(definition) = definitions
        .iter()
        .find(|definition| definition.name() == instance.name())
    else {
        return Vec::new();
    };
    let Some(body) = definition.matched.as_ref() else {
        return Vec::new();
    };
    let Some(AlgebraicValue::Algebraic(model)) = instance.fields().get(body.field_index) else {
        return Vec::new();
    };
    let Some(selection) = select_resource_model_arm(model, assumptions) else {
        return Vec::new();
    };
    let Some(arm) = body
        .arms
        .iter()
        .find(|arm| arm.variant == selection.variant())
    else {
        return Vec::new();
    };
    let Ok(evaluation) = instance_body_evaluation(state, instance, definition) else {
        return Vec::new();
    };
    let evaluation_assumptions = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads();
    arm_binding_free_facts(&evaluation, arm, &evaluation_assumptions)
}

/// Whether a resource body fact is a comparison of C expressions in which one
/// of `names` occurs. A fact of any other shape answers `true`, so the
/// refutation rule leaves it alone.
fn spec_proposition_mentions_any_name(fact: &SpecProposition, names: &BTreeSet<String>) -> bool {
    let SpecProposition::Comparison { left, right, .. } = fact else {
        return true;
    };
    [left, right].into_iter().any(|side| match side {
        SpecExpression::Value(_) => false,
        SpecExpression::CExpression(expression) => names
            .iter()
            .any(|name| c_expression_mentions_variable(expression, name)),
        _ => true,
    })
}

/// Incrementally exposes the memory cells beneath one newly evaluated
/// composite clause.  The outer section supply already expanded all facts
/// from the previous pass; walking only this fact and its nested children
/// keeps a dependency chain proportional to its own nodes and edges instead
/// of rescanning the complete section after every successful retry.
fn resource_clause_supply_with_fact(
    mut supply: ResourceContext,
    fact: CResourceFact,
    definitions: &[CCompositeResourceDefinition],
    memory: &CMemory,
    assumptions: &PureFactContext,
) -> (ResourceContext, Vec<CResourceFact>) {
    let mut added = Vec::new();
    if !supply.facts().contains(&fact) {
        supply = supply.unchecked_with_fact(fact.clone());
        added.push(fact.clone());
    }
    if definitions.is_empty() || !matches!(fact.resource(), CResource::Composite { .. }) {
        return (supply, added);
    }
    let mut pending = VecDeque::from([fact]);
    let mut seen = BTreeSet::new();
    while let Some(composite) = pending.pop_front() {
        if !seen.insert(composite.clone()) {
            continue;
        }
        let expansion_context = supply.clone().unchecked_with_fact(composite.clone());
        let Some((_, children, _)) = expand_composite_resource_fact_with_children(
            &expansion_context,
            &composite,
            definitions,
            memory,
            assumptions,
        ) else {
            continue;
        };
        for child in children {
            match child.resource() {
                CResource::Memory(range) => {
                    let view = CResourceFact::view_memory(range.clone());
                    if !supply.facts().contains(&view) {
                        supply = supply.unchecked_with_fact(view.clone());
                        added.push(view);
                    }
                }
                CResource::Composite { .. } => pending.push_back(child),
                CResource::Token { .. } | CResource::Instance(_) => {}
            }
        }
    }
    (supply, added)
}

/// Names which resource clause of a contract section could not be addressed.
///
/// Two checks reach this conclusion about the same contract: the surface
/// refuses a clause whose segment base reads a cell the contract holds no
/// authority over, and this evaluator refuses a clause whose base it cannot
/// read at all. They are one defect, so they identify the clause with one
/// wording, formatted here and in [`resource_clause_stall_note`].
pub(crate) fn resource_clause_position_note(index: usize, total: usize) -> String {
    format!("resource clause {} of {total}", index + 1)
}

/// Names two clauses that no order addresses. Clause order does not decide a
/// section, so reporting only the first position would send the user to a
/// clause that is fine on its own.
pub(crate) fn resource_clause_stall_note(index: usize, other: usize) -> String {
    format!(
        "resource clauses {} and {} cannot be evaluated in any order: each needs a cell no \
         clause evaluated before it supplies",
        index + 1,
        other + 1
    )
}

/// Names which resource clause of a contract section failed to evaluate. The
/// evaluator walks the declared clauses in order, so the position is the only
/// identification available here, and it is enough for a user to find the
/// clause. Structured errors already print the offending resource and are
/// passed through unchanged.
fn resource_clause_position(resources: &[CResourceSpec], index: usize) -> (usize, usize) {
    resources
        .get(index)
        .and_then(CResourceSpec::clause_position)
        .unwrap_or((index, resources.len()))
}

fn resource_clause_runtime_error(
    error: CRuntimeError,
    index: usize,
    resources: &[CResourceSpec],
) -> CRuntimeError {
    let CRuntimeError::FunctionContract(message) = error else {
        return error;
    };
    let (index, total) = resource_clause_position(resources, index);
    CRuntimeError::FunctionContract(format!(
        "{message} ({})",
        resource_clause_position_note(index, total)
    ))
}

/// Whether a clause failed for want of a value it had to read, which is the
/// only failure another clause's authority can repair. The evaluator reports
/// a section that stalls on these as a pair; anything else is one clause's own
/// problem.
fn resource_clause_failure_awaits_supply(error: &CRuntimeError) -> bool {
    let CRuntimeError::FunctionContract(message) = error else {
        return false;
    };
    message.starts_with("could not evaluate an owned memory resource segment")
        || message.starts_with("could not evaluate a viewed memory resource segment")
        || message.starts_with("could not evaluate resource `")
}

fn resource_clause_cycle_runtime_error(
    error: CRuntimeError,
    index: usize,
    other: usize,
    resources: &[CResourceSpec],
) -> CRuntimeError {
    let CRuntimeError::FunctionContract(message) = error else {
        return error;
    };
    let (index, _) = resource_clause_position(resources, index);
    let (other, _) = resource_clause_position(resources, other);
    CRuntimeError::FunctionContract(format!(
        "{message} ({})",
        resource_clause_stall_note(index, other)
    ))
}

fn resource_context_runtime_error(error: ResourceContextValidityError) -> CRuntimeError {
    match error {
        ResourceContextValidityError::DuplicateOwnedResourceFact(resource) => {
            CRuntimeError::DuplicateResource { resource }
        }
        ResourceContextValidityError::InvalidInstanceAccess(_) => CRuntimeError::FunctionContract(
            "field-bearing resource instances require exclusive ownership with quantity one".into(),
        ),
        ResourceContextValidityError::OverlappingOwnedMemoryResources { left, right } => {
            CRuntimeError::OverlappingOwnedMemoryResources {
                left: Box::new(left),
                right: Box::new(right),
            }
        }
    }
}

pub(super) fn evaluate_function_resource_spec(
    state: &CState,
    resource: &CResourceSpec,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<CResourceFact, CRuntimeError>> {
    evaluate_function_resource_spec_with_entry(state, state, resource, assumptions, budget)
}

pub(super) fn evaluate_function_resource_spec_with_entry(
    entry_state: &CState,
    state: &CState,
    resource: &CResourceSpec,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<CResourceFact, CRuntimeError>> {
    match resource.term() {
        CResourceTerm::Instance {
            identity,
            schema,
            resource: inner_term,
            ..
        } => {
            let inner = match CResourceSpec::new(
                (**inner_term).clone(),
                CResourceAccessMode::Own,
                CResourceQuantity::One,
                resource.role(),
                resource.snapshot(),
            ) {
                Ok(inner) => inner,
                Err(error) => {
                    return Ok(Err(CRuntimeError::FunctionContract(format!(
                        "invalid named resource body: {error}"
                    ))));
                }
            };
            let required = match evaluate_function_resource_spec_with_entry(
                entry_state,
                state,
                &inner,
                assumptions,
                budget,
            )? {
                Ok(resource) => resource,
                Err(error) => return Ok(Err(error)),
            };
            let Some(instance) = state.owned_resource_instance(*identity) else {
                return Ok(Err(CRuntimeError::FunctionContract(
                    "named resource instance is not owned".into(),
                )));
            };
            let CResourceFact::Own(CResource::Composite { name, arguments }, quantity) = required
            else {
                return Ok(Err(CRuntimeError::FunctionContract(
                    "named instance requires an owned resource definition".into(),
                )));
            };
            if quantity.as_const() != Some(1)
                || instance.name() != name
                || instance.schema() != schema
                || instance.arguments().len() != arguments.len()
                || !instance
                    .arguments()
                    .iter()
                    .zip(arguments.iter())
                    .all(|(a, b)| crate::kernel::resource_arguments_proven_equal(a, b, assumptions))
            {
                return Ok(Err(CRuntimeError::FunctionContract(
                    "named resource instance does not match its contract".into(),
                )));
            }
            Ok(Ok(CResourceFact::own(CResource::Instance(
                instance.clone(),
            ))))
        }
        CResourceTerm::Memory(segment) => {
            let element_width = segment.element_width();
            let segment = match evaluate_loop_effect_segment(state, segment, assumptions, budget)? {
                Ok(segment) => segment,
                Err(_) => {
                    return Ok(Err(CRuntimeError::FunctionContract(
                        if resource.is_view() {
                            "could not evaluate a viewed memory resource segment".to_string()
                        } else {
                            "could not evaluate an owned memory resource segment".to_string()
                        },
                    )));
                }
            };
            let range = CMemoryRange::new_with_element_width(
                segment.base,
                segment.start,
                segment.end,
                element_width,
            );
            Ok(Ok(if resource.is_view() {
                CResourceFact::view_memory(range)
            } else {
                CResourceFact::own_memory(range)
            }))
        }
        CResourceTerm::Composite {
            name,
            arguments,
            argument_snapshots,
            parameter_types,
        }
        | CResourceTerm::Token {
            name,
            arguments,
            argument_snapshots,
            parameter_types,
        } => {
            let family = resource.family();
            let mut fact = match evaluate_function_declared_resource_spec(
                entry_state,
                state,
                resource.access(),
                family,
                name,
                arguments,
                argument_snapshots,
                parameter_types,
                assumptions,
                budget,
            )? {
                Ok(fact) => fact,
                Err(error) => return Ok(Err(error)),
            };
            if let CResourceQuantity::Count(quantity) = resource.quantity() {
                if resource.access() != CResourceAccessMode::Own
                    || name == CResourceFact::ALLOCATION_RESOURCE_NAME
                {
                    return Ok(Err(CRuntimeError::FunctionContract(
                        "symbolic quantities require owned user-declared resources".to_string(),
                    )));
                }
                let quantity = match evaluate_loop_effect_segment_value(
                    match resource.quantity_snapshot() {
                        CResourceSnapshot::Entry => entry_state,
                        CResourceSnapshot::Current | CResourceSnapshot::Post => state,
                    },
                    quantity,
                    assumptions,
                    "declared resource quantity",
                    budget,
                )? {
                    Ok(CValue::Int32(quantity)) => quantity,
                    Ok(_) | Err(_) => {
                        return Ok(Err(CRuntimeError::FunctionContract(
                            "declared resource quantity must evaluate to int32".to_string(),
                        )));
                    }
                };
                if !quantity_condition_holds(
                    assumptions,
                    ConditionTerm::Bitvector32SignedGreaterEqual(
                        Box::new(quantity.clone()),
                        Box::new(Bitvector32Term::Constant(0)),
                    ),
                ) {
                    return Ok(Err(CRuntimeError::FunctionContract(
                        "declared resource quantity is not known nonnegative; state that the \
                         quantity expression is at least 0 as a requirement, an invariant, or a \
                         fact proved in scope"
                            .to_string(),
                    )));
                }
                let CResourceFact::Own(inner, _) = fact else {
                    return Ok(Err(CRuntimeError::FunctionContract(
                        "declared resource quantity did not lower to owned authority".to_string(),
                    )));
                };
                fact = CResourceFact::own_quantity(inner, quantity);
            }
            Ok(Ok(fact))
        }
    }
}

/// Lowers the nonnegativity conditions implicit in quantified resource
/// requirements. A function may assume these at its own entry just as it may
/// assume its ordinary `requires`; call sites still use
/// `evaluate_function_resource_spec` and must prove every condition.
pub(crate) fn quantified_resource_requirement_assumptions(
    state: &CState,
    resources: &[CResourceSpec],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<Vec<Proposition>, CRuntimeError>> {
    let mut propositions = Vec::new();
    for resource in resources {
        let CResourceQuantity::Count(quantity) = resource.quantity() else {
            continue;
        };
        let quantity = match evaluate_loop_effect_segment_value(
            state,
            quantity,
            assumptions,
            "declared resource quantity",
            budget,
        )? {
            Ok(CValue::Int32(quantity)) => quantity,
            Ok(_) | Err(_) => {
                return Ok(Err(CRuntimeError::FunctionContract(
                    "declared resource quantity must evaluate to int32".to_string(),
                )));
            }
        };
        propositions.push(Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedGreaterEqual(
                Box::new(quantity),
                Box::new(Bitvector32Term::Constant(0)),
            ),
            true,
        ));
    }
    Ok(Ok(propositions))
}

fn evaluate_function_declared_resource_spec(
    entry_state: &CState,
    state: &CState,
    access: CResourceAccessMode,
    family: ResourceFamily,
    name: &str,
    arguments: &[CExpression],
    argument_snapshots: &[CResourceSnapshot],
    parameter_types: &[CType],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<CResourceFact, CRuntimeError>> {
    if arguments.len() != parameter_types.len() || arguments.len() != argument_snapshots.len() {
        return Ok(Err(CRuntimeError::FunctionContract(format!(
            "resource `{name}` received the wrong number of arguments"
        ))));
    }
    let mut values = Vec::new();
    for (index, ((argument, argument_snapshot), parameter_type)) in arguments
        .iter()
        .zip(argument_snapshots)
        .zip(parameter_types)
        .enumerate()
    {
        let argument_state = match argument_snapshot {
            CResourceSnapshot::Entry => entry_state,
            CResourceSnapshot::Current | CResourceSnapshot::Post => state,
        };
        let allocation_element_count = (name == CResourceFact::ALLOCATION_RESOURCE_NAME
            && index == 1)
            .then(|| match argument {
                CExpression::Multiply(left, right)
                    if right.as_ref() == &CExpression::Value(int32(CType::Int32.byte_width())) =>
                {
                    Some(left.as_ref())
                }
                CExpression::Multiply(left, right)
                    if left.as_ref() == &CExpression::Value(int32(CType::Int32.byte_width())) =>
                {
                    Some(right.as_ref())
                }
                _ => None,
            })
            .flatten();
        let value = if let Some(element_count) = allocation_element_count {
            let count = match evaluate_loop_effect_segment_value(
                argument_state,
                element_count,
                assumptions,
                &format!("resource `{name}` argument {index} element count"),
                budget,
            )? {
                Ok(CValue::Int32(count)) => count,
                Ok(_) | Err(_) => {
                    return Ok(Err(CRuntimeError::FunctionContract(format!(
                        "resource `{name}` has an invalid allocation element count"
                    ))));
                }
            };
            int32(Bitvector32Term::multiply(
                count,
                Bitvector32Term::Constant(CType::Int32.byte_width()),
            ))
        } else {
            match evaluate_loop_effect_segment_value(
                argument_state,
                argument,
                assumptions,
                &format!("resource `{name}` argument {index}"),
                budget,
            )? {
                Ok(value) => value,
                Err(error) => {
                    return Ok(Err(CRuntimeError::FunctionContract(format!(
                        "could not evaluate resource `{name}` argument {index}: {error}"
                    ))));
                }
            }
        };
        let accepts_allocation_pointer = name == CResourceFact::ALLOCATION_RESOURCE_NAME
            && index == 0
            && matches!(&value, CValue::Pointer(pointer) if pointer.c_type().pointee_type().is_some());
        if !accepts_allocation_pointer && !parameter_type.accepts(&value) {
            return Ok(Err(CRuntimeError::FunctionContract(format!(
                "resource `{name}` argument {index} has the wrong type"
            ))));
        }
        values.push(value);
    }
    let resource = match family {
        ResourceFamily::Composite => CResource::Composite {
            name: name.to_string(),
            arguments: values.into_iter().map(AlgebraicValue::C).collect(),
        },
        ResourceFamily::Token => CResource::Token {
            name: name.to_string(),
            arguments: values.into_iter().map(AlgebraicValue::C).collect(),
        },
        ResourceFamily::Memory | ResourceFamily::Instance => {
            return Ok(Err(CRuntimeError::FunctionContract(
                "declared resources cannot use the raw memory family".to_string(),
            )));
        }
    };
    Ok(Ok(match access {
        CResourceAccessMode::Own => CResourceFact::own(resource),
        CResourceAccessMode::View => CResourceFact::View(resource),
    }))
}

fn resource_fact_transfer_priority(resource: &CResourceFact) -> u8 {
    match resource {
        CResourceFact::View(_) => 0,
        CResourceFact::Own(CResource::Memory(_), _) => 1,
        CResourceFact::Own(
            CResource::Composite { .. } | CResource::Token { .. } | CResource::Instance(_),
            _,
        ) => 2,
    }
}

/// Advisory hint for a leaked allocation that may belong to a counted
/// population body retired by clause arithmetic. Names counted families with
/// population-wide bodies so the author can prove non-emptiness
/// (`count(family(...)) != 0`) instead of freeing. Advisory only; never
/// affects checking.
fn counted_population_leak_hint(function: &CFunction) -> Option<String> {
    let mut names = Vec::new();
    for definition in function.composite_resource_definitions() {
        if definition.is_counted_population()
            && definition_has_population_wide_body(definition)
            && !names.contains(&definition.name().to_string())
        {
            names.push(definition.name().to_string());
        }
    }
    if names.is_empty() {
        return None;
    }
    let counts = names
        .iter()
        .map(|name| format!("count({name}(...)) != 0"))
        .collect::<Vec<_>>()
        .join(" or ");
    Some(format!(
        "To fix, either free it on this path or, if it belongs to a counted population that is actually non-empty here, prove that {counts}."
    ))
}

fn unreturned_allocation_obligation(
    actual_state: &CState,
    returned_resources: &ResourceContext,
    function: &CFunction,
    assumptions: &PureFactContext,
) -> Result<Option<(CResourceFact, Option<CResourceFact>)>, CRuntimeError> {
    let Some(actual) = expand_all_composite_resource_facts(
        actual_state.resources(),
        function.composite_resource_definitions(),
        actual_state.memory(),
        assumptions,
    ) else {
        return Err(CRuntimeError::FunctionContract(
            "could not inspect allocation obligations at function return".to_string(),
        ));
    };
    let mut budget = ExecutionBudget::beside_live_state();
    let population_bodies = match evaluate_resource_population_body_resources(
        returned_resources,
        actual_state,
        function.composite_resource_definitions(),
        assumptions,
        &mut budget,
        false,
    ) {
        Ok(Ok(resources)) => resources,
        Ok(Err(error)) => return Err(error),
        Err(limit) => {
            return Err(CRuntimeError::FunctionContract(format!(
                "counted population allocation inspection hit execution limit {limit:?}"
            )));
        }
    };
    let returned_resources = returned_resources
        .clone()
        .unchecked_with_facts(population_bodies.facts().iter().cloned());
    let allocation = actual
        .facts()
        .iter()
        .filter(|fact| fact.allocation().is_some())
        .find(|allocation| {
            returned_resources
                .cached_support_exposing_fact(allocation, assumptions)
                .is_none()
                && expose_composite_resource_fact(
                    &returned_resources,
                    allocation,
                    function.composite_resource_definitions(),
                    actual_state.memory(),
                    assumptions,
                )
                .is_none()
        })
        .cloned();
    Ok(allocation.map(|allocation| {
        let resource =
            resource_fact_containing_allocation(actual_state, &allocation, function, assumptions);
        (allocation, resource)
    }))
}

/// Finds the folded declared resource whose body accounts for a leaked
/// allocation. This is diagnostic provenance only: the allocation check
/// remains the authority, and failure to identify a containing resource must
/// not change verification.
fn resource_fact_containing_allocation(
    state: &CState,
    allocation: &CResourceFact,
    function: &CFunction,
    assumptions: &PureFactContext,
) -> Option<CResourceFact> {
    state
        .resources()
        .facts()
        .iter()
        .filter(|fact| {
            fact.is_own()
                && matches!(
                    fact.resource(),
                    CResource::Composite { .. } | CResource::Token { .. }
                )
        })
        .find_map(|candidate| {
            let singleton = ResourceContext::new().unchecked_with_fact(candidate.clone());
            let mut budget = ExecutionBudget::beside_live_state();
            let Ok(Ok(body)) = evaluate_resource_population_body_resources(
                &singleton,
                state,
                function.composite_resource_definitions(),
                assumptions,
                &mut budget,
                true,
            ) else {
                return None;
            };
            body.facts()
                .iter()
                .any(|fact| {
                    fact == allocation
                        || fact.core_with_assumptions(assumptions).is_some_and(|core| {
                            allocation
                                .core_with_assumptions(assumptions)
                                .is_some_and(|allocation_core| core == allocation_core)
                        })
                })
                .then(|| candidate.clone())
        })
}

/// A counted population body can keep an allocation live after the consumed
/// representative unit is gone.  The body is only a valid return support when
/// the post-transition population is nonempty; the transition emits that
/// condition as a proof obligation.  This helper identifies that support so
/// the allocation check can defer to the obligation instead of reporting a
/// premature leak before post-execution `have` facts are available.
fn active_counted_population_supports_allocation(
    actual_state: &CState,
    allocation: &CResourceFact,
    function: &CFunction,
    assumptions: &PureFactContext,
) -> bool {
    actual_state.counted_populations().any(|population| {
        let Some(definition) =
            function
                .composite_resource_definitions()
                .iter()
                .find(|definition| {
                    definition.name() == population.name && definition.is_counted_population()
                })
        else {
            return false;
        };
        let resource = CResourceFact::own(CResource::Composite {
            name: population.name.clone(),
            arguments: population.arguments.clone(),
        });
        let singleton = ResourceContext::new().unchecked_with_fact(resource);
        let mut budget = ExecutionBudget::beside_live_state();
        let Ok(Ok(body)) = evaluate_resource_population_body_resources(
            &singleton,
            actual_state,
            std::slice::from_ref(definition),
            assumptions,
            &mut budget,
            false,
        ) else {
            return false;
        };
        body.facts().iter().any(|fact| {
            fact == allocation
                || fact.core_with_assumptions(assumptions).is_some_and(|core| {
                    allocation
                        .core_with_assumptions(assumptions)
                        .is_some_and(|allocation_core| core == allocation_core)
                })
        })
    })
}

/// Returns the caller-visible memory after a function returns.
pub(in crate::kernel) fn function_exit_memory(
    caller_state: &CState,
    callee_state: &CState,
    value: &CValue,
    function: &CFunction,
) -> CMemory {
    if function.return_aggregate_layout().is_some() {
        return callee_state.memory.clone();
    }
    match value {
        CValue::Pointer(pointer)
            if pointer.pointer().block.starts_with("local:")
                && !caller_state.memory.has_block(&pointer.pointer().block) =>
        {
            callee_state
                .memory
                .without_local_block(&pointer.pointer().block)
        }
        _ => callee_state.memory.clone(),
    }
}

pub(crate) fn unreturned_allocation_at_function_exit(
    state: &CState,
    value: &CValue,
    function: &CFunction,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<Option<(CResourceFact, Option<CResourceFact>)>, CRuntimeError>> {
    let function_can_package_allocation =
        function
            .composite_resource_definitions()
            .iter()
            .any(|definition| {
                definition.contains().iter().any(|resource| {
                    resource.family() == ResourceFamily::Token
                        && resource.declared_name() == Some(CResourceFact::ALLOCATION_RESOURCE_NAME)
                })
            });
    if !function_can_package_allocation
        && !state
            .resources()
            .facts()
            .iter()
            .any(|fact| fact.allocation().is_some())
    {
        return Ok(Ok(None));
    }
    let Some(actual_resources) = expand_all_composite_resource_facts(
        state.resources(),
        function.composite_resource_definitions(),
        state.memory(),
        assumptions,
    ) else {
        return Ok(Err(CRuntimeError::FunctionContract(
            "could not inspect allocation obligations at function exit".to_string(),
        )));
    };
    if !actual_resources
        .facts()
        .iter()
        .any(|fact| fact.allocation().is_some())
    {
        return Ok(Ok(None));
    }
    let Some(argument_values) = arguments
        .iter()
        .map(|argument| match argument {
            CExpression::Value(value) => Some(value.clone()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()
    else {
        return Ok(Err(CRuntimeError::FunctionContract(
            "allocation-delta checking requires concrete symbolic contract arguments".to_string(),
        )));
    };
    let mut output_state = with_contract_argument_views(state, function, &argument_values);
    if function.return_type() != CType::Void {
        set_function_result(&mut output_state, function, value.clone());
    }
    let returned_resources = match evaluate_function_resource_context(
        &output_state,
        function.resource_ensures(),
        function.composite_resource_definitions(),
        assumptions,
        budget,
    )? {
        Ok(resources) => resources,
        Err(error) => return Ok(Err(error)),
    };
    Ok(unreturned_allocation_obligation(
        &output_state,
        &returned_resources,
        function,
        assumptions,
    ))
}

#[allow(clippy::too_many_arguments)]
fn function_outcome_from_body_with_population_transition(
    caller_state: &CState,
    function: &CFunction,
    outcome: CStatementOutcome,
    mut obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    argument_values: &[CValue],
    budget: &mut ExecutionBudget,
) -> ExecutionResult<(CFunctionOutcome, Vec<ProofObligation>)> {
    if let Some(error) = exceptional_outcome_declaration_error(function, &outcome) {
        return Ok((CFunctionOutcome::RuntimeError(error), obligations));
    }
    if matches!(&outcome, CStatementOutcome::Throw { .. })
        && (!function.resource_requires().is_empty()
            || !function.resource_ensures().is_empty()
            || !function.resource_constructors().is_empty())
    {
        return Ok((
            CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                "exceptional outcomes with population transitions require an exceptional contract interface"
                    .to_string(),
            )),
            obligations,
        ));
    }
    let CStatementOutcome::Return { value, mut state } = outcome else {
        return Ok(function_outcome_from_body(
            caller_state,
            function,
            outcome,
            obligations,
            assumptions,
            None,
        ));
    };
    let Some(value) = coerce_function_return_value(value, function, &mut obligations, assumptions)
    else {
        return Ok((
            CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                "{} returned a value that does not match its declared type",
                function.name()
            ))),
            obligations,
        ));
    };
    if function.return_type() != CType::Void {
        set_function_result(&mut state, function, value.clone());
    }
    let population_transition = match apply_counted_population_transitions(
        caller_state,
        &mut state,
        function,
        argument_values,
        assumptions,
        true,
        budget,
    )? {
        Ok(transition) => transition,
        Err(error) => return Ok((CFunctionOutcome::RuntimeError(error), obligations)),
    };
    obligations.extend(population_transition.postcondition_obligations);
    Ok(function_outcome_from_body(
        caller_state,
        function,
        CStatementOutcome::Return { value, state },
        obligations,
        assumptions,
        None,
    ))
}

#[allow(clippy::too_many_arguments)]
fn function_outcome_from_body_with_resource_transfer(
    caller_state: &CState,
    function: &CFunction,
    outcome: CStatementOutcome,
    mut obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    transfer: &CFunctionResourceTransfer,
    argument_values: &[CValue],
    reestablish_population_invariants: bool,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<(
    CFunctionOutcome,
    Vec<ProofObligation>,
    Option<Arc<CheckedLoanCallEvidence>>,
)> {
    if let Some(error) = exceptional_outcome_declaration_error(function, &outcome) {
        return Ok((CFunctionOutcome::RuntimeError(error), obligations, None));
    }
    if matches!(&outcome, CStatementOutcome::Throw { .. })
        && (!function.resource_requires().is_empty()
            || !function.resource_ensures().is_empty()
            || !function.resource_constructors().is_empty())
    {
        return Ok((
            CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(
                "exceptional outcomes with resource transitions require an exceptional contract interface"
                    .to_string(),
            )),
            obligations,
            None,
        ));
    }
    let CStatementOutcome::Return { value, mut state } = outcome else {
        let (outcome, obligations) = function_outcome_from_body(
            caller_state,
            function,
            outcome,
            obligations,
            assumptions,
            None,
        );
        return Ok((outcome, obligations, None));
    };
    let Some(value) = coerce_function_return_value(value, function, &mut obligations, assumptions)
    else {
        return Ok((
            CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                "{} returned a value that does not match its declared type",
                function.name()
            ))),
            obligations,
            None,
        ));
    };

    if function.return_type() != CType::Void {
        set_function_result(&mut state, function, value.clone());
    }
    let population_transition = match crate::instrumentation::measure_operation(
        function.name(),
        "contract resource transition",
        "return counted population transition",
        || {
            apply_counted_population_transitions(
                caller_state,
                &mut state,
                function,
                argument_values,
                assumptions,
                reestablish_population_invariants,
                budget,
            )
        },
    )? {
        Ok(transition) => transition,
        Err(error) => return Ok((CFunctionOutcome::RuntimeError(error), obligations, None)),
    };
    obligations.extend(
        population_transition
            .postcondition_obligations
            .iter()
            .cloned(),
    );
    let caller_resources_after_requirements = match crate::instrumentation::measure_operation(
        function.name(),
        "contract resource transition",
        "return population resource update",
        || {
            apply_counted_population_transition_resources(
                transfer.caller_resources_after_requirements.clone(),
                &population_transition,
                assumptions,
            )
        },
    ) {
        Ok(resources) => resources,
        Err(error) => return Ok((CFunctionOutcome::RuntimeError(error), obligations, None)),
    };
    let output_resource_state = with_contract_argument_views(&state, function, argument_values);
    let entry_resource_state =
        with_contract_argument_views(caller_state, function, argument_values);
    let mut transfer = transfer.clone();
    let ContractReturnResources {
        return_resources,
        ensured_views: returned_views,
        produced_borrowing_pieces,
    } = match crate::instrumentation::measure_operation(
        function.name(),
        "contract resource transition",
        "return resource evaluation",
        || {
            evaluate_function_return_resources(
                &caller_resources_after_requirements,
                escrowed_owners(&transfer),
                &entry_resource_state,
                &output_resource_state,
                function,
                assumptions,
                budget,
            )
        },
    )? {
        Ok(resources) => resources,
        Err(CRuntimeError::TypeMismatch) => {
            return Ok((
                CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                    "could not evaluate {} return resources",
                    function.name()
                ))),
                obligations,
                None,
            ));
        }
        Err(error) => return Ok((CFunctionOutcome::RuntimeError(error), obligations, None)),
    };
    transfer.candidate_output_views = returned_views;
    transfer.produced_borrowing_pieces = produced_borrowing_pieces;
    match crate::instrumentation::measure_operation(
        function.name(),
        "contract resource transition",
        "return allocation obligation check",
        || unreturned_allocation_obligation(&state, &return_resources, function, assumptions),
    ) {
        Ok(Some((allocation, _)))
            if active_counted_population_supports_allocation(
                &state,
                &allocation,
                function,
                assumptions,
            ) => {}
        Ok(Some((allocation, resource))) => {
            let hint = counted_population_leak_hint(function);
            return Ok((
                CFunctionOutcome::RuntimeError(CRuntimeError::LiveAllocationLeak {
                    allocation,
                    resource,
                    hint,
                }),
                obligations,
                None,
            ));
        }
        Err(error) => return Ok((CFunctionOutcome::RuntimeError(error), obligations, None)),
        Ok(None) => {}
    }

    let (return_resources, return_ledger, return_participant, return_view_bindings, loan_evidence) =
        match recover_candidate_stable_view_resources(
            caller_state,
            &state,
            &transfer,
            return_resources,
            assumptions,
            assumptions,
            &obligations,
        ) {
            Ok(recovered) => recovered,
            Err(error) => return Ok((CFunctionOutcome::RuntimeError(error), obligations, None)),
        };

    let mut return_state = caller_state.clone();
    return_state.set_memory(state.memory.clone());
    return_state.resources = return_resources;
    return_state.loan_ledger = return_ledger;
    return_state.loan_participant = return_participant;
    return_state = return_state.with_loan_view_bindings(return_view_bindings);
    return_state.counted_populations = state.counted_populations;
    return_state.next_local_frame = state.next_local_frame;
    return_state.next_local_lifetime = state.next_local_lifetime;
    Ok((
        CFunctionOutcome::Return {
            value,
            state: return_state,
        },
        obligations,
        loan_evidence,
    ))
}

fn without_loan_evidence(
    (outcome, obligations): (CFunctionOutcome, Vec<ProofObligation>),
) -> (
    CFunctionOutcome,
    Vec<ProofObligation>,
    Option<Arc<CheckedLoanCallEvidence>>,
) {
    (outcome, obligations, None)
}

/// The function-exit rule the verification execution applies to a body
/// outcome, so that a completed proof path ends in the same contract-level
/// state an independent execution would: the contract's resource transfer
/// when a composite needs one at the outcome, the declared-population
/// transition when the contract changes counted quantities, and otherwise
/// the plain outcome. A void fallthrough completes as a return first.
pub(super) fn contract_exit_outcome(
    caller_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    outcome: CStatementOutcome,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    purpose: ResourceTransitionPurpose,
) -> ExecutionResult<
    Result<
        (
            CFunctionOutcome,
            Vec<ProofObligation>,
            Option<Arc<CheckedLoanCallEvidence>>,
        ),
        CRuntimeError,
    >,
> {
    let Some(argument_values) = arguments
        .iter()
        .map(|argument| match argument {
            CExpression::Value(value) => Some(value.clone()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()
    else {
        return Ok(Err(CRuntimeError::FunctionContract(
            "contract exit rule requires symbolic value arguments".to_string(),
        )));
    };
    let outcome = complete_void_fallthrough(function, outcome);
    // A proof may hold the body's exit resources in a split representation
    // (one owned token twice rather than a quantity of two). Execution
    // composes its resources as it goes; compose the retained ones the same
    // way so the completed outcome is the canonical one certification compares.
    let outcome = match outcome {
        CStatementOutcome::Return { value, mut state } => {
            if state.loan_view_bindings().iter().next().is_none() {
                let resources = match ResourceContext::new()
                    .try_compose_with_facts(state.resources.facts().iter().cloned(), assumptions)
                {
                    Ok(resources) => resources,
                    Err(error) => return Ok(Err(resource_context_runtime_error(error))),
                };
                state = state.with_resource_context(resources);
            } else if state.resources.validity_error(assumptions).is_some()
                || !state.loan_bindings_are_consistent()
            {
                return Ok(Err(CRuntimeError::FunctionContract(
                    "stable-view return resources are not a valid bound context".to_string(),
                )));
            }
            CStatementOutcome::Return { value, state }
        }
        other => other,
    };
    let Some(callee_state) = bind_c_function_arguments(caller_state, function, &argument_values)
    else {
        return Ok(Err(CRuntimeError::TypeMismatch));
    };
    let transfer = match prepare_function_resource_transfer(
        caller_state,
        &callee_state,
        function,
        assumptions,
        budget,
        true,
        purpose,
    )? {
        Ok(transfer) => transfer,
        Err(error) => return Ok(Err(error)),
    };
    if function_needs_outcome_resource_transfer(function) {
        function_outcome_from_body_with_resource_transfer(
            caller_state,
            function,
            outcome,
            obligations,
            assumptions,
            &transfer,
            &argument_values,
            true,
            budget,
        )
        .map(Ok)
    } else if function_changes_declared_resource_quantities(function) {
        function_outcome_from_body_with_population_transition(
            caller_state,
            function,
            outcome,
            obligations,
            assumptions,
            &argument_values,
            budget,
        )
        .map(|outcome| Ok(without_loan_evidence(outcome)))
    } else {
        Ok(Ok(without_loan_evidence(function_outcome_from_body(
            caller_state,
            function,
            outcome,
            obligations,
            assumptions,
            None,
        ))))
    }
}

pub(super) fn apply_verified_contract_resource_transition(
    caller_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    outcome: CFunctionOutcome,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<(CFunctionOutcome, Vec<ProofObligation>), CRuntimeError>> {
    let Some(argument_values) = arguments
        .iter()
        .map(|argument| match argument {
            CExpression::Value(value) => Some(value.clone()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()
    else {
        return Ok(Err(CRuntimeError::FunctionContract(
            "contract resource transition requires symbolic value arguments".to_string(),
        )));
    };
    let Some(callee_state) = bind_c_function_arguments(caller_state, function, &argument_values)
    else {
        return Ok(Err(CRuntimeError::TypeMismatch));
    };
    let transfer = match prepare_function_resource_transfer(
        caller_state,
        &callee_state,
        function,
        assumptions,
        budget,
        true,
        ResourceTransitionPurpose::FunctionBoundary,
    )? {
        Ok(transfer) => transfer,
        Err(error) => return Ok(Err(error)),
    };
    let statement_outcome = match outcome {
        CFunctionOutcome::Return { value, state } => CStatementOutcome::Return { value, state },
        CFunctionOutcome::Throw { .. } => {
            return Ok(Err(CRuntimeError::FunctionContract(
                "exceptional outcomes require an exceptional contract interface".to_string(),
            )));
        }
        CFunctionOutcome::VerificationDiverges => {
            return Ok(Ok((CFunctionOutcome::VerificationDiverges, Vec::new())));
        }
        CFunctionOutcome::UndefinedBehavior(error) => {
            return Ok(Ok((CFunctionOutcome::UndefinedBehavior(error), Vec::new())));
        }
        CFunctionOutcome::RuntimeError(error) => return Ok(Err(error)),
    };
    let (outcome, obligations, _loan_evidence) = crate::instrumentation::measure_operation(
        function.name(),
        "contract resource transition",
        "contract resource outcome reconstruction",
        || {
            function_outcome_from_body_with_resource_transfer(
                caller_state,
                function,
                statement_outcome,
                Vec::new(),
                assumptions,
                &transfer,
                &argument_values,
                false,
                budget,
            )
        },
    )?;
    match outcome {
        CFunctionOutcome::RuntimeError(error) => Ok(Err(error)),
        outcome => Ok(Ok((outcome, obligations))),
    }
}

pub(super) fn function_outcome_from_body(
    caller_state: &CState,
    function: &CFunction,
    outcome: CStatementOutcome,
    mut obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    return_resources: Option<&ResourceContext>,
) -> (CFunctionOutcome, Vec<ProofObligation>) {
    match outcome {
        CStatementOutcome::Return { value, mut state } => {
            let Some(value) =
                coerce_function_return_value(value, function, &mut obligations, assumptions)
            else {
                return (
                    CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                        "{} returned a value that does not match its declared type",
                        function.name()
                    ))),
                    obligations,
                );
            };
            let value = if let Some(layout) = function.return_aggregate_layout() {
                // The return materializer copies the callee's aggregate into
                // a caller-visible slot. Reading an unwritten field there is
                // an uninitialized read, not a contract violation, so check
                // the source before materializing.
                if let CValue::Pointer(pointer) = &value
                    && !pointer.is_null()
                    && aggregate_copy_reads_uninitialized(&state.memory, pointer.pointer(), layout)
                {
                    return (
                        CFunctionOutcome::UndefinedBehavior(CUndefinedBehavior::UninitializedRead),
                        obligations,
                    );
                }
                let Some(value) = materialize_aggregate_return(&mut state, function, value) else {
                    return (
                        CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                            "{} returned an invalid struct value",
                            function.name()
                        ))),
                        obligations,
                    );
                };
                value
            } else {
                value
            };

            let mut caller_state = caller_state.clone();
            caller_state.set_memory(state.memory.clone());
            if function.has_inline_body() {
                // Inline bodies execute with a parameter-only local
                // environment, so pointer stores into caller locals cannot
                // synchronize their named bindings during body execution.
                // Reconcile those bindings from the shared caller memory
                // before the caller resumes evaluating its next statement.
                let memory = caller_state.memory.clone();
                caller_state.sync_scalar_locals_from_memory(&memory);
            }
            // The body ran on its entry ledger and may have projected viewed
            // composite children into it (or, for an inline body, made calls
            // on the caller's ledger); the return state carries the body's
            // ledger. A modular call's recovery replaces it afterwards.
            caller_state = caller_state
                .with_loan_ledger(state.loan_ledger().cloned())
                .with_loan_participant(state.loan_participant());
            if return_resources.is_none() {
                caller_state.instance_field_scope = state.instance_field_scope;
            }
            caller_state = caller_state
                .with_resource_context(return_resources.cloned().unwrap_or(state.resources));
            caller_state.counted_populations = state.counted_populations;
            caller_state.next_local_frame = state.next_local_frame;
            caller_state.next_local_lifetime = state.next_local_lifetime;
            (
                CFunctionOutcome::Return {
                    value,
                    state: caller_state,
                },
                obligations,
            )
        }
        CStatementOutcome::Throw { value, state } => {
            if !function.exceptional_signature().permits(&value) {
                return (
                    CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(format!(
                        "{} produced an exceptional outcome not declared by its signature",
                        function.name()
                    ))),
                    obligations,
                );
            }
            let mut caller_state = caller_state.clone();
            caller_state.set_memory(state.memory.clone());
            if function.has_inline_body() {
                let memory = caller_state.memory.clone();
                caller_state.sync_scalar_locals_from_memory(&memory);
            }
            caller_state = caller_state
                .with_loan_ledger(state.loan_ledger().cloned())
                .with_loan_participant(state.loan_participant());
            if return_resources.is_none() {
                caller_state.instance_field_scope = state.instance_field_scope;
            }
            caller_state = caller_state
                .with_resource_context(return_resources.cloned().unwrap_or(state.resources));
            caller_state.counted_populations = state.counted_populations;
            caller_state.next_local_frame = state.next_local_frame;
            caller_state.next_local_lifetime = state.next_local_lifetime;
            (
                CFunctionOutcome::Throw {
                    value,
                    state: caller_state,
                },
                obligations,
            )
        }
        CStatementOutcome::Normal(_) => (
            CFunctionOutcome::RuntimeError(CRuntimeError::MissingReturn),
            obligations,
        ),
        CStatementOutcome::Break(_)
        | CStatementOutcome::Continue(_)
        | CStatementOutcome::Jump { .. } => (
            CFunctionOutcome::RuntimeError(CRuntimeError::MissingReturn),
            obligations,
        ),
        CStatementOutcome::VerificationDiverges => {
            (CFunctionOutcome::VerificationDiverges, obligations)
        }
        CStatementOutcome::UndefinedBehavior(undefined_behavior) => (
            CFunctionOutcome::UndefinedBehavior(undefined_behavior),
            obligations,
        ),
        CStatementOutcome::RuntimeError(error) => {
            (CFunctionOutcome::RuntimeError(error), obligations)
        }
    }
}

fn exceptional_outcome_declaration_error(
    function: &CFunction,
    outcome: &CStatementOutcome,
) -> Option<CRuntimeError> {
    let CStatementOutcome::Throw { value, .. } = outcome else {
        return None;
    };
    (!function.exceptional_signature().permits(value)).then(|| {
        CRuntimeError::FunctionContract(format!(
            "{} produced an exceptional outcome not declared by its signature",
            function.name()
        ))
    })
}

impl From<u32> for Bitvector32Term {
    fn from(value: u32) -> Self {
        Self::Constant(value)
    }
}

impl From<bool> for ConditionTerm {
    fn from(value: bool) -> Self {
        Self::Constant(value)
    }
}

#[cfg(test)]
mod provisional_ensure_obligation_tests {
    use super::*;

    #[test]
    fn provisional_ensure_loadability_work_ignores_unrelated_facts() {
        let memory = CMemory::new();
        let data = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let state = CState::new()
            .with_local("data", CValue::pointer(data.clone()))
            .with_memory(memory.clone());
        let ensure = SpecProposition::Comparison {
            left: SpecExpression::MemoryLoad {
                memory: SpecMemory::Current,
                pointer: Box::new(SpecExpression::PointerOffset {
                    pointer: Box::new(SpecExpression::CExpression(c_variable("data"))),
                    elements: Box::new(SpecExpression::CExpression(c_int32_literal(1))),
                    byte_width: 4,
                }),
                value_type: CType::Int32,
            },
            operator: CComparisonOperator::Equal,
            right: SpecExpression::CExpression(c_int32_literal(0)),
        };
        let function = c_function(
            CType::Int32,
            "provisional_loadability_probe",
            vec![c_parameter("data", CType::Int32Pointer)],
            c_return(c_int32_literal(0)),
        )
        .with_contract(Vec::new(), vec![ensure], Vec::new(), Vec::new(), true);
        let base_assumptions =
            PureFactContext::new().assume_proposition(Proposition::CMemoryLoadable {
                memory: memory.clone(),
                base: data.clone(),
                bytes: Bitvector32Term::Constant(8),
            });
        let element_loadable = Proposition::CMemoryLoadable {
            memory,
            base: data.offset_by_int32_elements(Bitvector32Term::Constant(1)),
            bytes: Bitvector32Term::Constant(4),
        };
        let mut work_by_size = Vec::new();
        for unrelated_count in [16, 64, 256, 1024] {
            let mut assumptions = base_assumptions.clone();
            for index in 0..unrelated_count {
                assumptions = assumptions.assume_proposition(Proposition::Predicate {
                    name: format!("unrelated_{index}"),
                    arguments: Vec::new(),
                });
            }
            let mut facts = Vec::new();
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                add_verified_function_ensure_facts(
                    &mut facts,
                    &[],
                    &state,
                    &state,
                    &function,
                    &assumptions,
                    &mut ExecutionBudget::new(),
                )
            });
            result.expect("the provisional ensure should lower");
            assert!(
                facts
                    .iter()
                    .any(|fact| fact.proposition() == &element_loadable),
                "contextual loadability must remain an explicit provisional obligation"
            );
            work_by_size.push((unrelated_count, work));
        }

        let baseline = work_by_size[0].1.max(1);
        let largest = work_by_size.last().unwrap().1;
        assert!(
            largest <= baseline * 2,
            "provisional ensure work should be independent of unrelated facts: {work_by_size:?}"
        );
    }
}

#[cfg(test)]
mod verified_call_initialization_tests {
    use super::*;

    fn local_pointer() -> Pointer {
        Pointer {
            block: PointerBlock::Concrete("local:caller:x".to_string()),
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    fn owned_cell_spec() -> CResourceSpec {
        CResourceSpec::owned_memory(CMemorySegment::new(
            c_variable("p"),
            c_int32_literal(0),
            c_int32_literal(1),
        ))
    }

    fn caller_state(pointer: &Pointer) -> CState {
        let resources = ResourceContext::new().unchecked_with_fact(CResourceFact::own(
            CResource::Memory(CMemoryRange::new(
                pointer.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )),
        ));
        CState::new()
            .with_memory(CMemory::new().with_block(pointer.block.clone(), 4))
            .with_resource_context(resources)
    }

    fn apply(function: CFunction, state: &CState, pointer: &Pointer) -> Vec<CFunctionPath> {
        let environment =
            CExecutionEnvironment::new().with_verified_function_rule(CVerifiedFunctionRule {
                function: function.clone(),
                loop_semantics: CLoopSemantics::Verify,
            });
        execute_c_function_call_paths(
            state,
            &function,
            &[c_pointer_value(pointer.clone())],
            &PureFactContext::new(),
            &environment,
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &mut ExecutionBudget::new(),
        )
        .expect("verified call should execute")
    }

    #[test]
    fn owned_read_does_not_treat_ownership_as_initialization() {
        let pointer = local_pointer();
        let function = c_function(
            CType::Int32,
            "read_owned",
            vec![c_parameter("p", CType::Int32Pointer)],
            c_return(c_index(c_variable("p"), c_int32_literal(0))),
        )
        .with_resource_summary(vec![owned_cell_spec()], Vec::new());
        let paths = apply(function, &caller_state(&pointer), &pointer);
        assert!(matches!(
            paths.as_slice(),
            [CFunctionPath {
                outcome: CFunctionOutcome::UndefinedBehavior(CUndefinedBehavior::UninitializedRead),
                ..
            }]
        ));
    }

    #[test]
    fn owned_write_keeps_an_uninitialized_output_writable() {
        let pointer = local_pointer();
        let function = c_function(
            CType::Void,
            "write_owned",
            vec![c_parameter("p", CType::Int32Pointer)],
            c_store(
                c_index(c_variable("p"), c_int32_literal(0)),
                c_int32_literal(7),
            ),
        )
        .with_resource_summary(vec![owned_cell_spec()], Vec::new())
        .with_contract(
            Vec::new(),
            Vec::new(),
            vec![CMemorySegment::new(
                c_variable("p"),
                c_int32_literal(0),
                c_int32_literal(1),
            )],
            Vec::new(),
            true,
        );
        let paths = apply(function, &caller_state(&pointer), &pointer);
        assert!(matches!(
            paths.as_slice(),
            [CFunctionPath {
                outcome: CFunctionOutcome::Return { .. },
                ..
            }]
        ));
    }
}

#[cfg(test)]
mod integer_parameter_read_tests {
    use super::*;

    #[test]
    fn nested_integer_conversions_keep_current_parameter_reads_visible() {
        let value = SpecIntegerExpression::Negate(Box::new(SpecIntegerExpression::FromMachine(
            Box::new(SpecExpression::CExpression(c_variable("parameter"))),
        )));
        let conversion = SpecExpression::IntegerToMachine {
            value: Box::new(value.clone()),
            destination: MachineIntegerType::Int32,
        };
        assert!(spec_expression_reads_current_parameter(
            &conversion,
            "parameter"
        ));
        assert!(!spec_expression_reads_current_parameter(
            &conversion,
            "other"
        ));
        let comparison = SpecProposition::IntegerComparison {
            left: SpecIntegerExpression::Term(IntegerTerm::constant_i64(0)),
            operator: IntegerComparisonOperator::Equal,
            right: value,
        };
        assert!(spec_proposition_reads_current_parameter(
            &comparison,
            "parameter"
        ));
        assert!(!spec_proposition_reads_current_parameter(
            &comparison,
            "other"
        ));
    }
}

#[cfg(test)]
mod stable_view_call_tests {
    use super::*;
    use crate::kernel::loans::LoanRefusal;

    fn pointer() -> Pointer {
        Pointer {
            block: PointerBlock::Concrete("local:candidate_view:data".to_string()),
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    fn caller(pointer: &Pointer) -> CState {
        caller_with_owned_end(pointer, 1, 4)
    }

    fn caller_with_owned_end(pointer: &Pointer, owned_end: u32, bytes: u32) -> CState {
        let range = CMemoryRange::new(
            pointer.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(owned_end),
        );
        CState::new()
            .with_memory(
                CMemory::new()
                    .with_block(pointer.block.clone(), bytes)
                    .store(pointer.clone(), int32(7)),
            )
            .with_resource_context(
                ResourceContext::new()
                    .unchecked_with_fact(CResourceFact::own(CResource::Memory(range))),
            )
    }

    fn reader_with_output(name: &str, output_start: u32, output_end: u32) -> CFunction {
        let input = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1));
        let output = CMemorySegment::new(
            c_variable("p"),
            c_int32_literal(output_start),
            c_int32_literal(output_end),
        );
        c_function(
            CType::Int32,
            name,
            vec![c_parameter("p", CType::Int32Pointer)],
            c_return(c_load(c_variable("p"))),
        )
        .with_resource_summary(
            vec![CResourceSpec::viewed_memory(input)],
            vec![CResourceSpec::viewed_memory(output)],
        )
    }

    fn reader_for_input(name: &str, input_end: u32) -> CFunction {
        let input = CMemorySegment::new(
            c_variable("p"),
            c_int32_literal(0),
            c_int32_literal(input_end),
        );
        c_function(
            CType::Int32,
            name,
            vec![c_parameter("p", CType::Int32Pointer)],
            c_return(c_load(c_variable("p"))),
        )
        .with_resource_summary(vec![CResourceSpec::viewed_memory(input)], Vec::new())
    }

    fn reader_with_mutable_range(name: &str, mutable_start: u32, mutable_end: u32) -> CFunction {
        let input = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1));
        c_function(
            CType::Int32,
            name,
            vec![c_parameter("p", CType::Int32Pointer)],
            c_return(c_load(c_variable("p"))),
        )
        .with_resource_summary(vec![CResourceSpec::viewed_memory(input)], Vec::new())
        .with_contract(
            Vec::new(),
            Vec::new(),
            vec![CMemorySegment::new(
                c_variable("p"),
                c_int32_literal(mutable_start),
                c_int32_literal(mutable_end),
            )],
            Vec::new(),
            true,
        )
    }

    fn reader(name: &str, duplicate_view: bool) -> CFunction {
        let segment = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1));
        let mut requires = vec![CResourceSpec::viewed_memory(segment.clone())];
        if duplicate_view {
            requires.push(CResourceSpec::viewed_memory(segment));
        }
        c_function(
            CType::Int32,
            name,
            vec![c_parameter("p", CType::Int32Pointer)],
            c_return(c_load(c_variable("p"))),
        )
        .with_resource_summary(requires, Vec::new())
    }

    fn composite_reader(name: &str) -> CFunction {
        let segment = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1));
        let required = CResourceSpec::declared(
            ResourceFamily::Composite,
            CResourceAccessMode::View,
            "cell".into(),
            vec![c_variable("p")],
            vec![CType::Int32Pointer],
            CResourceTransferRole::Borrow,
            CResourceSnapshot::Entry,
        )
        .unwrap();
        let definition = CCompositeResourceDefinition::new(
            "cell",
            vec![c_parameter("p", CType::Int32Pointer)],
            None,
            false,
            vec![CResourceSpec::owned_memory(segment)],
            Vec::new(),
        );
        c_function(
            CType::Int32,
            name,
            vec![c_parameter("p", CType::Int32Pointer)],
            c_return(c_load(c_variable("p"))),
        )
        .with_resource_summary(vec![required], Vec::new())
        .with_composite_resource_definitions(vec![definition])
    }

    fn early_reader(name: &str) -> CFunction {
        let segment = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1));
        c_function(
            CType::Void,
            name,
            vec![c_parameter("p", CType::Int32Pointer)],
            CStatement::If {
                condition: c_int32_literal(1),
                then_branch: Box::new(c_return(c_void_value())),
                else_branch: Box::new(CStatement::Skip),
            },
        )
        .with_resource_summary(vec![CResourceSpec::viewed_memory(segment)], Vec::new())
    }

    /// `resource guarded_item(item) { if item != 0 { owns item[0..1]; } }`
    /// consumed by a function whose body reads nothing.
    fn conditional_owner(name: &str) -> (CFunction, CExecutionEnvironment) {
        let definition = CCompositeResourceDefinition::new(
            "guarded_item",
            vec![c_parameter("item", CType::Int32Pointer)],
            Some(SpecProposition::Comparison {
                left: SpecExpression::CExpression(c_variable("item")),
                operator: CComparisonOperator::NotEqual,
                right: SpecExpression::Value(CValue::pointer(Pointer::null())),
            }),
            false,
            vec![CResourceSpec::owned_memory(CMemorySegment::new(
                c_variable("item"),
                c_int32_literal(0),
                c_int32_literal(1),
            ))],
            Vec::new(),
        );
        let function = c_function(
            CType::Int32,
            name,
            vec![c_parameter("item", CType::Int32Pointer)],
            c_return(c_int32_literal(0)),
        )
        .with_resource_summary(
            vec![CResourceSpec::composite(
                CResourceAccessMode::Own,
                "guarded_item".to_string(),
                vec![c_variable("item")],
                vec![CType::Int32Pointer],
            )],
            Vec::new(),
        )
        .with_composite_resource_definitions(vec![definition]);
        let environment = environment(&function);
        (function, environment)
    }

    fn environment(function: &CFunction) -> CExecutionEnvironment {
        CExecutionEnvironment::new().with_verified_function_rule(CVerifiedFunctionRule {
            function: function.clone(),
            loop_semantics: CLoopSemantics::Verify,
        })
    }

    #[test]
    fn independent_verification_uses_the_call_transfer_boundary() {
        let pointer = pointer();
        let function = reader_for_input("candidate_verified_reader", 1);
        let state = caller(&pointer);
        let mut budget = ExecutionBudget::new();
        let mut variables = KernelVariableGenerator::fresh_for(0, BTreeSet::new());
        let paths = execute_c_function_verification_paths(
            &state,
            &function,
            &[c_pointer_value(pointer)],
            &PureFactContext::new(),
            &environment(&function),
            CExecutionSemantics::EXECUTE_BODIES,
            &mut budget,
            &mut variables,
            true,
        )
        .expect("verification should execute through the transfer boundary");
        assert!(matches!(
            paths.as_slice(),
            [CFunctionPath {
                outcome: CFunctionOutcome::Return { .. },
                ..
            }]
        ));
    }

    #[test]
    fn candidate_reader_escrows_owner_until_return() {
        let pointer = pointer();
        let function = reader("candidate_reader", false);
        let caller = caller(&pointer);
        let argument_values = vec![CValue::pointer(pointer.clone())];
        let callee = bind_c_function_arguments(&caller, &function, &argument_values)
            .expect("reader argument should bind");
        let transfer = prepare_function_resource_transfer(
            &caller,
            &callee,
            &function,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
            true,
            ResourceTransitionPurpose::CallSite,
        )
        .expect("candidate transfer should run")
        .expect("candidate transfer should be accepted");
        let plan = transfer
            .stable_view_plan
            .as_ref()
            .expect("candidate transfer records a loan plan");
        assert_eq!(plan.stable_views().len(), 1);
        assert!(
            !transfer.caller_resources_after_requirements.satisfies_fact(
                &CResourceFact::own_memory(CMemoryRange::new(
                    pointer,
                    Bitvector32Term::Constant(0),
                    Bitvector32Term::Constant(1),
                )),
                &PureFactContext::new()
            )
        );
        assert!(transfer.callee_resources.satisfies_fact(
            &CResourceFact::view_memory(CMemoryRange::new(
                Pointer {
                    block: PointerBlock::Concrete("local:candidate_view:data".to_string()),
                    offset: PointerOffsetTerm::Constant(0),
                },
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )),
            &PureFactContext::new(),
        ));
    }

    #[test]
    fn candidate_function_entry_preserves_outer_loan_authority() {
        let pointer = pointer();
        let function = c_function(
            CType::Void,
            "candidate_empty_resource_entry",
            vec![c_parameter("p", CType::Int32Pointer)],
            c_return(c_void_value()),
        );
        let ledger = LoanLedger::new();
        let participant = ledger.fresh_participant().expect("caller participant");
        let caller_state = caller(&pointer)
            .with_loan_ledger(Some(ledger.clone()))
            .with_loan_participant(Some(participant));
        let callee =
            bind_c_function_arguments(&caller_state, &function, &[CValue::pointer(pointer)])
                .expect("the function argument should bind");

        assert_eq!(callee.loan_ledger(), Some(&ledger));
        assert_eq!(callee.loan_participant(), Some(participant));
        assert!(callee.loan_bindings_are_consistent());
    }

    #[test]
    fn candidate_composite_call_lends_primitive_body_and_recovers_head() {
        let pointer = pointer();
        let head =
            CResourceFact::own_composite("cell".into(), vec![CValue::pointer(pointer.clone())]);
        let caller = CState::new()
            .with_memory(
                CMemory::new()
                    .with_block(pointer.block.clone(), 4)
                    .store(pointer.clone(), int32(7)),
            )
            .with_resource_context(ResourceContext::new().unchecked_with_fact(head.clone()));
        let function = composite_reader("candidate_composite_reader");
        let callee =
            bind_c_function_arguments(&caller, &function, &[CValue::pointer(pointer.clone())])
                .expect("composite reader arguments should bind");
        let transfer = prepare_function_resource_transfer(
            &caller,
            &callee,
            &function,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
            true,
            ResourceTransitionPurpose::CallSite,
        )
        .expect("composite transfer should run")
        .expect("composite transfer should be accepted");
        let plan = transfer
            .stable_view_plan
            .as_ref()
            .expect("composite transfer records a loan plan");
        assert_eq!(plan.stable_views().len(), 1);
        assert!(plan.ledger.has_active_memory_loans());
        let body_range = CMemoryRange::new(
            pointer.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        );
        assert_eq!(
            plan.ledger.permits_memory_access(&body_range),
            Err(LoanRefusal::ActiveDependency)
        );
        assert!(transfer.callee_resources.satisfies_fact(
            &CResourceFact::view_composite("cell".into(), vec![CValue::pointer(pointer.clone())],),
            &PureFactContext::new(),
        ));
        let callee_state = callee_state_with_resource_transfer(callee, &transfer);
        let (resources, _, _, _, evidence) = recover_candidate_stable_view_resources(
            &caller,
            &callee_state,
            &transfer,
            ResourceContext::new(),
            &PureFactContext::new(),
            &PureFactContext::new(),
            &[],
        )
        .expect("composite return should recover");
        assert!(resources.satisfies_fact(&head, &PureFactContext::new()));
        assert!(evidence.is_some());
    }

    /// A composite view lent twice in a row: the first return must leave
    /// the caller exactly the recovered head, so the second lend finds one
    /// owner and no exposed body piece beside it.
    fn composite_reader_with_definition(
        name: &str,
        definition: CCompositeResourceDefinition,
    ) -> CFunction {
        let required = CResourceSpec::declared(
            ResourceFamily::Composite,
            CResourceAccessMode::View,
            "cell".into(),
            vec![c_variable("p")],
            vec![CType::Int32Pointer],
            CResourceTransferRole::Borrow,
            CResourceSnapshot::Entry,
        )
        .unwrap();
        c_function(
            CType::Int32,
            name,
            vec![c_parameter("p", CType::Int32Pointer)],
            c_return(c_load(c_variable("p"))),
        )
        .with_resource_summary(vec![required], Vec::new())
        .with_composite_resource_definitions(vec![definition])
    }

    fn fact_bearing_cell_definition() -> CCompositeResourceDefinition {
        let segment = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1));
        CCompositeResourceDefinition::new(
            "cell",
            vec![c_parameter("p", CType::Int32Pointer)],
            None,
            false,
            vec![CResourceSpec::owned_memory(segment)],
            vec![SpecProposition::Defined(SpecExpression::Value(int32(0)))],
        )
    }

    fn plan_composite_lend(function: &CFunction) -> Result<(), CRuntimeError> {
        let pointer = pointer();
        let head =
            CResourceFact::own_composite("cell".into(), vec![CValue::pointer(pointer.clone())]);
        let caller = CState::new()
            .with_memory(
                CMemory::new()
                    .with_block(pointer.block.clone(), 4)
                    .store(pointer.clone(), int32(7)),
            )
            .with_resource_context(ResourceContext::new().unchecked_with_fact(head));
        let callee = bind_c_function_arguments(&caller, function, &[CValue::pointer(pointer)])
            .expect("composite reader arguments should bind");
        prepare_function_resource_transfer(
            &caller,
            &callee,
            function,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
            true,
            ResourceTransitionPurpose::CallSite,
        )
        .expect("composite transfer should run")
        .map(|_| ())
    }

    /// Recovery restores the exact escrowed head, so a body fact over the
    /// body's own cells is re-asserted as folded: such a composite lends.
    #[test]
    fn candidate_composite_with_body_facts_is_lendable() {
        let function = composite_reader_with_definition(
            "candidate_fact_bearing_reader",
            fact_bearing_cell_definition(),
        );
        plan_composite_lend(&function).expect("a fact over the body's own cells is loan-stable");
    }

    /// A fact that claims liveness of storage outside the body, or one that
    /// reads a population count, is not stabilized by the loan.
    #[test]
    fn candidate_composite_with_unstable_facts_is_refused() {
        let liveness = composite_reader_with_definition(
            "candidate_liveness_fact_reader",
            fact_bearing_cell_definition().with_liveness_facts(true),
        );
        let error = plan_composite_lend(&liveness).expect_err("a liveness fact is refused");
        assert!(
            matches!(&error, CRuntimeError::FunctionContract(message) if message.contains("allocation-liveness")),
            "{error:?}"
        );
        let segment = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1));
        let counted = composite_reader_with_definition(
            "candidate_counted_fact_reader",
            CCompositeResourceDefinition::counted_population(
                "cell",
                vec![c_parameter("p", CType::Int32Pointer)],
                None,
                vec![CResourceSpec::owned_memory(segment)],
                vec![SpecProposition::Defined(SpecExpression::Value(int32(0)))],
            ),
        );
        assert!(plan_composite_lend(&counted).is_err());
    }

    // The owned-interface-to-viewed-implementation adapter (docs/internals/stable-views.md):
    // the callee's clause names one composite, the caller owns another whose
    // checked frontier covers it.

    fn cell_definition(end: u32, facts: Vec<SpecProposition>) -> CCompositeResourceDefinition {
        let segment =
            CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(end));
        CCompositeResourceDefinition::new(
            "cell",
            vec![c_parameter("p", CType::Int32Pointer)],
            None,
            false,
            vec![CResourceSpec::owned_memory(segment)],
            facts,
        )
    }

    fn wide_definition(end: u32) -> CCompositeResourceDefinition {
        let segment =
            CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(end));
        CCompositeResourceDefinition::new(
            "wide",
            vec![c_parameter("p", CType::Int32Pointer)],
            None,
            false,
            vec![CResourceSpec::owned_memory(segment)],
            Vec::new(),
        )
    }

    /// A reader that views `cell(p)` and knows both definitions.
    fn adapter_reader(
        name: &str,
        cell: CCompositeResourceDefinition,
        wide: CCompositeResourceDefinition,
    ) -> CFunction {
        let required = CResourceSpec::declared(
            ResourceFamily::Composite,
            CResourceAccessMode::View,
            "cell".into(),
            vec![c_variable("p")],
            vec![CType::Int32Pointer],
            CResourceTransferRole::Borrow,
            CResourceSnapshot::Entry,
        )
        .unwrap();
        c_function(
            CType::Int32,
            name,
            vec![c_parameter("p", CType::Int32Pointer)],
            c_return(c_load(c_variable("p"))),
        )
        .with_resource_summary(vec![required], Vec::new())
        .with_composite_resource_definitions(vec![cell, wide])
    }

    /// The caller owns `wide(p)` over an eight-byte block and nothing else.
    fn adapter_caller(pointer: &Pointer) -> CState {
        let second = Pointer {
            block: pointer.block.clone(),
            offset: PointerOffsetTerm::Constant(4),
        };
        CState::new()
            .with_memory(
                CMemory::new()
                    .with_block(pointer.block.clone(), 8)
                    .store(pointer.clone(), int32(7))
                    .store(second, int32(9)),
            )
            .with_resource_context(ResourceContext::new().unchecked_with_fact(
                CResourceFact::own_composite("wide".into(), vec![CValue::pointer(pointer.clone())]),
            ))
    }

    fn plan_adapter_lend(
        function: &CFunction,
    ) -> (CState, Result<CFunctionResourceTransfer, CRuntimeError>) {
        let pointer = pointer();
        let caller = adapter_caller(&pointer);
        let callee =
            bind_c_function_arguments(&caller, function, &[CValue::pointer(pointer.clone())])
                .expect("adapter reader arguments should bind");
        let transfer = prepare_function_resource_transfer(
            &caller,
            &callee,
            function,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
            true,
            ResourceTransitionPurpose::CallSite,
        )
        .expect("adapter transfer should run");
        (caller, transfer)
    }

    /// The caller owns `wide(p)` over `p[0..2]`; the callee views `cell(p)`
    /// over `p[0..1]`. The lend escrows the owner the caller actually holds,
    /// `views cell(p)` joins that loan's permitted descriptions, and recovery
    /// restores `wide(p)` exactly.
    #[test]
    fn candidate_composite_view_is_backed_by_a_covering_owned_composite() {
        let function = adapter_reader(
            "candidate_adapter_reader",
            cell_definition(1, Vec::new()),
            wide_definition(2),
        );
        let pointer = pointer();
        let (caller, transfer) = plan_adapter_lend(&function);
        let transfer = transfer.expect("a covering owner backs the viewed composite");
        let plan = transfer
            .stable_view_plan
            .as_ref()
            .expect("the adapter lend records a loan plan");
        assert_eq!(plan.stable_views().len(), 1);
        assert!(transfer.callee_resources.satisfies_fact(
            &CResourceFact::view_composite("cell".into(), vec![CValue::pointer(pointer.clone())]),
            &PureFactContext::new(),
        ));
        // The whole escrowed frontier is protected, not just the adapted
        // clause's own bytes.
        for end in [1, 2] {
            let range = CMemoryRange::new(
                pointer.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(end),
            );
            assert_eq!(
                plan.ledger.permits_memory_access(&range),
                Err(LoanRefusal::ActiveDependency)
            );
        }
        let callee =
            bind_c_function_arguments(&caller, &function, &[CValue::pointer(pointer.clone())])
                .expect("adapter reader arguments should bind");
        let callee_state = callee_state_with_resource_transfer(callee, &transfer);
        let (resources, _, _, _, _) = recover_candidate_stable_view_resources(
            &caller,
            &callee_state,
            &transfer,
            ResourceContext::new(),
            &PureFactContext::new(),
            &PureFactContext::new(),
            &[],
        )
        .expect("the adapter lend should recover");
        let head = CResourceFact::own_composite("wide".into(), vec![CValue::pointer(pointer)]);
        assert!(resources.satisfies_fact(&head, &PureFactContext::new()));
        assert_eq!(resources.facts(), [head]);
    }

    /// The owner's body has to cover every piece of the viewed composite's
    /// checked frontier. Half of it is not backing.
    #[test]
    fn candidate_composite_view_over_an_uncovered_owner_is_refused() {
        let function = adapter_reader(
            "candidate_uncovered_adapter_reader",
            cell_definition(2, Vec::new()),
            wide_definition(1),
        );
        let (_, transfer) = plan_adapter_lend(&function);
        let error = transfer.expect_err("an owner that covers half the frontier is not backing");
        let CRuntimeError::LoanRefusal(diagnostic) = &error else {
            panic!("{error:?}");
        };
        assert_eq!(
            diagnostic.category(),
            crate::kernel::loans::LoanRefusalCategory::Missing
        );
        assert_eq!(
            diagnostic.subject().resource_fact(),
            Some(&CResourceFact::view_composite(
                "cell".into(),
                vec![CValue::pointer(pointer())]
            ))
        );
    }

    /// The viewed composite's facts are what `observe` publishes inside the
    /// callee, so the caller has to have established them. A fact the owner's
    /// frontier does not give is a refusal, not an assumption.
    #[test]
    fn candidate_composite_view_with_an_unestablished_fact_is_refused() {
        let unestablished = SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_load(c_variable("p"))),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::CExpression(c_int32_literal(0)),
        };
        let function = adapter_reader(
            "candidate_unestablished_fact_adapter_reader",
            cell_definition(1, vec![unestablished]),
            wide_definition(2),
        );
        let (_, transfer) = plan_adapter_lend(&function);
        let error = transfer.expect_err("an unestablished body fact is refused");
        let CRuntimeError::LoanRefusal(diagnostic) = &error else {
            panic!("{error:?}");
        };
        assert_eq!(
            diagnostic.category(),
            crate::kernel::loans::LoanRefusalCategory::Missing
        );
        // The same adapter with a fact the call already establishes is
        // accepted, so the refusal above is the fact check and not the shape.
        let established = adapter_reader(
            "candidate_established_fact_adapter_reader",
            cell_definition(
                1,
                vec![SpecProposition::Defined(SpecExpression::Value(int32(0)))],
            ),
            wide_definition(2),
        );
        plan_adapter_lend(&established)
            .1
            .expect("an established body fact backs the adapter");
    }

    /// With no owned composite to escrow, the planner materializes the viewed
    /// composite out of exactly the owned frontier the caller holds, and
    /// recovery hands those facts back: the caller's packaging is the same
    /// after the call as before it, and the unlent remainder stays writable.
    #[test]
    fn candidate_composite_view_is_materialized_from_the_caller_frontier() {
        let pointer = pointer();
        let function = composite_reader("candidate_materialized_adapter_reader");
        let caller = caller_with_owned_end(&pointer, 2, 8);
        let callee =
            bind_c_function_arguments(&caller, &function, &[CValue::pointer(pointer.clone())])
                .expect("composite reader arguments should bind");
        let transfer = prepare_function_resource_transfer(
            &caller,
            &callee,
            &function,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
            true,
            ResourceTransitionPurpose::CallSite,
        )
        .expect("materialized transfer should run")
        .expect("the caller's own frontier backs the viewed composite");
        let plan = transfer
            .stable_view_plan
            .as_ref()
            .expect("the materialized lend records a loan plan");
        let lent = CMemoryRange::new(
            pointer.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        );
        let kept = CMemoryRange::new(
            pointer.clone(),
            Bitvector32Term::Constant(1),
            Bitvector32Term::Constant(2),
        );
        assert_eq!(
            plan.ledger.permits_memory_access(&lent),
            Err(LoanRefusal::ActiveDependency)
        );
        assert_eq!(plan.ledger.permits_memory_access(&kept), Ok(()));
        assert!(transfer.callee_resources.satisfies_fact(
            &CResourceFact::view_composite("cell".into(), vec![CValue::pointer(pointer.clone())]),
            &PureFactContext::new(),
        ));
        let callee_state = callee_state_with_resource_transfer(callee, &transfer);
        let (resources, _, _, _, _) = recover_candidate_stable_view_resources(
            &caller,
            &callee_state,
            &transfer,
            ResourceContext::new(),
            &PureFactContext::new(),
            &PureFactContext::new(),
            &[],
        )
        .expect("the materialized lend should recover");
        // Recovery hands back the frontier the head was materialized from,
        // never a `cell(p)` head the caller never held. (`return_resources`
        // is empty here, so what is left is exactly the recovered escrow.)
        assert_eq!(
            resources.facts(),
            [CResourceFact::own(CResource::Memory(lent))]
        );
    }

    /// A callee that views `p[0..1]` and, in the same contract, produces a
    /// composite whose body is that same range. Whatever the caller lent, it
    /// gets back: composing the produced head beside it would leave the caller
    /// owning `p[0..1]` twice, once directly and once inside `zz_box3(p)`.
    fn view_and_produce_reader(name: &str) -> CFunction {
        let segment = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1));
        let produced = CResourceSpec::declared(
            ResourceFamily::Composite,
            CResourceAccessMode::Own,
            "zz_box3".into(),
            vec![c_variable("p")],
            vec![CType::Int32Pointer],
            CResourceTransferRole::Produce,
            CResourceSnapshot::Post,
        )
        .unwrap();
        let definition = CCompositeResourceDefinition::new(
            "zz_box3",
            vec![c_parameter("p", CType::Int32Pointer)],
            None,
            false,
            vec![CResourceSpec::owned_memory(segment.clone())],
            Vec::new(),
        );
        c_function(
            CType::Int32,
            name,
            vec![c_parameter("p", CType::Int32Pointer)],
            c_return(c_load(c_variable("p"))),
        )
        .with_resource_summary(vec![CResourceSpec::viewed_memory(segment)], vec![produced])
        .with_composite_resource_definitions(vec![definition])
    }

    #[test]
    fn produced_composite_over_a_viewed_owner_is_refused() {
        let pointer = pointer();
        let function = view_and_produce_reader("view_and_produce");
        let environment =
            CExecutionEnvironment::new().with_verified_function_rule(CVerifiedFunctionRule {
                function: function.clone(),
                loop_semantics: CLoopSemantics::Verify,
            });
        let paths = execute_c_function_call_paths(
            &caller(&pointer),
            &function,
            &[c_pointer_value(pointer)],
            &PureFactContext::new(),
            &environment,
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &mut ExecutionBudget::new(),
        )
        .expect("the call should execute");
        assert!(
            paths.iter().all(|path| matches!(
                &path.outcome,
                CFunctionOutcome::RuntimeError(error) if produced_composite_overlap(error)
            )),
            "{:?}",
            paths.iter().map(|path| &path.outcome).collect::<Vec<_>>()
        );
    }

    fn produced_composite_overlap(error: &CRuntimeError) -> bool {
        matches!(
            error,
            CRuntimeError::ProducedCompositeOverlapsHeldResource { .. }
        )
    }

    #[test]
    fn candidate_composite_reader_can_be_called_twice() {
        let pointer = pointer();
        let head =
            CResourceFact::own_composite("cell".into(), vec![CValue::pointer(pointer.clone())]);
        let caller = CState::new()
            .with_memory(
                CMemory::new()
                    .with_block(pointer.block.clone(), 4)
                    .store(pointer.clone(), int32(7)),
            )
            .with_resource_context(ResourceContext::new().unchecked_with_fact(head.clone()));
        let function = composite_reader("candidate_composite_reader_twice");
        let first = execute_c_function_call_paths(
            &caller,
            &function,
            &[CExpression::Value(CValue::pointer(pointer.clone()))],
            &PureFactContext::new(),
            &environment(&function),
            CExecutionSemantics::EXECUTE_BODIES,
            &mut ExecutionBudget::new(),
        )
        .expect("first composite call should execute");
        let [
            CFunctionPath {
                outcome:
                    CFunctionOutcome::Return {
                        state: after_first, ..
                    },
                ..
            },
        ] = first.as_slice()
        else {
            panic!("first composite call should return: {first:?}");
        };
        assert_eq!(after_first.resources().facts(), std::slice::from_ref(&head));
        let second = execute_c_function_call_paths(
            after_first,
            &function,
            &[CExpression::Value(CValue::pointer(pointer.clone()))],
            &PureFactContext::new(),
            &environment(&function),
            CExecutionSemantics::EXECUTE_BODIES,
            &mut ExecutionBudget::new(),
        )
        .expect("second composite call should execute");
        assert!(
            matches!(
                second.as_slice(),
                [CFunctionPath {
                    outcome: CFunctionOutcome::Return { .. },
                    ..
                }]
            ),
            "{second:?}"
        );
    }

    #[test]
    fn candidate_reader_recovers_owner_for_following_write() {
        let pointer = pointer();
        let function = reader("candidate_reader_return", false);
        let ledger = LoanLedger::new();
        let participant = ledger.fresh_participant().expect("caller participant");
        let caller_state = caller(&pointer)
            .with_loan_ledger(Some(ledger))
            .with_loan_participant(Some(participant));
        let paths = execute_c_function_call_paths(
            &caller_state,
            &function,
            &[CExpression::Value(CValue::pointer(pointer.clone()))],
            &PureFactContext::new(),
            &environment(&function),
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &mut ExecutionBudget::new(),
        )
        .expect("candidate call should execute");
        let CFunctionOutcome::Return { state, .. } = &paths[0].outcome else {
            panic!("candidate reader should return: {:?}", paths[0].outcome);
        };
        assert_eq!(paths[0].loan_evidence.len(), 1);
        let evidence_items = paths[0].loan_evidence.to_vec();
        let evidence = &evidence_items[0];
        let caller_ledger = caller_state
            .loan_ledger()
            .cloned()
            .expect("candidate execution publishes its caller ledger");
        evidence
            .recheck(
                &caller_ledger,
                caller_state.loan_participant(),
                &evidence.entry.ledger,
                Some(evidence.entry.callee_participant()),
            )
            .expect("retained candidate evidence rechecks");
        assert_eq!(state.loan_ledger(), Some(&evidence.recovered_ledger));
        assert!(state.resources().satisfies_fact(
            &CResourceFact::own_memory(CMemoryRange::new(
                pointer,
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )),
            &PureFactContext::new(),
        ));
    }

    #[test]
    fn candidate_direct_reader_recovers_owner_for_following_write() {
        let pointer = pointer();
        let function = reader("candidate_direct_reader", false);
        let paths = execute_c_function_paths(
            &caller(&pointer),
            &function,
            &[CExpression::Value(CValue::pointer(pointer.clone()))],
            &PureFactContext::new(),
            &environment(&function),
            CExecutionSemantics::EXECUTE_BODIES,
            &mut ExecutionBudget::new(),
        )
        .expect("candidate direct call should execute");
        let CFunctionOutcome::Return { state, .. } = &paths[0].outcome else {
            panic!(
                "candidate direct reader should return: {:?}",
                paths[0].outcome
            );
        };
        assert!(state.resources().satisfies_fact(
            &CResourceFact::own_memory(CMemoryRange::new(
                pointer,
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )),
            &PureFactContext::new(),
        ));
    }

    #[test]
    fn candidate_evidence_rejects_definitionally_equal_resources_with_new_identity() {
        let pointer = pointer();
        let function = reader("candidate_identity_guard", false);
        let caller_ledger = LoanLedger::new();
        let caller_participant = caller_ledger
            .fresh_participant()
            .expect("caller participant");
        let caller_state = caller(&pointer)
            .with_loan_ledger(Some(caller_ledger.clone()))
            .with_loan_participant(Some(caller_participant));
        let paths = execute_c_function_call_paths(
            &caller_state,
            &function,
            &[CExpression::Value(CValue::pointer(pointer))],
            &PureFactContext::new(),
            &environment(&function),
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &mut ExecutionBudget::new(),
        )
        .expect("candidate call should execute");
        let evidence_items = paths[0].loan_evidence.to_vec();
        let evidence = &evidence_items[0];
        let different_participant = caller_ledger
            .fresh_participant()
            .expect("fresh participant identity");
        assert_eq!(
            evidence
                .recheck(
                    &caller_ledger,
                    Some(different_participant),
                    &evidence.entry.ledger,
                    Some(evidence.entry.callee_participant()),
                )
                .expect_err("a different caller participant must be refused"),
            LoanRefusal::WrongHolder
        );
        assert_eq!(
            evidence
                .recheck(
                    &LoanLedger::new(),
                    Some(caller_participant),
                    &evidence.entry.ledger,
                    Some(evidence.entry.callee_participant()),
                )
                .expect_err("an unrelated predecessor ledger must be refused"),
            LoanRefusal::StalePredecessor
        );
    }

    #[test]
    fn candidate_nested_body_call_retains_inner_and_outer_evidence() {
        let pointer = pointer();
        let inner = reader("candidate_nested_inner", false);
        let segment = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1));
        let outer = c_function(
            CType::Int32,
            "candidate_nested_outer",
            vec![c_parameter("p", CType::Int32Pointer)],
            CStatement::Seq(
                Arc::new(c_declare("result", CType::Int32)),
                Arc::new(CStatement::Seq(
                    Arc::new(c_call_assign("result", inner.name(), vec![c_variable("p")])),
                    Arc::new(c_return(c_variable("result"))),
                )),
            ),
        )
        .with_resource_summary(vec![CResourceSpec::viewed_memory(segment)], Vec::new());
        let environment = environment(&outer).with_function(inner);
        let ledger = LoanLedger::new();
        let participant = ledger.fresh_participant().expect("caller participant");
        let caller_state = caller(&pointer)
            .with_loan_ledger(Some(ledger))
            .with_loan_participant(Some(participant));
        let paths = execute_c_function_call_paths(
            &caller_state,
            &outer,
            &[CExpression::Value(CValue::pointer(pointer))],
            &PureFactContext::new(),
            &environment,
            CExecutionSemantics::EXECUTE_BODIES,
            &mut ExecutionBudget::new(),
        )
        .expect("nested candidate call should execute");
        assert_eq!(paths.len(), 1);
        assert_eq!(paths[0].loan_evidence.len(), 2);
        let evidence = paths[0].loan_evidence.to_vec();
        assert_eq!(
            evidence[0].entry.caller_ledger(),
            &evidence[1].entry.ledger,
            "inner evidence starts at the outer callee ledger"
        );
    }

    /// A view of the activation's own local array is implicit authority, not
    /// a caller-supplied borrow: the call composes the in-bounds view for the
    /// callee without touching the loan ledger.
    #[test]
    fn candidate_local_array_view_is_intrinsic_and_lends_nothing() {
        let pointer = pointer();
        let function = reader("candidate_local_reader", false);
        let caller = CState::new().with_memory(
            CMemory::new()
                .with_block(pointer.block.clone(), 4)
                .store(pointer.clone(), int32(7)),
        );
        let paths = execute_c_function_call_paths(
            &caller,
            &function,
            &[CExpression::Value(CValue::pointer(pointer))],
            &PureFactContext::new(),
            &environment(&function),
            CExecutionSemantics::EXECUTE_BODIES,
            &mut ExecutionBudget::new(),
        )
        .expect("candidate local view call should execute");
        assert!(matches!(
            paths.as_slice(),
            [CFunctionPath {
                outcome: CFunctionOutcome::Return { state, .. },
                ..
            }] if state.loan_ledger().is_none_or(|ledger| !ledger.has_active_memory_loans())
        ));
    }

    /// The activation-local bounds rule still applies, and it decides the
    /// call before the callee reads anything: a local view past the end of
    /// its block names storage the block does not have, so the call is
    /// refused for the missing resource rather than for a read of whatever
    /// lies beyond the block.
    #[test]
    fn candidate_local_array_view_out_of_bounds_is_refused() {
        let pointer = pointer();
        let function = reader_for_input("candidate_local_wide_reader", 4);
        let caller = CState::new().with_memory(
            CMemory::new()
                .with_block(pointer.block.clone(), 4)
                .store(pointer.clone(), int32(7)),
        );
        let paths = execute_c_function_call_paths(
            &caller,
            &function,
            &[CExpression::Value(CValue::pointer(pointer))],
            &PureFactContext::new(),
            &environment(&function),
            CExecutionSemantics::EXECUTE_BODIES,
            &mut ExecutionBudget::new(),
        )
        .expect("candidate out-of-bounds local view should execute to a diagnostic");
        assert!(
            matches!(
                paths.as_slice(),
                [CFunctionPath {
                    outcome: CFunctionOutcome::RuntimeError(CRuntimeError::MissingResource {
                        resource
                    }),
                    ..
                }] if resource.is_view()
            ),
            "the bounds rule names the unbacked view, not a later read: {paths:?}"
        );
    }

    /// A conditional composite whose guard the assumptions decide false has
    /// an empty body, so the empty context satisfies it: the planner must
    /// discharge `owns guarded_item(null)` definitionally instead of
    /// demanding an owned entry the caller was never meant to hold.
    #[test]
    fn candidate_conditional_composite_with_a_false_guard_needs_no_owned_entry() {
        let (function, environment) = conditional_owner("candidate_guarded_free");
        let paths = execute_c_function_call_paths(
            &CState::new(),
            &function,
            &[c_pointer_value(Pointer::null())],
            &PureFactContext::new(),
            &environment,
            CExecutionSemantics::EXECUTE_BODIES,
            &mut ExecutionBudget::new(),
        )
        .expect("a false composite guard should execute");
        assert!(
            matches!(
                paths.as_slice(),
                [CFunctionPath {
                    outcome: CFunctionOutcome::Return { .. },
                    ..
                }]
            ),
            "an empty body is satisfied by the empty context: {paths:?}"
        );
    }

    /// The same requirement with an undecided guard keeps its entry: only a
    /// guard the assumptions decide collapses the body, so a symbolic
    /// argument still needs the caller to supply the composite.
    #[test]
    fn candidate_conditional_composite_with_an_undecided_guard_still_needs_its_entry() {
        let (function, environment) = conditional_owner("candidate_guarded_symbolic_free");
        let symbolic = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(910_101)), 4),
        };
        let paths = execute_c_function_call_paths(
            &CState::new(),
            &function,
            &[c_pointer_value(symbolic)],
            &PureFactContext::new(),
            &environment,
            CExecutionSemantics::EXECUTE_BODIES,
            &mut ExecutionBudget::new(),
        )
        .expect("an undecided composite guard should execute to a diagnostic");
        assert!(
            matches!(
                paths.as_slice(),
                [CFunctionPath {
                    outcome: CFunctionOutcome::RuntimeError(CRuntimeError::MissingResource {
                        resource
                    }),
                    ..
                }] if matches!(
                    resource.resource(),
                    CResource::Composite { name, .. } if name == "guarded_item"
                )
            ),
            "an undecided guard is not an empty body: {paths:?}"
        );
    }

    /// Two clauses naming one token are a single demand for their combined
    /// count. The caller holds one unit, so the refusal has to name quantity
    /// two: naming one unit would name a fact the caller does hold.
    #[test]
    fn candidate_repeated_token_requirement_reports_the_demanded_quantity() {
        let requirement = |parameter| {
            CResourceSpec::token(
                CResourceAccessMode::Own,
                "can_complete".to_string(),
                vec![c_variable(parameter)],
                vec![CType::Int32],
            )
        };
        let function = c_function(
            CType::Int32,
            "candidate_consume_two",
            vec![
                c_parameter("first", CType::Int32),
                c_parameter("second", CType::Int32),
            ],
            c_return(c_int32_literal(0)),
        )
        .with_resource_summary(
            vec![requirement("first"), requirement("second")],
            Vec::new(),
        );
        let token = CValue::Int32(Bitvector32Term::Constant(5));
        let caller =
            CState::new().with_resource_context(ResourceContext::new().unchecked_with_fact(
                CResourceFact::own_token("can_complete".to_string(), vec![token.clone()]),
            ));
        let paths = execute_c_function_call_paths(
            &caller,
            &function,
            &[CExpression::Value(token.clone()), CExpression::Value(token)],
            &PureFactContext::new(),
            &environment(&function),
            CExecutionSemantics::EXECUTE_BODIES,
            &mut ExecutionBudget::new(),
        )
        .expect("a doubled token requirement should execute to a diagnostic");
        assert!(
            matches!(
                paths.as_slice(),
                [CFunctionPath {
                    outcome: CFunctionOutcome::RuntimeError(CRuntimeError::MissingResource {
                        resource
                    }),
                    ..
                }] if resource.owned_quantity_term() == Some(&Bitvector32Term::Constant(2))
            ),
            "the refusal names the whole demand: {paths:?}"
        );
    }

    #[test]
    fn candidate_inline_reader_uses_the_callers_checked_resources() {
        let pointer = pointer();
        let function = reader("candidate_inline_reader", false).with_inline_body();
        let paths = execute_c_function_call_paths(
            &caller(&pointer),
            &function,
            &[CExpression::Value(CValue::pointer(pointer))],
            &PureFactContext::new(),
            &environment(&function),
            CExecutionSemantics::EXECUTE_BODIES,
            &mut ExecutionBudget::new(),
        )
        .expect("candidate inline call should execute");
        assert!(matches!(
            paths.as_slice(),
            [CFunctionPath {
                outcome: CFunctionOutcome::Return { .. },
                ..
            }]
        ));
    }

    #[test]
    fn candidate_unresolved_return_obligation_refuses_recovery() {
        let pointer = pointer();
        let function = reader("candidate_unresolved_return", false);
        let caller = caller(&pointer);
        let arguments = vec![CValue::pointer(pointer.clone())];
        let callee = bind_c_function_arguments(&caller, &function, &arguments)
            .expect("reader argument should bind");
        let transfer = prepare_function_resource_transfer(
            &caller,
            &callee,
            &function,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
            true,
            ResourceTransitionPurpose::CallSite,
        )
        .expect("candidate transfer should run")
        .expect("candidate transfer should be accepted");
        let callee = callee_state_with_resource_transfer(callee, &transfer);
        let unresolved = ProofObligation::verification_condition(Proposition::ConditionIs(
            ConditionTerm::Constant(false),
            true,
        ));
        let (outcome, _, _) = function_outcome_from_body_with_resource_transfer(
            &caller,
            &function,
            CStatementOutcome::Return {
                value: int32(7),
                state: callee,
            },
            vec![unresolved],
            &PureFactContext::new(),
            &transfer,
            &arguments,
            true,
            &mut ExecutionBudget::new(),
        )
        .expect("candidate return transition should complete");
        assert!(matches!(
            outcome,
            CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(message))
                if message.contains("undischarged return obligation")
        ));
    }

    #[test]
    fn candidate_rejects_malformed_ledger_participant_pairs() {
        let pointer = pointer();
        let function = reader("candidate_pair_mismatch", false);
        let assumptions = PureFactContext::new();
        let mut budget = ExecutionBudget::new();
        let caller_with_ledger = caller(&pointer).with_loan_ledger(Some(LoanLedger::new()));
        let callee = bind_c_function_arguments(
            &caller_with_ledger,
            &function,
            &[CValue::pointer(pointer.clone())],
        )
        .expect("reader argument should bind");
        let error = prepare_function_resource_transfer(
            &caller_with_ledger,
            &callee,
            &function,
            &assumptions,
            &mut budget,
            true,
            ResourceTransitionPurpose::CallSite,
        )
        .expect("pair validation should not hit the execution budget")
        .expect_err("ledger-only caller must be refused");
        assert!(matches!(
            error,
            CRuntimeError::LoanRefusal(diagnostic)
                if diagnostic.category() == crate::kernel::LoanRefusalCategory::Missing
                    && diagnostic.operation() == crate::kernel::LoanRefusalOperation::Plan
        ));

        let ledger = LoanLedger::new();
        let participant = ledger.fresh_participant().expect("participant");
        let caller_with_participant = caller(&pointer).with_loan_participant(Some(participant));
        let callee = bind_c_function_arguments(
            &caller_with_participant,
            &function,
            &[CValue::pointer(pointer)],
        )
        .expect("reader argument should bind");
        let error = prepare_function_resource_transfer(
            &caller_with_participant,
            &callee,
            &function,
            &assumptions,
            &mut ExecutionBudget::new(),
            true,
            ResourceTransitionPurpose::CallSite,
        )
        .expect("pair validation should not hit the execution budget")
        .expect_err("participant-only caller must be refused");
        assert!(matches!(
            error,
            CRuntimeError::LoanRefusal(diagnostic)
                if diagnostic.category() == crate::kernel::LoanRefusalCategory::Missing
                    && diagnostic.operation() == crate::kernel::LoanRefusalOperation::Plan
        ));
    }

    #[test]
    fn candidate_rejects_wrong_callee_participant_on_recovery() {
        let pointer = pointer();
        let function = reader("candidate_wrong_participant", false);
        let caller = caller(&pointer);
        let arguments = vec![CValue::pointer(pointer.clone())];
        let callee = bind_c_function_arguments(&caller, &function, &arguments)
            .expect("reader argument should bind");
        let transfer = prepare_function_resource_transfer(
            &caller,
            &callee,
            &function,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
            true,
            ResourceTransitionPurpose::CallSite,
        )
        .expect("candidate transfer should run")
        .expect("candidate transfer should be accepted");
        let plan = transfer
            .stable_view_plan
            .as_ref()
            .expect("candidate transfer records a loan plan");
        let wrong_participant = plan.caller_participant();
        let callee = callee_state_with_resource_transfer(callee, &transfer)
            .with_loan_participant(Some(wrong_participant));
        let missing_ledger = callee.clone().with_loan_ledger(None);
        let error = recover_candidate_stable_view_resources(
            &caller,
            &missing_ledger,
            &transfer,
            transfer.caller_resources_after_requirements.clone(),
            &PureFactContext::new(),
            &PureFactContext::new(),
            &[],
        )
        .expect_err("recovery without a ledger must be refused");
        assert!(matches!(
            error,
            CRuntimeError::LoanRefusal(diagnostic)
                if diagnostic.category() == crate::kernel::LoanRefusalCategory::Missing
                    && diagnostic.operation() == crate::kernel::LoanRefusalOperation::Recovery
        ));
        let error = recover_candidate_stable_view_resources(
            &caller,
            &callee,
            &transfer,
            transfer.caller_resources_after_requirements.clone(),
            &PureFactContext::new(),
            &PureFactContext::new(),
            &[],
        )
        .expect_err("recovery must refuse the wrong callee participant");
        assert!(matches!(
            error,
            CRuntimeError::LoanRefusal(diagnostic)
                if diagnostic.category() == crate::kernel::LoanRefusalCategory::WrongHolder
                    && diagnostic.operation() == crate::kernel::LoanRefusalOperation::Recovery
        ));
    }

    #[test]
    fn candidate_joint_planner_reuses_one_escrow_for_two_aliases() {
        let pointer = pointer();
        let function = reader("candidate_aliases", true);
        let caller = caller(&pointer);
        let callee =
            bind_c_function_arguments(&caller, &function, &[CValue::pointer(pointer.clone())])
                .expect("reader argument should bind");
        let transfer = prepare_function_resource_transfer(
            &caller,
            &callee,
            &function,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
            true,
            ResourceTransitionPurpose::CallSite,
        )
        .expect("candidate transfer should run")
        .expect("candidate transfer should be accepted");
        let plan = transfer
            .stable_view_plan
            .as_ref()
            .expect("candidate transfer records a loan plan");
        assert_eq!(plan.stable_views().len(), 2);
        assert_eq!(
            plan.stable_views()[0].loan,
            plan.stable_views()[1].loan,
            "aliases share one escrow"
        );
    }

    #[test]
    fn candidate_nested_reader_reborrows_and_restores_outer_view_binding() {
        let pointer = pointer();
        let function = reader("candidate_nested_reader", false);
        let caller = caller(&pointer);
        let outer_template =
            bind_c_function_arguments(&caller, &function, &[CValue::pointer(pointer.clone())])
                .expect("outer reader arguments should bind");
        let outer_transfer = prepare_function_resource_transfer(
            &caller,
            &outer_template,
            &function,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
            true,
            ResourceTransitionPurpose::CallSite,
        )
        .expect("outer transfer should run")
        .expect("outer transfer should be accepted");
        let outer_callee = callee_state_with_resource_transfer(outer_template, &outer_transfer);
        let inner_template = bind_c_function_arguments(
            &outer_callee,
            &function,
            &[CValue::pointer(pointer.clone())],
        )
        .expect("inner reader arguments should bind");
        let inner_transfer = prepare_function_resource_transfer(
            &outer_callee,
            &inner_template,
            &function,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
            true,
            ResourceTransitionPurpose::CallSite,
        )
        .expect("inner transfer should run")
        .expect("inner transfer should be accepted");
        let inner_plan = inner_transfer
            .stable_view_plan
            .as_ref()
            .expect("nested transfer should use the loan plan");
        let outer_plan = outer_transfer
            .stable_view_plan
            .as_ref()
            .expect("outer transfer should use the loan plan");
        assert_ne!(
            inner_plan.stable_views()[0].loan,
            outer_plan.stable_views()[0].loan,
            "nested reader gets a child loan"
        );
        let inner_callee = callee_state_with_resource_transfer(inner_template, &inner_transfer);
        let (resources, ledger, participant, bindings, _) =
            recover_candidate_stable_view_resources(
                &outer_callee,
                &inner_callee,
                &inner_transfer,
                inner_transfer.caller_resources_after_requirements.clone(),
                &PureFactContext::new(),
                &PureFactContext::new(),
                &[],
            )
            .expect("nested reader recovery should run");
        assert_eq!(ledger, outer_callee.loan_ledger().cloned());
        assert_eq!(participant, outer_callee.loan_participant());
        assert_eq!(bindings, outer_callee.loan_view_bindings().clone());
        assert!(resources.satisfies_fact(
            &CResourceFact::view_memory(CMemoryRange::new(
                pointer,
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )),
            &PureFactContext::new(),
        ));
    }

    #[test]
    fn candidate_nested_reader_body_call_reborrows_and_recovers_owner() {
        let pointer = pointer();
        let inner = reader("candidate_nested_body_inner", false);
        let segment = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1));
        let outer = c_function(
            CType::Int32,
            "candidate_nested_body_outer",
            vec![c_parameter("p", CType::Int32Pointer)],
            c_seq(
                c_call_assign("result", inner.name(), vec![c_variable("p")]),
                c_return(c_variable("result")),
            ),
        )
        .with_resource_summary(vec![CResourceSpec::viewed_memory(segment)], Vec::new());
        let environment = CExecutionEnvironment::new()
            .with_function(inner.clone())
            .with_verified_function_rule(CVerifiedFunctionRule {
                function: inner,
                loop_semantics: CLoopSemantics::Verify,
            });

        let paths = execute_c_function_paths(
            &caller(&pointer),
            &outer,
            &[CExpression::Value(CValue::pointer(pointer.clone()))],
            &PureFactContext::new(),
            &environment,
            CExecutionSemantics::EXECUTE_BODIES,
            &mut ExecutionBudget::new(),
        )
        .expect("nested candidate reader should execute through the real body call");
        let CFunctionOutcome::Return { value, state } = &paths[0].outcome else {
            panic!(
                "nested candidate reader should return: {:?}",
                paths[0].outcome
            );
        };
        assert_eq!(value, &int32(7));
        assert!(state.resources().satisfies_fact(
            &CResourceFact::own_memory(CMemoryRange::new(
                pointer,
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )),
            &PureFactContext::new(),
        ));
    }

    #[test]
    fn candidate_nested_call_preserves_outer_view_for_wider_output() {
        let pointer = pointer();
        let outer_function = reader_for_input("candidate_outer_view", 2);
        let caller = caller_with_owned_end(&pointer, 2, 8);
        let outer_template = bind_c_function_arguments(
            &caller,
            &outer_function,
            &[CValue::pointer(pointer.clone())],
        )
        .expect("outer arguments should bind");
        let outer_transfer = prepare_function_resource_transfer(
            &caller,
            &outer_template,
            &outer_function,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
            true,
            ResourceTransitionPurpose::CallSite,
        )
        .expect("outer transfer should run")
        .expect("outer transfer should be accepted");
        let outer_callee = callee_state_with_resource_transfer(outer_template, &outer_transfer);

        let inner_function = reader_with_output("candidate_outer_output", 0, 2);
        let inner_template = bind_c_function_arguments(
            &outer_callee,
            &inner_function,
            &[CValue::pointer(pointer.clone())],
        )
        .expect("inner arguments should bind");
        let inner_transfer = prepare_function_resource_transfer(
            &outer_callee,
            &inner_template,
            &inner_function,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
            true,
            ResourceTransitionPurpose::CallSite,
        )
        .expect("inner transfer should run")
        .expect("inner transfer should be accepted");
        let output = CResourceFact::view_memory(CMemoryRange::new(
            pointer,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(2),
        ));
        let (resources, ledger, participant, bindings, _loan_evidence) =
            recover_candidate_stable_view_resources(
                &outer_callee,
                &callee_state_with_resource_transfer(inner_template, &inner_transfer),
                &inner_transfer,
                ResourceContext::new().unchecked_with_fact(output.clone()),
                &PureFactContext::new(),
                &PureFactContext::new(),
                &[],
            )
            .expect("outer view should authorize the wider returned view");
        assert!(resources.satisfies_fact(&output, &PureFactContext::new()));
        assert_eq!(ledger, outer_callee.loan_ledger().cloned());
        assert_eq!(participant, outer_callee.loan_participant());
        assert_eq!(bindings, outer_callee.loan_view_bindings().clone());
    }

    fn assert_unbacked_output_rejected(output_start: u32, output_end: u32, name: &str) {
        let pointer = pointer();
        let function = reader_with_output(name, output_start, output_end);
        let paths = execute_c_function_call_paths(
            &caller_with_owned_end(&pointer, 3, 12),
            &function,
            &[CExpression::Value(CValue::pointer(pointer))],
            &PureFactContext::new(),
            &environment(&function),
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &mut ExecutionBudget::new(),
        )
        .expect("candidate output call should execute to a diagnostic path");
        assert!(
            matches!(
                paths.as_slice(),
                [CFunctionPath {
                    outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(message)),
                    ..
                }] if message.contains("without a checked input child")
            ),
            "unexpected output result: {paths:?}"
        );
    }

    #[test]
    fn candidate_rejects_new_output_view() {
        assert_unbacked_output_rejected(2, 3, "candidate_new_output");
    }

    #[test]
    fn candidate_rejects_different_output_view() {
        assert_unbacked_output_rejected(1, 2, "candidate_different_output");
    }

    #[test]
    fn candidate_rejects_wider_output_without_outer_binding() {
        assert_unbacked_output_rejected(0, 2, "candidate_wider_output");
    }

    /// Build a call whose return context carries `returned` as an extra view
    /// beside the caller's retained owner, either as a checked projection of
    /// that exact owned occurrence or as a bare equal fact.
    fn recover_with_extra_returned_view(
        projected_from_owner: bool,
    ) -> Result<ResourceContext, CRuntimeError> {
        let pointer = pointer();
        let function = reader("candidate_returned_projection", false);
        let caller = caller_with_owned_end(&pointer, 3, 12);
        let callee_template =
            bind_c_function_arguments(&caller, &function, &[CValue::pointer(pointer.clone())])
                .expect("reader argument should bind");
        let transfer = prepare_function_resource_transfer(
            &caller,
            &callee_template,
            &function,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
            true,
            ResourceTransitionPurpose::CallSite,
        )
        .expect("candidate transfer should run")
        .expect("candidate transfer should be accepted");
        let owner = CResourceFact::own_memory(CMemoryRange::new(
            pointer.clone(),
            Bitvector32Term::Constant(1),
            Bitvector32Term::Constant(3),
        ));
        let returned = CResourceFact::view_memory(CMemoryRange::new(
            pointer,
            Bitvector32Term::Constant(1),
            Bitvector32Term::Constant(3),
        ));
        let base = ResourceContext::new().unchecked_with_fact(owner.clone());
        let (support_occurrence, _) = base
            .unique_owned_occurrence_for_fact(&owner)
            .expect("the retained owner has one occurrence");
        let return_resources = if projected_from_owner {
            base.unchecked_with_supported_facts_from_occurrence_with_memory(
                support_occurrence,
                &owner,
                vec![returned],
                caller.memory(),
            )
        } else {
            base.unchecked_with_fact(returned)
        };
        recover_candidate_stable_view_resources(
            &caller,
            &callee_state_with_resource_transfer(callee_template, &transfer),
            &transfer,
            return_resources,
            &PureFactContext::new(),
            &PureFactContext::new(),
            &[],
        )
        .map(|(resources, ..)| resources)
    }

    #[test]
    fn candidate_accepts_a_returned_view_projected_from_a_returned_owner() {
        let resources = recover_with_extra_returned_view(true)
            .expect("a checked projection of the returned owner has provenance");
        let projected = CResourceFact::view_memory(CMemoryRange::new(
            pointer(),
            Bitvector32Term::Constant(1),
            Bitvector32Term::Constant(3),
        ));
        assert!(resources.satisfies_fact(&projected, &PureFactContext::new()));
    }

    #[test]
    fn candidate_rejects_a_returned_view_that_only_an_equal_owner_satisfies() {
        let error = recover_with_extra_returned_view(false)
            .expect_err("fact equality against an owner is not provenance");
        assert!(
            matches!(
                &error,
                CRuntimeError::FunctionContract(message)
                    if message.contains("without a checked input child")
            ),
            "unexpected refusal: {error:?}"
        );
    }

    /// A view of read-only storage is intrinsic read authority rather than a
    /// lent capability: `install_borrowed_contract_inputs` gives such a
    /// contract input view no borrowed root and `intrinsic_read_views`
    /// supplies such a requirement with no ledger transition, both by this
    /// block test, so a call that merely carries one across its boundary has
    /// provenance for it. Everything else about the two calls below is the
    /// same; only the carried block's mutability differs.
    fn recover_with_a_carried_view_of_another_block(
        read_only: bool,
    ) -> Result<ResourceContext, CRuntimeError> {
        let pointer = pointer();
        let other = Pointer {
            block: PointerBlock::Concrete("global:candidate_table#file-static:t.c".to_string()),
            offset: PointerOffsetTerm::Constant(0),
        };
        let function = reader("candidate_carried_view", false);
        let owned_caller = caller_with_owned_end(&pointer, 3, 12);
        let caller = owned_caller.clone().with_memory(
            owned_caller.memory().clone().with_block_or_read_only(
                other.block.clone(),
                8,
                read_only,
            ),
        );
        let callee_template =
            bind_c_function_arguments(&caller, &function, &[CValue::pointer(pointer)])
                .expect("reader argument should bind");
        let transfer = prepare_function_resource_transfer(
            &caller,
            &callee_template,
            &function,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
            true,
            ResourceTransitionPurpose::CallSite,
        )
        .expect("candidate transfer should run")
        .expect("candidate transfer should be accepted");
        let carried = CResourceFact::view_memory(CMemoryRange::new(
            other,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(2),
        ));
        let return_resources = transfer
            .caller_resources_after_requirements
            .clone()
            .unchecked_with_fact(carried);
        recover_candidate_stable_view_resources(
            &caller,
            &callee_state_with_resource_transfer(callee_template, &transfer),
            &transfer,
            return_resources,
            &PureFactContext::new(),
            &PureFactContext::new(),
            &[],
        )
        .map(|(resources, ..)| resources)
    }

    #[test]
    fn candidate_accepts_a_carried_view_of_read_only_storage() {
        let resources = recover_with_a_carried_view_of_another_block(true)
            .expect("a view of read-only storage is intrinsic read authority");
        let carried = CResourceFact::view_memory(CMemoryRange::new(
            Pointer {
                block: PointerBlock::Concrete("global:candidate_table#file-static:t.c".to_string()),
                offset: PointerOffsetTerm::Constant(0),
            },
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(2),
        ));
        assert!(resources.satisfies_fact(&carried, &PureFactContext::new()));
    }

    #[test]
    fn candidate_rejects_a_carried_view_of_mutable_storage() {
        let error = recover_with_a_carried_view_of_another_block(false)
            .expect_err("a view of mutable storage the caller never lent has no provenance");
        assert!(
            matches!(
                &error,
                CRuntimeError::FunctionContract(message)
                    if message.contains("without a checked input child")
            ),
            "unexpected refusal: {error:?}"
        );
    }

    #[test]
    fn candidate_direct_call_rejects_new_output_view() {
        let pointer = pointer();
        let function = reader_with_output("candidate_direct_new_output", 2, 3);
        let paths = execute_c_function_call_paths(
            &caller_with_owned_end(&pointer, 3, 12),
            &function,
            &[CExpression::Value(CValue::pointer(pointer))],
            &PureFactContext::new(),
            &environment(&function),
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &mut ExecutionBudget::new(),
        )
        .expect("a direct output call should execute to a diagnostic path");
        assert!(matches!(
            paths.as_slice(),
            [CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(message)),
                ..
            }] if message.contains("without a checked input child")
        ));
    }

    fn symbolic_bounded_range(
        start: Bitvector32Term,
        end: Bitvector32Term,
        element_width: u32,
    ) -> CMemoryRange {
        CMemoryRange::new_with_element_width(
            Pointer {
                block: PointerBlock::Concrete("candidate:separation".to_string()),
                offset: PointerOffsetTerm::Constant(0),
            },
            start,
            end,
            element_width,
        )
    }

    /// `p[0..n - 1]` and `p[n - 1..n]` are separate for every `n`, and the
    /// kernel's own arithmetic decides it. Nothing about the endpoints is
    /// concrete, so the bounds comparison alone reports unproved separation.
    #[test]
    fn candidate_proves_adjacent_symbolic_ranges_separate() {
        let count = Bitvector32Term::Variable(Variable(910));
        let boundary = Bitvector32Term::add(count.clone(), Bitvector32Term::Constant(u32::MAX));
        let viewed = symbolic_bounded_range(Bitvector32Term::Constant(0), boundary.clone(), 4);
        let mutable = symbolic_bounded_range(boundary, count, 4);
        assert_eq!(
            candidate_memory_ranges_relation_by_bounds(&mutable, &viewed, &PureFactContext::new()),
            CandidateMemoryRangeRelation::SeparationUnproved
        );
        assert_eq!(
            candidate_memory_ranges_relation(&mutable, &viewed, &PureFactContext::new()),
            CandidateMemoryRangeRelation::Disjoint
        );
    }

    /// The arithmetic oracle decides separation, it does not assume it: two
    /// unrelated symbolic ranges in one block stay unproved, and a proven
    /// overlap is never reinterpreted.
    #[test]
    fn candidate_leaves_unrelated_symbolic_ranges_unproved() {
        let left = symbolic_bounded_range(
            Bitvector32Term::Variable(Variable(911)),
            Bitvector32Term::Variable(Variable(912)),
            4,
        );
        let right = symbolic_bounded_range(
            Bitvector32Term::Variable(Variable(913)),
            Bitvector32Term::Variable(Variable(914)),
            4,
        );
        assert_eq!(
            candidate_memory_ranges_relation(&left, &right, &PureFactContext::new()),
            CandidateMemoryRangeRelation::SeparationUnproved
        );
        let overlapping = symbolic_bounded_range(
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(4),
            4,
        );
        let inner = symbolic_bounded_range(
            Bitvector32Term::Constant(1),
            Bitvector32Term::Constant(2),
            4,
        );
        assert_eq!(
            candidate_memory_ranges_relation(&overlapping, &inner, &PureFactContext::new()),
            CandidateMemoryRangeRelation::Overlap
        );
    }

    fn assert_mutable_view_effect_result(
        mutable_start: u32,
        mutable_end: u32,
        name: &str,
    ) -> Vec<CFunctionPath> {
        let pointer = pointer();
        let function = reader_with_mutable_range(name, mutable_start, mutable_end);
        execute_c_function_call_paths(
            &caller_with_owned_end(&pointer, 2, 8),
            &function,
            &[CExpression::Value(CValue::pointer(pointer))],
            &PureFactContext::new(),
            &environment(&function),
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &mut ExecutionBudget::new(),
        )
        .expect("candidate mutable call should execute")
    }

    #[test]
    fn candidate_rejects_mutable_effect_overlapping_view() {
        let paths = assert_mutable_view_effect_result(0, 1, "candidate_overlap_effect");
        assert!(matches!(
            paths.as_slice(),
            [CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::LoanRefusal(diagnostic)),
                ..
            }] if diagnostic.category() == crate::kernel::LoanRefusalCategory::ProvenOverlap
                && diagnostic.overlap() == crate::kernel::LoanOverlapStatus::ProvenOverlap
                && diagnostic.subject().memory_range().is_some()
        ));
    }

    /// A mutable effect on the same symbolic base as the lent view, at the
    /// same constant offsets, is a proven overlap even though the base
    /// offset is unknown: the symbolic view is retained outside the
    /// concrete index and compared by offset arithmetic.
    #[test]
    fn candidate_rejects_symbolic_same_base_overlapping_effect() {
        let pointer = Pointer {
            block: PointerBlock::Concrete("local:candidate_view:data".to_string()),
            offset: PointerOffsetTerm::Variable(Variable(700)),
        };
        let function = reader_with_mutable_range("candidate_symbolic_overlap_effect", 0, 1);
        let paths = execute_c_function_call_paths(
            &caller_with_owned_end(&pointer, 2, 8),
            &function,
            &[CExpression::Value(CValue::pointer(pointer))],
            &PureFactContext::new(),
            &environment(&function),
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &mut ExecutionBudget::new(),
        )
        .expect("candidate symbolic overlap should execute to a diagnostic path");
        assert!(matches!(
            paths.as_slice(),
            [CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::LoanRefusal(diagnostic)),
                ..
            }] if diagnostic.category() == crate::kernel::LoanRefusalCategory::ProvenOverlap
                && diagnostic.overlap() == crate::kernel::LoanOverlapStatus::ProvenOverlap
        ));
    }

    /// A mutable effect through a second pointer whose relation to the lent
    /// view is unknown is neither a proven overlap nor a proven separation;
    /// the call is refused as unproved rather than assumed disjoint.
    #[test]
    fn candidate_rejects_unproved_mutable_effect_separation() {
        let viewed = Pointer {
            block: PointerBlock::Concrete("local:candidate_view:data".to_string()),
            offset: PointerOffsetTerm::Variable(Variable(700)),
        };
        let mutated = Pointer {
            block: PointerBlock::Concrete("local:candidate_view:data".to_string()),
            offset: PointerOffsetTerm::Variable(Variable(701)),
        };
        let input = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1));
        let function = c_function(
            CType::Int32,
            "candidate_unknown_effect",
            vec![
                c_parameter("p", CType::Int32Pointer),
                c_parameter("q", CType::Int32Pointer),
            ],
            c_return(c_load(c_variable("p"))),
        )
        .with_resource_summary(vec![CResourceSpec::viewed_memory(input)], Vec::new())
        .with_contract(
            Vec::new(),
            Vec::new(),
            vec![CMemorySegment::new(
                c_variable("q"),
                c_int32_literal(0),
                c_int32_literal(1),
            )],
            Vec::new(),
            true,
        );
        let paths = execute_c_function_call_paths(
            &caller_with_owned_end(&viewed, 2, 8),
            &function,
            &[
                CExpression::Value(CValue::pointer(viewed)),
                CExpression::Value(CValue::pointer(mutated)),
            ],
            &PureFactContext::new(),
            &environment(&function),
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &mut ExecutionBudget::new(),
        )
        .expect("candidate unknown separation should execute to a diagnostic path");
        assert!(matches!(
            paths.as_slice(),
            [CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::LoanRefusal(diagnostic)),
                ..
            }] if diagnostic.category() == crate::kernel::LoanRefusalCategory::SeparationUnproved
                && diagnostic.overlap() == crate::kernel::LoanOverlapStatus::SeparationUnproved
        ));
    }

    /// A contract that views one parameter and owns another, with the whole
    /// write footprint derived from that ownership. Each requirement is
    /// served by a different owned occurrence of the caller's partition.
    fn viewer_and_writer(name: &str) -> CFunction {
        let viewed = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1));
        let owned = CMemorySegment::new(c_variable("q"), c_int32_literal(0), c_int32_literal(1));
        c_function(
            CType::Int32,
            name,
            vec![
                c_parameter("p", CType::Int32Pointer),
                c_parameter("q", CType::Int32Pointer),
            ],
            c_return(c_load(c_variable("p"))),
        )
        .with_resource_summary(
            vec![
                CResourceSpec::viewed_memory(viewed),
                CResourceSpec::owned_memory(owned),
            ],
            Vec::new(),
        )
        .with_resource_derived_mutable_frame()
    }

    /// The partition read at a call. The effect is reserved out of one owned
    /// occurrence and the view is lent from another, and the two symbolic
    /// ranges share a block with an unknown offset relation, so the
    /// arithmetic oracle can order neither. A valid resource context is a
    /// partition, so distinct owned occurrences are bytewise disjoint by
    /// construction and the call is accepted on that provenance alone. This
    /// is the `augment_rotate_callback_child_read` shape in miniature.
    #[test]
    fn candidate_allows_a_mutable_effect_reserved_from_another_owned_occurrence() {
        let viewed = Pointer {
            block: PointerBlock::Concrete("local:candidate_view:data".to_string()),
            offset: PointerOffsetTerm::Variable(Variable(700)),
        };
        let mutated = Pointer {
            block: PointerBlock::Concrete("local:candidate_view:data".to_string()),
            offset: PointerOffsetTerm::Variable(Variable(701)),
        };
        let owned_range = |pointer: &Pointer| {
            CResourceFact::own(CResource::Memory(CMemoryRange::new(
                pointer.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )))
        };
        let caller = CState::new()
            .with_memory(
                CMemory::new()
                    .with_block(viewed.block.clone(), 8)
                    .store(viewed.clone(), int32(7)),
            )
            .with_resource_context(
                ResourceContext::new()
                    .unchecked_with_fact(owned_range(&viewed))
                    .unchecked_with_fact(owned_range(&mutated)),
            );
        let function = viewer_and_writer("candidate_separate_occurrence_effect");
        let paths = execute_c_function_call_paths(
            &caller,
            &function,
            &[
                CExpression::Value(CValue::pointer(viewed)),
                CExpression::Value(CValue::pointer(mutated)),
            ],
            &PureFactContext::new(),
            &environment(&function),
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &mut ExecutionBudget::new(),
        )
        .expect("candidate separate-occurrence effect call should execute");
        assert!(matches!(
            paths.as_slice(),
            [CFunctionPath {
                outcome: CFunctionOutcome::Return { .. },
                ..
            }]
        ));
    }

    /// The same-occurrence case is not weakened. Here one caller occurrence
    /// has to serve both requirements: the exclusive reservation takes the
    /// owned bytes out of it first, and the overlapping view it would also
    /// have to back is no longer there. Provenance settles nothing, because
    /// the effect and the view would be the same partition element, and the
    /// call is refused rather than accepted on a support comparison.
    #[test]
    fn candidate_rejects_a_mutable_effect_overlapping_a_view_from_its_own_occurrence() {
        let pointer = pointer();
        let viewed = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(2));
        let owned = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1));
        let function = c_function(
            CType::Int32,
            "candidate_same_occurrence_overlap_effect",
            vec![c_parameter("p", CType::Int32Pointer)],
            c_return(c_load(c_variable("p"))),
        )
        .with_resource_summary(
            vec![
                CResourceSpec::viewed_memory(viewed),
                CResourceSpec::owned_memory(owned),
            ],
            Vec::new(),
        )
        .with_resource_derived_mutable_frame();
        let paths = execute_c_function_call_paths(
            &caller_with_owned_end(&pointer, 2, 8),
            &function,
            &[CExpression::Value(CValue::pointer(pointer))],
            &PureFactContext::new(),
            &environment(&function),
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &mut ExecutionBudget::new(),
        )
        .expect("candidate same-occurrence overlap should execute to a diagnostic path");
        assert!(matches!(
            paths.as_slice(),
            [CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::LoanRefusal(diagnostic)),
                ..
            }] if diagnostic.category() == crate::kernel::LoanRefusalCategory::ProvenOverlap
                && diagnostic.overlap() == crate::kernel::LoanOverlapStatus::ProvenOverlap
        ));
    }

    #[test]
    fn candidate_allows_provably_disjoint_mutable_effect() {
        let paths = assert_mutable_view_effect_result(1, 2, "candidate_disjoint_effect");
        assert!(matches!(
            paths.as_slice(),
            [CFunctionPath {
                outcome: CFunctionOutcome::Return { .. },
                ..
            }]
        ));
    }

    /// A composite reader whose contract also declares a mutable footprint.
    /// The requirement is `views cell(p)`, which carries no memory range of
    /// its own; the bytes it protects are the definition's checked frontier.
    fn composite_reader_with_mutable_range(
        name: &str,
        mutable_start: u32,
        mutable_end: u32,
    ) -> CFunction {
        let segment = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1));
        let required = CResourceSpec::declared(
            ResourceFamily::Composite,
            CResourceAccessMode::View,
            "cell".into(),
            vec![c_variable("p")],
            vec![CType::Int32Pointer],
            CResourceTransferRole::Borrow,
            CResourceSnapshot::Entry,
        )
        .unwrap();
        let definition = CCompositeResourceDefinition::new(
            "cell",
            vec![c_parameter("p", CType::Int32Pointer)],
            None,
            false,
            vec![CResourceSpec::owned_memory(segment)],
            Vec::new(),
        );
        c_function(
            CType::Int32,
            name,
            vec![c_parameter("p", CType::Int32Pointer)],
            c_return(c_load(c_variable("p"))),
        )
        .with_resource_summary(vec![required], Vec::new())
        .with_composite_resource_definitions(vec![definition])
        .with_contract(
            Vec::new(),
            Vec::new(),
            vec![CMemorySegment::new(
                c_variable("p"),
                c_int32_literal(mutable_start),
                c_int32_literal(mutable_end),
            )],
            Vec::new(),
            true,
        )
    }

    fn composite_mutable_effect_paths(
        mutable_start: u32,
        mutable_end: u32,
        name: &str,
    ) -> Vec<CFunctionPath> {
        let pointer = pointer();
        let head =
            CResourceFact::own_composite("cell".into(), vec![CValue::pointer(pointer.clone())]);
        let caller = CState::new()
            .with_memory(
                CMemory::new()
                    .with_block(pointer.block.clone(), 8)
                    .store(pointer.clone(), int32(7)),
            )
            .with_resource_context(ResourceContext::new().unchecked_with_fact(head));
        let function = composite_reader_with_mutable_range(name, mutable_start, mutable_end);
        execute_c_function_call_paths(
            &caller,
            &function,
            &[CExpression::Value(CValue::pointer(pointer))],
            &PureFactContext::new(),
            &environment(&function),
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &mut ExecutionBudget::new(),
        )
        .expect("candidate composite mutable call should execute")
    }

    /// F6. The head of a composite view has no memory range, so comparing the
    /// declared effects against requirement ranges alone saw nothing here.
    /// The checked one-level frontier is what the loan protects, and an
    /// effect over one of its pieces is a proven overlap.
    #[test]
    fn candidate_rejects_mutable_effect_overlapping_a_composite_view_piece() {
        let paths = composite_mutable_effect_paths(0, 1, "candidate_composite_overlap_effect");
        assert!(matches!(
            paths.as_slice(),
            [CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::LoanRefusal(diagnostic)),
                ..
            }] if diagnostic.category() == crate::kernel::LoanRefusalCategory::ProvenOverlap
                && diagnostic.overlap() == crate::kernel::LoanOverlapStatus::ProvenOverlap
                && diagnostic.subject().memory_range().is_some()
        ));
    }

    /// The same frontier keeps the supported partition usable: a composite
    /// body of `p[0..1]` beside an effect on `p[1..2]` is provably disjoint.
    #[test]
    fn candidate_allows_a_mutable_effect_disjoint_from_a_composite_view_piece() {
        let paths = composite_mutable_effect_paths(1, 2, "candidate_composite_disjoint_effect");
        assert!(matches!(
            paths.as_slice(),
            [CFunctionPath {
                outcome: CFunctionOutcome::Return { .. },
                ..
            }]
        ));
    }

    /// F6. An intrinsic local view is filtered out before planning, so no
    /// plan records it and the effect check could not see it either. The
    /// transfer carries its range, and an effect over the same bytes is
    /// refused exactly as it is for a lent view.
    #[test]
    fn candidate_rejects_mutable_effect_overlapping_an_intrinsic_local_view() {
        let pointer = pointer();
        let function = reader_with_mutable_range("candidate_intrinsic_overlap_effect", 0, 1);
        let caller = CState::new().with_memory(
            CMemory::new()
                .with_block(pointer.block.clone(), 8)
                .store(pointer.clone(), int32(7)),
        );
        let paths = execute_c_function_call_paths(
            &caller,
            &function,
            &[CExpression::Value(CValue::pointer(pointer))],
            &PureFactContext::new(),
            &environment(&function),
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &mut ExecutionBudget::new(),
        )
        .expect("candidate intrinsic view effect call should execute");
        assert!(matches!(
            paths.as_slice(),
            [CFunctionPath {
                outcome: CFunctionOutcome::RuntimeError(CRuntimeError::LoanRefusal(diagnostic)),
                ..
            }] if diagnostic.category() == crate::kernel::LoanRefusalCategory::ProvenOverlap
                && diagnostic.overlap() == crate::kernel::LoanOverlapStatus::ProvenOverlap
        ));
    }

    #[test]
    fn candidate_nested_reader_rejects_stale_outer_binding() {
        let pointer = pointer();
        let function = reader("candidate_stale_nested_reader", false);
        let caller = caller(&pointer);
        let outer_template =
            bind_c_function_arguments(&caller, &function, &[CValue::pointer(pointer.clone())])
                .expect("outer reader arguments should bind");
        let outer_transfer = prepare_function_resource_transfer(
            &caller,
            &outer_template,
            &function,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
            true,
            ResourceTransitionPurpose::CallSite,
        )
        .expect("outer transfer should run")
        .expect("outer transfer should be accepted");
        let outer_callee = callee_state_with_resource_transfer(outer_template, &outer_transfer)
            .with_loan_view_bindings(LoanViewBindings::default());
        let inner_template =
            bind_c_function_arguments(&outer_callee, &function, &[CValue::pointer(pointer)])
                .expect("inner reader arguments should bind");
        let result = prepare_function_resource_transfer(
            &outer_callee,
            &inner_template,
            &function,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
            true,
            ResourceTransitionPurpose::CallSite,
        )
        .expect("stale binding check should run");
        assert!(matches!(
            result,
            Err(CRuntimeError::LoanRefusal(diagnostic))
                if diagnostic.category() == crate::kernel::LoanRefusalCategory::Missing
                    && diagnostic.operation() == crate::kernel::LoanRefusalOperation::Plan
        ));
    }

    #[test]
    fn candidate_early_return_closes_call_scope() {
        let pointer = pointer();
        let function = early_reader("candidate_early_reader");
        let paths = execute_c_function_call_paths(
            &caller(&pointer),
            &function,
            &[CExpression::Value(CValue::pointer(pointer.clone()))],
            &PureFactContext::new(),
            &environment(&function),
            CExecutionSemantics::EXECUTE_BODIES,
            &mut ExecutionBudget::new(),
        )
        .expect("candidate early return should execute");
        let CFunctionOutcome::Return { state, .. } = &paths[0].outcome else {
            panic!(
                "candidate early reader should return: {:?}",
                paths[0].outcome
            );
        };
        assert!(state.resources().satisfies_fact(
            &CResourceFact::own_memory(CMemoryRange::new(
                pointer,
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )),
            &PureFactContext::new(),
        ));
    }

    #[test]
    fn candidate_wrong_scope_close_is_refused() {
        let ledger = LoanLedger::new();
        let owner = ledger.fresh_participant().expect("owner participant");
        let reader = ledger.fresh_participant().expect("reader participant");
        let escrow = CResourceFact::own(CResource::Token {
            name: "candidate_scope".to_string(),
            arguments: Vec::new().into(),
        });
        let support = ResourceContext::new()
            .unchecked_with_fact(escrow.clone())
            .unique_owned_occurrence_for_fact(&escrow)
            .expect("token backing")
            .0;
        let opening = ledger
            .lend(owner, reader, support, escrow)
            .expect("loan opening");
        let ledger = ledger.apply(&opening.transition).expect("loan apply");
        let refusal = ledger
            .end(opening.scope, reader)
            .expect_err("a non-owner cannot close the scope");
        assert_eq!(
            refusal
                .diagnostic(crate::kernel::LoanRefusalOperation::Transition)
                .category(),
            crate::kernel::LoanRefusalCategory::WrongHolder
        );
        let wrong_scope = super::super::loans::LoanScopeId::for_test(
            opening.scope.arena_for_test(),
            opening.scope.ordinal_for_test().saturating_add(1),
        );
        let refusal = ledger
            .end(wrong_scope, owner)
            .expect_err("an unknown scope cannot be closed");
        assert_eq!(
            refusal
                .diagnostic(crate::kernel::LoanRefusalOperation::Transition)
                .category(),
            crate::kernel::LoanRefusalCategory::WrongScope
        );
    }

    /// An empty-bodied token population: the caller holds one representative
    /// unit and the declared cardinality lives in the tracked population, so
    /// `n of slot(p)` is never one owned entry the reservation can select.
    fn token_population_reader(name: &str, population: &str) -> CFunction {
        let segment = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1));
        let unit = CResourceSpec::declared(
            ResourceFamily::Composite,
            CResourceAccessMode::Own,
            population.into(),
            vec![c_variable("p")],
            vec![CType::Int32Pointer],
            CResourceTransferRole::Consume,
            CResourceSnapshot::Entry,
        )
        .expect("a unit population term");
        let counted = CResourceSpec::quantified(
            c_variable("n"),
            unit,
            CResourceTransferRole::Consume,
            CResourceSnapshot::Entry,
        )
        .expect("a counted population requirement");
        c_function(
            CType::Int32,
            name,
            vec![
                c_parameter("p", CType::Int32Pointer),
                c_parameter("n", CType::Int32),
            ],
            c_return(c_load(c_variable("p"))),
        )
        .with_resource_summary(
            vec![CResourceSpec::viewed_memory(segment), counted],
            Vec::new(),
        )
        .with_composite_resource_definitions(vec![
            CCompositeResourceDefinition::counted_population(
                population,
                vec![c_parameter("p", CType::Int32Pointer)],
                None,
                Vec::new(),
                Vec::new(),
            ),
        ])
    }

    /// A declared quantity must be known nonnegative before any resource
    /// route looks at it; that check is unrelated to the planner gap.
    fn nonnegative_quantity(quantity: Variable) -> PureFactContext {
        PureFactContext::new().assume_condition(
            ConditionTerm::Bitvector32SignedGreaterEqual(
                Box::new(Bitvector32Term::Variable(quantity)),
                Box::new(Bitvector32Term::Constant(0)),
            ),
            true,
        )
    }

    fn token_population_unit(population: &str, pointer: &Pointer) -> CResourceFact {
        CResourceFact::own_composite(population.into(), vec![CValue::pointer(pointer.clone())])
    }

    /// The planner's exclusive reservation has no "N units out of a
    /// population whose count is at least N" step, and a token population
    /// protects no memory, so nothing about the loan ledger could supply one.
    /// Such a requirement is planned the way legacy plans it, beside a view
    /// the same call lends.
    #[test]
    fn candidate_symbolic_token_population_consume_plans_beside_a_lent_view() {
        let pointer = pointer();
        let function = token_population_reader("candidate_population_reader", "slot");
        let unit = token_population_unit("slot", &pointer);
        let base = caller(&pointer);
        let caller = base
            .clone()
            .with_resource_context(base.resources().clone().unchecked_with_fact(unit.clone()))
            .with_counted_population(
                "slot",
                vec![CValue::pointer(pointer.clone()).into()].into(),
                Bitvector32Term::Constant(2),
            );
        let arguments = vec![
            CValue::pointer(pointer.clone()),
            CValue::Int32(Bitvector32Term::Variable(Variable(4242))),
        ];
        let assumptions = nonnegative_quantity(Variable(4242));
        let callee = bind_c_function_arguments(&caller, &function, &arguments)
            .expect("population reader arguments should bind");
        let transfer = prepare_function_resource_transfer(
            &caller,
            &callee,
            &function,
            &assumptions,
            &mut ExecutionBudget::new(),
            true,
            ResourceTransitionPurpose::CallSite,
        )
        .expect("population transfer should run")
        .expect("a symbolic population quantity should not refuse the plan");
        let plan = transfer
            .stable_view_plan
            .as_ref()
            .expect("the view clause still records a loan plan");
        assert_eq!(plan.stable_views().len(), 1);
        let viewed = CMemoryRange::new(
            pointer.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        );
        assert_eq!(
            plan.ledger.permits_memory_access(&viewed),
            Err(LoanRefusal::ActiveDependency)
        );
        assert!(
            transfer
                .callee_resources
                .satisfies_fact(&CResourceFact::view_memory(viewed), &PureFactContext::new())
        );
    }

    /// The count itself is still checked, by the counted-population
    /// transition rather than by the planner.
    #[test]
    fn token_population_consume_without_a_known_count_is_refused() {
        let pointer = pointer();
        let function = token_population_reader("candidate_uncounted_population_reader", "slot");
        let caller = caller(&pointer);
        let arguments = vec![
            CExpression::Value(CValue::pointer(pointer.clone())),
            CExpression::Value(CValue::Int32(Bitvector32Term::Variable(Variable(4242)))),
        ];
        let refusal = || {
            let environment =
                CExecutionEnvironment::new().with_verified_function_rule(CVerifiedFunctionRule {
                    function: function.clone(),
                    loop_semantics: CLoopSemantics::Verify,
                });
            let paths = execute_c_function_call_paths(
                &caller,
                &function,
                &arguments,
                &nonnegative_quantity(Variable(4242)),
                &environment,
                CExecutionSemantics::APPLY_VERIFIED_RULES,
                &mut ExecutionBudget::new(),
            )
            .expect("the population call should execute");
            let [
                CFunctionPath {
                    outcome: CFunctionOutcome::RuntimeError(error),
                    ..
                },
            ] = paths.as_slice()
            else {
                panic!("an uninitialized population should refuse: {paths:?}");
            };
            error.clone()
        };
        let refusal = refusal();
        assert!(
            matches!(&refusal, CRuntimeError::FunctionContract(message)
                if message.contains("counted population `slot` is not initialized")),
            "{refusal:?}"
        );
    }
}
