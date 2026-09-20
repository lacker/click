use super::diagnostics::*;
use super::*;

mod algebraic_rewrite;
mod contract_evaluation;
mod integer_affine_planner;
mod predicates;
mod segments;
mod signed_arithmetic_planner;
mod simp;
mod special_arithmetic_planner;
use crate::kernel::memory_effect_write_pointers;
pub(super) use contract_evaluation::*;
pub(super) use integer_affine_planner::*;
pub(super) use predicates::*;
pub(super) use segments::*;
#[allow(unused_imports)]
pub(super) use signed_arithmetic_planner::*;
pub(super) use simp::*;
pub(super) use special_arithmetic_planner::*;

/// Exact resource production evidence for one claim in one checked execution.
/// Fields are private to the checker; presentation syntax cannot create it.
#[derive(Clone)]
pub(super) struct CheckedResourceClaim<'e> {
    execution: &'e CCheckedFunctionExecution,
    path_index: usize,
    key: CFunctionContractClaimKey,
    returned_resources: crate::kernel::ResourceContext,
    borrowed: bool,
}

impl CheckedResourceClaim<'_> {
    pub(super) fn matches(
        &self,
        execution: &CCheckedFunctionExecution,
        path_index: usize,
        key: &CFunctionContractClaimKey,
    ) -> bool {
        std::ptr::eq(self.execution, execution) && self.path_index == path_index && &self.key == key
    }
    pub(super) fn claim_key(&self) -> &CFunctionContractClaimKey {
        &self.key
    }
    pub(super) fn path_index(&self) -> usize {
        self.path_index
    }
    pub(super) fn returned_resources(&self) -> &crate::kernel::ResourceContext {
        &self.returned_resources
    }
    pub(super) fn contributes_returned_resources(&self) -> bool {
        !self.borrowed
    }
}

/// Checks the allocation-lifetime obligation owned by one exact outcome.
/// The caller decides how to render a leaked allocation; this shared checker
/// keeps explicit resource claims and the implicit function-exit closer on
/// the same semantic obligation.
pub(super) fn check_allocation_lifetime(
    checked_execution: &CCheckedFunctionExecution,
    obligation: &crate::kernel::proof::AllocationLifetimeObligation,
    path_index: usize,
    assumptions: &crate::kernel::PureFactContext,
    returned_resources: Option<&crate::kernel::ResourceContext>,
    outcome: &CFunctionOutcome,
) -> Result<
    Result<Option<crate::kernel::proof::LiveAllocationObligation>, crate::kernel::CRuntimeError>,
    ClickError,
> {
    if obligation.path_index() != path_index {
        return Err(ClickError::new(
            "allocation-lifetime obligation belongs to a different execution path",
        ));
    }
    let CFunctionOutcome::Return { value, state } = outcome else {
        return Ok(Ok(None));
    };
    let mut lifetime_budget = ExecutionBudget::beside_live_state();
    let result = match returned_resources {
        Some(returned_resources) => {
            crate::kernel::unreturned_allocation_with_checked_returned_resources(
                state,
                value,
                checked_execution.function(),
                checked_execution.function_arguments(),
                returned_resources,
                assumptions,
                &mut lifetime_budget,
            )
        }
        None => crate::kernel::unreturned_allocation_at_function_exit(
            state,
            value,
            checked_execution.function(),
            checked_execution.function_arguments(),
            assumptions,
            &mut lifetime_budget,
        )
        .map_err(|limit| {
            ClickError::new(format!(
                "allocation-lifetime obligation stopped at {}",
                limit.describe()
            ))
        })?,
    };
    Ok(result)
}

pub(super) fn prove_ensure_resource<'e>(
    checked_execution: &'e CCheckedFunctionExecution,
    claim_key: CFunctionContractClaimKey,
    claim_label: &str,
    path_index: usize,
    _allocation_lifetime: &crate::kernel::proof::AllocationLifetimeObligation,
    execution_pure_facts: &[crate::kernel::ExecutionPureFact],
    available_pure_facts: &(impl PropositionSource + ?Sized),
    resource: &ResourceClause,
    borrowed: bool,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    entry_state: &CState,
    outcome: &CFunctionOutcome,
) -> Result<CheckedResourceClaim<'e>, ClickError> {
    // Post-return resource folds can extend the checked path before final
    // contract certification. Its typed outcome Proof supplies the returning
    // state checked below; the original artifact supplies stable path identity.
    if checked_execution.paths().get(path_index).is_none() {
        return Err(ClickError::new(
            "resource claim has no checked execution path",
        ));
    }
    let CFunctionOutcome::Return {
        value: result,
        state: post_state,
    } = outcome
    else {
        return Err(ClickError::new(format!(
            "`{claim_label}` failed on path {path_index}: {}\n{}",
            describe_function_outcome(outcome, parameters, arguments),
            describe_proof_context(
                &available_pure_facts
                    .propositions()
                    .cloned()
                    .collect::<Vec<_>>(),
                pre_state.resources().facts(),
                parameters,
                arguments,
                execution_pure_facts
            )
        )));
    };
    // A borrowed resource is returned as it was lent: its clause is read at
    // entry, where address expressions still see the caller's values.
    let clause_state = if borrowed && !matches!(resource, ResourceClause::Named { .. }) {
        pre_state
    } else {
        post_state
    };
    let assumptions = assumptions_from_propositions(available_pure_facts);
    let expected = lower_resource_clause_facts_at_state_with_result_and_entry(
        resource,
        parameters,
        arguments,
        entry_state,
        clause_state,
        result,
        &assumptions,
    )?;
    if expected.iter().all(|expected| {
        post_state
            .resources()
            .satisfies_fact(expected, &assumptions)
    }) {
        return Ok(CheckedResourceClaim {
            execution: checked_execution,
            path_index,
            key: claim_key,
            returned_resources: crate::kernel::ResourceContext::new()
                .unchecked_with_facts(expected.iter().cloned()),
            borrowed,
        });
    }
    let expected = expected
        .iter()
        .find(|expected| {
            !post_state
                .resources()
                .satisfies_fact(expected, &assumptions)
        })
        .expect("resource ensure has an unsatisfied fact");
    Err(ClickError::new(format!(
        "`{claim_label}` failed on path {path_index}: {}",
        describe_missing_resource_fact(
            expected,
            &available_pure_facts
                .propositions()
                .cloned()
                .collect::<Vec<_>>(),
            post_state.resources().facts(),
            parameters,
            arguments,
            execution_pure_facts
        )
    )))
}

pub(super) fn evaluate_witness_tactic_value(
    witness: &ProofWitness,
    claim_label: &str,
    path_index: usize,
    tactic_index: usize,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    pre_state: &CState,
    post_state: &CState,
    result: Option<&CValue>,
    assumptions: &PureFactContext,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    recorded_snapshots: &RecordedSnapshots,
) -> Result<CValue, ClickError> {
    let mut active_functions = BTreeSet::new();
    let value = evaluate_contract_expression_with_environment(
        values,
        array_refs,
        pre_state,
        post_state,
        result,
        assumptions,
        &witness.value,
        predicate_environment,
        click_function_environment,
        recorded_snapshots,
        &mut active_functions,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`witness` failed for `{claim_label}` path {path_index}, tactic {tactic_index}: could not evaluate witness value for `{}`: {message}",
            witness.name
        ))
    })?;
    Ok(value)
}

pub(super) fn apply_witness_tactic(
    witness: &ProofWitness,
    witness_value: CValue,
    goal: Proposition,
    claim_label: &str,
    path_index: usize,
    tactic_index: usize,
) -> Result<Proposition, ClickError> {
    let Proposition::Exists {
        name,
        var,
        sort,
        body,
    } = goal
    else {
        return Err(ClickError::new(format!(
            "`witness` failed for `{claim_label}` path {path_index}, tactic {tactic_index}: goal is not an existential proposition"
        )));
    };
    if name != witness.name {
        return Err(ClickError::new(format!(
            "`witness` failed for `{claim_label}` path {path_index}, tactic {tactic_index}: goal binds `{name}`, but proof provided witness `{}`",
            witness.name
        )));
    }

    let result = match (sort, witness_value) {
        (Sort::CInt32, CValue::Int32(value)) => {
            substitute_int32_variable_in_proposition(&body, var, value)
        }
        (Sort::CPointer(expected), CValue::Pointer(pointer))
            if expected.accepts(&CValue::Pointer(pointer.clone())) =>
        {
            crate::kernel::substitute_pointer_variable_in_proposition(&body, var, pointer.pointer())
        }
        (Sort::CPointer(_), CValue::Pointer(_)) => {
            return Err(ClickError::new(format!(
                "`witness` failed for `{claim_label}` path {path_index}, tactic {tactic_index}: witness `{}` has the wrong pointer kind",
                witness.name
            )));
        }
        (Sort::CInt32, _) => {
            return Err(ClickError::new(format!(
                "`witness` failed for `{claim_label}` path {path_index}, tactic {tactic_index}: witness `{}` did not evaluate to int32",
                witness.name
            )));
        }
        _ => {
            return Err(ClickError::new(format!(
                "`witness` failed for `{claim_label}` path {path_index}, tactic {tactic_index}: unsupported existential witness sort for `{}`",
                witness.name
            )));
        }
    };
    Ok(result)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn lower_ensure_proposition_goal(
    available_pure_facts: &(impl PropositionSource + ?Sized),
    proposition: &ClickProposition,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    outcome: &CFunctionOutcome,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    recorded_snapshots: &RecordedSnapshots,
    unfolded_predicates: &[String],
) -> Result<Proposition, String> {
    let CFunctionOutcome::Return { value, state } = outcome else {
        return Err("the execution path does not return".to_string());
    };
    let proposition = lower_outcome_proposition_with_recorded_snapshots(
        parameters,
        arguments,
        pre_state,
        state,
        value,
        available_pure_facts,
        proposition,
        predicate_environment,
        click_function_environment,
        recorded_snapshots,
    );
    if crate::instrumentation::deadline_exceeded() {
        return Err(format!(
            "verification budget exhausted inside {}",
            crate::instrumentation::deadline_context()
        ));
    }
    let proposition = proposition?;
    let assumptions = assumptions_from_propositions(available_pure_facts);
    unfold_predicates_in_proposition(
        predicate_environment,
        click_function_environment,
        unfolded_predicates,
        &proposition,
        &assumptions,
    )
}

pub(super) fn comparison_condition(
    actual: Bitvector32Term,
    operator: ComparisonOperator,
    expected: Bitvector32Term,
    unsigned: bool,
) -> Option<(ConditionTerm, bool)> {
    match operator {
        ComparisonOperator::Equal => Some((bitvector32_equal(actual, expected), true)),
        ComparisonOperator::NotEqual => Some((bitvector32_equal(actual, expected), false)),
        ComparisonOperator::LessThan => Some((
            if unsigned {
                ConditionTerm::unsigned_less_than(actual, expected)
            } else {
                signed_less_than(actual, expected)
            },
            true,
        )),
        ComparisonOperator::LessEqual => Some((
            if unsigned {
                ConditionTerm::unsigned_less_equal(actual, expected)
            } else {
                signed_less_equal(actual, expected)
            },
            true,
        )),
        ComparisonOperator::GreaterThan => Some((
            if unsigned {
                ConditionTerm::unsigned_greater_than(actual, expected)
            } else {
                signed_greater_than(actual, expected)
            },
            true,
        )),
        ComparisonOperator::GreaterEqual => Some((
            if unsigned {
                ConditionTerm::unsigned_greater_equal(actual, expected)
            } else {
                signed_greater_equal(actual, expected)
            },
            true,
        )),
        ComparisonOperator::In => None,
    }
}
