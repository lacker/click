use super::diagnostics::*;
use super::*;
use crate::surface::proof_diagnostics::render::render_resource_fact_diagnostic;

mod arithmetic_engine;
mod contract_evaluation;
mod integer_affine_planner;
mod integer_refutation_planner;
mod normalization;
mod predicates;
mod segments;
mod signed_arithmetic_planner;
mod simplex;
mod special_arithmetic_planner;
pub(super) use arithmetic_engine::*;
pub(super) use contract_evaluation::*;
pub(super) use integer_refutation_planner::*;
pub(super) use normalization::*;
pub(super) use predicates::*;
pub(super) use segments::*;
#[allow(unused_imports)]
pub(super) use signed_arithmetic_planner::*;
pub(super) use special_arithmetic_planner::*;

/// Exact resource production evidence for one claim in one checked execution.
/// Fields are private to the checker; presentation syntax cannot create it.
#[derive(Clone)]
pub(super) struct CheckedResourceClaim<'e> {
    execution: &'e CheckedFunctionExecution,
    path_index: usize,
    key: FunctionContractClaimKey,
    returned_resources: crate::kernel::ResourceContext,
    borrowed: bool,
    deferred_guard: bool,
}

impl CheckedResourceClaim<'_> {
    pub(super) fn inactive(
        execution: &CheckedFunctionExecution,
        path_index: usize,
        key: FunctionContractClaimKey,
        borrowed: bool,
    ) -> CheckedResourceClaim<'_> {
        CheckedResourceClaim {
            execution,
            path_index,
            key,
            returned_resources: crate::kernel::ResourceContext::new(),
            borrowed,
            deferred_guard: false,
        }
    }

    pub(super) fn deferred(
        execution: &CheckedFunctionExecution,
        path_index: usize,
        key: FunctionContractClaimKey,
        borrowed: bool,
    ) -> CheckedResourceClaim<'_> {
        CheckedResourceClaim {
            execution,
            path_index,
            key,
            returned_resources: crate::kernel::ResourceContext::new(),
            borrowed,
            deferred_guard: true,
        }
    }

    pub(super) fn matches(
        &self,
        execution: &CheckedFunctionExecution,
        path_index: usize,
        key: &FunctionContractClaimKey,
    ) -> bool {
        std::ptr::eq(self.execution, execution) && self.path_index == path_index && &self.key == key
    }
    pub(super) fn claim_key(&self) -> &FunctionContractClaimKey {
        &self.key
    }
    pub(super) fn path_index(&self) -> usize {
        self.path_index
    }
    pub(super) fn returned_resources(&self) -> &crate::kernel::ResourceContext {
        &self.returned_resources
    }
    pub(super) fn contributes_returned_resources(&self) -> bool {
        !self.borrowed && !self.deferred_guard
    }
    pub(super) fn defers_resource_transition(&self) -> bool {
        self.deferred_guard
    }
}

/// A plain produced memory clause hands the caller initialized bytes, so the
/// function must have written every byte of it that holds a value. The first
/// range it has not, rendered for a diagnostic.
fn produced_range_left_uninitialized(
    resource: &ResourceClause,
    expected: &[ResourceFact],
    parameter_binding: ParameterBinding<'_>,
    post_state: &ExecutionState,
    assumptions: &PureFactContext,
) -> Option<String> {
    let segments = match resource {
        ResourceClause::OwnMemory(segment) => std::slice::from_ref(segment),
        ResourceClause::MemoryAggregate { segments, .. } => segments.as_slice(),
        _ => return None,
    };
    if segments.iter().any(ContractSegment::is_uninitialized) {
        return None;
    }
    expected.iter().enumerate().find_map(|(index, fact)| {
        let Resource::Memory(range) = fact.resource() else {
            return None;
        };
        let runs = (expected.len() == segments.len())
            .then(|| {
                crate::surface::lowering::contract_segment_value_runs(
                    parameter_binding.parameters,
                    &segments[index],
                )
            })
            .flatten();
        (!crate::kernel::memory_range_is_initialized(
            post_state.memory(),
            range,
            runs.as_deref(),
            assumptions,
        ))
        .then(|| {
            let rendered = render_resource_fact_diagnostic(fact, parameter_binding);
            rendered
                .strip_prefix("owns ")
                .map_or(rendered.clone(), str::to_string)
        })
    })
}

pub(super) fn prove_ensure_resource<'e>(
    checked_execution: &'e CheckedFunctionExecution,
    claim_key: FunctionContractClaimKey,
    claim_label: &str,
    path_index: usize,
    // Read only to describe a failure: a path's merged facts are its whole
    // history, so a claim that holds does not build them.
    execution_pure_facts: impl Fn() -> crate::kernel::ExecutionFacts,
    available_pure_facts: &(impl PropositionSource + ?Sized),
    resource: &ResourceClause,
    borrowed: bool,
    parameter_binding: ParameterBinding<'_>,
    pre_state: &ExecutionState,
    entry_state: &ExecutionState,
    outcome: &FunctionOutcome,
    guard_active: Option<bool>,
    guard_deferred: bool,
) -> Result<CheckedResourceClaim<'e>, ClickError> {
    let mut requirement = None;
    let checked = (|| {
        // Post-return resource folds can extend the checked path before final
        // contract certification. Its typed outcome Proof supplies the returning
        // state checked below; the original artifact supplies stable path identity.
        if checked_execution.paths().get(path_index).is_none() {
            return Err(ClickError::new(
                "resource claim has no checked execution path",
            ));
        }
        let FunctionOutcome::Return {
            value: result,
            state: post_state,
        } = outcome
        else {
            return Err(ClickError::new(format!(
                "`{claim_label}` failed on path {path_index}: {}\n{}",
                describe_function_outcome(outcome, parameter_binding),
                describe_proof_context(
                    &available_pure_facts
                        .propositions()
                        .cloned()
                        .collect::<Vec<_>>(),
                    pre_state.resources().facts(),
                    parameter_binding,
                    &execution_pure_facts()
                )
            )));
        };
        if guard_deferred {
            return Ok(CheckedResourceClaim::deferred(
                checked_execution,
                path_index,
                claim_key,
                borrowed,
            ));
        }
        if guard_active == Some(false) {
            return Ok(CheckedResourceClaim::inactive(
                checked_execution,
                path_index,
                claim_key,
                borrowed,
            ));
        }
        // A borrowed resource is returned as it was lent: its clause is read at
        // entry, where address expressions still see the caller's values.
        let clause_state = if borrowed && !matches!(resource, ResourceClause::Named { .. }) {
            pre_state
        } else {
            post_state
        };
        let assumptions = assumptions_from_propositions(available_pure_facts);
        let lower_at = |clause_state: &ExecutionState| {
            lower_resource_clause_facts_at_state_with_result_and_entry(
                resource,
                parameter_binding,
                entry_state,
                clause_state,
                &result.native(),
                &assumptions,
            )
        };
        let expected = match lower_at(clause_state) {
            Ok(expected) => expected,
            Err(error) => {
                // A clause whose argument loads a cell inside a folded
                // field-bearing instance the function holds at this state reads
                // it through the cells that instance's unmatched body owns, as
                // the contract's clauses do everywhere else they are evaluated.
                // Views grant reads only; nothing is opened.
                let definitions = checked_execution
                    .function()
                    .composite_resource_definitions();
                let published = clause_state
                    .resources()
                    .facts()
                    .iter()
                    .flat_map(|fact| {
                        crate::kernel::unmatched_instance_body_views(
                            fact,
                            definitions,
                            clause_state,
                            &assumptions,
                        )
                    })
                    .collect::<Vec<_>>();
                if published.is_empty() {
                    return Err(error);
                }
                let published_state = clause_state.clone().with_resource_context(
                    clause_state
                        .resources()
                        .clone()
                        .unchecked_with_facts(published),
                );
                lower_at(&published_state).map_err(|_| error)?
            }
        };
        if expected.iter().all(|expected| {
            post_state
                .resources()
                .satisfies_fact(expected, &assumptions)
        }) {
            if !borrowed
                && let Some(uninitialized) = produced_range_left_uninitialized(
                    resource,
                    &expected,
                    parameter_binding,
                    post_state,
                    &assumptions,
                )
            {
                requirement = Some(uninitialized.clone());
                return Err(ClickError::new(format!(
                    "`{claim_label}` failed on path {path_index}: the function produces `{uninitialized}` as initialized memory, but has not initialized every byte of it; memory a function returns unwritten is produced as `uninitialized(...)`"
                )));
            }
            return Ok(CheckedResourceClaim {
                execution: checked_execution,
                path_index,
                key: claim_key,
                returned_resources: crate::kernel::ResourceContext::new_with_equalities(
                    &assumptions,
                )
                .unchecked_with_facts(expected.iter().cloned()),
                borrowed,
                deferred_guard: false,
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
        if matches!(
            resource,
            ResourceClause::OwnMemory(_)
                | ResourceClause::ViewMemory(_)
                | ResourceClause::MemoryAggregate { .. }
        ) {
            requirement = Some(render_resource_fact_diagnostic(expected, parameter_binding));
        }
        Err(ClickError::new(format!(
            "`{claim_label}` failed on path {path_index}: {}",
            describe_missing_resource_fact(
                expected,
                &available_pure_facts
                    .propositions()
                    .cloned()
                    .collect::<Vec<_>>(),
                post_state.resources().facts(),
                parameter_binding,
                &execution_pure_facts()
            )
        )))
    })();
    checked.map_err(|error: ClickError| {
        if borrowed {
            error
        } else {
            let requirement = requirement
                .unwrap_or_else(|| crate::surface::validation::describe_resource_clause(resource));
            ClickError::new(format!(
                "{}\nRequires produces {requirement}",
                error.raw_summary()
            ))
        }
    })
}

pub(super) fn evaluate_witness_tactic_value(
    witness: &ProofWitness,
    claim_label: &str,
    path_index: usize,
    tactic_index: usize,
    contract_environment: ContractEnvironment<'_>,
    pre_state: &ExecutionState,
    post_state: &ExecutionState,
    result: Option<&ProgramValue>,
    assumptions: &PureFactContext,
    spec_definitions: SpecDefinitions<'_>,
    recorded_states: &RecordedStates,
) -> Result<ProgramValue, ClickError> {
    let mut active_functions = BTreeSet::new();
    let value = evaluate_contract_expression_with_environment(
        contract_environment.values,
        contract_environment.array_refs,
        pre_state,
        post_state,
        result,
        assumptions,
        witness.value(),
        spec_definitions,
        recorded_states,
        &mut active_functions,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`witness` failed for `{claim_label}` path {path_index}, tactic {tactic_index}: could not evaluate witness value for `{}`: {message}",
            witness.name()
        ))
    })?;
    Ok(value)
}

pub(super) fn apply_witness_tactic(
    witness: &ProofWitness,
    witness_value: ProgramValue,
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
    if name != witness.name() {
        return Err(ClickError::new(format!(
            "`witness` failed for `{claim_label}` path {path_index}, tactic {tactic_index}: goal binds `{name}`, but proof provided witness `{}`",
            witness.name()
        )));
    }

    let expected = match &sort {
        sort if sort.machine_integer_type().is_some() => {
            Some(sort.machine_integer_type().unwrap().program_type())
        }
        Sort::ProgramPointer(interface_type) | Sort::ProgramObjectPointer(interface_type, _) => {
            Some(*interface_type)
        }
        _ => None,
    };
    if let Some(expected) = expected
        && !expected.accepts(&witness_value)
    {
        let actual = match witness_value.numeric_value() {
            ProgramValue::PointerInteger(_) => unreachable!("numeric projection"),
            ProgramValue::Parameter(_) => witness_value.program_type(),
            ProgramValue::Void => ProgramType::Void,
            ProgramValue::Bool(_) => ProgramType::Bool,
            ProgramValue::Int8(_) => ProgramType::Int8,
            ProgramValue::Int16(_) => ProgramType::Int16,
            ProgramValue::Int32(_) => ProgramType::Int32,
            ProgramValue::UInt8(_) => ProgramType::UInt8,
            ProgramValue::UInt16(_) => ProgramType::UInt16,
            ProgramValue::UInt32(_) => ProgramType::UInt32,
            ProgramValue::Int64(_) => ProgramType::Int64,
            ProgramValue::UInt64(_) => ProgramType::UInt64,
            ProgramValue::Int128(_) => ProgramType::Int128,
            ProgramValue::UInt128(_) => ProgramType::UInt128,
            ProgramValue::Float32(_) => ProgramType::Float32,
            ProgramValue::Float64(_) => ProgramType::Float64,
            ProgramValue::Pointer(pointer) => pointer.program_type(),
        };
        return Err(ClickError::new(format!(
            "`witness` failed for `{claim_label}` path {path_index}, tactic {tactic_index}: witness `{}` has the wrong type: expected {}, got {}",
            witness.name(),
            describe_interface_type(super::generics::interface_type_from_program_type(expected)),
            describe_interface_type(super::generics::interface_type_from_program_type(actual)),
        )));
    }

    if let Sort::ProgramObjectPointer(ty, class) = &sort
        && !crate::kernel::AlgebraicValueType::ObjectPointer(*ty, class.clone())
            .accepts_program_value(&witness_value)
    {
        return Err(ClickError::new(
            "pointer witness lacks the required original object class",
        ));
    }
    let result = match (sort, witness_value) {
        (sort, value) if sort.machine_integer_type().is_some() => {
            let value = match value {
                crate::kernel::integer_c_value!(v) => v,
                _ => unreachable!("witness type was checked above"),
            };
            substitute_int32_variable_in_proposition(&body, var, value)
        }
        (
            Sort::ProgramPointer(expected) | Sort::ProgramObjectPointer(expected, _),
            ProgramValue::Pointer(pointer),
        ) if expected.accepts(&ProgramValue::Pointer(pointer.clone())) => {
            crate::kernel::substitute_pointer_value_in_proposition(&body, var, &pointer)
                .map_err(ClickError::new)?
        }
        _ => {
            return Err(ClickError::new(format!(
                "`witness` failed for `{claim_label}` path {path_index}, tactic {tactic_index}: unsupported existential witness sort for `{}`",
                witness.name()
            )));
        }
    };
    Ok(result)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn comparison_condition(
    actual: MachineTerm,
    operator: ComparisonOperator,
    expected: MachineTerm,
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
