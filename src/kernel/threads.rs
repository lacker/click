//! Checked thread creation and join for one joinable worker.
//!
//! A worker is an ordinary C function verified once against its own
//! contract. `pthread_create` runs that contract as an ordinary verified
//! call at the spawn point, but hands the parent only the frame it holds
//! *during* the call: the resources left after the worker's requirements,
//! the loan ledger with the worker's views still lent, and the havoc of the
//! worker's effect region. Everything the call's return half produced (the
//! recovered resources, the worker's guarantees, the ledger recovery) is
//! withheld in a suspension record keyed by the fresh handle value written
//! to `*thread`, and one linear `joinable` token carries that handle.
//! `pthread_join` consumes the token and installs the record.
//!
//! Soundness under C11/POSIX: creation synchronizes with the worker's start,
//! so the worker's entry state is the parent's state at the spawn;
//! termination synchronizes with join's return, so the worker's guarantees
//! and returned resources reach the parent only at join. Between the two,
//! the parent holds no authority over the transferred region, so modeling
//! the worker's effect at the spawn is unobservable to it.

use std::sync::Arc;

use super::KernelVariableGenerator;
use super::functions::{evaluate_c_arguments_paths, execute_verified_function_rule};
use super::loans::{CheckedLoanCallEvidenceSequence, LoanLedger};
use super::reasoning::path_facts::assumptions_with_path_context;
use super::reasoning::{collect_assumption_variables, collect_c_state_bitvector_variables};
use super::{
    AlgebraicValue, Bitvector32Term, CExecutionEnvironment, CExpression, CFunction,
    CFunctionOutcome, CFunctionPath, CResource, CResourceFact, CRuntimeError, CState, CType,
    CValue, ConditionTerm, ExecutionBudget, ExecutionPureFact, ExecutionResult, PointerBlock,
    Proposition, PureFactContext, ResourceContext, Variable,
};
use std::collections::BTreeSet;

/// The kernel-builtin linear right to join one created thread. Its
/// arguments are the handle value written by the creating call, the
/// worker's address, and the worker's argument.
pub const JOINABLE_RESOURCE_NAME: &str = "joinable";

/// The withheld return half of a worker's call, installed at join.
#[derive(Clone, Debug)]
pub(crate) struct SuspendedJoin {
    id: u64,
    worker: String,
    /// The parent's frame during the call: what remains after the worker's
    /// requirements were reserved. Subtracting it from the recovered frame
    /// yields exactly the call's outputs.
    mid_frame: ResourceContext,
    mid_ledger: Option<LoanLedger>,
    /// The fully recovered caller state the ordinary call produced.
    return_state: CState,
    /// The call's facts: its effect summary and the worker's guarantees.
    facts: Vec<ExecutionPureFact>,
    loan_evidence: CheckedLoanCallEvidenceSequence,
}

impl PartialEq for SuspendedJoin {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}
impl Eq for SuspendedJoin {}
impl std::hash::Hash for SuspendedJoin {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}
impl PartialOrd for SuspendedJoin {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for SuspendedJoin {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id.cmp(&other.id)
    }
}

/// Fresh kernel variables that collide with nothing the caller's state or
/// assumptions mention, minted the way the call executor mints them.
fn fresh_variables(
    caller_state: &CState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    count: usize,
) -> Vec<Variable> {
    let mut existing = BTreeSet::new();
    collect_c_state_bitvector_variables(caller_state, &mut existing);
    collect_assumption_variables(assumptions, &mut existing);
    let mut generator = KernelVariableGenerator::fresh_for(budget.next_kernel_variable, existing);
    let variables = (0..count).map(|_| generator.next()).collect();
    budget.next_kernel_variable = generator.next;
    variables
}

fn thread_failure(message: impl Into<String>) -> CFunctionPath {
    CFunctionPath {
        outcome: CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(message.into())),
        facts: Vec::new(),
        obligations: Vec::new(),
        loan_evidence: super::loans::empty_checked_loan_evidence_sequence(),
    }
}

fn joinable_token(handle: &CValue, worker: &CValue, argument: &CValue) -> CResourceFact {
    CResourceFact::own(CResource::Token {
        name: JOINABLE_RESOURCE_NAME.to_string(),
        arguments: Arc::from(vec![
            AlgebraicValue::C(handle.clone()),
            AlgebraicValue::C(worker.clone()),
            AlgebraicValue::C(argument.clone()),
        ]),
    })
}

fn memory_effect_facts(facts: &[ExecutionPureFact]) -> Vec<ExecutionPureFact> {
    facts
        .iter()
        .filter(|fact| {
            matches!(
                fact.proposition(),
                Proposition::CMemoryEffectSummary { .. } | Proposition::CMemoryMutatesOnly { .. }
            )
        })
        .cloned()
        .collect()
}

fn result_fact(result: Variable, is_zero: bool) -> ExecutionPureFact {
    ExecutionPureFact::certified(Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::Variable(result),
            Bitvector32Term::Constant(0),
        ),
        is_zero,
    ))
}

/// `pthread_create(thread, attr, start, arg)`.
pub(super) fn execute_thread_create(
    caller_state: &CState,
    declaration: &CFunction,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CFunctionPath>> {
    if arguments.len() != 4 {
        return Ok(vec![thread_failure(format!(
            "`{}` takes four arguments",
            declaration.name()
        ))]);
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
                loan_evidence: super::loans::empty_checked_loan_evidence_sequence(),
            });
            continue;
        }
        let [thread, attributes, start, argument] = arguments_path.values.as_slice() else {
            paths.push(thread_failure("thread creation arguments did not evaluate"));
            continue;
        };
        let CValue::Pointer(thread) = thread else {
            paths.push(thread_failure(
                "the thread handle argument must be a pointer",
            ));
            continue;
        };
        if !matches!(attributes, CValue::Pointer(pointer) if pointer.is_null()) {
            paths.push(thread_failure(
                "thread attributes are not supported; pass a null `pthread_attr_t *`",
            ));
            continue;
        }
        let Some(worker_name) = (match start {
            CValue::Pointer(pointer) => match &pointer.pointer().block {
                PointerBlock::Function(name) => Some(name.clone()),
                _ => None,
            },
            _ => None,
        }) else {
            paths.push(thread_failure(
                "the worker must be the address of a verified C function; abstract callbacks are not supported yet",
            ));
            continue;
        };
        let Some(rule) = environment.get_verified_function_rule(&worker_name) else {
            paths.push(thread_failure(format!(
                "worker `{worker_name}` is not a verified function in this project"
            )));
            continue;
        };
        let path_assumptions = assumptions_with_path_context(
            assumptions,
            &arguments_path.facts,
            &arguments_path.obligations,
        );
        // The handle is stored the way an ordinary assignment stores: the
        // cell must be writable here, as a live local block or an owned
        // range.
        if !path_assumptions.proves_memory_access(caller_state.memory(), thread.pointer(), 8) {
            paths.push(thread_failure(
                "the caller must be able to write the `pthread_t` cell the created handle is written to",
            ));
            continue;
        }
        let worker_argument = [CExpression::Value(argument.clone())];
        // The worker's call boundary, run at the spawn point. Its entry half
        // reserves the task; the ordinary call then recovers everything,
        // and the recovered frame is withheld until join.
        let prepared = super::functions::prepare_spawned_worker_frame(
            caller_state,
            rule,
            &worker_argument,
            &path_assumptions,
            environment,
            budget,
        )?;
        let (mid_frame, mid_ledger, mid_participant) = match prepared {
            Ok(frame) => frame,
            Err(failure) => {
                paths.push(failure);
                continue;
            }
        };
        let worker_paths = execute_verified_function_rule(
            caller_state,
            rule,
            &worker_argument,
            &path_assumptions,
            environment,
            budget,
        )?;
        let mut return_path = None;
        for worker_path in worker_paths {
            match worker_path.outcome {
                CFunctionOutcome::Return { state, .. } => {
                    if return_path.is_some() {
                        paths.push(thread_failure(
                            "a worker with more than one return frontier is not supported",
                        ));
                        continue;
                    }
                    return_path = Some((state, worker_path.facts, worker_path.loan_evidence));
                }
                CFunctionOutcome::Throw { .. } | CFunctionOutcome::VerificationDiverges => {
                    paths.push(thread_failure(
                        "a worker must return; exceptional workers are not supported",
                    ));
                }
                outcome @ (CFunctionOutcome::UndefinedBehavior(_)
                | CFunctionOutcome::RuntimeError(_)) => {
                    paths.push(CFunctionPath {
                        outcome,
                        facts: worker_path.facts,
                        obligations: worker_path.obligations,
                        loan_evidence: super::loans::empty_checked_loan_evidence_sequence(),
                    });
                }
            }
        }
        let Some((return_state, worker_facts, loan_evidence)) = return_path else {
            continue;
        };
        let [handle_variable, result_variable, unspecified_variable] =
            fresh_variables(caller_state, &path_assumptions, budget, 3)
                .try_into()
                .expect("three fresh variables");
        let handle = CValue::UInt64(Bitvector32Term::Variable(handle_variable));
        let result = CValue::Int32(Bitvector32Term::Variable(result_variable));

        // Success: the parent keeps its mid-call frame plus the right.
        let token = joinable_token(&handle, start, argument);
        let mut success = caller_state.clone();
        success.set_memory(
            return_state
                .memory()
                .clone()
                .store(thread.pointer().clone(), handle.clone()),
        );
        let resources = match mid_frame
            .clone()
            .try_compose_into_valid_context_delaying_normalization([token], &path_assumptions)
        {
            Ok(resources) => resources,
            Err(error) => {
                paths.push(thread_failure(format!(
                    "could not mint the completion right: {error:?}"
                )));
                continue;
            }
        };
        success.resources = resources;
        if let Some(ledger) = &mid_ledger {
            success.loan_ledger = Some(ledger.clone());
            success.loan_participant = mid_participant;
        }
        success.next_local_frame = return_state.next_local_frame;
        success.next_local_lifetime = return_state.next_local_lifetime;
        let record = SuspendedJoin {
            id: handle_variable.0,
            worker: worker_name.clone(),
            mid_frame: mid_frame.clone(),
            mid_ledger: mid_ledger.clone(),
            return_state,
            facts: worker_facts.clone(),
            loan_evidence,
        };
        Arc::make_mut(&mut success.pending_joins)
            .insert(Bitvector32Term::Variable(handle_variable), Arc::new(record));
        let mut success_facts = arguments_path.facts.clone();
        success_facts.extend(memory_effect_facts(&worker_facts));
        success_facts.push(result_fact(result_variable, true));
        paths.push(CFunctionPath {
            outcome: CFunctionOutcome::Return {
                value: result.clone(),
                state: success,
            },
            facts: success_facts,
            obligations: arguments_path.obligations.clone(),
            loan_evidence: super::loans::empty_checked_loan_evidence_sequence(),
        });

        // Failure: nothing was transferred and no right exists. The handle
        // cell is unspecified.
        let mut failure = caller_state.clone();
        let unspecified = CValue::UInt64(Bitvector32Term::Variable(unspecified_variable));
        failure.set_memory(
            caller_state
                .memory()
                .clone()
                .store(thread.pointer().clone(), unspecified),
        );
        let mut failure_facts = arguments_path.facts;
        failure_facts.push(result_fact(result_variable, false));
        paths.push(CFunctionPath {
            outcome: CFunctionOutcome::Return {
                value: result,
                state: failure,
            },
            facts: failure_facts,
            obligations: arguments_path.obligations,
            loan_evidence: super::loans::empty_checked_loan_evidence_sequence(),
        });
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

/// `pthread_join(thread, retval)`.
pub(super) fn execute_thread_join(
    caller_state: &CState,
    declaration: &CFunction,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CFunctionPath>> {
    if arguments.len() != 2 {
        return Ok(vec![thread_failure(format!(
            "`{}` takes two arguments",
            declaration.name()
        ))]);
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
                loan_evidence: super::loans::empty_checked_loan_evidence_sequence(),
            });
            continue;
        }
        let [handle, result_slot] = arguments_path.values.as_slice() else {
            paths.push(thread_failure("thread join arguments did not evaluate"));
            continue;
        };
        if !matches!(result_slot, CValue::Pointer(pointer) if pointer.is_null()) {
            paths.push(thread_failure(
                "collecting a worker's return value is not supported; pass a null `void **`",
            ));
            continue;
        }
        let CValue::UInt64(handle_term) = handle else {
            paths.push(thread_failure(
                "the joined handle must be a `pthread_t` value",
            ));
            continue;
        };
        let path_assumptions = assumptions_with_path_context(
            assumptions,
            &arguments_path.facts,
            &arguments_path.obligations,
        );
        let Some(record) = caller_state.pending_joins.get(handle_term).cloned() else {
            paths.push(thread_failure(
                "join requires a handle written by a successful creation on this path; the handle's bits carry no authority",
            ));
            continue;
        };
        let token = caller_state.resources().facts().iter().find(|fact| {
            matches!(fact.resource(), CResource::Token { name, arguments }
                if name == JOINABLE_RESOURCE_NAME
                    && arguments.first() == Some(&AlgebraicValue::C(handle.clone())))
                && fact.is_own()
        });
        let Some(token) = token.cloned() else {
            paths.push(thread_failure(
                "join requires the completion right for this handle; it was already consumed or never held",
            ));
            continue;
        };
        if caller_state.loan_ledger().cloned() != record.mid_ledger {
            paths.push(thread_failure(
                "join after other stable-view activity in the parent is not supported yet",
            ));
            continue;
        }
        let Some(without_token) = caller_state
            .resources()
            .clone()
            .without_fact_incrementally(&token, &path_assumptions)
        else {
            paths.push(thread_failure("could not consume the completion right"));
            continue;
        };
        // The call's outputs are the recovered frame minus the mid-call frame.
        let outputs = record
            .mid_frame
            .facts()
            .iter()
            .try_fold(record.return_state.resources().clone(), |outputs, held| {
                outputs.without_fact_incrementally(held, &path_assumptions)
            });
        let Some(outputs) = outputs else {
            paths.push(thread_failure(
                "the withheld return frame does not extend the frame held during the call",
            ));
            continue;
        };
        let resources = match without_token.try_compose_into_valid_context_delaying_normalization(
            outputs.facts().iter().cloned(),
            &path_assumptions,
        ) {
            Ok(resources) => resources,
            Err(error) => {
                paths.push(thread_failure(format!(
                    "could not install the worker's returned resources: {error:?}"
                )));
                continue;
            }
        };
        let mut joined = caller_state.clone();
        joined.resources = resources;
        joined.loan_ledger = record.return_state.loan_ledger.clone();
        joined.loan_participant = record.return_state.loan_participant;
        joined.loan_view_bindings = record.return_state.loan_view_bindings.clone();
        joined.counted_populations = record.return_state.counted_populations.clone();
        Arc::make_mut(&mut joined.pending_joins).remove(handle_term);
        let mut facts = arguments_path.facts;
        facts.extend(record.facts.iter().cloned());
        let _ = (&record.worker, &CType::Int32);
        paths.push(CFunctionPath {
            outcome: CFunctionOutcome::Return {
                value: CValue::Int32(Bitvector32Term::Constant(0)),
                state: joined,
            },
            facts,
            obligations: arguments_path.obligations,
            loan_evidence: record.loan_evidence.clone(),
        });
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}
