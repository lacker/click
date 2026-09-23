//! Internal, checked fork/join ownership transitions.
//!
//! This module is deliberately not connected to C library declarations yet.
//! A successful creation reserves a verified, terminating worker's task once,
//! havocs only its checked mutable footprint, and withholds its outputs until
//! join. The opaque completion right lives in a persistent, linear registry;
//! an integer or a resource with a convenient name cannot manufacture it.
//!
//! The initial profile supports explicit external-memory ownership and stable views with
//! no escaping borrows, allocation, exceptions, cancellation, or detachment.
//! Join assumes success only for this context's live, unique, terminating child.

use std::sync::Arc;

use crate::persistent::PersistentMap;

use super::functions::suspend_verified_worker;
use super::loans::{LoanLedger, StableViewTransferPlan};
use super::{
    CExecutionEnvironment, CMemory, CMemoryRange, CState, CValue, CVerifiedFunctionRule,
    CVerifiedFunctionTerminationRule, ExecutionBudget, ExecutionPureFact, ExecutionResult,
    Proposition, PureFactContext, ResourceContext,
};

/// A kernel identity, not the integer representation of `pthread_t`. The C
/// boundary will need a checked binding to the actual written handle value.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(super) struct ThreadHandle(u64);

/// An explicit runtime assumption, scoped by `join` to a live child of this
/// parent with matching termination evidence. It grants no right by itself.
#[derive(Clone, Copy, Debug)]
pub(super) enum JoinRuntimeAssumption {
    ValidJoinSucceeds,
}

/// Constructed only by the shared verified-call engine, before synchronous
/// recovery. The worker's output delta is separate from the caller's frame.
#[derive(Clone, Debug)]
pub(super) struct WorkerCompletion {
    plan: StableViewTransferPlan,
    outputs: ResourceContext,
    memory: CMemory,
    effects: Vec<CMemoryRange>,
    facts: Vec<ExecutionPureFact>,
}

impl WorkerCompletion {
    pub(super) fn checked(
        plan: StableViewTransferPlan,
        outputs: ResourceContext,
        memory: CMemory,
        effects: Vec<CMemoryRange>,
        facts: Vec<ExecutionPureFact>,
    ) -> Self {
        Self {
            plan,
            outputs,
            memory,
            effects,
            facts,
        }
    }
}

#[derive(Clone, Debug)]
struct CompletionRight {
    // Retain the exact callback, task argument, and checked resource plan.
    worker: Arc<CVerifiedFunctionRule>,
    argument: CValue,
    completion: WorkerCompletion,
}

/// A checked task application before the runtime chooses whether creation
/// succeeded. Both outcomes are available only after the worker contract and
/// exact termination evidence have been validated against this parent.
pub(super) struct PreparedThreadCreate<'a> {
    parent: &'a ThreadContext,
    worker: &'a CVerifiedFunctionRule,
    argument: CValue,
    completion: WorkerCompletion,
}

impl PreparedThreadCreate<'_> {
    pub(super) fn failure(&self) -> ThreadContext {
        self.parent.clone()
    }

    pub(super) fn success(self) -> (ThreadContext, ThreadHandle, ExecutionPureFact) {
        static NEXT_HANDLE: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
        let handle = ThreadHandle(NEXT_HANDLE.fetch_add(1, std::sync::atomic::Ordering::Relaxed));
        let effect = ExecutionPureFact::internal(Proposition::CMemoryEffectSummary {
            before: self.parent.parent.memory().clone(),
            after: self.completion.memory.clone(),
            mutable_ranges: self.completion.effects.clone(),
        })
        .into_certified();
        let mut next = self.parent.clone();
        next.parent = next
            .parent
            .with_resource_context(
                self.completion
                    .plan
                    .caller_resources_after_requirements
                    .clone(),
            )
            .with_loan_ledger(Some(self.completion.plan.ledger.clone()))
            .with_memory(self.completion.memory.clone());
        next.rights.insert(
            handle,
            Arc::new(CompletionRight {
                worker: Arc::new(self.worker.clone()),
                argument: self.argument,
                completion: self.completion,
            }),
        );
        (next, handle, effect)
    }
}

/// One parent path. Clones share immutable roots, just like ordinary C state;
/// a successful join consumes its entry in the successor path's registry.
#[derive(Clone)]
pub(super) struct ThreadContext {
    parent: CState,
    rights: PersistentMap<ThreadHandle, Arc<CompletionRight>>,
}

impl ThreadContext {
    pub(super) fn new(mut parent: CState) -> Result<Self, &'static str> {
        match (parent.loan_ledger(), parent.loan_participant()) {
            (None, None) => {
                let ledger = LoanLedger::new();
                let participant = ledger
                    .fresh_participant()
                    .map_err(|_| "invalid parent participant")?;
                parent = parent
                    .with_loan_ledger(Some(ledger))
                    .with_loan_participant(Some(participant));
            }
            (Some(ledger), Some(participant)) if ledger.contains_participant(participant) => {}
            _ => return Err("inconsistent parent loan context"),
        }
        Ok(Self {
            parent,
            rights: PersistentMap::default(),
        })
    }

    pub(super) fn parent(&self) -> &CState {
        &self.parent
    }

    pub(super) fn prepare_create<'a>(
        &'a self,
        worker: &'a CVerifiedFunctionRule,
        termination: Option<&CVerifiedFunctionTerminationRule>,
        argument: CValue,
        assumptions: &PureFactContext,
        environment: &CExecutionEnvironment,
        budget: &mut ExecutionBudget,
    ) -> ExecutionResult<Result<PreparedThreadCreate<'a>, String>> {
        if termination.is_none_or(|termination| termination.function != worker.function) {
            return Ok(Err(
                "spawn requires termination evidence for the exact worker".to_string(),
            ));
        }
        let completion = match suspend_verified_worker(
            &self.parent,
            worker,
            argument.clone(),
            assumptions,
            environment,
            budget,
        )? {
            Ok(completion) => completion,
            Err(error) => return Ok(Err(error)),
        };
        if completion.plan.caller_participant()
            != self.parent.loan_participant().expect("parent participant")
        {
            return Ok(Err(
                "worker partition belongs to a different parent".to_string()
            ));
        }
        if completion
            .plan
            .recheck_entry(self.parent.loan_ledger().expect("parent ledger"))
            .is_err()
        {
            return Ok(Err("invalid worker entry evidence".to_string()));
        }
        Ok(Ok(PreparedThreadCreate {
            parent: self,
            worker,
            argument,
            completion,
        }))
    }

    pub(super) fn spawn(
        &self,
        worker: &CVerifiedFunctionRule,
        termination: Option<&CVerifiedFunctionTerminationRule>,
        argument: CValue,
        assumptions: &PureFactContext,
        environment: &CExecutionEnvironment,
        budget: &mut ExecutionBudget,
    ) -> ExecutionResult<Result<(Self, ThreadHandle, ExecutionPureFact), String>> {
        Ok(self
            .prepare_create(
                worker,
                termination,
                argument,
                assumptions,
                environment,
                budget,
            )?
            .map(PreparedThreadCreate::success))
    }

    pub(super) fn join(
        &self,
        handle: ThreadHandle,
        _runtime: JoinRuntimeAssumption,
        assumptions: &PureFactContext,
    ) -> Result<(Self, Vec<ExecutionPureFact>), &'static str> {
        let right = self
            .rights
            .get(&handle)
            .ok_or("no live completion right for this handle")?;
        let completion = &right.completion;
        let ledger = self.parent.loan_ledger().expect("parent ledger");
        if self.parent.loan_participant() != Some(completion.plan.caller_participant()) {
            return Err("completion right belongs to a different parent");
        }
        // Compose only this worker's checked output delta into today's frame.
        // No saved parent memory, ledger, bindings or resource frame is restored.
        let resources = self
            .parent
            .resources()
            .clone()
            .try_compose_into_valid_context_delaying_normalization(
                completion.outputs.facts().iter().cloned(),
                assumptions,
            )
            .map_err(|_| "worker outputs conflict with the current parent frame")?;
        let recovery = completion
            .plan
            .clone()
            .recover_suspended_views(
                ledger.clone(),
                resources,
                self.parent.loan_view_bindings().clone(),
                assumptions,
            )
            .map_err(|_| "worker loans cannot be recovered in the current parent context")?;
        let mut next = self.clone();
        next.parent = next
            .parent
            .with_resource_context(recovery.resources)
            .with_loan_ledger(Some(recovery.ledger))
            .with_loan_view_bindings(recovery.view_bindings);
        next.rights.remove(&handle);
        Ok((next, completion.facts.clone()))
    }
}
