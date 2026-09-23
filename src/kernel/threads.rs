//! Internal, checked fork/join ownership transitions.
//!
//! The modeled pthread binding connects these transitions to checked C calls.
//! A successful creation reserves a verified, terminating worker's task once,
//! havocs only its checked mutable footprint, and withholds its outputs until
//! join. The opaque completion right lives in a persistent, linear registry;
//! an integer or a resource with a convenient name cannot manufacture it.
//!
//! The initial profile supports explicit external-memory ownership and stable views with
//! no escaping borrows, allocation, exceptions, cancellation, or detachment.
//! Join assumes success only for this context's live, unique, terminating child.

use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use crate::persistent::PersistentMap;

use super::functions::suspend_verified_worker;
use super::loans::{LoanLedger, StableViewTransferPlan};
use super::{
    Bitvector32Term, CExecutionEnvironment, CMemory, CMemoryRange, CState, CValue,
    CVerifiedFunctionRule, CVerifiedFunctionTerminationRule, ConditionTerm, ExecutionBudget,
    ExecutionPureFact, ExecutionResult, Pointer, PointerBlock, Proposition, PureFactContext,
    ResourceContext,
};

/// A kernel identity, not the integer representation of `pthread_t`. The C
/// binding writes an opaque value carrying this identity to a checked slot.
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

/// The only intervening operations supported while a create status is
/// unresolved are scalar local declarations and assignments. Record their
/// exact memory deltas so choosing either outcome preserves those writes.
#[derive(Clone, Debug)]
pub(super) enum PendingThreadMemoryDelta {
    Declare { block: PointerBlock, bytes: u32 },
    Store { pointer: Pointer, value: CValue },
}

#[derive(Clone)]
pub(super) struct PendingThreadCreate {
    storage: Arc<PendingThreadCreateStorage>,
}

struct PendingThreadCreateStorage {
    identity: u64,
    status: Bitvector32Term,
    handle_slot: Pointer,
    success: CState,
    failure: CState,
    deltas: PersistentMap<u64, PendingThreadMemoryDelta>,
    next_delta: u64,
}

impl PendingThreadCreate {
    fn fresh_identity() -> u64 {
        static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
        NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    }

    pub(super) fn protects_local(&self, state: &CState, name: &str) -> bool {
        state
            .locals
            .slots
            .get(&self.storage.handle_slot)
            .is_some_and(|output| output == name)
    }

    pub(super) fn new(
        status: Bitvector32Term,
        handle_slot: Pointer,
        success: CState,
        failure: CState,
    ) -> Self {
        debug_assert!(success.pending_thread_create.is_none());
        debug_assert!(failure.pending_thread_create.is_none());
        Self {
            storage: Arc::new(PendingThreadCreateStorage {
                identity: Self::fresh_identity(),
                status,
                handle_slot,
                success,
                failure,
                deltas: PersistentMap::default(),
                next_delta: 0,
            }),
        }
    }

    pub(super) fn with_delta(&self, delta: PendingThreadMemoryDelta) -> Self {
        let storage = &self.storage;
        Self {
            storage: Arc::new(PendingThreadCreateStorage {
                identity: Self::fresh_identity(),
                status: storage.status.clone(),
                handle_slot: storage.handle_slot.clone(),
                success: storage.success.clone(),
                failure: storage.failure.clone(),
                deltas: storage.deltas.with_inserted(storage.next_delta, delta),
                next_delta: storage.next_delta + 1,
            }),
        }
    }

    pub(super) fn map_terms(
        &self,
        status: impl Fn(&Bitvector32Term) -> Bitvector32Term,
        state: impl Fn(&CState) -> CState,
        pointer: impl Fn(&Pointer) -> Pointer,
        value: impl Fn(&CValue) -> CValue,
    ) -> Self {
        let storage = &self.storage;
        let mut deltas = PersistentMap::default();
        for (index, delta) in &storage.deltas {
            let mapped = match delta {
                PendingThreadMemoryDelta::Declare { block, bytes } => {
                    PendingThreadMemoryDelta::Declare {
                        block: block.clone(),
                        bytes: *bytes,
                    }
                }
                PendingThreadMemoryDelta::Store {
                    pointer: address,
                    value: stored,
                } => PendingThreadMemoryDelta::Store {
                    pointer: pointer(address),
                    value: value(stored),
                },
            };
            deltas = deltas.with_inserted(*index, mapped);
        }
        Self {
            storage: Arc::new(PendingThreadCreateStorage {
                identity: Self::fresh_identity(),
                status: status(&storage.status),
                handle_slot: pointer(&storage.handle_slot),
                success: state(&storage.success),
                failure: state(&storage.failure),
                deltas,
                next_delta: storage.next_delta,
            }),
        }
    }

    pub(super) fn resolve(
        &self,
        visible: &CState,
        assumptions: &PureFactContext,
    ) -> Option<CState> {
        let zero = ConditionTerm::Bitvector32Equal(
            Box::new(self.storage.status.clone()),
            Box::new(Bitvector32Term::Constant(0)),
        );
        let success = assumptions.decide(&zero)?;
        let mut selected = if success {
            self.storage.success.clone()
        } else {
            self.storage.failure.clone()
        };
        for (_, delta) in &self.storage.deltas {
            crate::instrumentation::record_deterministic_work(1);
            let memory = match delta {
                PendingThreadMemoryDelta::Declare { block, bytes } => {
                    selected.memory.clone().with_block(block.clone(), *bytes)
                }
                PendingThreadMemoryDelta::Store { pointer, value } => selected
                    .memory
                    .clone()
                    .store_with_context(pointer.clone(), value.clone(), assumptions),
            };
            selected.set_memory(memory);
        }
        let output_binding = selected
            .locals
            .slots
            .get(&self.storage.handle_slot)
            .and_then(|name| {
                selected
                    .locals
                    .bindings
                    .get(name)
                    .map(|binding| (name.clone(), binding.clone()))
            });
        selected.locals = visible.locals.clone();
        if let Some((name, binding)) = output_binding {
            std::sync::Arc::make_mut(&mut selected.locals.bindings).insert(name, binding);
        }
        selected.next_local_frame = visible.next_local_frame;
        selected.next_local_lifetime = visible.next_local_lifetime;
        selected.enclosing_frame_holds_locals = visible.enclosing_frame_holds_locals;
        Some(selected)
    }
}

impl std::fmt::Debug for PendingThreadCreate {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("PendingThreadCreate")
            .field("identity", &self.storage.identity)
            .field("status", &self.storage.status)
            .field("local_deltas", &self.storage.next_delta)
            .finish()
    }
}

impl PartialEq for PendingThreadCreate {
    fn eq(&self, other: &Self) -> bool {
        self.storage.identity == other.storage.identity
    }
}
impl Eq for PendingThreadCreate {}
impl Hash for PendingThreadCreate {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.storage.identity.hash(state);
    }
}
impl PartialOrd for PendingThreadCreate {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for PendingThreadCreate {
    fn cmp(&self, other: &Self) -> Ordering {
        self.storage.identity.cmp(&other.storage.identity)
    }
}

/// Path-local completion authority stored with ordinary C execution state.
/// Clones share the root; an insertion or removal touches only one map path.
/// Like the loan ledger, equality uses a fresh state identity so ordinary
/// state comparisons never walk unrelated live children.
#[derive(Clone)]
pub(super) struct ThreadLedger {
    storage: Arc<ThreadLedgerStorage>,
}

struct ThreadLedgerStorage {
    state: u64,
    rights: PersistentMap<ThreadHandle, Arc<CompletionRight>>,
}

impl ThreadLedger {
    fn fresh_state() -> u64 {
        static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
        NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    }

    pub(super) fn new() -> Self {
        Self {
            storage: Arc::new(ThreadLedgerStorage {
                state: Self::fresh_state(),
                rights: PersistentMap::default(),
            }),
        }
    }

    fn right(&self, handle: ThreadHandle) -> Option<&Arc<CompletionRight>> {
        self.storage.rights.get(&handle)
    }

    pub(super) fn has_live_rights(&self) -> bool {
        !self.storage.rights.is_empty()
    }

    fn with_right(&self, handle: ThreadHandle, right: CompletionRight) -> Self {
        Self {
            storage: Arc::new(ThreadLedgerStorage {
                state: Self::fresh_state(),
                rights: self.storage.rights.with_inserted(handle, Arc::new(right)),
            }),
        }
    }

    fn without_right(&self, handle: ThreadHandle) -> Self {
        Self {
            storage: Arc::new(ThreadLedgerStorage {
                state: Self::fresh_state(),
                rights: self.storage.rights.without_key(&handle),
            }),
        }
    }
}

impl ThreadHandle {
    pub(super) fn c_value(self) -> CValue {
        CValue::UInt64(super::Bitvector32Term::PureFunctionApplication {
            // This name cannot be spelled by C or Click source. The term is
            // copied as an opaque pthread_t value, never derived from its
            // machine integer representation.
            name: format!("\0click.pthread.handle:{}", self.0),
            arguments: vec![],
        })
    }

    pub(super) fn from_c_value(value: &CValue) -> Option<Self> {
        match value {
            CValue::UInt64(super::Bitvector32Term::PureFunctionApplication { name, arguments })
                if arguments.is_empty() =>
            {
                name.strip_prefix("\0click.pthread.handle:")?
                    .parse()
                    .ok()
                    .map(Self)
            }
            _ => None,
        }
    }
}

#[cfg(test)]
mod handle_tests {
    use super::*;

    #[test]
    fn handle_identity_survives_symbolic_variable_substitution() {
        let handle = ThreadHandle(42);
        let value = handle.c_value();
        let substituted = super::super::reasoning::substitute_bitvector_variable_in_c_value(
            &value,
            super::super::Variable(42),
            &super::super::Bitvector32Term::Variable(super::super::Variable(43)),
        );
        assert_eq!(substituted, value);
        assert_eq!(ThreadHandle::from_c_value(&substituted), Some(handle));
        assert_ne!(substituted, ThreadHandle(43).c_value());
    }
}

impl std::fmt::Debug for ThreadLedger {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("ThreadLedger")
            .field("state", &self.storage.state)
            .field("live_rights", &self.storage.rights.len())
            .finish()
    }
}

impl PartialEq for ThreadLedger {
    fn eq(&self, other: &Self) -> bool {
        self.storage.state == other.storage.state
    }
}

impl Eq for ThreadLedger {}

impl Hash for ThreadLedger {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.storage.state.hash(state);
    }
}

impl PartialOrd for ThreadLedger {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ThreadLedger {
    fn cmp(&self, other: &Self) -> Ordering {
        self.storage.state.cmp(&other.storage.state)
    }
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
        let ledger = next.parent.thread_ledger.as_ref().expect("thread ledger");
        next.parent.thread_ledger = Some(ledger.with_right(
            handle,
            CompletionRight {
                worker: Arc::new(self.worker.clone()),
                argument: self.argument,
                completion: self.completion,
            },
        ));
        (next, handle, effect)
    }
}

/// One parent path. Clones share immutable roots, just like ordinary C state;
/// a successful join consumes its entry in the successor path's registry.
#[derive(Clone)]
pub(super) struct ThreadContext {
    parent: CState,
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
        if parent.thread_ledger.is_none() {
            parent.thread_ledger = Some(ThreadLedger::new());
        }
        Ok(Self { parent })
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
            .parent
            .thread_ledger
            .as_ref()
            .and_then(|ledger| ledger.right(handle))
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
        next.parent.thread_ledger = Some(
            next.parent
                .thread_ledger
                .as_ref()
                .expect("thread ledger")
                .without_right(handle),
        );
        Ok((next, completion.facts.clone()))
    }
}
