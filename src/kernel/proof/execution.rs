//! Semantic execution-frontier state owned by the checked proof object.
//!
//! A frontier identifies the exact C region and next statement a checked
//! execution proof must advance. It contains no Surface Click syntax,
//! certificate builder, diagnostic cursor, or smart-planning state.

use super::{PersistentOrderedSet, PersistentSequence, ProofFacts, SharedValue, SharedVec};
#[cfg(test)]
use crate::kernel::ConditionTerm;
use crate::kernel::LoadKind;
use crate::kernel::population_authority::c_creation::{
    CheckedPopulationAuthorityExchange, CheckedPopulationMemberExchange,
};
use crate::kernel::{
    Bitvector32Term, CCompositeResourceDefinition, CConditionOutcome, CExpression, CFunction,
    CFunctionExecutionCandidates, CFunctionOutcome, CMemory, CMemoryRange, CResource,
    CResourceFact, CResourceSpec, CRuntimeError, CState, CStatement, CStatementOutcome, CValue,
    CVerifiedLoopRule, ExecutionBudget, ExecutionLimit, ExecutionPureFact, Pointer, Proposition,
    PureFactContext, ResourceContext, SpecProposition, Theorem, Variable,
};
use crate::kernel::{ExecutionFactSource, ExecutionFacts};
use crate::persistent::PersistentSet;
use std::collections::{BTreeMap, HashMap};
use std::ops::{Deref, DerefMut};
use std::sync::Arc;

#[cfg(test)]
thread_local! {
    static MATCH_SCOPE_INDEX_BUILDS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static MATCH_FRESHNESS_PROBES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static CHECKED_CALL_EVENT_LOOKUP_CANDIDATES: std::cell::Cell<usize> =
        const { std::cell::Cell::new(0) };
}

/// The typed identity of the execution region a frontier executes.
#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub(crate) enum ExecutionRegionKind {
    #[default]
    Function,
    LoopBody,
    /// One arm of a C `if`: exhausting the arm reaches its typed boundary.
    BranchArm,
}

/// How a checked path inside a loop body reached that region's boundary.
///
/// A path that falls off the end of the body reaches the back edge and
/// carries `BodyEnd`. `break` and `continue` reach the same typed boundary
/// early, and the loop rule owes each of them a different obligation: a
/// `break` is an exit, a `continue` is the back edge.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) enum LoopControlExit {
    /// The body ran to its end: the ordinary back edge.
    #[default]
    BodyEnd,
    /// A `break`: the path leaves the loop with whatever it established.
    Break,
    /// A `continue`: the path reaches the back edge before the body's end.
    Continue,
    /// The natural cycle's checked forward `goto` leaves the loop at its
    /// named exit target.
    NaturalExit(crate::kernel::CControlTargetId),
}

impl LoopControlExit {
    /// Whether this path leaves the loop rather than returning to its head.
    pub(crate) fn is_exit(self) -> bool {
        matches!(self, Self::Break | Self::NaturalExit(_))
    }
}

/// Kernel-issued evidence for one semantic C transition accepted by this
/// proof path.
///
/// The proof driver may choose which feasible transition to take, but it
/// cannot manufacture either theorem. Retaining the exact theorem here lets
/// function-exit certification check the chosen path without executing the C
/// body again.
#[derive(Clone)]
pub(crate) enum CheckedExecutionEvent {
    Statement(Theorem),
    /// One opaque call occurrence introduced by the preceding checked
    /// statement. Its registered snapshots are exact recomputed views of that
    /// occurrence, not a structural claim that matching calls are equal.
    Call(CheckedCallEvent),
    Condition(Theorem),
    /// The kernel fact context the preceding `Statement` or `Condition`
    /// theorem was proved under. A transition's theorem lists that context
    /// as its premises; retaining the context is what lets the record call check
    /// those premises exactly, including facts a `have`, `apply`, or
    /// `unfold` established mid-execution, instead of rebuilding the
    /// context from function entry. The context is persistent, so this
    /// shares structure with the proof rather than copying it.
    Context(PureFactContext),
    /// How many memory effects the statement just recorded added to the
    /// proof's effect list. The recorder that pushes the statement appends
    /// those effects itself, so a later join reads a statement's effects off
    /// the list by count instead of matching memories to find them.
    StatementEffects(usize),
    Branch(CheckedExecutionBranch),
    ProofCase(CheckedProofCaseArm),
    /// Every live arm of one logical partition, rejoined at one program
    /// point and one state. What follows it is checked once.
    ProofCaseJoin(CheckedProofCaseJoin),
    ResourceObservation(CheckedResourceObservation),
    AutomaticLifetimeEnd(CheckedAutomaticLifetimeEnd),
    ResourceRewrite(CheckedResourceRewrite),
    ReturnProposition(CheckedReturnProposition),
    PopulationAuthorityRewrite(CheckedPopulationAuthorityRewrite),
    PopulationMemberRewrite(CheckedPopulationMemberRewrite),
    /// One iterated guarded-ownership step (`take`, `give`, `gather`,
    /// `scatter`). Like a lifetime end, it changes only the resource context
    /// and is re-derived from its input state when the trace is checked.
    IteratedStep(CheckedIteratedStep),
    /// One application of a user-defined tactic: the verified rule of a
    /// procedure whose body runs no code, applied with no C statement. It
    /// changes the resource context and adds the rule's `ensures` facts.
    TacticApplication(CheckedTacticApplication),
}

/// A kernel-published return, shared by all logical proofs on that path.
#[derive(Clone)]
struct CheckedReturnContext {
    origin: CStatementOutcome,
    published: CFunctionOutcome,
    facts: ExecutionFacts,
}

impl CheckedReturnContext {
    fn from_candidate(
        origin: CStatementOutcome,
        candidate: &crate::kernel::CFunctionExecutionCandidate,
    ) -> Self {
        let mut facts = candidate.facts().clone();
        facts.extend_shared(candidate.effect_facts());
        Self {
            origin,
            published: candidate.outcome().clone(),
            facts,
        }
    }
}

/// A completed proposition; its assumptions are checked against the retained
/// path when the completion is used by a subsequent resource fold.
#[derive(Clone)]
pub(crate) struct CheckedReturnProposition {
    proof: super::CheckedProposition,
    base: ProofFacts,
    context: Arc<CheckedReturnContext>,
}

impl CheckedReturnProposition {
    fn check(
        proof: super::CheckedProposition,
        base: &ProofFacts,
        context: Arc<CheckedReturnContext>,
    ) -> Result<Self, String> {
        let CFunctionOutcome::Return { value, state } = &context.published else {
            return Err("return proof requires a published return".into());
        };
        let outcome = proof.outcome().ok_or("return proof has no outcome")?;
        // As for checked function propositions, resource representation may
        // change during the proof. The program snapshot and result may not.
        if outcome.is_exceptional
            || outcome.result.as_ref() != value
            || outcome.state.locals() != state.locals()
            || outcome.state.typed_access_policy() != state.typed_access_policy()
            || outcome.state.aggregate_destination != state.aggregate_destination
            || !crate::kernel::api::contract_certification::c_memories_definitionally_equal(
                outcome.state.memory(),
                state.memory(),
                proof.root_assumptions().assumptions(),
            )
        {
            return Err("return proof has a different program snapshot".into());
        }
        Ok(Self {
            proof,
            base: base.clone(),
            context,
        })
    }
}

/// A checked application of a verified tactic rule.
///
/// Only [`Self::check`] builds one, and it applies the rule itself through
/// [`crate::kernel::functions::apply_verified_tactic_rule`], so holding the
/// event is holding the kernel's verdict on that exact before state and fact
/// context. Trace certification then only has to connect the states.
#[derive(Clone)]
pub(crate) struct CheckedTacticApplication {
    /// The tactic whose rule was applied: one call edge of the proof that
    /// applied it, for the termination check.
    name: String,
    before_state: CState,
    pub(crate) after_state: CState,
    before_facts: ProofFacts,
    pub(crate) after_facts: ProofFacts,
}

impl CheckedTacticApplication {
    fn check(
        before_state: &CState,
        before_facts: &ProofFacts,
        name: &str,
        arguments: &[crate::kernel::CValue],
        environment: &crate::kernel::CExecutionEnvironment,
        next_kernel_variable: u64,
    ) -> Result<(Self, u64), crate::kernel::functions::TacticApplicationRefusal> {
        let transition = crate::kernel::functions::apply_verified_tactic_rule(
            before_state,
            name,
            arguments,
            before_facts,
            environment,
            next_kernel_variable,
        )?;
        let after_facts = transition
            .facts
            .iter()
            .fold(before_facts.clone(), |facts, fact| {
                facts.with_kernel_checked_fact(fact.proposition().clone())
            });
        Ok((
            Self {
                name: name.to_string(),
                before_state: before_state.clone(),
                after_state: transition.state,
                before_facts: before_facts.clone(),
                after_facts,
            },
            transition.next_kernel_variable,
        ))
    }

    pub(crate) fn before_state(&self) -> &CState {
        &self.before_state
    }

    fn advance_checked(&self, state: &CState, facts: &ProofFacts) -> Option<ProofFacts> {
        if state != &self.before_state || facts.introduced_since(&self.before_facts).is_none() {
            return None;
        }
        Some(
            self.after_facts
                .introduced_since(&self.before_facts)?
                .into_iter()
                .fold(facts.clone(), |facts, fact| {
                    if facts.contains_top_level(&fact) {
                        facts
                    } else {
                        facts.with_fact(fact)
                    }
                }),
        )
    }
}

/// Proof-object-owned authority for one checked call occurrence.
///
/// Construction may register additional exact result snapshots when a later
/// statement theorem is accepted from a recomputed view of the running state.
/// Consumers can only cite this opaque object and snapshots in its registry;
/// evaluator-local havoc variables never act as authority.
#[derive(Default)]
struct CheckedCallEventRegistryData {
    canonical_views: HashMap<u64, crate::kernel::SharedCMemory>,
    events_by_view: HashMap<crate::kernel::SharedCMemory, Vec<u64>>,
}

/// Shared exact-view index for one family of forked execution proofs.
#[derive(Clone)]
struct CheckedCallEventRegistry {
    identity: Arc<()>,
    next_id: Arc<std::sync::atomic::AtomicU64>,
    data: Arc<std::sync::Mutex<CheckedCallEventRegistryData>>,
}

impl CheckedCallEventRegistry {
    fn new() -> Self {
        Self {
            identity: Arc::new(()),
            next_id: Arc::new(std::sync::atomic::AtomicU64::new(0)),
            data: Arc::new(std::sync::Mutex::new(
                CheckedCallEventRegistryData::default(),
            )),
        }
    }

    fn same_registry(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.identity, &other.identity)
    }

    fn new_event(&self, canonical_view: crate::kernel::SharedCMemory) -> CheckedCallEvent {
        let id = self
            .next_id
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let mut data = self.data.lock().expect("checked call registry poisoned");
        data.canonical_views.insert(id, canonical_view.clone());
        data.events_by_view
            .entry(canonical_view)
            .or_default()
            .push(id);
        CheckedCallEvent {
            registry: self.clone(),
            id,
        }
    }

    fn register_view(&self, id: u64, view: crate::kernel::SharedCMemory) {
        let mut data = self.data.lock().expect("checked call registry poisoned");
        assert!(
            data.canonical_views.contains_key(&id),
            "checked call event belongs to its registry"
        );
        let events = data.events_by_view.entry(view).or_default();
        if !events.contains(&id) {
            events.push(id);
        }
    }

    fn contains_view(&self, id: u64, view: &crate::kernel::SharedCMemory) -> bool {
        self.data
            .lock()
            .expect("checked call registry poisoned")
            .events_by_view
            .get(view)
            .is_some_and(|events| events.contains(&id))
    }

    fn event_ids_for_view(&self, view: &crate::kernel::SharedCMemory) -> Vec<u64> {
        self.data
            .lock()
            .expect("checked call registry poisoned")
            .events_by_view
            .get(view)
            .cloned()
            .unwrap_or_default()
    }

    fn canonical_view(&self, id: u64) -> crate::kernel::SharedCMemory {
        self.data
            .lock()
            .expect("checked call registry poisoned")
            .canonical_views
            .get(&id)
            .expect("checked call event belongs to its registry")
            .clone()
    }
}

/// Opaque identity for one call occurrence. Membership in a proof path is
/// carried separately by [`CheckedCallEvents`].
#[derive(Clone)]
pub(crate) struct CheckedCallEvent {
    registry: CheckedCallEventRegistry,
    id: u64,
}

impl CheckedCallEvent {
    #[cfg(test)]
    pub(crate) fn new(canonical_view: crate::kernel::SharedCMemory) -> Self {
        CheckedCallEventRegistry::new().new_event(canonical_view)
    }

    fn canonical_view(&self) -> crate::kernel::SharedCMemory {
        self.registry.canonical_view(self.id)
    }

    pub(crate) fn same_authority(&self, other: &Self) -> bool {
        self.id == other.id && self.registry.same_registry(&other.registry)
    }
}

impl std::fmt::Debug for CheckedCallEvent {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("CheckedCallEvent")
            .field("canonical_view", &self.canonical_view().arena_id())
            .finish_non_exhaustive()
    }
}

impl PartialEq for CheckedCallEvent {
    fn eq(&self, other: &Self) -> bool {
        self.same_authority(other)
    }
}

impl Eq for CheckedCallEvent {}

#[derive(Clone)]
struct CheckedCallEventGroup {
    registry: CheckedCallEventRegistry,
    active: PersistentSet<u64>,
}

/// Indexed checked-call authority available on one proof path.
///
/// Registry storage is shared across forks, while `active` is persistent and
/// path-local. Exact-view lookup is therefore proportional to the events
/// registered for that view, not to the proof's complete call history.
#[derive(Clone, Default)]
pub(crate) struct CheckedCallEvents {
    groups: Vec<CheckedCallEventGroup>,
}

impl CheckedCallEvents {
    fn new() -> Self {
        Self {
            groups: vec![CheckedCallEventGroup {
                registry: CheckedCallEventRegistry::new(),
                active: PersistentSet::default(),
            }],
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.groups.iter().all(|group| group.active.is_empty())
    }

    fn new_event(&mut self, canonical_view: crate::kernel::SharedCMemory) -> CheckedCallEvent {
        if self.groups.is_empty() {
            self.groups.push(CheckedCallEventGroup {
                registry: CheckedCallEventRegistry::new(),
                active: PersistentSet::default(),
            });
        }
        debug_assert_eq!(self.groups.len(), 1);
        let group = &mut self.groups[0];
        let event = group.registry.new_event(canonical_view);
        group.active = group.active.with_value(event.id);
        event
    }

    fn insert(&mut self, event: &CheckedCallEvent) {
        if let Some(group) = self
            .groups
            .iter_mut()
            .find(|group| group.registry.same_registry(&event.registry))
        {
            group.active = group.active.with_value(event.id);
            return;
        }
        self.groups.push(CheckedCallEventGroup {
            registry: event.registry.clone(),
            active: PersistentSet::default().with_value(event.id),
        });
    }

    #[cfg(test)]
    pub(crate) fn containing_for_test(event: &CheckedCallEvent) -> Self {
        let mut events = Self::default();
        events.insert(event);
        events
    }

    pub(crate) fn extend(&mut self, other: &Self) {
        for group in &other.groups {
            for id in group.active.iter() {
                self.insert(&CheckedCallEvent {
                    registry: group.registry.clone(),
                    id: *id,
                });
            }
        }
    }

    pub(crate) fn contains(&self, event: &CheckedCallEvent) -> bool {
        self.groups.iter().any(|group| {
            group.registry.same_registry(&event.registry) && group.active.contains(&event.id)
        })
    }

    pub(crate) fn contains_view(
        &self,
        event: &CheckedCallEvent,
        view: &crate::kernel::SharedCMemory,
    ) -> bool {
        self.contains(event) && event.registry.contains_view(event.id, view)
    }

    pub(crate) fn register_view(
        &self,
        event: &CheckedCallEvent,
        view: crate::kernel::SharedCMemory,
    ) {
        if self.contains(event) {
            event.registry.register_view(event.id, view);
        }
    }

    pub(crate) fn events_for_view(
        &self,
        view: &crate::kernel::SharedCMemory,
    ) -> Vec<CheckedCallEvent> {
        let mut events = Vec::new();
        for group in &self.groups {
            let indexed = group.registry.event_ids_for_view(view);
            #[cfg(test)]
            CHECKED_CALL_EVENT_LOOKUP_CANDIDATES.with(|count| {
                count.set(count.get().saturating_add(indexed.len()));
            });
            events.extend(
                indexed
                    .into_iter()
                    .filter(|id| group.active.contains(id))
                    .map(|id| CheckedCallEvent {
                        registry: group.registry.clone(),
                        id,
                    }),
            );
        }
        events
    }

    #[cfg(test)]
    fn reset_lookup_candidates_for_test() {
        CHECKED_CALL_EVENT_LOOKUP_CANDIDATES.with(|count| count.set(0));
    }

    #[cfg(test)]
    fn lookup_candidates_for_test() -> usize {
        CHECKED_CALL_EVENT_LOOKUP_CANDIDATES.with(std::cell::Cell::get)
    }
}

impl std::fmt::Debug for CheckedCallEvents {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("CheckedCallEvents")
            .field(
                "active_count",
                &self
                    .groups
                    .iter()
                    .map(|group| group.active.len())
                    .sum::<usize>(),
            )
            .finish_non_exhaustive()
    }
}

// This is retained checking authority, not part of an execution's semantic
// result. Public execution equality deliberately ignores it.
impl PartialEq for CheckedCallEvents {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl Eq for CheckedCallEvents {}

/// Kernel-checked evidence for a fold, unfold, or scoped open/close that
/// changes only the definitional representation of one composite resource.
#[derive(Clone)]
pub(crate) struct CheckedResourceRewrite {
    before_state: CState,
    pub(crate) after_state: CState,
    pub(crate) before_facts: ProofFacts,
    pub(crate) after_facts: ProofFacts,
    definition: CCompositeResourceDefinition,
    consumption_contract: Option<Arc<CheckedFunctionEntry>>,
    instance: Option<crate::kernel::ResourceInstance>,
    selected_children: Option<Arc<[(String, Variable)]>>,
    load_equalities: Vec<crate::kernel::CheckedLoadEquality>,
    delta_proofs: Arc<Vec<CheckedResourceDeltaProof>>,
}

/// A checked establish or retirement of source population authority. This is
/// a state transition, so it has its own event and rechecks the exact exchange
/// rather than using definitional composite-resource rewriting.
#[derive(Clone)]
pub(crate) struct CheckedPopulationAuthorityRewrite {
    before_state: CState,
    after_state: CState,
    before_facts: ProofFacts,
    after_facts: ProofFacts,
    selected: CResourceFact,
    establish: bool,
    witness: CheckedPopulationAuthorityExchange,
}

/// A birth or consumption of one field-free member, checked together with
/// the exact population ledger and the ordinary owned resource exchange.
#[derive(Clone)]
pub(crate) struct CheckedPopulationMemberRewrite {
    before_state: CState,
    after_state: CState,
    before_facts: ProofFacts,
    after_facts: ProofFacts,
    selected: CResourceFact,
    produce: bool,
    witness: CheckedPopulationMemberExchange,
    definition: CCompositeResourceDefinition,
}

fn checks_population_authority_exchange(
    before: &CState,
    after: &CState,
    selected: &CResourceFact,
    establish: bool,
    witness: &CheckedPopulationAuthorityExchange,
    assumptions: &PureFactContext,
) -> Result<(), String> {
    let CResourceFact::Own(CResource::PopulationAuthority(description), quantity) = selected else {
        return Err("population authority rewrite requires an owned authority".into());
    };
    if quantity.as_const() != Some(1) {
        return Err("population authority rewrite requires unit ownership".into());
    }
    let [crate::kernel::AlgebraicValue::C(CValue::Pointer(pointer))] = description.arguments()
    else {
        return Err("population authority rewrite requires one pointer anchor".into());
    };
    let anchor = pointer.pointer();
    let imported_retirement = !establish
        && anchor.block == crate::kernel::PointerBlock::ExternalArgument
        && before
            .population_effects
            .creation
            .as_ref()
            .is_some_and(|events| events.recognizes_imported_population(description));
    if imported_retirement {
        before.population_effects.creation.as_ref().expect("imported population")
            .check_imported_retirement(description, assumptions)
            .map_err(|_| format!("Requires count({}(...)) == 0 and no outstanding member custody before authority retirement", description.family()))?;
    }
    if !imported_retirement
        && (anchor.offset != crate::kernel::PointerOffsetTerm::Constant(0)
            || !(matches!(&anchor.block, crate::kernel::PointerBlock::Heap(_))
                && before.memory.live_heap_block_size(anchor).is_some()
                || anchor.block.starts_with("local:") && before.memory.has_block(&anchor.block)))
    {
        return Err("population authority rewrite requires live base storage".into());
    }
    let (Some(before_events), Some(after_events)) = (
        before.population_effects.creation.as_ref(),
        after.population_effects.creation.as_ref(),
    ) else {
        return Err("population authority rewrite requires creation history".into());
    };
    if !witness.matches(before_events, after_events, description, establish) {
        return Err("population authority rewrite has mismatched creation evidence".into());
    }
    let expected_resources = if establish {
        before
            .resources
            .clone()
            .try_compose_with_fact(selected.clone(), assumptions)
            .map_err(|_| "population authority establishment has invalid ownership")?
    } else {
        before
            .resources
            .clone()
            .without_fact_incrementally(selected, assumptions)
            .ok_or("population authority retirement lacks exact ownership")?
    };
    if !after
        .resources
        .same_exchange_from(&expected_resources, &before.resources)
        || !Arc::ptr_eq(
            &after.resources.loan_dependencies,
            &expected_resources.loan_dependencies,
        )
    {
        return Err("population authority rewrite has the wrong resource exchange".into());
    }
    let same_bindings = match (&before.resource_bindings, &after.resource_bindings) {
        (None, None) => true,
        (Some(left), Some(right)) => Arc::ptr_eq(left, right),
        _ => false,
    };
    if !Arc::ptr_eq(
        &before.instance_field_scope.storage,
        &after.instance_field_scope.storage,
    ) || !Arc::ptr_eq(
        &before.instance_field_scope.loan_dependencies,
        &after.instance_field_scope.loan_dependencies,
    ) || !same_bindings
        || !Arc::ptr_eq(&before.locals.bindings, &after.locals.bindings)
        || !Arc::ptr_eq(&before.locals.slots, &after.locals.slots)
        || before.memory.diagnostic_identity() != after.memory.diagnostic_identity()
        || before.loan_ledger != after.loan_ledger
        || before.loan_participant != after.loan_participant
        || before.loan_view_bindings != after.loan_view_bindings
        || before.thread_ledger != after.thread_ledger
        || before.mutex_ledger != after.mutex_ledger
        || before.preserves_mutex_protocols != after.preserves_mutex_protocols
        || before.mutex_input_reservations != after.mutex_input_reservations
        || before.opaque_mutex_acquisitions != after.opaque_mutex_acquisitions
        || before.named_mutex_authorities != after.named_mutex_authorities
        || before.pending_thread_create != after.pending_thread_create
        || before.population_access != after.population_access
        || !before
            .observed_population_families
            .shares_storage_with(&after.observed_population_families)
        || before.aggregate_destination != after.aggregate_destination
        || before.next_local_frame != after.next_local_frame
        || before.next_local_lifetime != after.next_local_lifetime
        || before.enclosing_frame_holds_locals != after.enclosing_frame_holds_locals
    {
        return Err("population authority rewrite changed unrelated execution state".into());
    }
    Ok(())
}

impl CheckedPopulationAuthorityRewrite {
    pub(crate) fn before_state(&self) -> &CState {
        &self.before_state
    }

    fn check(
        before_state: &CState,
        before_facts: &ProofFacts,
        selected: &CResourceFact,
        establish: bool,
        witness: &CheckedPopulationAuthorityExchange,
        after_state: &CState,
        after_facts: &ProofFacts,
    ) -> Result<Self, String> {
        checks_population_authority_exchange(
            before_state,
            after_state,
            selected,
            establish,
            witness,
            before_facts.assumptions(),
        )?;
        if !after_facts
            .introduced_since(before_facts)
            .is_some_and(|introduced| introduced.is_empty())
        {
            return Err("population authority rewrite introduced unchecked pure facts".into());
        }
        Ok(Self {
            before_state: before_state.clone(),
            after_state: after_state.clone(),
            before_facts: before_facts.clone(),
            after_facts: after_facts.clone(),
            selected: selected.clone(),
            establish,
            witness: witness.clone(),
        })
    }

    fn advance_checked(&self, state: &CState, facts: &ProofFacts) -> Option<ProofFacts> {
        if state.memory.diagnostic_identity() != self.before_state.memory.diagnostic_identity()
            || !state.shares_non_memory_storage_with(&self.before_state)
            || facts.introduced_since(&self.before_facts).is_none()
            || !self
                .after_facts
                .introduced_since(&self.before_facts)
                .is_some_and(|introduced| introduced.is_empty())
            || checks_population_authority_exchange(
                state,
                &self.after_state,
                &self.selected,
                self.establish,
                &self.witness,
                self.before_facts.assumptions(),
            )
            .is_err()
        {
            return None;
        }
        Some(facts.clone())
    }
}

fn checks_population_member_exchange(
    definition: &CCompositeResourceDefinition,
    before: &CState,
    after: &CState,
    selected: &CResourceFact,
    produce: bool,
    witness: &CheckedPopulationMemberExchange,
    assumptions: &PureFactContext,
) -> Result<(), String> {
    let CResourceFact::Own(CResource::Composite { name, arguments }, quantity) = selected else {
        return Err("population member rewrite requires an owned declared resource".into());
    };
    let batch = quantity.as_const() != Some(1);
    if definition.name != *name
        || !definition.resource_parameters.is_empty()
        || definition.matched.is_some()
        || !definition.witnesses.is_empty()
        || definition.condition.is_some()
        || definition.facts_claim_liveness
        || definition.contains.iter().any(|spec| {
            !matches!(
                spec.term(),
                crate::kernel::CResourceTerm::Memory(_)
                    | crate::kernel::CResourceTerm::Token { .. }
                    | crate::kernel::CResourceTerm::Composite { .. }
            ) || spec.access() != crate::kernel::CResourceAccessMode::Own
                || spec.quantity() != &crate::kernel::CResourceQuantity::One
                || spec.guard().is_some()
                || !spec.resource_arguments().is_empty()
        })
        || !definition.children.is_empty()
        || definition
            .instance_schema
            .as_ref()
            .is_some_and(|schema| !schema.fields().is_empty())
    {
        return Err("population member rewrite requires a private body of owned memory or declared resources".into());
    }
    if batch && (!definition.contains().is_empty() || !definition.facts().is_empty()) {
        return Err("quantified population members need an empty body".into());
    }
    let description = crate::kernel::ResourceDescription::new(
        name.clone(),
        arguments.clone(),
        crate::kernel::ResourceFieldSchema::new(vec![]).expect("empty resource schema"),
    );
    let Some(crate::kernel::AlgebraicValue::C(CValue::Pointer(pointer))) =
        description.arguments().first()
    else {
        return Err("population member rewrite requires one pointer anchor".into());
    };
    let anchor = pointer.pointer();
    let imported_member_exchange =
        before
            .population_effects
            .creation
            .as_ref()
            .is_some_and(|events| {
                if produce {
                    events.recognizes_imported_population(&description)
                } else {
                    events.owns_imported_population_member(&description)
                }
            });
    if !imported_member_exchange
        && (anchor.offset != crate::kernel::PointerOffsetTerm::Constant(0)
            || !(matches!(&anchor.block, crate::kernel::PointerBlock::Heap(_))
                && before.memory.live_heap_block_size(anchor).is_some()
                || anchor.block.starts_with("local:") && before.memory.has_block(&anchor.block)))
    {
        return Err("population member rewrite requires live base storage".into());
    }
    let governing = before
        .population_effects
        .creation
        .as_ref()
        .and_then(|events| events.governing_authority(&description))
        .ok_or_else(|| {
            format!(
                "Requires owns authority({name}(anchor, {}))",
                std::iter::repeat_n("_", arguments.len().saturating_sub(1))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        })?;
    let authority = CResourceFact::own(CResource::PopulationAuthority(governing));
    if !before.resources.satisfies_fact(&authority, assumptions) {
        return Err("Requires owns authority(R(p))".into());
    }
    let (Some(before_events), Some(after_events)) = (
        before.population_effects.creation.as_ref(),
        after.population_effects.creation.as_ref(),
    ) else {
        return Err("population member rewrite requires creation history".into());
    };
    if !witness.matches(before_events, after_events, &description, produce) {
        return Err("population member rewrite has mismatched conservation evidence".into());
    }
    let (expected, _) =
        before.checked_population_member_exchange(selected, produce, definition, assumptions)?;
    let expected_resources = expected.resources;
    if !after
        .resources
        .same_exchange_from(&expected_resources, &before.resources)
        || !Arc::ptr_eq(
            &after.resources.loan_dependencies,
            &expected_resources.loan_dependencies,
        )
    {
        return Err("population member rewrite has the wrong resource exchange".into());
    }
    let same_bindings = match (&before.resource_bindings, &after.resource_bindings) {
        (None, None) => true,
        (Some(left), Some(right)) => Arc::ptr_eq(left, right),
        _ => false,
    };
    if !Arc::ptr_eq(
        &before.instance_field_scope.storage,
        &after.instance_field_scope.storage,
    ) || !Arc::ptr_eq(
        &before.instance_field_scope.loan_dependencies,
        &after.instance_field_scope.loan_dependencies,
    ) || !same_bindings
        || !Arc::ptr_eq(&before.locals.bindings, &after.locals.bindings)
        || !Arc::ptr_eq(&before.locals.slots, &after.locals.slots)
        || before.memory.diagnostic_identity() != after.memory.diagnostic_identity()
        || before.loan_ledger != after.loan_ledger
        || before.loan_participant != after.loan_participant
        || before.loan_view_bindings != after.loan_view_bindings
        || before.thread_ledger != after.thread_ledger
        || before.mutex_ledger != after.mutex_ledger
        || before.preserves_mutex_protocols != after.preserves_mutex_protocols
        || before.mutex_input_reservations != after.mutex_input_reservations
        || before.opaque_mutex_acquisitions != after.opaque_mutex_acquisitions
        || before.named_mutex_authorities != after.named_mutex_authorities
        || before.pending_thread_create != after.pending_thread_create
        || before.population_access != after.population_access
        || !before
            .observed_population_families
            .shares_storage_with(&after.observed_population_families)
        || before.aggregate_destination != after.aggregate_destination
        || before.next_local_frame != after.next_local_frame
        || before.next_local_lifetime != after.next_local_lifetime
        || before.enclosing_frame_holds_locals != after.enclosing_frame_holds_locals
    {
        return Err("population member rewrite changed unrelated execution state".into());
    }
    Ok(())
}

impl CheckedPopulationMemberRewrite {
    pub(crate) fn before_state(&self) -> &CState {
        &self.before_state
    }

    fn check(
        function: &CFunction,
        before_state: &CState,
        before_facts: &ProofFacts,
        selected: &CResourceFact,
        produce: bool,
        witness: &CheckedPopulationMemberExchange,
        after_state: &CState,
        after_facts: &ProofFacts,
    ) -> Result<Self, String> {
        let CResource::Composite { name, .. } = selected.resource() else {
            return Err("population member rewrite requires a declared resource".into());
        };
        let definition = function
            .composite_resource_definition(name)
            .ok_or("population member rewrite requires a declared resource definition")?;
        checks_population_member_exchange(
            definition,
            before_state,
            after_state,
            selected,
            produce,
            witness,
            before_facts.assumptions(),
        )?;
        let rewrite = Self {
            before_state: before_state.clone(),
            after_state: after_state.clone(),
            before_facts: before_facts.clone(),
            after_facts: after_facts.clone(),
            selected: selected.clone(),
            produce,
            witness: witness.clone(),
            definition: definition.clone(),
        };
        rewrite
            .checked_introductions()
            .ok_or("population member rewrite introduced unchecked pure facts")?;
        Ok(rewrite)
    }

    fn checked_introductions(&self) -> Option<Vec<Proposition>> {
        let introduced = self.after_facts.introduced_since(&self.before_facts)?;
        if introduced.is_empty() {
            return Some(introduced);
        }
        if self.produce || self.definition.facts().is_empty() {
            return None;
        }
        let allowed = crate::kernel::functions::instantiate_private_member_body_facts(
            &self.selected,
            &self.definition,
            &self.before_state,
            self.before_facts.assumptions(),
        )?
        .propositions
        .into_iter()
        .collect::<std::collections::BTreeSet<_>>();
        introduced
            .iter()
            .all(|fact| allowed.contains(fact))
            .then_some(introduced)
    }

    fn advance_checked(&self, state: &CState, facts: &ProofFacts) -> Option<ProofFacts> {
        if state.memory.diagnostic_identity() != self.before_state.memory.diagnostic_identity()
            || !state.shares_non_memory_storage_with(&self.before_state)
            || facts.introduced_since(&self.before_facts).is_none()
            || checks_population_member_exchange(
                &self.definition,
                state,
                &self.after_state,
                &self.selected,
                self.produce,
                &self.witness,
                self.before_facts.assumptions(),
            )
            .is_err()
        {
            return None;
        }
        let mut advanced = facts.clone();
        for fact in self.checked_introductions()? {
            advanced = advanced.with_kernel_checked_fact(fact);
        }
        Some(advanced)
    }
}

/// Whether `after` differs from `before` only by cells that name their own
/// load: each added cell holds the canonical form of the load of that very
/// pointer at `before`. Adding one is definitional — it records what the
/// snapshot already said about the cell — so a rewrite that names the cells it
/// exposes stays checkable without a second state comparison rule. Bounded by
/// the cell count, with no assumption consulted and nothing searched.
///
/// Returns a description of the first deviation when the rule does not hold,
/// naming the offending cell, so the caller can report which cell or field a
/// rejected rewrite changed.
fn memory_only_adds_named_cells(
    before: &crate::kernel::CMemory,
    after: &crate::kernel::CMemory,
) -> Result<(), String> {
    let mut rebased = after.clone();
    rebased.cells = before.cells.clone();
    if rebased != *before {
        let changed = if rebased.blocks != before.blocks {
            "blocks"
        } else if rebased.union_cells != before.union_cells {
            "union cells"
        } else if rebased.forgotten != before.forgotten {
            "forgotten-cell provenance"
        } else if rebased.heap.initialized != before.heap.initialized {
            "initialized bytes"
        } else {
            "heap allocation state"
        };
        return Err(format!("changed non-cell memory state ({changed})"));
    }
    let base = crate::kernel::intern_c_memory(before.clone());
    for change in before.cells.diff(&after.cells) {
        let crate::kernel::SnapshotMapChange::Added(pointer) = change else {
            return Err("removed or rewrote an existing cell".into());
        };
        let value = after.cells.get(pointer).expect("added cell exists");
        let Some(kind) = LoadKind::of_value(&value) else {
            return Err("added a cell no load reads".into());
        };
        let load = crate::kernel::canonical_form_of_load(base.clone(), pointer.clone(), kind);
        if !cell_value_is_exactly_load(&value, &load, pointer) {
            return Err(describe_unnamed_cell_addition(
                &base, pointer, &value, &load,
            ));
        }
    }
    Ok(())
}

/// Explains a rejected unnamed-cell addition with bounded, actionable detail.
///
/// Names the held value and the recomputed canonical load, the pre-rewrite
/// snapshot and epoch identities (compact arena ids, not
/// memory dumps), and whether the pointer itself embeds an inner load whose own
/// epoch drift would cascade into this outer name. The epoch lookup is the same
/// assumption-free memoized walk the naming itself uses, so this adds no proof
/// search or ambient-fact scan.
fn describe_unnamed_cell_addition(
    base: &crate::kernel::SharedCMemory,
    pointer: &crate::kernel::Pointer,
    value: &CValue,
    load: &Bitvector32Term,
) -> String {
    let held = truncate_debug(value, 240);
    let expected = truncate_debug(load, 240);
    let (base_arena, base_id) = base.arena_id();
    let epoch_note = match crate::kernel::resource_tracker::last_same_point(
        crate::kernel::resource_tracker::Resource::Cell {
            pointer,
            bytes: crate::kernel::resource_tracker::widest_scalar_access_bytes(),
        },
        &crate::kernel::resource_tracker::ProgramPoint::at(base),
    ) {
        Some(epoch) => {
            let (epoch_arena, epoch_id) = epoch.snapshot().arena_id();
            format!("epoch snapshot ({epoch_arena},{epoch_id})")
        }
        None => "epoch snapshot none (unwritten at a derivation root)".to_string(),
    };
    let mut detail = format!(
        "added a cell at {pointer:?} that is not the canonical load of its own pointer at the pre-rewrite snapshot; \
held {held} but canonical is {expected}; \
pre-rewrite snapshot ({base_arena},{base_id}), {epoch_note}"
    );
    let embedded: Vec<String> = pointer
        .offset
        .scaled_values()
        .iter()
        .take(2)
        .map(|term| truncate_debug(term, 120))
        .collect();
    if !embedded.is_empty() {
        detail.push_str(&format!(
            "; pointer embeds {} scaled value(s) such as {} — if that inner load's epoch drifted, this outer name drifts too",
            pointer.offset.scaled_values().len(),
            embedded.join(", "),
        ));
    }
    detail.push_str(
        "; the proposed rewrite stored a different load variable than the consistency check \
recomputed from the rewrite's input state; this is an internal naming divergence",
    );
    detail
}

/// Renders a value for diagnostics without risking a huge repeated
/// internal-state dump: load terms can embed whole memory snapshots, so cap
/// the text at `width` chars.
fn truncate_debug<T: std::fmt::Debug>(value: &T, width: usize) -> String {
    let shown = format!("{value:?}");
    if shown.len() <= width {
        shown
    } else {
        format!(
            "{}…[{} chars total]",
            &shown[..width.min(shown.len())],
            shown.len()
        )
    }
}

/// Names the part of a state that differs when two states agree on memory and
/// resources, for diagnostics.
fn describe_changed_state_field(changed: &CState, original: &CState) -> &'static str {
    if changed.locals != original.locals {
        "local values"
    } else if changed.instance_field_scope != original.instance_field_scope {
        "the open resource field scope"
    } else if changed.observed_population_families != original.observed_population_families {
        "observed population families"
    } else {
        "state outside memory, locals, and resources"
    }
}

/// Whether a materialized cell's value is exactly the given load of its own
/// cell, in one of the representations resource projection writes: the scalar
/// term itself, the `_Bool` normalization of it, or a pointer whose offset is
/// that term scaled by its pointee width in the cell's own block.
fn cell_value_is_exactly_load(
    value: &CValue,
    load: &Bitvector32Term,
    pointer: &crate::kernel::Pointer,
) -> bool {
    match value {
        CValue::Int8(term) => term == load,
        CValue::Int16(term)
        | CValue::Int32(term)
        | CValue::UInt8(term)
        | CValue::UInt16(term)
        | CValue::UInt32(term)
        | CValue::Int64(term)
        | CValue::UInt64(term)
        | CValue::Float32(term)
        | CValue::Float64(term) => term == load,
        CValue::Bool(term) => {
            term == &Bitvector32Term::if_then_else(
                crate::kernel::ConditionTerm::equal(load.clone(), Bitvector32Term::Constant(0)),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )
        }
        CValue::Pointer(value) => {
            let target = value.pointer();
            value.designation().is_none()
                && target.block == pointer.block
                && matches!(
                    &target.offset,
                    crate::kernel::PointerOffsetTerm::Int32Scaled { value, .. }
                        if value.as_ref() == load
                )
        }
        _ => false,
    }
}

/// A unit checkout preserves the mathematical sum only when neither child
/// update wraps. Check the three original domains through named/indexed facts;
/// modular equality of the two sums alone is insufficient.
fn authority_control_evaluation_condition_proven(
    assumptions: &PureFactContext,
    goal: &Proposition,
) -> bool {
    use crate::kernel::ConditionTerm;
    let stated = |goal: &Proposition| {
        let canonical = crate::kernel::canonical_condition_fact(goal);
        if assumptions.contains_assumed_exact(&canonical) {
            return true;
        }
        let Proposition::ConditionIs(condition, truth) = &canonical else {
            return false;
        };
        let operands = |condition: &ConditionTerm| match condition {
            ConditionTerm::Bitvector32SignedAddOverflows(left, right) => {
                Some((true, left.as_ref().clone(), right.as_ref().clone()))
            }
            ConditionTerm::Bitvector32SignedSubtractOverflows(left, right) => {
                Some((false, left.as_ref().clone(), right.as_ref().clone()))
            }
            _ => None,
        };
        let Some((add, left, right)) = operands(condition) else {
            return false;
        };
        let mut variables = std::collections::BTreeSet::new();
        let mut pending = vec![left.clone(), right.clone()];
        while let Some(term) = pending.pop() {
            match term {
                Bitvector32Term::Variable(variable) => {
                    variables.insert(variable);
                }
                Bitvector32Term::Add(left, right)
                | Bitvector32Term::Subtract(left, right)
                | Bitvector32Term::Multiply(left, right) => {
                    pending.push(*left);
                    pending.push(*right);
                }
                _ => {}
            }
        }
        let equivalent = |candidate: &ConditionTerm, candidate_truth| {
            if candidate_truth != *truth {
                return false;
            }
            let Some((candidate_add, candidate_left, candidate_right)) = operands(candidate) else {
                return false;
            };
            candidate_add == add
                && (assumptions.int32_values_known_equal(&left, &candidate_left)
                    && assumptions.int32_values_known_equal(&right, &candidate_right)
                    || add
                        && assumptions.int32_values_known_equal(&left, &candidate_right)
                        && assumptions.int32_values_known_equal(&right, &candidate_left))
        };
        for variable in variables {
            let key = crate::kernel::primitives::AtomicConnectionKey::Variable(variable);
            let (candidates, _) = assumptions.atomic_facts_connected_to(&key, true);
            for candidate in candidates {
                crate::instrumentation::record_deterministic_work(1);
                match candidate {
                    crate::kernel::primitives::AtomicConnectedFact::Condition(condition, truth)
                        if equivalent(condition, truth) =>
                    {
                        return true;
                    }
                    crate::kernel::primitives::AtomicConnectedFact::Condition(_, _) => {}
                    crate::kernel::primitives::AtomicConnectedFact::Proposition(proposition) => {
                        let mut conjuncts = vec![proposition];
                        while let Some(conjunct) = conjuncts.pop() {
                            match conjunct {
                                Proposition::And(left, right) => {
                                    conjuncts.push(left);
                                    conjuncts.push(right);
                                }
                                Proposition::ConditionIs(condition, truth)
                                    if equivalent(condition, *truth) =>
                                {
                                    return true;
                                }
                                _ => {}
                            }
                        }
                    }
                }
            }
        }
        false
    };
    if stated(goal) {
        return true;
    }
    let Proposition::ConditionIs(ConditionTerm::Bitvector32SignedAddOverflows(left, right), false) =
        goal
    else {
        return false;
    };
    let pair = match (left.as_ref(), right.as_ref()) {
        (Bitvector32Term::Add(value, increment), Bitvector32Term::Subtract(other, decrement))
        | (Bitvector32Term::Subtract(other, decrement), Bitvector32Term::Add(value, increment))
            if increment.as_const() == Some(1) && decrement.as_const() == Some(1) =>
        {
            (value.as_ref(), other.as_ref())
        }
        _ => return false,
    };
    let one = Bitvector32Term::Constant(1);
    let guards = [
        ConditionTerm::signed_add_overflows(pair.0.clone(), pair.1.clone()),
        ConditionTerm::signed_add_overflows(pair.0.clone(), one.clone()),
        ConditionTerm::signed_subtract_overflows(pair.1.clone(), one),
    ];
    guards.iter().all(|condition| {
        if stated(&Proposition::ConditionIs(condition.clone(), false)) {
            return true;
        }
        if let ConditionTerm::Bitvector32SignedAddOverflows(left, right) = condition
            && stated(&Proposition::ConditionIs(
                ConditionTerm::signed_add_overflows(right.as_ref().clone(), left.as_ref().clone()),
                false,
            ))
        {
            return true;
        }
        match condition {
            ConditionTerm::Bitvector32SignedAddOverflows(value, one)
                if one.as_const() == Some(1) =>
            {
                assumptions
                    .indexed_constant_interval(value)
                    .is_some_and(|(_, high)| high < i64::from(i32::MAX))
            }
            ConditionTerm::Bitvector32SignedSubtractOverflows(value, one)
                if one.as_const() == Some(1) =>
            {
                assumptions
                    .indexed_constant_interval(value)
                    .is_some_and(|(low, _)| low > i64::from(i32::MIN))
            }
            _ => false,
        }
    })
}

impl CheckedResourceRewrite {
    pub(crate) fn before_state(&self) -> &CState {
        &self.before_state
    }

    #[cfg(test)]
    fn check(
        function: &CFunction,
        before_state: &CState,
        before_facts: &ProofFacts,
        selected: &CResourceFact,
        after_state: &CState,
        after_facts: &ProofFacts,
        call_events: &CheckedCallEvents,
    ) -> Result<Self, String> {
        Self::check_with_children(
            function,
            before_state,
            before_facts,
            selected,
            after_state,
            after_facts,
            call_events,
            None,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn check_authority_wrapper(
        before_state: &CState,
        before_facts: &ProofFacts,
        selected: &CResourceFact,
        after_state: &CState,
        after_facts: &ProofFacts,
        call_events: &CheckedCallEvents,
        definition: &CCompositeResourceDefinition,
        selected_children: Option<Arc<[(String, Variable)]>>,
    ) -> Result<Self, String> {
        let CResourceFact::Own(CResource::Composite { name, arguments }, quantity) = selected
        else {
            return Err("authority control requires one owned composite".into());
        };
        if quantity.as_const() != Some(1) || selected_children.is_some() {
            return Err("authority control requires one whole owned composite".into());
        }
        let assumptions = before_facts.assumptions();
        if !before_state.loan_bindings_are_consistent()
            || !after_state.loan_bindings_are_consistent()
        {
            return Err("authority control changed loan bindings".into());
        }
        let before_folded = before_state
            .resources()
            .satisfies_fact(selected, assumptions);
        let after_folded = after_state
            .resources()
            .satisfies_fact(selected, after_facts.assumptions());
        let was_open = before_state.population_body_is_open(name, arguments);
        let now_open = after_state.population_body_is_open(name, arguments);
        let (exposing, folded) = match (before_folded, after_folded, was_open, now_open) {
            (false, true, false, false) => (false, after_state),
            (true, false, false, false) => (true, before_state),
            (true, true, false, true) => (true, before_state),
            (true, true, true, false) => (false, after_state),
            _ => return Err("authority control requires one fold, unfold, open, or close".into()),
        };
        if (was_open != now_open
            && !before_state.population_access.checks_rewrite(
                &after_state.population_access,
                &(name.clone(), arguments.clone()),
            ))
            || (was_open == now_open
                && before_state.population_access != after_state.population_access)
        {
            return Err("authority control changed another open scope".into());
        }
        let (children, _) =
            folded.checked_authority_wrapper_body(selected, definition, assumptions)?;
        if children.len() != definition.contains().len()
            || children
                .iter()
                .filter(|child| matches!(child.resource(), CResource::PopulationAuthority(_)))
                .count()
                == 0
        {
            return Err("authority control has an unsupported body".into());
        }
        let imported_counts = folded
            .checked_authority_wrapper_import_components(selected, definition, assumptions)
            .ok()
            .and_then(|components| {
                components
                    .iter()
                    .map(|(description, _)| {
                        folded
                            .population_effects
                            .creation
                            .as_ref()
                            .and_then(|ledger| ledger.observe_symbolic(description))
                    })
                    .collect::<Option<Vec<_>>>()
            });
        let imported_control_cell = imported_counts.is_some();
        for child in &children {
            let Some(range) = child.memory_own_range() else {
                continue;
            };
            let (Some(start), Some(end)) = (range.constant_start(), range.constant_end()) else {
                return Err("authority control memory needs concrete bounds".into());
            };
            let bytes = (end as i32)
                .checked_sub(start as i32)
                .filter(|length| *length > 0)
                .and_then(|length| length.checked_mul(range.element_width() as i32))
                .and_then(|bytes| u32::try_from(bytes).ok())
                .ok_or("authority control memory needs a positive bounded range")?;
            let base = range.start_pointer();
            if !folded.memory().access_in_bounds(&base, bytes) && !imported_control_cell {
                return Err("authority control body exceeds live storage".into());
            }
            if let Some(ledger) = folded.loan_ledger() {
                ledger
                    .permits_memory_access_with_assumptions(range, assumptions)
                    .map_err(|_| "authority control body has an active borrow")?;
            }
        }
        let expected_resources = if exposing {
            let base = if after_folded {
                before_state.resources().clone()
            } else {
                before_state
                    .resources()
                    .clone()
                    .without_fact_incrementally(selected, assumptions)
                    .ok_or("authority control cannot consume its folded resource")?
            };
            base.try_compose_with_facts_delaying_normalization(
                children.iter().cloned(),
                assumptions,
            )
            .map_err(|_| "authority control body overlaps existing ownership")?
        } else {
            let mut base = before_state.resources().clone();
            for child in &children {
                base = base
                    .without_fact_incrementally(child, assumptions)
                    .ok_or("Requires the authority control body")?;
            }
            if before_folded {
                base
            } else {
                base.try_compose_with_facts_delaying_normalization(
                    std::iter::once(selected.clone()),
                    assumptions,
                )
                .map_err(|_| "authority control duplicates its folded resource")?
            }
        };
        if !after_state
            .resources()
            .same_exchange_from(&expected_resources, before_state.resources())
            || !Arc::ptr_eq(
                &after_state.resources.loan_dependencies,
                &expected_resources.loan_dependencies,
            )
        {
            return Err("authority control has the wrong resource exchange".into());
        }
        if exposing {
            let native_baseline = crate::kernel::functions::assume_checked_native_composite_places(
                before_state,
                selected,
                std::slice::from_ref(definition),
                assumptions,
            )?;
            memory_only_adds_named_cells(native_baseline.memory(), after_state.memory())?;
        } else if !crate::kernel::api::contract_certification::c_memories_definitionally_equal(
            before_state.memory(),
            after_state.memory(),
            assumptions,
        ) {
            return Err("authority control close changed C memory".into());
        }
        let expected_creation = if exposing {
            before_state.population_effects.creation.clone()
        } else {
            before_state
                .clone()
                .with_resource_context(after_state.resources().clone())
                .with_checked_current_control_wrapper(selected, definition, assumptions)?
                .population_effects
                .creation
                .clone()
        };
        if after_state.population_effects.creation != expected_creation {
            return Err("authority control changed its population registration".into());
        }
        let mut unchanged = after_state.clone();
        Arc::make_mut(&mut unchanged.population_effects).creation =
            before_state.population_effects.creation.clone();
        unchanged.memory = before_state.memory.clone();
        unchanged.resources = before_state.resources.clone();
        unchanged.population_access = before_state.population_access.clone();
        if unchanged != *before_state {
            return Err(format!(
                "authority control changed {} outside its body",
                describe_changed_state_field(&unchanged, before_state),
            ));
        }
        let (projected, _) =
            folded.checked_authority_wrapper_projection(selected, definition, assumptions)?;
        let mut evaluation = folded.clone().with_resource_context(projected);
        for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
            let value = argument
                .as_c_value()
                .ok_or("authority control requires C arguments")?;
            if value.c_type() != parameter.c_type() {
                return Err("authority control argument type mismatch".into());
            }
            evaluation.locals.set_typed(
                parameter.name().to_string(),
                value.clone(),
                parameter.c_type(),
            );
        }
        let child_context = ResourceContext::new_with_equalities(assumptions)
            .unchecked_with_facts(children.clone());
        let mut allowed = child_context.observable_facts_assuming_valid(assumptions);
        for child in &children {
            if let Some(owned) = child.owned_resource() {
                allowed.push(Proposition::CResourceContains {
                    parent: Box::new(selected.resource().clone()),
                    child: Box::new(owned.clone()),
                });
            }
        }
        allowed.push(Proposition::CResourceComposition(
            ResourceContext::new_with_equalities(assumptions).unchecked_with_facts(children),
        ));
        let mut evaluation_assumptions = assumptions.clone();
        for imported in imported_counts.into_iter().flatten() {
            let bound = Proposition::ConditionIs(
                crate::kernel::ConditionTerm::signed_greater_equal(
                    imported.entry_count,
                    imported
                        .entry_symbolic_members
                        .clone()
                        .unwrap_or(Bitvector32Term::Constant(imported.entry_owned_members)),
                ),
                true,
            );
            allowed.push(bound.clone());
            evaluation_assumptions = evaluation_assumptions.assume_proposition(bound);
        }
        if let Some(loadable) =
            crate::kernel::functions::evaluate_composite_resource_loadable_propositions(
                selected,
                std::slice::from_ref(definition),
                after_state.memory(),
                assumptions,
            )
        {
            allowed.extend(loadable);
        }
        let mut budget = ExecutionBudget::beside_live_state();
        for (index, source) in definition.facts().iter().enumerate() {
            let paths =
                crate::kernel::spec::lower_spec_proposition_at_state_with_algebraic_bindings(
                    &evaluation,
                    source,
                    None,
                    assumptions,
                    &BTreeMap::new(),
                    &mut budget,
                )
                .map_err(|_| "authority control could not lower its invariant")?;
            let path =
                crate::kernel::api::exactly_selected_spec_proposition_path(&paths, assumptions)
                    .ok_or("authority control invariant needs one checked path")?;
            if !path.facts.iter().all(|fact| {
                authority_control_evaluation_condition_proven(
                    &evaluation_assumptions,
                    fact.proposition(),
                )
            }) || !path.obligations.iter().all(|obligation| {
                authority_control_evaluation_condition_proven(
                    &evaluation_assumptions,
                    obligation.proposition(),
                )
            }) {
                return Err(
                    "authority control invariant has an unproved evaluation condition".into(),
                );
            }
            if !exposing
                && !crate::kernel::PureFactContext::settles_exactly(assumptions, &path.proposition)
            {
                return Err(format!(
                    "Requires {}",
                    definition
                        .fact_source_spelling(index)
                        .unwrap_or("the control resource fact"),
                ));
            }
            allowed.push(path.proposition.clone());
        }
        let introduced = after_facts
            .introduced_since(before_facts)
            .ok_or("authority control facts do not descend from their input")?;
        let allowed_assumptions = allowed.iter().fold(assumptions.clone(), |facts, fact| {
            facts.assume_proposition(fact.clone())
        });
        if let Some(unchecked) = introduced.iter().find(|fact| {
            !allowed.contains(fact)
                && !allowed_assumptions.proves_exact(fact)
                && !resource_composition_is_supported_by(
                    fact,
                    &ResourceContext::new_with_equalities(assumptions)
                        .unchecked_with_facts(expected_resources.facts().iter().cloned()),
                    assumptions,
                )
        }) {
            return Err(format!(
                "authority control introduced an unchecked pure fact: {}",
                truncate_debug(unchecked, 240)
            ));
        }
        Ok(Self {
            before_state: before_state.clone(),
            after_state: after_state.clone(),
            before_facts: before_facts.clone(),
            after_facts: after_facts.clone(),
            definition: definition.clone(),
            consumption_contract: None,
            instance: None,
            selected_children: None,
            load_equalities: crate::kernel::CheckedLoadEqualityCapture::start_with_call_events(
                call_events,
            )
            .finish(),
            delta_proofs: Arc::new(Vec::new()),
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn check_transfer_wrapper(
        before_state: &CState,
        before_facts: &ProofFacts,
        selected: &CResourceFact,
        after_state: &CState,
        after_facts: &ProofFacts,
        call_events: &CheckedCallEvents,
        definition: &CCompositeResourceDefinition,
        selected_children: Option<Arc<[(String, Variable)]>>,
    ) -> Result<Self, String> {
        let CResourceFact::Own(CResource::Composite { name, arguments }, quantity) = selected
        else {
            return Err("transfer wrapper requires one owned resource".into());
        };
        if quantity.as_const() != Some(1)
            || !definition.resource_parameters.is_empty()
            || definition.matched.is_some()
            || !definition.witnesses.is_empty()
            || definition.condition.is_some()
            || !definition.children.is_empty()
            || !definition.facts.is_empty()
            || definition
                .instance_schema
                .as_ref()
                .is_some_and(|schema| !schema.fields().is_empty())
            || definition.contains().iter().any(|spec| {
                spec.access() != crate::kernel::CResourceAccessMode::Own
                    || spec.quantity() != &crate::kernel::CResourceQuantity::One
                    || spec.guard().is_some()
                    || !spec.resource_arguments().is_empty()
            })
            || selected_children
                .as_ref()
                .is_some_and(|children| !children.is_empty())
        {
            return Err("authority transfer wrapper has an unsupported body".into());
        }
        let description = crate::kernel::ResourceDescription::new(
            name.clone(),
            arguments.clone(),
            crate::kernel::ResourceFieldSchema::new(vec![]).expect("empty schema"),
        );
        if before_state
            .population_effects
            .creation
            .as_ref()
            .is_some_and(|ledger| {
                ledger.tracks_population(&description)
                    || ledger.recognizes_imported_population(&description)
            })
        {
            return Err("an authority member cannot use an ordinary wrapper rewrite".into());
        }
        let assumptions = before_facts.assumptions();
        let singleton =
            ResourceContext::new_with_equalities(assumptions).unchecked_with_fact(selected.clone());
        let expanded = crate::kernel::functions::expand_composite_resource_fact(
            &singleton,
            selected,
            std::slice::from_ref(definition),
            before_state.memory(),
            assumptions,
        )
        .ok_or("cannot instantiate authority transfer wrapper")?;
        let exposing = before_state
            .resources()
            .satisfies_fact(selected, assumptions)
            && !after_state
                .resources()
                .satisfies_fact(selected, assumptions);
        let expected = if exposing {
            before_state
                .resources()
                .clone()
                .without_fact_incrementally(selected, assumptions)
                .ok_or("transfer wrapper is missing its folded resource")?
                .try_compose_with_facts_delaying_normalization(
                    expanded.facts().iter().cloned(),
                    assumptions,
                )
                .map_err(|_| "transfer wrapper overlaps existing children")?
        } else {
            let mut resources = before_state.resources().clone();
            for child in expanded.facts() {
                resources = resources
                    .without_fact_incrementally(child, assumptions)
                    .ok_or("transfer wrapper is missing an existing child")?;
            }
            resources
                .try_compose_with_facts_delaying_normalization(
                    std::iter::once(selected.clone()),
                    assumptions,
                )
                .map_err(|_| "transfer wrapper duplicates its folded resource")?
        };
        if !before_state.loan_bindings_are_consistent()
            || !after_state.loan_bindings_are_consistent()
            || !after_state
                .resources()
                .same_exchange_from(&expected, before_state.resources())
            || !Arc::ptr_eq(
                &after_state.resources.loan_dependencies,
                &expected.loan_dependencies,
            )
        {
            return Err("transfer wrapper has the wrong resource exchange".into());
        }
        let same_bindings = match (
            &before_state.resource_bindings,
            &after_state.resource_bindings,
        ) {
            (None, None) => true,
            (Some(left), Some(right)) => Arc::ptr_eq(left, right),
            _ => false,
        };
        if !before_state
            .memory()
            .same_storage_roots(after_state.memory())
            || before_state.population_access != after_state.population_access
            || !same_bindings
            || !Arc::ptr_eq(&before_state.locals.bindings, &after_state.locals.bindings)
            || !Arc::ptr_eq(&before_state.locals.slots, &after_state.locals.slots)
            || !Arc::ptr_eq(
                &before_state.instance_field_scope.storage,
                &after_state.instance_field_scope.storage,
            )
            || !Arc::ptr_eq(
                &before_state.instance_field_scope.loan_dependencies,
                &after_state.instance_field_scope.loan_dependencies,
            )
            || before_state.loan_ledger != after_state.loan_ledger
            || before_state.loan_participant != after_state.loan_participant
            || before_state.loan_view_bindings != after_state.loan_view_bindings
            || before_state.thread_ledger != after_state.thread_ledger
            || before_state.mutex_ledger != after_state.mutex_ledger
            || before_state.preserves_mutex_protocols != after_state.preserves_mutex_protocols
            || before_state.mutex_input_reservations != after_state.mutex_input_reservations
            || before_state.opaque_mutex_acquisitions != after_state.opaque_mutex_acquisitions
            || before_state.named_mutex_authorities != after_state.named_mutex_authorities
            || before_state.pending_thread_create != after_state.pending_thread_create
            || before_state.population_effects.creation != after_state.population_effects.creation
            || !before_state
                .observed_population_families
                .shares_storage_with(&after_state.observed_population_families)
            || before_state.aggregate_destination != after_state.aggregate_destination
            || before_state.next_local_frame != after_state.next_local_frame
            || before_state.next_local_lifetime != after_state.next_local_lifetime
            || before_state.enclosing_frame_holds_locals != after_state.enclosing_frame_holds_locals
        {
            return Err("transfer wrapper changed state outside its resources".into());
        }
        let introduced = after_facts
            .introduced_since(before_facts)
            .ok_or("transfer wrapper facts do not descend from their input")?;
        let child_context = ResourceContext::new_with_equalities(assumptions)
            .unchecked_with_facts(expanded.facts().iter().cloned());
        let mut allowed = child_context.observable_facts_assuming_valid(assumptions);
        for child in expanded.facts() {
            if let Some(owned) = child.owned_resource() {
                allowed.push(Proposition::CResourceContains {
                    parent: Box::new(selected.resource().clone()),
                    child: Box::new(owned.clone()),
                })
            }
        }
        allowed.push(Proposition::CResourceComposition(child_context));
        if introduced.iter().any(|fact| {
            !allowed.contains(fact)
                && !assumptions.proves_exact(fact)
                && !resource_composition_is_supported_by(fact, &expected, assumptions)
        }) {
            return Err("transfer wrapper introduced unchecked facts".into());
        }
        Ok(Self {
            before_state: before_state.clone(),
            after_state: after_state.clone(),
            before_facts: before_facts.clone(),
            after_facts: after_facts.clone(),
            definition: definition.clone(),
            consumption_contract: None,
            instance: None,
            selected_children: None,
            load_equalities: crate::kernel::CheckedLoadEqualityCapture::start_with_call_events(
                call_events,
            )
            .finish(),
            delta_proofs: Arc::new(Vec::new()),
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn check_with_children(
        function: &CFunction,
        before_state: &CState,
        before_facts: &ProofFacts,
        selected: &CResourceFact,
        after_state: &CState,
        after_facts: &ProofFacts,
        call_events: &CheckedCallEvents,
        selected_children: Option<Arc<[(String, Variable)]>>,
    ) -> Result<Self, String> {
        // A family that reaches no population keeps its ordinary definition
        // law; only population-reaching bodies take the checks below.
        let reaches_population = match selected.resource() {
            CResource::Composite { name, .. } => function
                .composite_resource_definition(name)
                .is_none_or(|definition| definition.reaches_population()),
            _ => true,
        };
        if !matches!(selected.resource(), CResource::Instance(_)) {
            if let CResource::Composite { name, .. } = selected.resource()
                && let Some(definition) = function.composite_resource_definition(name)
                && definition.contains().iter().any(|spec| {
                    matches!(
                        spec.term(),
                        crate::kernel::CResourceTerm::PopulationAuthority { .. }
                    )
                })
            {
                return Self::check_authority_wrapper(
                    before_state,
                    before_facts,
                    selected,
                    after_state,
                    after_facts,
                    call_events,
                    definition,
                    selected_children,
                );
            }
            if let CResourceFact::Own(CResource::Composite { name, arguments }, _) = selected
                && let Some(definition) = function.composite_resource_definition(name)
                && !before_state.tracks_authority_member(selected)
                && before_state.population_body_is_open(name, arguments)
                    == after_state.population_body_is_open(name, arguments)
                && !definition.contains().is_empty()
                && definition.contains().iter().all(|spec| {
                    matches!(
                        spec.term(),
                        crate::kernel::CResourceTerm::Composite { .. }
                            | crate::kernel::CResourceTerm::Token { .. }
                    )
                })
            {
                let checked = Self::check_transfer_wrapper(
                    before_state,
                    before_facts,
                    selected,
                    after_state,
                    after_facts,
                    call_events,
                    definition,
                    selected_children.clone(),
                );
                // A wrapper that reaches no population and has a body this
                // delta check does not model keeps its ordinary definition law.
                if checked.is_ok() || reaches_population {
                    return checked;
                }
            }
            // Population accounting covers only `authorized resource`
            // families; any other family keeps its ordinary definition law.
            let ordinary_family = !reaches_population
                || matches!(
                    selected,
                    CResourceFact::Own(CResource::Composite { name, .. }, _)
                        if function
                            .composite_resource_definition(name)
                            .is_some_and(|definition| !definition.is_authorized())
                );
            if !ordinary_family {
                let CResourceFact::Own(CResource::Composite { name, arguments }, quantity) =
                    selected
                else {
                    return Err("member body access requires one owned member".into());
                };
                let definition = function
                    .composite_resource_definition(name)
                    .ok_or("member body access needs its registered definition")?;
                if quantity.as_const() != Some(1)
                    || !definition.resource_parameters.is_empty()
                    || definition.matched.is_some()
                    || !definition.witnesses.is_empty()
                    || definition.condition.is_some()
                    || definition.facts_claim_liveness
                    || !definition.children.is_empty()
                    || definition
                        .instance_schema
                        .as_ref()
                        .is_some_and(|schema| !schema.fields().is_empty())
                    || definition.contains.iter().any(|spec| {
                        !matches!(
                            spec.term(),
                            crate::kernel::CResourceTerm::Memory(_)
                                | crate::kernel::CResourceTerm::Composite { .. }
                        ) || spec.access() != crate::kernel::CResourceAccessMode::Own
                            || spec.quantity() != &crate::kernel::CResourceQuantity::One
                            || spec.guard().is_some()
                            || !spec.resource_arguments().is_empty()
                    })
                    || selected_children.is_some()
                {
                    return Err(
                    "member body access requires a private body of owned memory or declared resources".into(),
                );
                }
                if !before_state.loan_bindings_are_consistent()
                    || !after_state.loan_bindings_are_consistent()
                {
                    return Err("member body access changed loan bindings".into());
                }
                if !before_state
                    .resources()
                    .satisfies_fact(selected, before_facts.assumptions())
                    || !after_state
                        .resources()
                        .satisfies_fact(selected, after_facts.assumptions())
                {
                    return Err("member body access requires the folded member throughout".into());
                }
                let introduced = after_facts
                    .introduced_since(before_facts)
                    .ok_or("member body access facts do not descend from their input")?;
                let assumptions = before_facts.assumptions();
                let was_open = before_state.population_body_is_open(name, arguments);
                let now_open = after_state.population_body_is_open(name, arguments);
                if was_open == now_open {
                    return Err("member body access must open or close one member".into());
                }
                if !before_state.population_access.checks_rewrite(
                    &after_state.population_access,
                    &(name.clone(), arguments.clone()),
                ) {
                    return Err("member body access changed another open scope".into());
                }
                let singleton = ResourceContext::new_with_equalities(assumptions)
                    .unchecked_with_fact(selected.clone());
                let expanded = crate::kernel::functions::expand_composite_resource_fact(
                    &singleton,
                    selected,
                    std::slice::from_ref(definition),
                    before_state.memory(),
                    assumptions,
                )
                .ok_or("member body access cannot instantiate its private body")?;
                let children = expanded.facts();
                // The exact owned member checked above carries its private body,
                // including at an abstract helper entry. Body access does not
                // change membership and requires no population authority import.
                // Concrete bodies still need live bounds; a caller can only fold
                // a member by transferring those owned memory ranges into it.
                for child in children {
                    let Some(range) = child.memory_own_range() else {
                        if let CResourceFact::Own(CResource::Composite { .. }, quantity) = child
                            && quantity.as_const() == Some(1)
                        {
                            // The exact child stays folded until its own checked
                            // open; no body facts or memory are published here.
                            continue;
                        }
                        return Err("member body access contains a nonprivate resource".into());
                    };
                    let (Some(start), Some(end)) = (range.constant_start(), range.constant_end())
                    else {
                        return Err("member private body needs concrete bounds".into());
                    };
                    let bytes = (end as i32)
                        .checked_sub(start as i32)
                        .filter(|length| *length > 0)
                        .and_then(|length| length.checked_mul(range.element_width() as i32))
                        .and_then(|bytes| u32::try_from(bytes).ok())
                        .ok_or("member private body needs a positive bounded range")?;
                    let base = range.start_pointer();
                    if !before_state.memory().access_in_bounds(&base, bytes)
                        && base.block != crate::kernel::PointerBlock::ExternalArgument
                    {
                        return Err("member private body exceeds live storage".into());
                    }
                    if let Some(ledger) = before_state.loan_ledger() {
                        ledger
                            .permits_memory_access_with_assumptions(range, assumptions)
                            .map_err(|_| "member private body has an active borrow")?;
                    }
                }
                let child_context = ResourceContext::new_with_equalities(assumptions)
                    .unchecked_with_facts(children.iter().cloned());
                let mut allowed = child_context.observable_facts_assuming_valid(assumptions);
                allowed.push(Proposition::CResourceComposition(child_context.clone()));
                if let Some(propositions) =
                    crate::kernel::functions::evaluate_composite_resource_relation_propositions(
                        selected,
                        function.composite_resource_definitions(),
                        after_state.memory(),
                        assumptions,
                    )
                {
                    allowed.extend(propositions);
                }
                if let Some(propositions) =
                    crate::kernel::functions::evaluate_composite_resource_loadable_propositions(
                        selected,
                        function.composite_resource_definitions(),
                        after_state.memory(),
                        assumptions,
                    )
                {
                    allowed.extend(propositions);
                }
                if !definition.facts().is_empty() {
                    let body_facts =
                        crate::kernel::functions::instantiate_private_member_body_facts(
                            selected,
                            definition,
                            after_state,
                            assumptions,
                        )
                        .ok_or("Requires ownership of every cell read by member body facts")?;
                    if !now_open
                        && body_facts
                            .declared
                            .iter()
                            .any(|(_, fact)| !assumptions.proves_exact(fact))
                    {
                        return Err("member body close requires its current declared facts".into());
                    }
                    allowed.extend(body_facts.propositions);
                }
                let allowed_assumptions =
                    allowed.iter().fold(assumptions.clone(), |facts, fact| {
                        facts.assume_proposition(fact.clone())
                    });
                if let Some(unchecked) = introduced.iter().find(|fact| {
                    !allowed.contains(fact)
                        && !allowed_assumptions.proves_exact(fact)
                        && !resource_composition_is_supported_by(fact, &child_context, assumptions)
                        && !resource_composition_is_supported_by(
                            fact,
                            after_state.resources(),
                            after_facts.assumptions(),
                        )
                }) {
                    return Err(format!(
                        "member body access introduced an unchecked pure fact: {}",
                        truncate_debug(unchecked, 240)
                    ));
                }
                let expected_resources = if now_open {
                    before_state
                        .resources()
                        .clone()
                        .try_compose_with_facts_delaying_normalization(
                            children.iter().cloned(),
                            assumptions,
                        )
                        .map_err(|_| "member body access duplicates private ownership")?
                } else {
                    let mut resources = before_state.resources().clone();
                    for child in children {
                        resources = resources
                            .without_fact_incrementally(child, assumptions)
                            .ok_or("member body close lacks its private ownership")?;
                    }
                    resources
                };
                if !after_state
                    .resources()
                    .same_exchange_from(&expected_resources, before_state.resources())
                    || !Arc::ptr_eq(
                        &after_state.resources.loan_dependencies,
                        &expected_resources.loan_dependencies,
                    )
                {
                    return Err("member body access has the wrong resource exchange".into());
                }
                if now_open {
                let native_baseline = crate::kernel::functions::assume_checked_native_composite_places(
                    before_state, selected, function.composite_resource_definitions(), assumptions,
                )?;
                memory_only_adds_named_cells(native_baseline.memory(), after_state.memory())?;
            } else if !crate::kernel::api::contract_certification::c_memories_definitionally_equal(
                before_state.memory(),
                after_state.memory(),
                assumptions,
            ) {
                return Err("member body close changed C memory".into());
            }
                let same_bindings = match (
                    &before_state.resource_bindings,
                    &after_state.resource_bindings,
                ) {
                    (None, None) => true,
                    (Some(left), Some(right)) => Arc::ptr_eq(left, right),
                    _ => false,
                };
                if !same_bindings
                    || !Arc::ptr_eq(&before_state.locals.bindings, &after_state.locals.bindings)
                    || !Arc::ptr_eq(&before_state.locals.slots, &after_state.locals.slots)
                    || !Arc::ptr_eq(
                        &before_state.instance_field_scope.storage,
                        &after_state.instance_field_scope.storage,
                    )
                    || !Arc::ptr_eq(
                        &before_state.instance_field_scope.loan_dependencies,
                        &after_state.instance_field_scope.loan_dependencies,
                    )
                    || before_state.loan_ledger != after_state.loan_ledger
                    || before_state.loan_participant != after_state.loan_participant
                    || before_state.loan_view_bindings != after_state.loan_view_bindings
                    || before_state.thread_ledger != after_state.thread_ledger
                    || before_state.mutex_ledger != after_state.mutex_ledger
                    || before_state.preserves_mutex_protocols
                        != after_state.preserves_mutex_protocols
                    || before_state.mutex_input_reservations != after_state.mutex_input_reservations
                    || before_state.opaque_mutex_acquisitions
                        != after_state.opaque_mutex_acquisitions
                    || before_state.named_mutex_authorities != after_state.named_mutex_authorities
                    || before_state.pending_thread_create != after_state.pending_thread_create
                    || before_state.population_effects.creation
                        != after_state.population_effects.creation
                    || !before_state
                        .observed_population_families
                        .shares_storage_with(&after_state.observed_population_families)
                    || before_state.aggregate_destination != after_state.aggregate_destination
                    || before_state.next_local_frame != after_state.next_local_frame
                    || before_state.next_local_lifetime != after_state.next_local_lifetime
                    || before_state.enclosing_frame_holds_locals
                        != after_state.enclosing_frame_holds_locals
                {
                    return Err("member body access changed unrelated execution state".into());
                }
                return Ok(Self {
                    before_state: before_state.clone(),
                    after_state: after_state.clone(),
                    before_facts: before_facts.clone(),
                    after_facts: after_facts.clone(),
                    definition: definition.clone(),
                    consumption_contract: None,
                    instance: None,
                    selected_children: None,
                    load_equalities:
                        crate::kernel::CheckedLoadEqualityCapture::start_with_call_events(
                            call_events,
                        )
                        .finish(),
                    delta_proofs: Arc::new(Vec::new()),
                });
            }
        }
        if !before_state.loan_bindings_are_consistent()
            || !after_state.loan_bindings_are_consistent()
        {
            return Err("resource rewrite carries mismatched loan dependency sidecar".to_string());
        }
        let load_equality_capture =
            crate::kernel::CheckedLoadEqualityCapture::start_with_call_events(call_events);
        let assumptions = before_facts.assumptions();
        if let CResource::Instance(instance) = selected.resource() {
            let definition = function
                .composite_resource_definition(instance.name())
                .ok_or_else(|| {
                    "instance definition is not registered on the function".to_string()
                })?;
            // Ordinary named memory resources retain their existing checked
            // definitional exchange. Population members cannot be introduced
            // through this path: those require ledger evidence. An exact owned
            // authority may move into or out of a control instance; the
            // creation-ledger equality below proves that no population changed.
            if definition.reaches_population() {
                let memory_only = |spec: &crate::kernel::CResourceSpec| {
                    matches!(
                        spec.term(),
                        crate::kernel::CResourceTerm::Memory(_)
                            | crate::kernel::CResourceTerm::Token { .. }
                            | crate::kernel::CResourceTerm::PopulationAuthority { .. }
                    )
                };
                // A named child is admitted when its own definition reaches no
                // population, so it cannot hide a member or an authority; the
                // exchange then moves only memory, tokens, and this body's own
                // authority, which the ledger equality below checks.
                let ordinary_child = |child: &crate::kernel::CResourceChildSpec| {
                    function
                        .composite_resource_definition(&child.resource)
                        .is_some_and(|child| !child.reaches_population())
                };
                if !definition.children.iter().all(ordinary_child)
                    || !definition.contains().iter().all(memory_only)
                    || definition.matched.as_ref().is_some_and(|body| {
                        body.arms.iter().any(|arm| {
                            !arm.children.iter().all(ordinary_child)
                                || !arm.contains.iter().all(memory_only)
                        })
                    })
                {
                    return Err("named resource rewrite requires an ordinary memory body".into());
                }
            }
            let unfold = before_state
                .resources()
                .owned_instance(instance.identity())
                .is_some();
            let rewrite = crate::kernel::rewrite_resource_instance_selecting_children(
                before_state,
                instance,
                definition,
                function.composite_resource_definitions(),
                assumptions,
                unfold,
                selected_children.as_deref(),
            )
            .map_err(|refusal| refusal.describe())?;
            let expected = rewrite.state;
            let allowed = rewrite.semantic_facts.into_iter().chain(
                rewrite
                    .body_clauses
                    .iter()
                    .map(|clause| clause.proposition.clone()),
            );
            if after_state.population_effects.creation != expected.population_effects.creation {
                return Err(
                    "instance rewrite changed population custody outside its checked exchange"
                        .into(),
                );
            }
            let mut unchanged = after_state.clone();
            unchanged = unchanged.with_resource_context(before_state.resources.clone());
            Arc::make_mut(&mut unchanged.population_effects).creation =
                before_state.population_effects.creation.clone();
            let metadata_baseline = before_state.clone().with_memory(expected.memory().clone());
            if unchanged != metadata_baseline {
                // An unfold names the cells it exposes, which materializes
                // them in the snapshot so the body's facts and a later C read
                // of one of those cells are one load variable
                // (`docs/internals/canonicalization.md`). Adding such a cell
                // is the only memory change a resource rewrite may make, and
                // each added cell must hold the canonical load form of its own
                // pointer at the pre-rewrite snapshot. That is a definitional
                // identity, checked here per added cell with no search.
                if let Err(detail) =
                    memory_only_adds_named_cells(expected.memory(), after_state.memory())
                {
                    return Err(if unfold {
                        format!(
                            "internal error while applying an unfold: Click named an exposed cell \
inconsistently; it {detail}; this is a Click implementation error, not an invalid unfold"
                        )
                    } else {
                        format!("a fold may not change the memory snapshot, but it {detail}")
                    });
                }
                if !unfold {
                    return Err("a fold may not change the memory snapshot".to_string());
                }
                unchanged.memory = expected.memory.clone();
                if unchanged != metadata_baseline {
                    return Err(format!(
                        "instance rewrite changed {} outside its own resources",
                        describe_changed_state_field(&unchanged, before_state)
                    ));
                }
            }
            if !expected
                .resources
                .same_exchange_from(&after_state.resources, &before_state.resources)
            {
                return Err(
                    "internal error while checking an instance rewrite: the resource context is not "
                        .to_string()
                        + "the exchange its definition requires; this is a Click implementation "
                        + "error, not an invalid proof",
                );
            }
            let introduced = after_facts.introduced_since(before_facts).ok_or_else(|| {
                "instance rewrite facts do not descend from their input".to_string()
            })?;
            let allowed = allowed
                .into_iter()
                .collect::<std::collections::BTreeSet<_>>();
            // A visible return projection may repeat a fact already checked
            // at its frozen snapshot. Accept it only when the input context
            // independently proves that exact memory/resource proposition.
            if introduced.iter().any(|fact| {
                !allowed.contains(fact)
                    && !(matches!(fact, Proposition::CMemoryReadDefined { .. })
                        && assumptions.proves_atomic_memory_or_resource(fact))
            }) {
                return Err("instance rewrite introduced an unchecked fact".to_string());
            }
            return Ok(Self {
                before_state: before_state.clone(),
                after_state: after_state.clone(),
                before_facts: before_facts.clone(),
                after_facts: after_facts.clone(),
                definition: definition.clone(),
                consumption_contract: None,
                instance: Some(instance.clone()),
                selected_children,
                load_equalities: load_equality_capture.finish(),
                delta_proofs: Arc::new(Vec::new()),
            });
        }
        let crate::kernel::CResource::Composite { name, .. } = selected.resource() else {
            return Err("resource rewrite evidence requires a composite resource".to_string());
        };
        let definition = function
            .composite_resource_definition(name)
            .cloned()
            .ok_or_else(|| {
                "the rewritten composite definition is not registered on the function".to_string()
            })?;

        let crate::kernel::CResource::Composite { arguments, .. } = selected.resource() else {
            unreachable!()
        };
        if before_state
            .resources()
            .directly_supporting_fact(selected, assumptions)
            .is_none()
            && after_state
                .resources()
                .directly_supporting_fact(selected, after_facts.assumptions())
                .is_none()
        {
            return Err(
                "the rewritten composite is absent from both resource representations".to_string(),
            );
        }
        if before_state
            .resources()
            .directly_supporting_fact(selected, assumptions)
            .is_none()
            && !crate::kernel::functions::check_native_required_formations(
                before_state,
                selected,
                function.composite_resource_definitions(),
                assumptions,
            )
        {
            return Err(
                "composite fold requires its native place carriers to be authenticated".into(),
            );
        }
        let access_key = (name.clone(), arguments.clone());
        if !before_state
            .population_access
            .checks_rewrite(&after_state.population_access, &access_key)
        {
            return Err("resource rewrite changed another population's access authority".into());
        }
        let native_baseline = crate::kernel::functions::assume_checked_native_composite_places(
            before_state,
            selected,
            function.composite_resource_definitions(),
            assumptions,
        )?;
        let mut population_after = after_state.clone();
        population_after.population_access = before_state.population_access.clone();
        let mut concrete_after = after_state.clone();
        concrete_after.set_memory(before_state.memory.clone());
        concrete_after = concrete_after.with_resource_context(before_state.resources.clone());
        concrete_after.observed_population_families =
            before_state.observed_population_families.clone();
        concrete_after.population_access = before_state.population_access.clone();
        if concrete_after != *before_state
            || !crate::kernel::api::contract_certification::c_memories_definitionally_equal(
                native_baseline.memory(),
                after_state.memory(),
                assumptions,
            )
            || !crate::kernel::api::population_observations_equal(before_state, &population_after)
        {
            #[cfg(test)]
            if std::env::var_os("CLICK_RESOURCE_REWRITE_PROBE").is_some() {
                eprintln!(
                    "resource-rewrite-probe name={name} concrete={} memory={} population={}",
                    concrete_after == *before_state,
                    crate::kernel::api::contract_certification::c_memories_definitionally_equal(
                        native_baseline.memory(),
                        after_state.memory(),
                        assumptions,
                    ),
                    crate::kernel::api::population_observations_equal(
                        before_state,
                        &population_after
                    ),
                );
                if name == "MaybeRaw" {
                    let left = native_baseline.memory();
                    let right = after_state.memory();
                    eprintln!(
                        "resource-rewrite-memory-probe heap={} blocks={} forgotten={} cells={}/{} union={}/{}",
                        left.heap == right.heap,
                        left.blocks == right.blocks,
                        left.forgotten == right.forgotten,
                        left.cells.len(),
                        right.cells.len(),
                        left.union_cells.len(),
                        right.union_cells.len()
                    );
                    for (label, memory) in [("baseline", left), ("after", right)] {
                        for (identity, row) in memory.heap.native_record_inputs.iter().take(4) {
                            eprintln!("resource-rewrite-native-probe {label} {identity:?} {row:?}");
                        }
                        for (pointer, value) in memory.cells.iter().take(4) {
                            eprintln!("resource-rewrite-cell-probe {label} {pointer:?} {value:?}");
                            if let CValue::Int32(Bitvector32Term::Variable(variable)) = value {
                                eprintln!(
                                    "resource-rewrite-cell-origin-probe {label} {:?}",
                                    crate::kernel::eval::registered_load_term_for_variable(
                                        variable
                                    )
                                );
                            }
                        }
                    }
                }
            }
            return Err(
                "resource rewrite changed more than a definitional representation".to_string(),
            );
        }
        let expansion_matches = |folded: &CState, exposed: &CState| {
            let Some(authority) = folded
                .resources()
                .directly_supporting_fact(selected, assumptions)
            else {
                return false;
            };
            let Some(expanded) = crate::kernel::functions::expand_composite_resource_fact(
                folded.resources(),
                authority,
                function.composite_resource_definitions(),
                folded.memory(),
                assumptions,
            ) else {
                return false;
            };
            let normalized_expanded = expanded.clone().normalized(assumptions);
            let normalized_exposed = exposed.resources().clone().normalized(assumptions);
            resource_contexts_match_modulo_redundant_views(
                &normalized_expanded,
                &normalized_exposed,
                assumptions,
            )
                || crate::kernel::api::contract_certification::resource_contexts_definitionally_equal_with_definitions(
                function.composite_resource_definitions(),
                exposed.memory(),
                &expanded,
                exposed.memory(),
                exposed.resources(),
                assumptions,
            )
        };
        let open_borrow_matches = |folded: &CState, opened: &CState| {
            let Some(authority) = folded
                .resources()
                .directly_supporting_fact(selected, assumptions)
            else {
                return false;
            };
            let singleton = ResourceContext::new_with_equalities(assumptions)
                .unchecked_with_fact(authority.clone());
            let Some(body) = crate::kernel::functions::expand_composite_resource_fact(
                &singleton,
                authority,
                function.composite_resource_definitions(),
                folded.memory(),
                assumptions,
            ) else {
                return false;
            };
            let Ok(expected) = folded
                .resources()
                .clone()
                .try_compose_with_facts_delaying_normalization(
                    body.facts().iter().cloned(),
                    assumptions,
                )
            else {
                return false;
            };
            let expected = expected.normalized(assumptions);
            let actual = opened.resources().clone().normalized(assumptions);
            resource_contexts_match_modulo_redundant_views(&expected, &actual, assumptions)
        };
        if before_state.resources() != after_state.resources()
            && !expansion_matches(before_state, after_state)
            && !expansion_matches(after_state, before_state)
            && !open_borrow_matches(before_state, after_state)
            && !open_borrow_matches(after_state, before_state)
        {
            return Err(
                "resource rewrite does not match the selected composite definition".to_string(),
            );
        }

        let introduced = after_facts.introduced_since(before_facts).ok_or_else(|| {
            "resource rewrite facts do not descend from the input facts".to_string()
        })?;
        let temporary =
            ResourceContext::new_with_equalities(assumptions).unchecked_with_fact(selected.clone());
        let expanded = crate::kernel::functions::expand_composite_resource_fact(
            &temporary,
            selected,
            function.composite_resource_definitions(),
            after_state.memory(),
            assumptions,
        )
        .ok_or_else(|| "the rewritten composite body could not be instantiated".to_string())?;
        let children = expanded
            .facts()
            .iter()
            .filter(|fact| *fact != selected)
            .cloned()
            .collect::<Vec<_>>();
        let child_context =
            ResourceContext::new_with_equalities(assumptions).unchecked_with_facts(children);
        let mut allowed = child_context.observable_facts_assuming_valid(assumptions);
        allowed.push(Proposition::CResourceComposition(child_context.clone()));
        allowed.extend(
            after_state
                .resources()
                .observable_facts_assuming_valid(after_facts.assumptions()),
        );
        let mut body_premises = Vec::new();
        let relation_authority = CResourceFact::own(selected.resource().clone());
        if let Some(propositions) =
            crate::kernel::functions::evaluate_composite_resource_relation_propositions(
                &relation_authority,
                function.composite_resource_definitions(),
                after_state.memory(),
                assumptions,
            )
        {
            body_premises.extend(propositions.iter().cloned());
            allowed.extend(propositions);
        }
        if let Some(propositions) =
            crate::kernel::functions::evaluate_composite_resource_loadable_propositions(
                selected,
                function.composite_resource_definitions(),
                after_state.memory(),
                assumptions,
            )
        {
            body_premises.extend(propositions.iter().cloned());
            allowed.extend(propositions);
        }
        let delta_premises = ResourceDeltaPremises::new(&body_premises);
        if let Some(propositions) =
            crate::kernel::functions::evaluate_composite_resource_fact_propositions(
                selected,
                function.composite_resource_definitions(),
                after_state.memory(),
                &child_context,
                assumptions,
            )
        {
            allowed.extend(propositions);
        }
        let allowed_assumptions = allowed.iter().fold(assumptions.clone(), |facts, fact| {
            facts.assume_proposition(fact.clone())
        });
        let allowed = allowed.iter().collect::<std::collections::BTreeSet<_>>();
        let mut delta_proofs = Vec::new();
        for fact in &introduced {
            if allowed.contains(fact)
                || allowed_assumptions.proves_exact(fact)
                || resource_composition_is_supported_by(fact, &child_context, assumptions)
            {
                continue;
            }
            let proof = delta_premises
                .prove_with_facts(fact, &allowed_assumptions)
                .ok_or_else(|| {
                    "resource rewrite produced an unchecked pure-fact delta".to_string()
                })?;
            delta_proofs.push(proof);
        }

        let load_equalities = load_equality_capture.finish();
        Ok(Self {
            before_state: before_state.clone(),
            after_state: after_state.clone(),
            before_facts: before_facts.clone(),
            after_facts: after_facts.clone(),
            definition,
            consumption_contract: None,
            instance: None,
            selected_children: None,
            load_equalities,
            delta_proofs: Arc::new(delta_proofs),
        })
    }

    fn advance_checked(
        &self,
        state: &CState,
        facts: &ProofFacts,
        call_events: &CheckedCallEvents,
    ) -> Option<ProofFacts> {
        if state != &self.before_state
            || facts.introduced_since(&self.before_facts).is_none()
            || self
                .delta_proofs
                .iter()
                .any(|read| !read.matches_completed_goal())
            || self.load_equalities.iter().any(|equality| {
                !equality.checks_with_call_events(self.before_facts.assumptions(), call_events)
            })
        {
            return None;
        }
        Some(
            self.after_facts
                .introduced_since(&self.before_facts)?
                .into_iter()
                .fold(facts.clone(), |facts, fact| {
                    if facts.contains_top_level(&fact) {
                        facts
                    } else {
                        facts.with_fact(fact)
                    }
                }),
        )
    }

    /// The registered composite definition the event applied.
    pub(crate) fn definition(&self) -> &CCompositeResourceDefinition {
        &self.definition
    }
}

type ResourceReadKey = (
    crate::kernel::Pointer,
    Bitvector32Term,
    crate::kernel::primitives::ReadRegionIdentity,
);

fn resource_read_key(proposition: &Proposition) -> Option<ResourceReadKey> {
    let Proposition::CMemoryLoadable {
        memory,
        base,
        bytes,
        wide: false,
    } = proposition
    else {
        return None;
    };
    Some((
        base.clone(),
        bytes.clone(),
        memory.read_region_identity(base),
    ))
}

/// One exact read-range rule, with no value equality, arithmetic, memory-DAG
/// walk, or ambient premise search. The identity pins its retirement metadata.
pub(super) fn resource_read_preserves_range(source: &Proposition, goal: &Proposition) -> bool {
    resource_read_key(source)
        .zip(resource_read_key(goal))
        .is_some_and(|(source, goal)| source == goal)
}

fn resource_delta_pointer_equality(
    source: &Proposition,
    goal: &Proposition,
) -> Option<Proposition> {
    if let (Some((_, source_range)), Some((_, goal_range))) =
        (source.memory_containment(), goal.memory_containment())
    {
        return (resource_containment_key(source) == resource_containment_key(goal)).then(|| {
            Proposition::ConditionIs(
                crate::kernel::ConditionTerm::pointer_equal(
                    source_range.base().clone(),
                    goal_range.base().clone(),
                ),
                true,
            )
        });
    }
    let (source_base, source_bytes, source_lifetime) = resource_read_key(source)?;
    let (goal_base, goal_bytes, goal_lifetime) = resource_read_key(goal)?;
    (source_base.block == goal_base.block
        && source_bytes == goal_bytes
        && source_lifetime == goal_lifetime)
        .then(|| {
            Proposition::ConditionIs(
                crate::kernel::ConditionTerm::pointer_equal(source_base, goal_base),
                true,
            )
        })
}

type ResourceContainmentKey = (
    CResource,
    Bitvector32Term,
    Bitvector32Term,
    u32,
    crate::kernel::RangeIndexKind,
);

fn resource_containment_key(proposition: &Proposition) -> Option<ResourceContainmentKey> {
    let (parent, range) = proposition.memory_containment()?;
    Some((
        parent.clone(),
        range.bound_terms().0.clone(),
        range.bound_terms().1.clone(),
        range.element_width(),
        range.kind(),
    ))
}

pub(super) fn resource_delta_uses_exact_equality(
    source: &Proposition,
    equality: &Proposition,
    goal: &Proposition,
) -> bool {
    resource_delta_pointer_equality(source, goal).as_ref() == Some(equality)
}

struct CheckedResourceDeltaProof {
    source: Option<Proposition>,
    equality: Option<Proposition>,
    goal: Proposition,
    proof: super::CheckedProposition,
}

impl CheckedResourceDeltaProof {
    fn matches_completed_goal(&self) -> bool {
        crate::instrumentation::record_deterministic_work(1);
        match (&self.source, self.proof.proposition()) {
            (Some(source), Proposition::Implies(premise, conclusion)) => {
                source == premise.as_ref()
                    && match (&self.equality, conclusion.as_ref()) {
                        (Some(equality), Proposition::Implies(selected, goal)) => {
                            equality == selected.as_ref() && &self.goal == goal.as_ref()
                        }
                        (None, goal) => &self.goal == goal,
                        _ => false,
                    }
            }
            (None, proposition) => self.equality.is_none() && proposition == &self.goal,
            _ => false,
        }
    }
}

/// Only the explicitly instantiated body facts are indexed, once per event.
/// The key excludes stored values and pins allocation metadata rather than
/// hashing or comparing whole snapshots. Duplicate keys are interchangeable
/// premises of the same local rule.
struct ResourceDeltaPremises {
    by_range: std::collections::BTreeMap<ResourceReadKey, Proposition>,
    unique_by_layout: std::collections::BTreeMap<
        (
            Bitvector32Term,
            crate::kernel::primitives::ReadRegionIdentity,
        ),
        Option<Proposition>,
    >,
    unique_containment: std::collections::BTreeMap<ResourceContainmentKey, Option<Proposition>>,
}

impl ResourceDeltaPremises {
    fn new(allowed: &[Proposition]) -> Self {
        let mut by_range = std::collections::BTreeMap::new();
        let mut unique_by_layout = std::collections::BTreeMap::new();
        let mut unique_containment = std::collections::BTreeMap::new();
        for premise in allowed {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(key) = resource_read_key(premise) {
                if !by_range.contains_key(&key) {
                    unique_by_layout
                        .entry((key.1.clone(), key.2.clone()))
                        .and_modify(|source| *source = None)
                        .or_insert_with(|| Some(premise.clone()));
                }
                by_range.insert(key, premise.clone());
            }
            if let Some(key) = resource_containment_key(premise) {
                unique_containment
                    .entry(key)
                    .and_modify(|source: &mut Option<Proposition>| {
                        if source.as_ref() != Some(premise) {
                            *source = None;
                        }
                    })
                    .or_insert_with(|| Some(premise.clone()));
            }
        }
        Self {
            by_range,
            unique_by_layout,
            unique_containment,
        }
    }

    #[cfg(test)]
    fn prove(&self, goal: &Proposition) -> Option<CheckedResourceDeltaProof> {
        self.prove_with_facts(goal, &PureFactContext::new())
    }

    fn prove_with_facts(
        &self,
        goal: &Proposition,
        facts: &PureFactContext,
    ) -> Option<CheckedResourceDeltaProof> {
        use super::{
            OutcomeProofState, ProofBranch, ProofBranchState, ProofObject, ProofObligation,
            PropositionObligation,
        };
        type Leaf = ProofObject<(), ProofObligation<(), Arc<OutcomeProofState<()>>>, ()>;
        let root = |proposition| {
            Leaf::root(
                (),
                ProofBranch::new(
                    ProofObligation::Proposition(PropositionObligation::new(proposition, ())),
                    ProofBranchState {
                        facts: ProofFacts::default(),
                        unfolded_predicates: Default::default(),
                        execution: None,
                    },
                ),
            )
        };
        if matches!(goal, Proposition::ConditionIs(..))
            && let Some(closed) = root(goal.clone()).apply_interface_leaf(None, None)
        {
            return Some(CheckedResourceDeltaProof {
                source: None,
                equality: None,
                goal: goal.clone(),
                proof: closed.completed_proposition()?,
            });
        }
        let source = if let Some(key) = resource_read_key(goal) {
            self.by_range
                .get(&key)
                .or_else(|| self.unique_by_layout.get(&(key.1, key.2))?.as_ref())?
        } else {
            self.unique_containment
                .get(&resource_containment_key(goal)?)?
                .as_ref()?
        };
        // A unique explicitly named range needs no candidate search.
        // Ambiguous layouts are not resolved by trying pointer pairs.
        let equality = if resource_read_preserves_range(source, goal) {
            None
        } else {
            let equality = resource_delta_pointer_equality(source, goal)?;
            if !facts.proves_exact(&equality) {
                return None;
            }
            Some(equality)
        };
        // Prove the implication directly, rather than rebuilding a fact
        // index containing a snapshot for every read. The event already
        // checked this exact source as an instantiated body premise.
        let conclusion = equality.as_ref().map_or_else(
            || goal.clone(),
            |equality| Proposition::Implies(Box::new(equality.clone()), Box::new(goal.clone())),
        );
        let implication = Proposition::Implies(Box::new(source.clone()), Box::new(conclusion));
        let proof = root(implication)
            .apply_resource_delta()?
            .completed_proposition()?;
        Some(CheckedResourceDeltaProof {
            source: Some(source.clone()),
            equality,
            goal: goal.clone(),
            proof,
        })
    }
}

/// An exact automatic-storage retirement, retained beside the C transition
/// that leaves the source scope. Construction is private to the kernel.
#[derive(Clone)]
pub(crate) struct CheckedAutomaticLifetimeEnd {
    before_state: CState,
    after_state: CState,
    names: Vec<String>,
}

impl CheckedAutomaticLifetimeEnd {
    pub(crate) fn before_state(&self) -> &CState {
        &self.before_state
    }
    fn advance_checked(&self, state: &CState) -> Option<CState> {
        if state != &self.before_state
            || self.after_state
                != crate::kernel::eval::end_scope_automatic_lifetimes(state, &self.names).ok()?
        {
            return None;
        }
        Some(self.after_state.clone())
    }
}

/// One iterated guarded-ownership step, retained with the exact state it
/// started from and the fact context it was decided under. Construction is
/// private to the kernel: `record_iterated_step` applies the step itself, and
/// trace checking applies it again from the same input.
#[derive(Clone)]
pub(crate) struct CheckedIteratedStep {
    before_state: CState,
}

impl CheckedIteratedStep {
    pub(crate) fn before_state(&self) -> &CState {
        &self.before_state
    }
}

/// Kernel-checked evidence for one source-ordered, non-consuming, one-layer
/// observation of a folded composite resource. The event advances no C
/// source; it changes only the ghost-resource representation and the exact
/// facts available to later retained C theorems.
#[derive(Clone)]
pub(crate) struct CheckedResourceObservation {
    before_state: CState,
    pub(crate) after_state: CState,
    pub(crate) before_facts: ProofFacts,
    pub(crate) after_facts: ProofFacts,
    definition: Option<CCompositeResourceDefinition>,
    load_equalities: Vec<crate::kernel::CheckedLoadEquality>,
}

impl CheckedResourceObservation {
    pub(crate) fn before_state(&self) -> &CState {
        &self.before_state
    }

    fn check(
        function: &CFunction,
        before_state: &CState,
        before_facts: &ProofFacts,
        observed: &CResourceFact,
        after_state: &CState,
        after_facts: &ProofFacts,
        derivations: &PersistentOrderedSet<Theorem>,
        call_events: &CheckedCallEvents,
    ) -> Result<Self, &'static str> {
        // Only an authorized family has a population count to observe; any
        // other observation is an ordinary resource observation.
        let counted = match observed.resource() {
            crate::kernel::CResource::Composite { name, .. } => function
                .composite_resource_definition(name)
                .is_none_or(|definition| definition.is_authorized()),
            crate::kernel::CResource::Token { name, .. } => !function
                .contract_interface()
                .is_ordinary_abstract_family(name),
            _ => true,
        };
        if counted {
            let unchanged = before_state.memory.diagnostic_identity()
                == after_state.memory.diagnostic_identity()
                && before_state.shares_non_memory_storage_with(after_state)
                && Arc::ptr_eq(
                    &before_state.population_effects,
                    &after_state.population_effects,
                );
            if !unchanged {
                return Err("count observation changed execution state or member custody");
            }
            let crate::kernel::CResource::Composite { name, .. } = observed.resource() else {
                return Err("count observation requires an owned declared member");
            };
            function
                .composite_resource_definition(name)
                .ok_or("the observed definition is not registered on the function")?;
            let bound = crate::kernel::api::checked_owned_resource_count_lower_bound(
                before_state,
                observed,
                before_facts.assumptions(),
            )
            .ok_or("count observation lacks member ownership or count authority")?;
            let quantity = observed
                .owned_quantity_term()
                .ok_or("count observation requires owned member quantity")?;
            let nonnegative = Proposition::ConditionIs(
                crate::kernel::ConditionTerm::signed_less_equal(
                    Bitvector32Term::Constant(0),
                    quantity.clone(),
                ),
                true,
            );
            let introduced = after_facts
                .introduced_since(before_facts)
                .ok_or("count observation facts do not descend from input facts")?;
            for fact in introduced {
                let checked = if fact == bound {
                    // The bound was reconstructed and certified from this
                    // immutable ledger and its exact member custody above.
                    continue;
                } else if fact == nonnegative {
                    crate::kernel::api::prove_owned_resource_quantity_nonnegative(
                        before_state,
                        observed,
                        &fact,
                        before_facts.assumptions(),
                    )
                } else {
                    return Err("count observation introduced an unrelated fact or member body");
                };
                if checked.is_none() {
                    return Err("count observation has no checked bound derivation");
                }
            }
            return Ok(Self {
                before_state: before_state.clone(),
                after_state: after_state.clone(),
                before_facts: before_facts.clone(),
                after_facts: after_facts.clone(),
                definition: None,
                load_equalities: Vec::new(),
            });
        }
        if !before_state.loan_bindings_are_consistent()
            || !after_state.loan_bindings_are_consistent()
        {
            return Err("resource observation carries mismatched loan dependency sidecar");
        }
        let load_equality_capture =
            crate::kernel::CheckedLoadEqualityCapture::start_with_call_events(call_events);
        let assumptions = before_facts.assumptions();
        let zero_quantity = observed.has_proven_zero_quantity(assumptions);
        if !zero_quantity
            && before_state
                .resources()
                .directly_supporting_fact(observed, assumptions)
                .is_none()
        {
            return Err("the observed resource is not available in the input state");
        }
        let crate::kernel::CResource::Composite { name, .. } = observed.resource() else {
            return Err("resource observation evidence requires a composite resource");
        };
        let definition = function
            .composite_resource_definitions()
            .iter()
            .find(|definition| definition.name() == name)
            .cloned()
            .ok_or("the observed composite definition is not registered on the function")?;

        let native_baseline = crate::kernel::functions::assume_checked_native_composite_places(
            before_state,
            observed,
            function.composite_resource_definitions(),
            assumptions,
        )
        .map_err(|_| "resource observation could not reconstruct native metadata")?;
        let mut concrete_after = after_state.clone();
        concrete_after.set_memory(before_state.memory.clone());
        concrete_after = concrete_after.with_resource_context(before_state.resources.clone());
        if concrete_after != *before_state
            || (memory_only_adds_named_cells(native_baseline.memory(), after_state.memory())
                .is_err()
                && !crate::kernel::api::contract_certification::c_memories_definitionally_equal(
                    native_baseline.memory(),
                    after_state.memory(),
                    assumptions,
                ))
        {
            return Err("resource observation changed concrete execution state");
        }

        let observation_support = before_state
            .resources()
            .directly_supporting_owned_entry(observed, assumptions);
        let observation_authority = before_state
            .resources()
            .directly_supporting_fact(observed, assumptions)
            .unwrap_or(observed);
        let projects_body =
            observed.is_view() || observed.has_proven_positive_quantity(assumptions);
        let (children, raw_children) = if !projects_body {
            (Vec::new(), Vec::new())
        } else {
            let definition_authority = CResourceFact::own(observed.resource().clone());
            let temporary = ResourceContext::new_with_equalities(assumptions)
                .unchecked_with_fact(definition_authority.clone());
            let (_, children, raw_children) =
                crate::kernel::functions::expand_composite_resource_fact_with_children(
                    &temporary,
                    &definition_authority,
                    function.composite_resource_definitions(),
                    after_state.memory(),
                    assumptions,
                )
                .ok_or("the observed composite body could not be instantiated")?;
            (children, raw_children)
        };
        let body_is_already_exposed = raw_children.iter().any(CResourceFact::is_own)
            && raw_children
                .iter()
                .filter(|fact| fact.is_own())
                .all(|fact| {
                    before_state
                        .resources()
                        .directly_supporting_fact(fact, assumptions)
                        .is_some()
                });
        let expected_views = if body_is_already_exposed {
            Vec::new()
        } else {
            raw_children
                .iter()
                .filter_map(|fact| fact.core_with_assumptions(assumptions))
                .filter(|fact| !before_state.resources().contains_exact_representation(fact))
                .collect::<Vec<_>>()
        };
        let Some(resource_delta) = after_state
            .resources()
            .facts()
            .strip_prefix(before_state.resources().facts())
        else {
            return Err("resource observation changed an existing resource representation");
        };
        if resource_delta != expected_views.as_slice() {
            return Err("resource observation produced an unchecked resource delta");
        }
        if let Some((support_occurrence, support)) = observation_support {
            if !after_state
                .resources()
                .support_occurrence_is_live(support_occurrence, support)
            {
                return Err("resource observation support is stale or malformed");
            }
            if expected_views.iter().any(|fact| {
                !after_state
                    .resources()
                    .has_supported_projection(fact, support_occurrence, support)
            }) {
                return Err("resource observation views are missing their owned support");
            }
        }

        let introduced = after_facts
            .introduced_since(before_facts)
            .ok_or("resource observation facts do not descend from the input facts")?;
        let child_context =
            ResourceContext::new_with_equalities(assumptions).unchecked_with_facts(children);
        let mut allowed = child_context.observable_facts_assuming_valid(assumptions);
        allowed.push(Proposition::CResourceComposition(child_context.clone()));
        let relation_authority = CResourceFact::own(observed.resource().clone());
        if projects_body
            && let Some(propositions) =
                crate::kernel::functions::evaluate_composite_resource_relation_propositions(
                    &relation_authority,
                    function.composite_resource_definitions(),
                    after_state.memory(),
                    assumptions,
                )
        {
            allowed.extend(propositions);
        }
        if projects_body
            && let Some(propositions) =
                crate::kernel::functions::evaluate_composite_resource_loadable_propositions(
                    observation_authority,
                    function.composite_resource_definitions(),
                    after_state.memory(),
                    assumptions,
                )
        {
            allowed.extend(propositions);
        }
        if projects_body
            && let Some(propositions) =
                crate::kernel::functions::evaluate_composite_resource_fact_propositions(
                    observation_authority,
                    function.composite_resource_definitions(),
                    after_state.memory(),
                    &child_context,
                    assumptions,
                )
        {
            allowed.extend(propositions);
        }
        allowed.extend(
            derivations
                .iter()
                .map(|theorem| theorem.proposition().clone()),
        );
        let allowed_assumptions = allowed.iter().fold(assumptions.clone(), |facts, fact| {
            facts.assume_proposition(fact.clone())
        });
        if introduced.iter().any(|fact| {
            !allowed.contains(fact)
                && !resource_composition_is_supported_by(fact, &child_context, assumptions)
                && !allowed_assumptions.proves_exact(fact)
        }) {
            return Err("resource observation produced an unchecked pure-fact delta");
        }

        let load_equalities = load_equality_capture.finish();
        Ok(Self {
            before_state: before_state.clone(),
            after_state: after_state.clone(),
            before_facts: before_facts.clone(),
            after_facts: after_facts.clone(),
            definition: Some(definition),
            load_equalities,
        })
    }

    fn advance_checked(
        &self,
        state: &CState,
        facts: &ProofFacts,
        call_events: &CheckedCallEvents,
    ) -> Option<ProofFacts> {
        let same_state = {
            state.memory.diagnostic_identity() == self.before_state.memory.diagnostic_identity()
                && state.shares_non_memory_storage_with(&self.before_state)
                && Arc::ptr_eq(
                    &state.population_effects,
                    &self.before_state.population_effects,
                )
        };
        if !same_state
            || facts.introduced_since(&self.before_facts).is_none()
            || self.load_equalities.iter().any(|equality| {
                !equality.checks_with_call_events(self.before_facts.assumptions(), call_events)
            })
        {
            return None;
        }
        Some(
            self.after_facts
                .introduced_since(&self.before_facts)?
                .into_iter()
                .fold(facts.clone(), |facts, fact| {
                    if facts.contains_top_level(&fact) {
                        facts
                    } else {
                        facts.with_fact(fact)
                    }
                }),
        )
    }

    /// The registered composite definition the event applied.
    pub(crate) fn definition(&self) -> Option<&CCompositeResourceDefinition> {
        self.definition.as_ref()
    }
}

fn resource_composition_is_supported_by(
    proposition: &Proposition,
    available: &ResourceContext,
    assumptions: &PureFactContext,
) -> bool {
    let Proposition::CResourceComposition(required) = proposition else {
        return false;
    };
    // Observing the exact checked context needs no resource consumption.
    // In particular, a retained view and its owner can coexist in that
    // context even though consuming both in sequence would fail.
    if available.shares_storage_with(required) || available.contains_exact_facts_of(required) {
        return true;
    }
    available
        .clone()
        .without_facts(required.facts(), assumptions)
        .is_some()
}

fn resource_contexts_match_modulo_redundant_views(
    left: &ResourceContext,
    right: &ResourceContext,
    assumptions: &PureFactContext,
) -> bool {
    let owned_counts = |context: &ResourceContext| {
        context.facts().iter().filter(|fact| fact.is_own()).fold(
            BTreeMap::<CResourceFact, usize>::new(),
            |mut counts, fact| {
                *counts.entry(fact.clone()).or_default() += 1;
                counts
            },
        )
    };
    owned_counts(left) == owned_counts(right)
        && left
            .facts()
            .iter()
            .filter(|fact| fact.is_view())
            .all(|fact| right.satisfies_fact(fact, assumptions))
        && right
            .facts()
            .iter()
            .filter(|fact| fact.is_view())
            .all(|fact| left.satisfies_fact(fact, assumptions))
}

/// Kernel-issued evidence for the exact contract-entry state from which a
/// function proof begins. In particular, this retains population materialization
/// instead of asking finalization to reconstruct it from Surface bookkeeping.
#[derive(Clone)]
pub(crate) struct CheckedFunctionEntry {
    caller_state: CState,
    function: Arc<CFunction>,
    arguments: Vec<CExpression>,
    entry_state: CState,
    boundary_transfer: Option<Arc<crate::kernel::functions::CheckedBoundaryResourceTransfer>>,
    /// The facts the proof assumes at entry: the contract's requirements
    /// and the caller's facts, before any step. Recorded evidence is
    /// checked under these, not under each step's full context, so the
    /// definitional comparisons stay proportional to the entry.
    assumptions: PureFactContext,
    /// `resource_relation_assumptions(&self.assumptions)`, computed once.
    relation_facts: Option<PureFactContext>,
}

impl CheckedFunctionEntry {
    fn check(
        caller_state: &CState,
        function: &CFunction,
        arguments: &[CExpression],
        expected_entry_state: &CState,
        assumptions: PureFactContext,
    ) -> Result<Arc<Self>, CRuntimeError> {
        let entry_state = crate::kernel::c_function_entry_state(caller_state, function, arguments)
            .ok_or_else(|| {
                CRuntimeError::FunctionContract(
                    "could not bind the function entry arguments".into(),
                )
            })?;
        if &entry_state != expected_entry_state {
            return Err(CRuntimeError::FunctionContract(
                "the checked function entry does not match the proof entry".into(),
            ));
        }
        let function = Arc::new(function.clone());
        let boundary_transfer = {
            Some(
                crate::kernel::functions::capture_checked_boundary_resource_transfer(
                    caller_state,
                    function.clone(),
                    arguments,
                    &assumptions,
                    &mut ExecutionBudget::beside_live_state(),
                )
                .map_err(|limit| {
                    CRuntimeError::FunctionContract(format!(
                        "checking the function entry resource transfer stopped at {}",
                        limit.describe(),
                    ))
                })??,
            )
        };
        let mut entry = Self {
            caller_state: caller_state.clone(),
            function,
            arguments: arguments.to_vec(),
            entry_state,
            boundary_transfer,
            assumptions,
            relation_facts: None,
        };
        entry.relation_facts = entry.resource_relation_assumptions(&entry.assumptions);
        Ok(Arc::new(entry))
    }

    /// The facts the proof assumed at entry.
    pub(crate) fn assumptions(&self) -> &PureFactContext {
        &self.assumptions
    }

    /// The entry resources' relation facts under the entry assumptions,
    /// when the entry's composites expand.
    pub(crate) fn relation_facts(&self) -> Option<&PureFactContext> {
        self.relation_facts.as_ref()
    }

    pub(crate) fn entry_state_for(
        &self,
        caller_state: &CState,
        function: &CFunction,
        arguments: &[CExpression],
        assumptions: &PureFactContext,
    ) -> Option<CState> {
        if self.function.as_ref() != function || self.arguments != arguments {
            return None;
        }
        if &self.caller_state == caller_state {
            return Some(self.entry_state.clone());
        }
        let rebased_entry =
            crate::kernel::c_function_entry_state(caller_state, function, arguments)?;
        crate::kernel::api::function_entry_representation_states_match(
            function,
            &self.entry_state,
            &rebased_entry,
            assumptions,
        )
        .then_some(rebased_entry)
    }

    pub(crate) fn trace_entry_state(
        &self,
        function: &CFunction,
        arguments: &[CExpression],
    ) -> Option<&CState> {
        (self.function.has_same_entry_and_source(function) && self.arguments == arguments)
            .then_some(&self.entry_state)
    }

    pub(crate) fn resource_relation_assumptions(
        &self,
        assumptions: &PureFactContext,
    ) -> Option<PureFactContext> {
        let (_, propositions) = {
            crate::kernel::functions::expand_all_composite_resource_facts_and_propositions_at_state(
                self.entry_state.resources(),
                self.function.composite_resource_definitions(),
                &self.entry_state,
                assumptions,
            )?
        };
        Some(
            propositions
                .into_iter()
                .fold(assumptions.clone(), |facts, proposition| {
                    facts.assume_proposition(proposition)
                }),
        )
    }

    pub(crate) fn caller_state(&self) -> &CState {
        &self.caller_state
    }
}

/// One kernel-issued complementary logical partition over an unchanged C
/// execution frontier.
#[derive(Clone)]
pub(crate) struct CheckedProofCasePartition {
    identity: Arc<()>,
    root_facts: ProofFacts,
    case_facts: Vec<Proposition>,
    /// The exact delta each arm adds to `root_facts`: its constructor case,
    /// followed by any facts checked for the one resource field that was
    /// matched. Keeping this in the kernel-issued partition makes independent
    /// certificate checking use the same premises without trusting surface
    /// bookkeeping.
    arm_additions: Vec<Vec<Proposition>>,
    /// Ordered declaration correspondence, including clauses whose exact
    /// proposition was already in the arm's fact store.
    arm_body_clauses: Vec<Vec<crate::kernel::functions::ResourceBodyClauseRecord>>,
    /// Exact contradictions checked under that arm's canonical premises.
    excluded: Vec<Option<Proposition>>,
    /// Generative constructor witnesses are introduced only at their unchanged
    /// entry scope. Complementary propositional splits need no such scope.
    witness_scope: Option<SharedValue<CState>>,
}

/// One entry of an outcome-evidence fork plan
/// ([`ExecutionProofCore::fork_outcome_evidence`]): keep a path's trace, or
/// split it into the two arms of a checked partition.
pub(crate) enum OutcomeEvidenceFork {
    Keep,
    Split {
        partition: Arc<CheckedProofCasePartition>,
        arm_facts: [ProofFacts; 2],
    },
    NestedSplit {
        partition: Arc<CheckedProofCasePartition>,
        arm_facts: [ProofFacts; 2],
        arms: [Box<OutcomeEvidenceFork>; 2],
    },
}

/// How many traces one entry of an outcome evidence fork plan produces.
fn outcome_fork_count(fork: &OutcomeEvidenceFork) -> usize {
    match fork {
        OutcomeEvidenceFork::Keep => 1,
        OutcomeEvidenceFork::Split { arm_facts, .. } => arm_facts.len(),
        OutcomeEvidenceFork::NestedSplit { arms, .. } => {
            arms.iter().map(|arm| outcome_fork_count(arm)).sum()
        }
    }
}

/// One arm of a checked logical partition. This event advances no C source;
/// it changes only the authoritative fact context for later evidence.
#[derive(Clone)]
pub(crate) struct CheckedProofCaseArm {
    partition: Arc<CheckedProofCasePartition>,
    arm_index: usize,
    facts: ProofFacts,
}

impl CheckedProofCasePartition {
    pub(crate) fn excluding_constructor_case(
        &self,
        index: usize,
        fact: Proposition,
    ) -> Option<Arc<Self>> {
        self.witness_scope.as_ref()?;
        if !self.facts_for_case(index)?.contradicts(&fact) {
            return None;
        }
        let mut successor = self.clone();
        // Coverage from the old partition must not discharge this new one.
        successor.identity = Arc::new(());
        successor.excluded[index] = Some(fact);
        Some(Arc::new(successor))
    }

    /// Excludes a constructor whose arm refutes itself after bridging steps.
    ///
    /// `arm_facts` are the facts the arm's own proof reached: this case's
    /// facts plus what the arm's `have`s established from them, each checked
    /// by its own proof. The arm is refuted when those facts contradict
    /// `fact`, exactly as [`Self::excluding_constructor_case`] decides it for
    /// a sole `contradiction`. The facts must hold this case's fact, so a
    /// context from another arm, or from before the split, cannot exclude
    /// this one.
    pub(crate) fn excluding_constructor_case_in(
        &self,
        index: usize,
        arm_facts: &ProofFacts,
        fact: Proposition,
    ) -> Option<Arc<Self>> {
        self.witness_scope.as_ref()?;
        if !arm_facts.contains(self.case_fact(index)?) || !arm_facts.contradicts(&fact) {
            return None;
        }
        let mut successor = self.clone();
        successor.identity = Arc::new(());
        successor.excluded[index] = Some(fact);
        Some(Arc::new(successor))
    }

    pub(crate) fn case_fact(&self, index: usize) -> Option<&Proposition> {
        self.case_facts.get(index)
    }

    pub(crate) fn body_clauses_for_case(
        &self,
        index: usize,
    ) -> Option<&[crate::kernel::functions::ResourceBodyClauseRecord]> {
        self.arm_body_clauses.get(index).map(Vec::as_slice)
    }

    pub(crate) fn facts_for_case(&self, index: usize) -> Option<ProofFacts> {
        let additions = self.arm_additions.get(index)?;
        Some(
            additions
                .iter()
                .cloned()
                .fold(self.root_facts.clone(), |facts, fact| facts.with_fact(fact)),
        )
    }

    /// The facts this partition was issued against. An arm's premises are
    /// these plus that arm's case fact, so a caller entering an arm builds
    /// the arm's context from here rather than from its own branch: the
    /// partition may carry model facts the frontier's premises force on the
    /// scrutinee's instance (A26, gap 57b), and those belong to every arm.
    pub(crate) fn root_facts(&self) -> &ProofFacts {
        &self.root_facts
    }
    pub(crate) fn check(
        root_facts: &ProofFacts,
        then_fact: Proposition,
        else_fact: Proposition,
    ) -> Option<Arc<Self>> {
        let negated_then = Proposition::Not(Box::new(then_fact.clone()));
        if else_fact != negated_then
            && !super::fact_reasoning::condition_polarity_forms(&negated_then).contains(&else_fact)
        {
            return None;
        }
        let arm_additions = [&then_fact, &else_fact]
            .into_iter()
            .map(|fact| {
                root_facts
                    .with_fact(fact.clone())
                    .introduced_since(root_facts)
                    .unwrap_or_default()
            })
            .collect();
        Some(Arc::new(Self {
            identity: Arc::new(()),
            root_facts: root_facts.clone(),
            case_facts: vec![then_fact.clone(), else_fact.clone()],
            arm_additions,
            arm_body_clauses: vec![Vec::new(), Vec::new()],
            excluded: vec![None, None],
            witness_scope: None,
        }))
    }
}

impl CheckedProofCaseArm {
    pub(crate) fn excluded_cases(&self) -> Vec<bool> {
        self.partition
            .excluded
            .iter()
            .map(Option::is_some)
            .collect()
    }
    pub(crate) fn identity(&self) -> usize {
        Arc::as_ptr(&self.partition.identity) as usize
    }

    pub(crate) fn arm_index(&self) -> usize {
        self.arm_index
    }

    pub(crate) fn width(&self) -> usize {
        self.partition.case_facts.len()
    }

    pub(crate) fn is_valid(&self) -> bool {
        self.arm_index < self.width()
            && self
                .facts
                .introduced_since(&self.partition.root_facts)
                .is_some_and(|introduced| {
                    introduced == self.partition.arm_additions[self.arm_index]
                })
    }
}

/// Arms of one checked logical partition, rejoined.
///
/// A partition splits a frontier by facts alone: under each case the proof
/// runs an arm. When arms end at the same program point in the same state,
/// that state is reached whichever of their cases holds, so the proof
/// continues from it once. This is case analysis.
///
/// A join need not take every case at once. Each arm covers one case, or the
/// cases an earlier join of the same partition merged, so a wide `match` is
/// joined pairwise. Whether the cases are exhaustive is not this join's
/// concern: every path's coverage of every partition is checked once, over
/// the finished traces.
///
/// Only [`Self::check`] and [`Self::check_interface`] build one. A join
/// keeps each arm's events and the facts they were proved under, so trace
/// certification re-walks every arm from the split and compares where it
/// lands.
#[derive(Clone)]
pub(crate) struct CheckedProofCaseJoin {
    partition: Arc<CheckedProofCasePartition>,
    arms: Vec<CheckedProofCaseJoinArm>,
    start_state: CState,
    joined_state: CState,
    /// The facts the proof holds after the join: the partition's root facts,
    /// and what every arm established or the interface admits.
    joined_facts: ProofFacts,
    /// Present when the arms ended in different states and were merged
    /// through an explicit `ensuring` interface.
    interface: Option<CheckedProofCaseJoinInterface>,
}

/// What an interface join of two logical cases retains beyond the arms: the
/// same record a `branch ensuring` keeps.
#[derive(Clone)]
struct CheckedProofCaseJoinInterface {
    execution_facts: crate::kernel::ExecutionFacts,
    effect_facts: crate::kernel::ExecutionFacts,
    resource_definitions: Vec<crate::kernel::CCompositeResourceDefinition>,
    lowerings: Arc<Vec<[CheckedInterfaceLowering; 3]>>,
    next_kernel_variable: u64,
}

#[derive(Clone)]
struct CheckedProofCaseJoinArm {
    /// The cases of the partition this arm stands for.
    cases: Vec<usize>,
    facts: ProofFacts,
    events: Vec<CheckedExecutionEvent>,
}

impl CheckedProofCaseJoinArm {
    /// The events to re-walk against the arm's final facts. An arm that
    /// entered one case begins with that entry, which only swaps the facts
    /// and is validated on its own; an arm that is itself a join is walked
    /// whole.
    fn walked_events(&self) -> &[CheckedExecutionEvent] {
        match self.events.first() {
            Some(CheckedExecutionEvent::ProofCase(_)) => &self.events[1..],
            _ => &self.events,
        }
    }
}

/// How one arm of a join begins: the partition it belongs to, the cases it
/// covers, and the facts its own facts must extend.
fn case_join_arm_entry(
    events: &[CheckedExecutionEvent],
) -> Option<(&Arc<CheckedProofCasePartition>, Vec<usize>, &ProofFacts)> {
    match events.first()? {
        CheckedExecutionEvent::ProofCase(entered) if entered.is_valid() => {
            Some((&entered.partition, vec![entered.arm_index], &entered.facts))
        }
        CheckedExecutionEvent::ProofCaseJoin(inner) => {
            Some((&inner.partition, inner.covered_cases(), &inner.joined_facts))
        }
        _ => None,
    }
}

/// The arms of one partition, walked from the split to one program point.
struct WalkedCaseArms {
    partition: Arc<CheckedProofCasePartition>,
    arms: Vec<CheckedProofCaseJoinArm>,
    start_state: CState,
    /// Each arm's memory changes, as its walk met them.
    memory_steps: Vec<Vec<CheckedMemoryStep>>,
}

impl CheckedProofCaseJoin {
    /// Checks that `arms` are arms of one partition over disjoint cases,
    /// each continuing `parent`'s one trace to the same program point, and
    /// with `same_state` to the same state.
    fn walk_arms(
        parent: &ExecutionProofCore,
        arms: &[(&ExecutionProofCore, &ProofFacts)],
        function: &CFunction,
        arguments: &[CExpression],
        same_state: bool,
    ) -> Result<WalkedCaseArms, &'static str> {
        if arms.len() < 2 {
            return Err("a case join needs at least two arms");
        }
        let [parent_trace] = parent.execution_evidence.as_slice() else {
            return Err("the case-join parent does not have one execution trace");
        };
        let start_state = parent
            .running_state(function, arguments)
            .map_err(|_| "the case-join parent has no running state")?
            .into_owned();
        let source = parent.current_source(function).cloned();
        let mut partition: Option<Arc<CheckedProofCasePartition>> = None;
        let mut covered = std::collections::BTreeSet::new();
        let mut checked: Vec<CheckedProofCaseJoinArm> = Vec::with_capacity(arms.len());
        let mut memory_steps = Vec::with_capacity(arms.len());
        let mut joined: Option<(&ExecutionProofCore, Option<CStatement>)> = None;
        for (arm, facts) in arms {
            let [trace] = arm.execution_evidence.as_slice() else {
                return Err("a case-join arm does not have one execution trace");
            };
            let events = trace
                .suffix_since(parent_trace)
                .ok_or("a case-join arm trace does not descend from the parent trace")?;
            let (entered, cases, entry_facts) = case_join_arm_entry(&events)
                .ok_or("a case-join arm does not begin by entering a case")?;
            match &partition {
                None => partition = Some(entered.clone()),
                Some(partition) if Arc::ptr_eq(partition, entered) => {}
                Some(_) => return Err("the case-join arms entered different partitions"),
            }
            for case in &cases {
                if entered.excluded.get(*case).is_none_or(Option::is_some) {
                    return Err("a case-join arm stands for a case its partition excluded");
                }
                if !covered.insert(*case) {
                    return Err("two case-join arms stand for the same case");
                }
            }
            // The facts offered for the arm must be this arm's: the facts it
            // entered with, extended by what it went on to establish.
            if facts.introduced_since(entry_facts).is_none() {
                return Err("a case-join arm's facts do not extend the facts it entered with");
            }
            if arm.evidence_completed {
                return Err("a case-join arm has already completed its trace");
            }
            let walked = CheckedProofCaseJoinArm {
                cases,
                facts: (*facts).clone(),
                events,
            };
            let progress = check_evidence_events(
                walked.walked_events(),
                facts,
                start_state.clone(),
                source.clone(),
            )
            .ok_or("a case-join arm trace does not follow its C source from the split")?;
            if progress.completed.is_some() {
                return Err("a case-join arm has already completed its trace");
            }
            if same_state && &progress.state != arm.reached_state() {
                return Err("a case-join arm trace does not reach its recorded state");
            }
            match &joined {
                None => joined = Some((arm, progress.remaining)),
                Some((first, remaining)) => {
                    if progress.remaining != *remaining {
                        return Err("the case-join arms end at different program points");
                    }
                    if same_state && arm.reached_state() != first.reached_state() {
                        return Err("the case-join arms end in different states");
                    }
                    if arm.evidence_try_stack != first.evidence_try_stack {
                        return Err("the case-join arms end in different `try` regions");
                    }
                }
            }
            memory_steps.push(progress.memory_steps);
            checked.push(walked);
        }
        Ok(WalkedCaseArms {
            partition: partition.expect("a join of two arms found their partition"),
            arms: checked,
            start_state,
            memory_steps,
        })
    }

    /// Checks that `arms` rejoin in one state, and that `successor_facts`
    /// adds to the partition's root facts only what every arm established.
    fn check(
        parent: &ExecutionProofCore,
        arms: &[(&ExecutionProofCore, &ProofFacts)],
        function: &CFunction,
        arguments: &[CExpression],
        successor_facts: &ProofFacts,
    ) -> Result<Self, &'static str> {
        let WalkedCaseArms {
            partition,
            arms: checked,
            start_state,
            ..
        } = Self::walk_arms(parent, arms, function, arguments, true)?;
        // A fact every arm established holds whichever of their cases does.
        // The case facts themselves differ between arms, so none survives.
        let introduced = successor_facts
            .introduced_since(&partition.root_facts)
            .ok_or("the case-join successor facts do not extend the partition's root facts")?;
        if introduced
            .iter()
            .any(|fact| checked.iter().any(|arm| !arm.facts.contains(fact)))
        {
            return Err("the case-join successor holds a fact that not every arm established");
        }
        Ok(Self {
            partition,
            arms: checked,
            start_state,
            joined_state: arms[0].0.reached_state().clone(),
            joined_facts: successor_facts.clone(),
            interface: None,
        })
    }

    /// Checks a two-arm join through an explicit interface: the arms end at
    /// one program point but in different states, and `joined_state` is the
    /// abstraction of both that keeps what the interface names. The
    /// abstraction and every interface fact are checked exactly as for a
    /// `branch ensuring`; only where the arms came from differs.
    #[allow(clippy::too_many_arguments)]
    fn check_interface(
        parent: &ExecutionProofCore,
        root_facts: &ProofFacts,
        arms: [(&ExecutionProofCore, &ProofFacts); 2],
        function: &CFunction,
        arguments: &[CExpression],
        stable_join_locals: &BTreeMap<String, CValue>,
        interface_specs: &[SpecProposition],
        interface_resource_specs: &[CResourceSpec],
        arm_effect_facts: [&(impl ExecutionFactSource + ?Sized); 2],
        joined_state: &CState,
        successor_facts: &ProofFacts,
        old_reference: Option<&CState>,
    ) -> Result<Self, &'static str> {
        let WalkedCaseArms {
            partition,
            arms: checked,
            start_state,
            memory_steps,
        } = Self::walk_arms(parent, &arms, function, arguments, false)?;
        let exact_root = partition
            .root_facts
            .introduced_since(root_facts)
            .is_some_and(|delta| delta.is_empty())
            && root_facts
                .introduced_since(&partition.root_facts)
                .is_some_and(|delta| delta.is_empty());
        if !exact_root {
            return Err("the interface join does not start from its partition's root facts");
        }
        let arm_cores = [arms[0].0, arms[1].0];
        let arm_facts = [arms[0].1, arms[1].1];
        if !arm_effect_deltas_are_exact(parent, arm_cores, arm_effect_facts) {
            return Err("an interface arm effect delta is not exact");
        }
        let CheckedInterfaceAbstraction {
            next_kernel_variable,
            arm_interface_resources,
            introduced,
            interface_lowerings,
        } = check_interface_abstraction(
            root_facts,
            &start_state,
            parent,
            arm_cores,
            arm_facts,
            stable_join_locals,
            interface_specs,
            interface_resource_specs,
            joined_state,
            successor_facts,
            old_reference,
        )?;
        let conditional_heap_frees = conditional_heap_frees(arm_effect_facts);
        if !conditional_heap_frees.is_empty()
            && !interface_resources_guard_heap_frees(
                function,
                &arm_interface_resources,
                [arm_cores[0].reached_state(), arm_cores[1].reached_state()],
                arm_facts,
                &conditional_heap_frees,
            )
        {
            return Err(
                "a conditional heap deallocation must be represented by an arm-sensitive owned resource",
            );
        }
        let effect_facts = checked_interface_effect_facts_along(
            &start_state,
            joined_state,
            arm_cores,
            arm_facts,
            arm_effect_facts,
            Some([&memory_steps[0], &memory_steps[1]]),
        )?;
        Ok(Self {
            partition,
            arms: checked,
            start_state,
            joined_state: joined_state.clone(),
            joined_facts: successor_facts.clone(),
            interface: Some(CheckedProofCaseJoinInterface {
                execution_facts: introduced
                    .into_iter()
                    .map(ExecutionPureFact::certified)
                    .collect(),
                effect_facts,
                resource_definitions: function.composite_resource_definitions().to_vec(),
                lowerings: Arc::new(interface_lowerings),
                next_kernel_variable,
            }),
        })
    }

    /// The facts an interface join certified for the successor, in the form
    /// trace completion retains them.
    pub(crate) fn interface_execution_facts(&self) -> &crate::kernel::ExecutionFacts {
        self.interface.as_ref().map_or_else(
            || {
                static EMPTY: std::sync::LazyLock<ExecutionFacts> =
                    std::sync::LazyLock::new(ExecutionFacts::new);
                &*EMPTY
            },
            |interface| &interface.execution_facts,
        )
    }

    /// The facts the proof holds after an interface join, when this is one.
    pub(crate) fn interface_successor_facts(&self) -> Option<&ProofFacts> {
        self.interface.as_ref().map(|_| &self.joined_facts)
    }

    /// Whether an interface join was checked under this function's resource
    /// definitions and kept a complete, consistent lowering of every
    /// interface fact. A structural join has nothing of the kind to check.
    pub(crate) fn matches_interface_resource_definitions(&self, function: &CFunction) -> bool {
        let Some(interface) = &self.interface else {
            return true;
        };
        let [then_arm, else_arm] = self.arms.as_slice() else {
            return false;
        };
        interface.resource_definitions == function.composite_resource_definitions()
            && interface.lowerings.iter().all(|lowerings| {
                lowerings
                    .iter()
                    .all(CheckedInterfaceLowering::has_complete_proof)
                    && lowerings[0].spec == lowerings[1].spec
                    && lowerings[0].spec == lowerings[2].spec
                    && lowerings[0].reference == lowerings[1].reference
                    && lowerings[0].reference == lowerings[2].reference
                    && lowerings[2].snapshot == self.joined_state
                    && lowerings[0].facts.shares_premises_with(&then_arm.facts)
                    && lowerings[1].facts.shares_premises_with(&else_arm.facts)
                    && lowerings[2].facts.shares_premises_with(&self.joined_facts)
            })
    }

    pub(crate) fn start_state(&self) -> &CState {
        &self.start_state
    }

    pub(crate) fn joined_state(&self) -> &CState {
        &self.joined_state
    }

    /// The cases of the partition this join merged.
    fn covered_cases(&self) -> Vec<usize> {
        self.arms
            .iter()
            .flat_map(|arm| arm.cases.iter().copied())
            .collect()
    }

    /// Whether any arm did more than reason: it advanced the C program or
    /// changed the state. When no arm did, the joined state is the split
    /// state and the frontier is where the split found it.
    pub(crate) fn arms_changed_execution(&self) -> bool {
        self.joined_state != self.start_state
            || self.arms.iter().any(|arm| {
                arm.events.iter().any(|event| match event {
                    CheckedExecutionEvent::ProofCase(_)
                    | CheckedExecutionEvent::Context(_)
                    | CheckedExecutionEvent::StatementEffects(_) => false,
                    CheckedExecutionEvent::ProofCaseJoin(inner) => inner.arms_changed_execution(),
                    _ => true,
                })
            })
    }

    /// The events of every arm.
    pub(crate) fn live_arm_events(&self) -> impl Iterator<Item = &[CheckedExecutionEvent]> {
        self.arms.iter().map(|arm| arm.events.as_slice())
    }

    /// Re-walks every arm from `state` over `source` and returns the source
    /// they all leave, or `None` if any arm fails to reach that one program
    /// point, or without an interface the joined state.
    fn advance_checked(
        &self,
        state: &CState,
        source: &Option<CStatement>,
        call_events: &CheckedCallEvents,
    ) -> Option<Option<CStatement>> {
        if state != &self.start_state {
            return None;
        }
        let mut remaining: Option<Option<CStatement>> = None;
        for arm in &self.arms {
            let (entered, cases, _) = case_join_arm_entry(&arm.events)?;
            if !Arc::ptr_eq(entered, &self.partition) || cases != arm.cases {
                return None;
            }
            let progress = check_evidence_events_with_call_events(
                arm.walked_events(),
                &arm.facts,
                state.clone(),
                source.clone(),
                call_events.clone(),
            )?;
            if progress.completed.is_some()
                || (self.interface.is_none() && progress.state != self.joined_state)
            {
                return None;
            }
            match &remaining {
                None => remaining = Some(progress.remaining),
                Some(first) if *first == progress.remaining => {}
                Some(_) => return None,
            }
        }
        remaining
    }
}

/// The resources on both sides of an interface join: what each arm gives up
/// to the interface, what the successor holds for it, and the successor's
/// whole resource context.
struct InterfaceJoinResources {
    arm_interface_resources: [Vec<CResourceFact>; 2],
    successor_interface_resources: Vec<CResourceFact>,
    successor_interface_resource_facts: Vec<Proposition>,
    /// What neither arm changed, with the interface resources composed in,
    /// in the one normal form the successor must carry.
    expected_resources: ResourceContext,
}

fn interface_join_resources(
    parent: &ExecutionProofCore,
    arms: [&ExecutionProofCore; 2],
    arm_facts: [&ProofFacts; 2],
    interface_resource_specs: &[CResourceSpec],
    joined_state: &CState,
    successor_facts: &ProofFacts,
) -> Result<InterfaceJoinResources, &'static str> {
    let mut arm_interface_resources = [Vec::new(), Vec::new()];
    let mut successor_interface_resources = Vec::new();
    let mut successor_interface_resource_facts = Vec::new();
    for spec in interface_resource_specs {
        for (index, (arm, facts)) in arms.iter().zip(arm_facts).enumerate() {
            let fact = evaluate_interface_resource_spec(spec, arm.reached_state(), facts)
                .ok_or("an interface resource does not lower in a concrete arm")?;
            arm_interface_resources[index].push(fact);
        }
        let fact = evaluate_interface_resource_spec(spec, joined_state, successor_facts)
            .ok_or("an interface resource does not lower at the abstract successor")?;
        if let Some(proposition) = interface_resource_intrinsic_fact(spec, &fact, joined_state) {
            successor_interface_resource_facts.push(proposition);
        }
        successor_interface_resources.push(fact);
    }
    let mut arm_residuals = Vec::with_capacity(2);
    for (index, (arm, facts)) in arms.iter().zip(arm_facts).enumerate() {
        let mut remaining = arm.state.resources().clone();
        // Views are non-consuming. Check them while their owned support
        // is still present, then consume the owned interface facts in
        // their source order so consuming a parent cannot erase a view
        // that the same interface has already established.
        for required in arm_interface_resources[index]
            .iter()
            .filter(|fact| fact.is_view())
        {
            if remaining
                .clone()
                .without_facts(std::slice::from_ref(required), facts.assumptions())
                .is_none()
            {
                return Err("an interface resource is not owned by one concrete arm");
            }
        }
        for required in arm_interface_resources[index]
            .iter()
            .filter(|fact| fact.is_own())
        {
            // Consume through the local indexes: giving up one interface
            // resource must not rewrite the unrelated rest of the context.
            let Some(next) = remaining
                .clone()
                .without_fact_incrementally(required, facts.assumptions())
            else {
                return Err("an interface resource is not owned by one concrete arm");
            };
            remaining = next;
        }
        arm_residuals.push(remaining);
    }
    let common_resources = ResourceContext::common_exact_descendant(
        &arm_residuals[0],
        &arm_residuals[1],
        parent.reached_state().resources(),
    )
    .ok_or("the interface arm resources do not descend from the branch root")?;
    // A view already established by the common residual needs no second
    // occurrence. Match the builder's non-consuming view route so unrelated
    // allocation owners do not change resource ordering at this interface.
    let additions = successor_interface_resources
        .iter()
        .filter(|fact| {
            fact.is_own() || !common_resources.satisfies_fact(fact, successor_facts.assumptions())
        })
        .cloned()
        .collect::<Vec<_>>();
    let expected_resources = common_resources
        .try_compose_into_valid_context_delaying_normalization(
            additions.iter().cloned(),
            successor_facts.assumptions(),
        )
        .map_err(|_| "the interface resources do not form a valid successor context")?
        .normalized_around_facts(&additions, successor_facts.assumptions());
    Ok(InterfaceJoinResources {
        arm_interface_resources,
        successor_interface_resources,
        successor_interface_resource_facts,
        expected_resources,
    })
}

/// What an explicit join interface makes of two concrete arms: the
/// abstraction both agree on, the interface resources each arm gives up, the
/// facts the successor gains, and the checked lowering of every interface
/// fact. The split the arms came from, a C `if` or a logical partition,
/// plays no part here.
struct CheckedInterfaceAbstraction {
    next_kernel_variable: u64,
    arm_interface_resources: [Vec<CResourceFact>; 2],
    introduced: Vec<Proposition>,
    interface_lowerings: Vec<[CheckedInterfaceLowering; 3]>,
}

#[allow(clippy::too_many_arguments)]
fn check_interface_abstraction(
    root_facts: &ProofFacts,
    split_state: &CState,
    parent: &ExecutionProofCore,
    arms: [&ExecutionProofCore; 2],
    arm_facts: [&ProofFacts; 2],
    stable_join_locals: &BTreeMap<String, CValue>,
    interface_specs: &[SpecProposition],
    interface_resource_specs: &[CResourceSpec],
    joined_state: &CState,
    successor_facts: &ProofFacts,
    old_reference: Option<&CState>,
) -> Result<CheckedInterfaceAbstraction, &'static str> {
    let expected_stable_locals = arms[0]
        .state
        .locals()
        .object_values()
        .filter(|(name, value)| arms[1].reached_state().locals().get(name) == Some(*value))
        .map(|(name, value)| (name.to_string(), value.clone()))
        .collect::<BTreeMap<_, _>>();
    if &expected_stable_locals != stable_join_locals {
        return Err("the interface stable-local set is not exact");
    }
    let sibling_states = [arms[0].reached_state(), arms[1].reached_state()];
    // Both arms abstract from the same counter, the higher of the two, so
    // the abstraction is the same whichever arm allocated more and neither
    // arm's own identities can be re-issued by the join.
    let join_next_kernel_variable = arms[0]
        .next_kernel_variable
        .max(arms[1].next_kernel_variable);
    let mut abstract_then = crate::kernel::abstract_c_state_for_interface_join_across(
        arms[0].reached_state(),
        &sibling_states,
        stable_join_locals,
        join_next_kernel_variable,
    )
    .map_err(|_| "the then interface state could not be abstracted")?;
    let mut abstract_else = crate::kernel::abstract_c_state_for_interface_join_across(
        arms[1].reached_state(),
        &sibling_states,
        stable_join_locals,
        join_next_kernel_variable,
    )
    .map_err(|_| "the else interface state could not be abstracted")?;
    // Reconstruct the prefix transfer independently for both incoming full
    // carriers. The resource interface is no evidence of typed geometry.
    abstract_then.state = crate::kernel::project_interface_native_spans(
        arms[0].reached_state(),
        &abstract_then.state,
        interface_resource_specs,
        arm_facts[0].assumptions(),
    )
    .map_err(|_| "the then interface typed prefix is not established")?;
    abstract_else.state = crate::kernel::project_interface_native_spans(
        arms[1].reached_state(),
        &abstract_else.state,
        interface_resource_specs,
        arm_facts[1].assumptions(),
    )
    .map_err(|_| "the else interface typed prefix is not established")?;
    // Both abstractions derive from the memory at the split, so they are
    // compared by what each changed from it.
    if abstract_then.next_kernel_variable != abstract_else.next_kernel_variable
        || !abstract_then
            .state
            .eq_with_memories_from(&abstract_else.state, split_state.memory())
    {
        return Err("the interface arms do not have one deterministic abstraction");
    }
    // The successor and the arm abstraction reach an empty resource
    // context by different routes, so compare the shape with the context
    // dropped the same way on both sides, then check the successor's loan
    // authority explicitly. The shape comparison still covers the ledger
    // and the participant, because dropping a resource context does not
    // touch either.
    if !joined_state
        .clone()
        .with_resource_context(ResourceContext::new())
        .eq_with_memories_from(&abstract_then.state, split_state.memory())
    {
        return Err("the interface successor is not the checked arm abstraction");
    }
    // D2 law 9: a join keeps the arms' authority, it never sums it. Every
    // loan dependency the successor's interface carries must be one an arm
    // already held; a changed or invented root is not admitted here.
    if !interface_successor_loans_are_inherited(joined_state, sibling_states) {
        return Err("the interface successor claims a loan dependency no arm held");
    }
    let InterfaceJoinResources {
        arm_interface_resources,
        successor_interface_resources,
        successor_interface_resource_facts,
        expected_resources,
    } = interface_join_resources(
        parent,
        arms,
        arm_facts,
        interface_resource_specs,
        joined_state,
        successor_facts,
    )?;
    if &expected_resources != joined_state.resources() {
        return Err("the interface successor resource context is not exact");
    }
    if successor_interface_resources.iter().any(|fact| {
        !joined_state
            .resources()
            .satisfies_fact(fact, successor_facts.assumptions())
    }) {
        return Err("an interface resource is absent from the abstract successor");
    }

    // `old(...)` in an interface fact names one fixed earlier state. Any
    // state serves, so long as every lowering of the fact below reads the
    // same one; the proof side says which, because inside a loop body it is
    // the function's entry and not the body's own start.
    let reference_state = old_reference.unwrap_or_else(|| {
        parent
            .frontier
            .execution_start_state
            .as_ref()
            .unwrap_or(split_state)
    });
    let concrete_access = [0, 1].map(|index| {
        InterfaceReadPremises::new(
            interface_resource_specs
                .iter()
                .zip(&arm_interface_resources[index])
                .filter_map(|(spec, resource)| {
                    interface_resource_intrinsic_fact(spec, resource, arms[index].reached_state())
                }),
        )
    });
    let successor_access =
        InterfaceReadPremises::new(successor_interface_resource_facts.iter().cloned());
    let mut interface_lowerings = Vec::with_capacity(interface_specs.len());
    let _ = take_unestablished_interface_goal();
    for (spec_index, spec) in interface_specs.iter().enumerate() {
        let concrete = |index: usize| {
            let checked = CheckedInterfaceLowering::check(
                spec,
                arms[index].reached_state(),
                reference_state,
                arm_facts[index],
                &concrete_access[index],
            );
            if checked.is_none() {
                // Say which fact, in which arm, for the refusal's report.
                UNESTABLISHED_INTERFACE_GOAL.with(|unestablished| {
                    if let Some(unestablished) = unestablished.borrow_mut().as_mut() {
                        unestablished.fact = spec_index;
                        unestablished.arm = index;
                    }
                });
            }
            checked.ok_or("an interface fact is not established by both concrete arms")
        };
        let then_lowering = concrete(0)?;
        let else_lowering = concrete(1)?;
        let successor = CheckedInterfaceLowering::check_in(
            spec,
            joined_state,
            reference_state,
            successor_facts,
            &successor_access,
            &PureFactContext::new(),
        )
        .ok_or("an interface fact is not retained at the abstract successor")?;
        interface_lowerings.push([then_lowering, else_lowering, successor]);
    }
    let interface_propositions = interface_lowerings
        .iter()
        .map(|lowerings| &lowerings[2].path.proposition)
        .collect::<std::collections::BTreeSet<_>>();
    let introduced = successor_facts
        .introduced_since(root_facts)
        .ok_or("the interface successor facts do not descend from the branch root")?;
    for fact in &introduced {
        let common_arm_fact = arm_facts
            .iter()
            .all(|facts| checked_branch_fact_is_available(facts, fact));
        let interface_fact = interface_propositions.contains(fact);
        let interface_resource_fact =
            ResourceContext::new_with_equalities(successor_facts.assumptions())
                .unchecked_with_facts(successor_interface_resources.clone())
                .observable_facts_assuming_valid(successor_facts.assumptions())
                .contains(fact)
                || successor_interface_resource_facts.contains(fact);
        if !common_arm_fact && !interface_fact && !interface_resource_fact {
            return Err("the interface successor contains an unchecked new fact");
        }
    }

    // A named interface instance carries a model the arms need not agree on.
    // The successor must hold it with the fresh model this join mints, so
    // nothing is known of that model beyond what the interface facts state.
    let mut next_kernel_variable = abstract_then.next_kernel_variable;
    for spec in interface_resource_specs {
        let (Some(identity), Some(schema)) = (spec.instance_identity(), spec.instance_schema())
        else {
            continue;
        };
        let (expected, next) = crate::kernel::functions::interface_join_instance_fields(
            schema,
            identity,
            next_kernel_variable,
        )
        .ok_or("a named interface resource could not be given a fresh model")?;
        let fresh = joined_state
            .resources()
            .owned_instance(identity)
            .is_some_and(|instance| instance.fields == expected);
        if !fresh {
            return Err(
                "the interface successor does not hold a named resource with a fresh model",
            );
        }
        next_kernel_variable = next;
    }
    Ok(CheckedInterfaceAbstraction {
        next_kernel_variable,
        arm_interface_resources,
        introduced,
        interface_lowerings,
    })
}

/// One exhaustive nonterminal C `if`, checked against its exact source arms
/// and retained as a nested execution-evidence node.
#[derive(Clone)]
pub(crate) struct CheckedExecutionBranch {
    split: CheckedBranchSplit,
    arms: [CheckedExecutionBranchArm; 2],
    joined_state: CState,
    interface_successor_facts: Option<ProofFacts>,
    interface_execution_facts: crate::kernel::ExecutionFacts,
    interface_effect_facts: crate::kernel::ExecutionFacts,
    interface_resource_definitions: Option<Vec<crate::kernel::CCompositeResourceDefinition>>,
    // Keep the actual selected lowering results, not just their boolean verdicts.
    // Every retained judgment has a completed local proof.
    interface_lowerings: Arc<Vec<[CheckedInterfaceLowering; 3]>>,
    /// The fresh-variable counter the joined execution continues from, from
    /// the abstraction this check recomputed itself. A structural join invents
    /// no identity and leaves this `None`; an interface join does, and the
    /// recorder installs this mark rather than trusting a caller's.
    interface_next_kernel_variable: Option<u64>,
}

#[derive(Clone)]
struct CheckedExecutionBranchArm {
    facts: ProofFacts,
    events: Vec<CheckedExecutionEvent>,
}

fn branch_split_starts_at_parent(
    parent: &ExecutionProofCore,
    split_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    root_facts: &ProofFacts,
) -> bool {
    if split_state == parent.reached_state() {
        return true;
    }
    if !parent.frontier.is_at_function_entry()
        || parent.execution_evidence.len() != 1
        || parent.execution_evidence[0].iter().any(|event| {
            !matches!(
                event,
                CheckedExecutionEvent::ResourceObservation(_)
                    | CheckedExecutionEvent::ResourceRewrite(_)
                    | CheckedExecutionEvent::PopulationAuthorityRewrite(_)
                    | CheckedExecutionEvent::PopulationMemberRewrite(_)
            )
        })
    {
        return false;
    }
    let Some(entry_state) =
        crate::kernel::c_function_entry_state(parent.reached_state(), function, arguments)
    else {
        return false;
    };
    crate::kernel::api::execution_evidence_states_match(
        function,
        &entry_state,
        split_state,
        root_facts.assumptions(),
    )
}

impl CheckedExecutionBranch {
    #[allow(clippy::too_many_arguments)]
    fn check(
        split: CheckedBranchSplit,
        root_facts: &ProofFacts,
        arm_theorems: [&Theorem; 2],
        arm_facts: [&ProofFacts; 2],
        parent: &ExecutionProofCore,
        arms: [&ExecutionProofCore; 2],
        function: &CFunction,
        arguments: &[CExpression],
        arm_effect_facts: [&(impl ExecutionFactSource + ?Sized); 2],
    ) -> Result<Self, &'static str> {
        let condition = &split.condition;
        if !branch_split_starts_at_parent(parent, &split.state, function, arguments, root_facts) {
            return Err("the branch split does not start at the parent execution state");
        }
        if parent.execution_evidence.len() != 1 {
            return Err("the branch parent does not have one execution trace");
        }
        if arms.iter().any(|arm| arm.execution_evidence.len() != 1) {
            return Err("a branch arm does not have one execution trace");
        }
        if !arm_effect_deltas_are_exact(parent, arms, arm_effect_facts) {
            return Err("a branch arm effect delta is not exact");
        }
        if arms.iter().any(|arm| !arm.frontier.is_at_region_boundary()) {
            return Err("a branch arm has not reached its typed boundary");
        }
        if arms[0].reached_state() != arms[1].reached_state() {
            return Err("the branch arms do not have one joined state");
        }
        if !split.validates_exhaustive_join(
            &split.state,
            condition,
            root_facts,
            [Some(arm_theorems[0]), Some(arm_theorems[1])],
            [Some(arm_facts[0]), Some(arm_facts[1])],
        ) {
            return Err("the branch arms do not exhaust the checked condition split");
        }
        let parent_trace = &parent.execution_evidence[0];
        let full_source = prepend_checked_evidence_statement(
            split.branch_statement.clone(),
            split.continuation.clone(),
        );
        let mut checked_arms = Vec::with_capacity(2);
        for (index, arm) in arms.iter().enumerate() {
            let events = arm.execution_evidence[0]
                .suffix_since(parent_trace)
                .ok_or("a branch arm trace does not descend from the parent trace")?;
            // Even an empty source arm has this condition event. Its exact
            // theorem also fixes the arm's polarity through the checked split.
            if !matches!(
                events.first(),
                Some(CheckedExecutionEvent::Condition(theorem)) if theorem == arm_theorems[index]
            ) {
                return Err("a branch arm does not begin with its checked condition theorem");
            }
            let progress = check_evidence_events(
                &events,
                arm_facts[index],
                split.state.clone(),
                Some(full_source.clone()),
            )
            .ok_or("a branch arm theorem trace does not follow its exact C source")?;
            if progress.completed.is_some() || progress.remaining != split.continuation {
                return Err("a branch arm theorem trace does not reach the shared continuation");
            }
            if &progress.state != arm.reached_state() {
                return Err("a branch arm theorem trace does not reach its recorded state");
            }
            checked_arms.push(CheckedExecutionBranchArm {
                facts: arm_facts[index].clone(),
                events,
            });
        }
        let [then_arm, else_arm] = checked_arms
            .try_into()
            .map_err(|_| "the checked branch does not have exactly two arms")?;
        let interface_effect_facts = checked_interface_effect_facts(
            &split.state,
            arms[0].reached_state(),
            arms,
            arm_facts,
            arm_effect_facts,
        )?;
        Ok(Self {
            split,
            arms: [then_arm, else_arm],
            joined_state: arms[0].reached_state().clone(),
            interface_successor_facts: None,
            interface_execution_facts: Vec::new().into(),
            interface_effect_facts,
            interface_resource_definitions: None,
            interface_lowerings: Arc::new(Vec::new()),
            interface_next_kernel_variable: None,
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn check_interface(
        split: CheckedBranchSplit,
        root_facts: &ProofFacts,
        arm_theorems: [&Theorem; 2],
        arm_facts: [&ProofFacts; 2],
        parent: &ExecutionProofCore,
        arms: [&ExecutionProofCore; 2],
        function: &CFunction,
        arguments: &[CExpression],
        stable_join_locals: &BTreeMap<String, CValue>,
        interface_specs: &[SpecProposition],
        interface_resource_specs: &[CResourceSpec],
        arm_effect_facts: [&(impl ExecutionFactSource + ?Sized); 2],
        joined_state: &CState,
        successor_facts: &ProofFacts,
        old_reference: Option<&CState>,
    ) -> Result<Self, &'static str> {
        if !branch_split_starts_at_parent(parent, &split.state, function, arguments, root_facts) {
            return Err("the interface split does not start at the parent state");
        }
        if parent.execution_evidence.len() != 1
            || arms.iter().any(|arm| arm.execution_evidence.len() != 1)
        {
            return Err("the interface branch does not have one trace per frontier");
        }
        if !arm_effect_deltas_are_exact(parent, arms, arm_effect_facts) {
            return Err("an interface arm effect delta is not exact");
        }
        if arms.iter().any(|arm| !arm.frontier.is_at_region_boundary()) {
            return Err("an interface arm has not reached its typed boundary");
        }
        if !split.validates_exhaustive_join(
            &split.state,
            &split.condition,
            root_facts,
            [Some(arm_theorems[0]), Some(arm_theorems[1])],
            [Some(arm_facts[0]), Some(arm_facts[1])],
        ) {
            return Err("the interface arms do not exhaust the checked condition split");
        }

        let CheckedInterfaceAbstraction {
            next_kernel_variable,
            arm_interface_resources,
            introduced,
            interface_lowerings,
        } = check_interface_abstraction(
            root_facts,
            &split.state,
            parent,
            arms,
            arm_facts,
            stable_join_locals,
            interface_specs,
            interface_resource_specs,
            joined_state,
            successor_facts,
            old_reference,
        )?;
        let parent_trace = &parent.execution_evidence[0];
        let full_source = prepend_checked_evidence_statement(
            split.branch_statement.clone(),
            split.continuation.clone(),
        );
        let mut checked_arms = Vec::with_capacity(2);
        let mut memory_steps = Vec::with_capacity(2);
        for (index, arm) in arms.iter().enumerate() {
            let events = arm.execution_evidence[0]
                .suffix_since(parent_trace)
                .ok_or("an interface arm trace does not descend from the parent trace")?;
            if !matches!(
                events.first(),
                Some(CheckedExecutionEvent::Condition(theorem)) if theorem == arm_theorems[index]
            ) {
                return Err("an interface arm does not begin with its checked condition theorem");
            }
            let progress = check_evidence_events(
                &events,
                arm_facts[index],
                split.state.clone(),
                Some(full_source.clone()),
            )
            .ok_or("an interface arm trace does not follow its exact C source")?;
            if progress.completed.is_some() || progress.remaining != split.continuation {
                return Err("an interface arm trace does not reach the shared continuation");
            }
            if !crate::kernel::api::execution_evidence_states_match(
                function,
                &progress.state,
                arm.reached_state(),
                arm_facts[index].assumptions(),
            ) {
                return Err("an interface arm trace does not reach its recorded state");
            }
            memory_steps.push(progress.memory_steps);
            checked_arms.push(CheckedExecutionBranchArm {
                facts: arm_facts[index].clone(),
                events,
            });
        }
        let [then_arm, else_arm] = checked_arms
            .try_into()
            .map_err(|_| "the checked interface branch does not have exactly two arms")?;
        let conditional_heap_frees = conditional_heap_frees(arm_effect_facts);
        if !conditional_heap_frees.is_empty()
            && !interface_resources_guard_heap_frees(
                function,
                &arm_interface_resources,
                [arms[0].reached_state(), arms[1].reached_state()],
                arm_facts,
                &conditional_heap_frees,
            )
        {
            return Err(
                "a conditional heap deallocation must be represented by an arm-sensitive owned resource",
            );
        }
        // The walk above is each arm's memory history, so the effects are
        // read off it and not chained by comparing memories.
        let interface_effect_facts = checked_interface_effect_facts_along(
            &split.state,
            joined_state,
            arms,
            arm_facts,
            arm_effect_facts,
            Some([&memory_steps[0], &memory_steps[1]]),
        )?;
        Ok(Self {
            split,
            arms: [then_arm, else_arm],
            joined_state: joined_state.clone(),
            interface_successor_facts: Some(successor_facts.clone()),
            interface_execution_facts: introduced
                .into_iter()
                .map(ExecutionPureFact::certified)
                .collect(),
            interface_effect_facts,
            interface_resource_definitions: Some(
                function.composite_resource_definitions().to_vec(),
            ),
            interface_lowerings: Arc::new(interface_lowerings),
            interface_next_kernel_variable: Some(next_kernel_variable),
        })
    }

    /// The counter the joined execution continues from, when this join
    /// invented identities of its own.
    pub(crate) fn interface_next_kernel_variable(&self) -> Option<u64> {
        self.interface_next_kernel_variable
    }

    pub(crate) fn matches_source(
        &self,
        state: &CState,
        branch_statement: &CStatement,
        continuation: &Option<CStatement>,
    ) -> bool {
        &self.split.state == state
            && &self.split.branch_statement == branch_statement
            && statement_sequence_is_prefix(&self.split.continuation, continuation)
    }

    pub(crate) fn joined_state(&self) -> &CState {
        &self.joined_state
    }

    pub(crate) fn start_statement(&self) -> &CStatement {
        &self.split.branch_statement
    }

    pub(crate) fn continuation(&self) -> &Option<CStatement> {
        &self.split.continuation
    }

    pub(crate) fn start_state(&self) -> &CState {
        &self.split.state
    }

    pub(crate) fn arm_facts(&self, index: usize) -> &ProofFacts {
        &self.arms[index].facts
    }

    pub(crate) fn arm_events(&self, index: usize) -> &[CheckedExecutionEvent] {
        &self.arms[index].events
    }

    pub(crate) fn interface_successor_facts(&self) -> Option<&ProofFacts> {
        self.interface_successor_facts.as_ref()
    }

    pub(crate) fn interface_execution_facts(&self) -> &crate::kernel::ExecutionFacts {
        &self.interface_execution_facts
    }

    pub(crate) fn interface_effect_facts(&self) -> &crate::kernel::ExecutionFacts {
        &self.interface_effect_facts
    }

    pub(crate) fn matches_interface_resource_definitions(&self, function: &CFunction) -> bool {
        self.interface_resource_definitions
            .as_ref()
            .is_none_or(|definitions| definitions == function.composite_resource_definitions())
            && self.interface_lowerings.iter().all(|lowerings| {
                lowerings
                    .iter()
                    .all(CheckedInterfaceLowering::has_complete_proof)
                    && lowerings[0].spec == lowerings[1].spec
                    && lowerings[0].spec == lowerings[2].spec
                    && lowerings[0].reference == lowerings[1].reference
                    && lowerings[0].reference == lowerings[2].reference
                    && lowerings[2].snapshot == self.joined_state
                    && lowerings[0].facts.shares_premises_with(&self.arms[0].facts)
                    && lowerings[1].facts.shares_premises_with(&self.arms[1].facts)
                    && self
                        .interface_successor_facts
                        .as_ref()
                        .is_some_and(|facts| lowerings[2].facts.shares_premises_with(facts))
            })
    }
}

/// Whether every stable-view loan dependency the interface successor carries
/// was already held by a concrete arm.
///
/// The checked quantity is the binding itself -- the
/// loan, scope, share, support occurrence, and viewed fact -- which names the
/// exact authority that licenses reading the exported view. Requiring each of
/// those to appear in some arm keeps the join from minting authority that no
/// alternative execution actually reached (D2 law 9).
///
/// The binding count follows the proof -- one binding per exposed child per
/// unfold or observe -- while the loans themselves follow the contract, so
/// comparing the two sides pairwise would be quadratic in proof length. The
/// arms' binding *values* are folded into one membership index first and each
/// successor binding is then one lookup. That is the same predicate: a binding
/// is inherited exactly when some arm holds an equal one, at whatever
/// occurrence. The occurrence keys cannot serve as that index, because a
/// `branch ensuring` interface rebuilds its resource context from the declared
/// clauses and its occurrences are fresh.
fn interface_successor_loans_are_inherited(successor: &CState, arms: [&CState; 2]) -> bool {
    let mut held = std::collections::HashSet::new();
    for arm in arms {
        for (_, binding) in arm.loan_view_bindings().iter() {
            crate::instrumentation::record_deterministic_work(1);
            held.insert(binding);
        }
    }
    successor.loan_view_bindings().iter().all(|(_, binding)| {
        crate::instrumentation::record_deterministic_work(1);
        held.contains(binding)
    })
}

/// Collapses two alternative, kernel-issued arm effect chains into the one
/// transition published by an interface join. Arm effects are alternatives,
/// never sequential facts: concatenating them would describe an impossible
/// execution whenever both start at the split memory.
fn arm_effect_deltas_are_exact(
    parent: &ExecutionProofCore,
    arms: [&ExecutionProofCore; 2],
    supplied: [&(impl ExecutionFactSource + ?Sized); 2],
) -> bool {
    arms.iter().zip(supplied).all(|(arm, supplied)| {
        arm.effect_facts
            .suffix_since(&parent.effect_facts)
            .is_some_and(|expected| expected.iter().eq(supplied.fact_iter()))
    })
}

fn memory_diff_is_covered_by_writes(
    before: &CMemory,
    after: &CMemory,
    changed: &[(Pointer, u32)],
    assumptions: &PureFactContext,
    fact: &ExecutionPureFact,
) -> bool {
    let erased_cells_are_certified_store_bookkeeping =
        fact.certified_store_data().is_some_and(|store| {
            store.before == *before
                && store.after == *after
                && changed.iter().any(|(changed_pointer, bytes)| {
                    changed_pointer == &store.pointer && *bytes == store.value.byte_width()
                })
        });
    if erased_cells_are_certified_store_bookkeeping {
        return true;
    }
    before
        .differing_cell_pointers(after)
        .into_iter()
        .filter(|pointer| !pointer.block.starts_with("local:"))
        .all(|diff_pointer| {
            if !after.has_known_cell_at(&diff_pointer) {
                return false;
            }
            let Some(value) = after.known_value(&diff_pointer) else {
                return false;
            };
            changed.iter().any(|(changed_pointer, bytes)| {
                assumptions.pointer_access_in_range(
                    &diff_pointer,
                    value.byte_width(),
                    changed_pointer,
                    &Bitvector32Term::Constant(0),
                    &Bitvector32Term::Constant(1),
                    *bytes,
                )
            })
        })
}

fn memory_diff_is_covered_by_ranges(
    before: &CMemory,
    after: &CMemory,
    mutable_ranges: &[CMemoryRange],
    assumptions: &PureFactContext,
) -> bool {
    let erased_cells_are_call_havoc_bookkeeping = after.matches_call_memory_havoc_result(
        before,
        mutable_ranges,
        assumptions,
        crate::kernel::primitives::CallKeptOwnership::recorded_on(after, assumptions).as_ref(),
    );
    if erased_cells_are_call_havoc_bookkeeping {
        return true;
    }
    before
        .differing_cell_pointers(after)
        .into_iter()
        .filter(|pointer| !pointer.block.starts_with("local:"))
        .all(|diff_pointer| {
            if !after.has_known_cell_at(&diff_pointer) {
                return false;
            }
            mutable_ranges.iter().any(|range| {
                assumptions.pointer_access_in_memory_range(
                    &diff_pointer,
                    after.known_value(&diff_pointer).map_or_else(
                        crate::kernel::resource_tracker::widest_scalar_access_bytes,
                        |value| value.byte_width(),
                    ),
                    range,
                )
            })
        })
}

/// Whether the memory an arm's effects have produced so far is `recorded`,
/// the memory the arm recorded at this point.
///
/// Effects account for writes. An arm that returns from an inlined call also
/// ends the lifetimes of that call's automatic objects, which writes nothing
/// and leaves no effect, so the recorded memory may hold tombstones the
/// effects do not produce. Those objects are ended here the same way before
/// the comparison. The join carries every arm's tombstones on its own
/// ([`CMemory::with_interface_memory_havoc_preserving_loans`]), so this
/// admits no write the effects do not cover.
fn interface_chain_memory_matches(
    produced: &CMemory,
    recorded: &CMemory,
    assumptions: &PureFactContext,
) -> bool {
    use crate::kernel::api::contract_certification::c_memories_definitionally_equal;
    // End the lifetimes first: with them the memories are usually the same
    // snapshot, which the comparison answers without looking at a cell.
    let mut ended: Option<CMemory> = None;
    for block in recorded.ended_local_blocks() {
        if !produced.is_ended_local_block(block) {
            ended = Some(
                ended
                    .as_ref()
                    .unwrap_or(produced)
                    .without_local_block(block),
            );
        }
    }
    c_memories_definitionally_equal(ended.as_ref().unwrap_or(produced), recorded, assumptions)
}

fn checked_interface_effect_facts(
    split_state: &CState,
    joined_state: &CState,
    arms: [&ExecutionProofCore; 2],
    arm_facts: [&ProofFacts; 2],
    arm_effect_facts: [&(impl ExecutionFactSource + ?Sized); 2],
) -> Result<crate::kernel::ExecutionFacts, &'static str> {
    checked_interface_effect_facts_along(
        split_state,
        joined_state,
        arms,
        arm_facts,
        arm_effect_facts,
        None,
    )
}

fn is_memory_effect(proposition: &Proposition) -> bool {
    matches!(
        proposition,
        Proposition::CMemoryMutatesOnly { .. }
            | Proposition::CMemoryEffectSummary { .. }
            | Proposition::CHeapAllocationFreed { .. }
    )
}

/// Whether an arm's memory effects account for every memory change its walk
/// passed through that could have written.
///
/// The walk has already checked that the arm's events follow one another
/// from the split to the arm's end, so its steps are the arm's whole memory
/// history. A step that cannot write needs no effect. A step that can is
/// covered when the effects starting at its first snapshot lead to its last,
/// and snapshots are matched by identity first: only a statement that reads
/// or assigns a local before it stores leaves two that differ, and those
/// differ in what that one statement cached.
///
/// This is why the join does not compare the arm's memories as wholes. A
/// comparison of two snapshots that differ in the reads an `unfold` cached
/// has to justify each read against the memory history, and its cost grows
/// with the proof before the split rather than with the arm.
fn arm_effects_follow_memory_steps(
    steps: &[CheckedMemoryStep],
    effects: &(impl ExecutionFactSource + ?Sized),
    assumptions: &PureFactContext,
) -> bool {
    use crate::kernel::api::contract_certification::c_memories_definitionally_equal;
    let mut effects = effects
        .fact_iter()
        .filter_map(|fact| match fact.proposition() {
            Proposition::CMemoryMutatesOnly { before, after, .. }
            | Proposition::CMemoryEffectSummary { before, after, .. }
            | Proposition::CHeapAllocationFreed { before, after, .. } => Some((before, after)),
            _ => None,
        })
        .peekable();
    for step in steps.iter().filter(|step| step.may_write) {
        if let Some(count) = step.statement_effects {
            // The recorder that checked this statement appended exactly
            // these effects, in this order.
            if effects.by_ref().take(count).count() != count {
                return false;
            }
            continue;
        }
        let mut memory = &step.before;
        while memory != &step.after {
            if let Some((_, after)) = effects.next_if(|(before, _)| *before == memory) {
                memory = after;
            } else if c_memories_definitionally_equal(memory, &step.after, assumptions) {
                break;
            } else if let Some((_, after)) = effects
                .next_if(|(before, _)| c_memories_definitionally_equal(memory, before, assumptions))
            {
                memory = after;
            } else {
                return false;
            }
        }
    }
    effects.next().is_none()
}

fn checked_interface_effect_facts_along(
    split_state: &CState,
    joined_state: &CState,
    arms: [&ExecutionProofCore; 2],
    arm_facts: [&ProofFacts; 2],
    arm_effect_facts: [&(impl ExecutionFactSource + ?Sized); 2],
    arm_memory_steps: Option<[&[CheckedMemoryStep]; 2]>,
) -> Result<crate::kernel::ExecutionFacts, &'static str> {
    let mut writes = Vec::new();
    let mut ranges = Vec::new();
    let mut heap_frees = [Vec::new(), Vec::new()];
    for arm_index in 0..2 {
        let assumptions = arm_facts[arm_index].assumptions();
        // When the arm's walk vouches for the chain, the effects are read
        // for what they cover and are not chained a second time.
        let chained = arm_memory_steps.is_some_and(|steps| {
            arm_effects_follow_memory_steps(
                steps[arm_index],
                arm_effect_facts[arm_index],
                assumptions,
            )
        });
        let mut memory = split_state.memory().clone();
        for fact in arm_effect_facts[arm_index].fact_iter() {
            match fact.proposition() {
                Proposition::CMemoryMutatesOnly {
                    before,
                    after,
                    writes: changed,
                } => {
                    if !fact.is_certified() {
                        return Err("an interface arm contains an uncertified memory effect");
                    }
                    if !chained && !interface_chain_memory_matches(&memory, before, assumptions) {
                        return Err(
                            "an interface arm effect chain does not start at its current memory",
                        );
                    }
                    if !fact.is_join_summary()
                        && !memory_diff_is_covered_by_writes(
                            before,
                            after,
                            changed,
                            assumptions,
                            fact,
                        )
                    {
                        return Err(
                            "an interface arm memory effect does not cover its memory diff",
                        );
                    }
                    memory = after.clone();
                    for pointer in changed {
                        if !writes.contains(pointer) {
                            writes.push(pointer.clone());
                        }
                    }
                }
                Proposition::CMemoryEffectSummary {
                    before,
                    after,
                    mutable_ranges,
                } => {
                    if !fact.is_certified() {
                        return Err("an interface arm contains an uncertified memory effect");
                    }
                    if !chained && !interface_chain_memory_matches(&memory, before, assumptions) {
                        return Err(
                            "an interface arm effect summary does not start at its current memory",
                        );
                    }
                    if !fact.is_join_summary()
                        && !memory_diff_is_covered_by_ranges(
                            before,
                            after,
                            mutable_ranges,
                            assumptions,
                        )
                    {
                        return Err(
                            "an interface arm memory effect does not cover its memory diff",
                        );
                    }
                    memory = after.clone();
                    for range in mutable_ranges {
                        if !ranges.contains(range) {
                            ranges.push(range.clone());
                        }
                    }
                }
                Proposition::CHeapAllocationFreed {
                    before,
                    after,
                    allocation_base,
                    bytes,
                } => {
                    if !chained && !interface_chain_memory_matches(&memory, before, assumptions) {
                        return Err(
                            "an interface heap-free effect does not start at its current memory",
                        );
                    }
                    memory = after.clone();
                    heap_frees[arm_index].push((
                        allocation_base.clone(),
                        bytes.clone(),
                        after.clone(),
                    ));
                }
                _ if fact.is_certified() => {}
                _ => return Err("an interface arm contains unchecked effect metadata"),
            }
        }
        if !chained
            && !interface_chain_memory_matches(&memory, arms[arm_index].state.memory(), assumptions)
        {
            return Err("an interface arm effect chain does not reach its recorded memory");
        }
    }

    if writes.is_empty() && ranges.is_empty() {
        if heap_frees[0] == heap_frees[1] && !heap_frees[0].is_empty() {
            let facts = heap_frees[0]
                .iter()
                .map(|(allocation_base, bytes, after)| {
                    ExecutionPureFact::certified(Proposition::CHeapAllocationFreed {
                        before: split_state.memory().clone(),
                        after: after.clone(),
                        allocation_base: allocation_base.clone(),
                        bytes: bytes.clone(),
                    })
                })
                .collect::<Vec<_>>();
            return Ok(facts.into());
        }
        return Ok(common_non_memory_effect_facts(arm_effect_facts));
    }
    let proposition = if ranges.is_empty() {
        Proposition::CMemoryMutatesOnly {
            before: split_state.memory().clone(),
            after: joined_state.memory().clone(),
            writes,
        }
    } else {
        for (pointer, bytes) in writes {
            let range = CMemoryRange::new_with_element_width(
                pointer,
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
                bytes,
            );
            if !ranges.contains(&range) {
                ranges.push(range);
            }
        }
        Proposition::CMemoryEffectSummary {
            before: split_state.memory().clone(),
            after: joined_state.memory().clone(),
            mutable_ranges: ranges,
        }
    };
    let mut facts = vec![ExecutionPureFact::certified_join_summary(proposition)];
    facts.extend(common_non_memory_effect_facts(arm_effect_facts));
    Ok(facts.into())
}

fn conditional_heap_frees(
    arm_effect_facts: [&(impl ExecutionFactSource + ?Sized); 2],
) -> [Vec<(Pointer, Bitvector32Term)>; 2] {
    std::array::from_fn(|arm_index| {
        arm_effect_facts[arm_index]
            .fact_iter()
            .filter_map(|fact| match fact.proposition() {
                Proposition::CHeapAllocationFreed {
                    allocation_base,
                    bytes,
                    ..
                } => Some((allocation_base.clone(), bytes.clone())),
                _ => None,
            })
            .collect()
    })
}

fn interface_resources_guard_heap_frees(
    function: &CFunction,
    arm_resources: &[Vec<CResourceFact>; 2],
    arm_states: [&CState; 2],
    arm_facts: [&ProofFacts; 2],
    heap_frees: &[Vec<(Pointer, Bitvector32Term)>; 2],
) -> bool {
    let has_allocation = |arm_index: usize, base: &Pointer, bytes: &Bitvector32Term| {
        arm_resources[arm_index].iter().any(|resource| {
            if resource
                .allocation()
                .is_some_and(|(candidate_base, candidate_bytes)| {
                    candidate_base == base && candidate_bytes == bytes
                })
            {
                return true;
            }
            if !resource.is_own() || !matches!(resource.resource(), CResource::Composite { .. }) {
                return false;
            }
            crate::kernel::functions::expand_composite_resource_fact(
                &ResourceContext::new_with_equalities(arm_facts[arm_index].assumptions())
                    .unchecked_with_fact(resource.clone()),
                resource,
                function.composite_resource_definitions(),
                arm_states[arm_index].memory(),
                arm_facts[arm_index].assumptions(),
            )
            .is_some_and(|expanded| {
                expanded.facts().iter().any(|fact| {
                    fact.allocation()
                        .is_some_and(|(candidate_base, candidate_bytes)| {
                            candidate_base == base && candidate_bytes == bytes
                        })
                })
            })
        })
    };

    if heap_frees[0] == heap_frees[1] {
        return true;
    }
    if heap_frees[0].is_empty() == heap_frees[1].is_empty() {
        return false;
    }
    let freed_arm = usize::from(heap_frees[0].is_empty());
    heap_frees[freed_arm].iter().all(|(base, bytes)| {
        !has_allocation(freed_arm, base, bytes) && has_allocation(1 - freed_arm, base, bytes)
    })
}

fn common_non_memory_effect_facts(
    arm_effect_facts: [&(impl ExecutionFactSource + ?Sized); 2],
) -> crate::kernel::ExecutionFacts {
    arm_effect_facts[0]
        .fact_iter()
        .filter(|fact| {
            fact.is_certified()
                && !matches!(
                    fact.proposition(),
                    Proposition::CMemoryMutatesOnly { .. }
                        | Proposition::CMemoryEffectSummary { .. }
                        | Proposition::CHeapAllocationFreed { .. }
                )
                && arm_effect_facts[1].fact_iter().any(|other| other == *fact)
        })
        .cloned()
        .collect()
}

fn interface_spec_paths(
    spec: &SpecProposition,
    state: &CState,
    reference_state: &CState,
    assumptions: &PureFactContext,
) -> Option<Vec<crate::kernel::spec::SpecPropositionPath>> {
    let mut paths = crate::kernel::spec::lower_spec_proposition_at_state_with_loop_entry(
        state,
        spec,
        Some(reference_state),
        assumptions,
        &mut ExecutionBudget::beside_live_state(),
    )
    .ok()?;
    for path in &mut paths {
        // Producer-derived read equations are local consequences of this
        // lowering, not interface requirements. Do not export them from an
        // arm or ask the other arm or abstract successor to establish them.
        path.facts.retain(|fact| !fact.is_logical_read_equation());
    }
    Some(paths)
}

fn evaluate_interface_resource_spec(
    spec: &CResourceSpec,
    state: &CState,
    facts: &ProofFacts,
) -> Option<CResourceFact> {
    (crate::kernel::functions::evaluate_function_resource_spec(
        state,
        spec,
        facts.assumptions(),
        &mut ExecutionBudget::beside_live_state(),
    )
    .ok()?)
    .ok()
}

fn interface_resource_intrinsic_fact(
    spec: &CResourceSpec,
    resource: &CResourceFact,
    state: &CState,
) -> Option<Proposition> {
    let segment = spec.memory_segment()?;
    let range = resource.memory_range()?;
    (segment.element_width() == range.element_width()).then(|| range.loadable_fact(state.memory()))
}

/// The selected kernel lowering and the precise context in which it passed
/// the local proof rules. Every value, generated fact, and safety obligation
/// has a completed proof rooted in these exact premises. Load definitions
/// use their kernel origin, not a contextual proof search.
#[derive(Clone)]
struct CheckedInterfaceLowering {
    spec: Arc<SpecProposition>,
    snapshot: CState,
    reference: CState,
    facts: ProofFacts,
    path: Arc<crate::kernel::spec::SpecPropositionPath>,
    proofs: Arc<Vec<super::CheckedProposition>>,
}

/// What an arm was found not to hold when an interface fact was refused:
/// which interface fact, in which arm, and the goal that was not there, the
/// fact itself or a condition its terms need to denote a value.
#[derive(Clone)]
pub(crate) struct UnestablishedInterfaceGoal {
    pub(crate) fact: usize,
    pub(crate) arm: usize,
    pub(crate) goal: Proposition,
    pub(crate) side_condition: bool,
}

thread_local! {
    static UNESTABLISHED_INTERFACE_GOAL: std::cell::RefCell<Option<UnestablishedInterfaceGoal>> =
        const { std::cell::RefCell::new(None) };
}

/// The goal the last refused interface fact was missing, for a diagnostic.
/// It carries no authority: the refusal stands whatever this says.
pub(crate) fn take_unestablished_interface_goal() -> Option<UnestablishedInterfaceGoal> {
    UNESTABLISHED_INTERFACE_GOAL.with(|unestablished| unestablished.borrow_mut().take())
}

impl CheckedInterfaceLowering {
    fn has_complete_proof(&self) -> bool {
        let expected = std::iter::once(&self.path.proposition)
            .chain(self.path.facts.iter().map(ExecutionPureFact::proposition))
            .chain(
                self.path
                    .obligations
                    .iter()
                    .map(crate::kernel::ProofObligation::proposition),
            );
        self.proofs.len() == 1 + self.path.facts.len() + self.path.obligations.len()
            && expected.zip(self.proofs.iter()).all(|(goal, proof)| {
                crate::instrumentation::record_deterministic_work(1);
                goal == proof.proposition()
            })
    }

    fn check(
        spec: &SpecProposition,
        state: &CState,
        reference_state: &CState,
        facts: &ProofFacts,
        access: &InterfaceReadPremises,
    ) -> Option<Self> {
        let assumptions = facts
            .assumptions()
            .clone()
            .defer_non_exact_condition_reasoning()
            .defer_non_exact_loadability_obligations();
        Self::check_in(spec, state, reference_state, facts, access, &assumptions)
    }

    fn check_in(
        spec: &SpecProposition,
        state: &CState,
        reference_state: &CState,
        facts: &ProofFacts,
        access: &InterfaceReadPremises,
        assumptions: &PureFactContext,
    ) -> Option<Self> {
        // Concrete reads use this arm's checked aliases. The abstract
        // successor instead retains the state-only exported spelling.
        // Lowering grants no authority: check each resulting fact and
        // safety obligation against the exact retained context below.
        let paths = interface_spec_paths(spec, state, reference_state, assumptions)?;
        paths.into_iter().find_map(|path| {
            crate::instrumentation::record_deterministic_work(1);
            let prove =
                |goal: &Proposition, definition: Option<&CheckedInterfaceLoadDefinition>| {
                    use super::{
                        OutcomeProofState, ProofBranch, ProofBranchState, ProofObject,
                        ProofObligation, PropositionObligation,
                    };
                    type Leaf =
                        ProofObject<(), ProofObligation<(), Arc<OutcomeProofState<()>>>, ()>;
                    let read_premise = access.for_goal(goal);
                    let root_facts = read_premise
                        .map_or_else(|| facts.clone(), |premise| facts.with_fact(premise.clone()));
                    let root = Leaf::root(
                        (),
                        ProofBranch::new(
                            ProofObligation::Proposition(PropositionObligation::new(
                                goal.clone(),
                                (),
                            )),
                            ProofBranchState {
                                facts: root_facts,
                                unfolded_predicates: Default::default(),
                                execution: None,
                            },
                        ),
                    );
                    let closed = root.apply_interface_leaf(definition, read_premise)?;
                    closed.completed_proposition()
                };
            // A goal the arm does not hold is noted for the refusal's
            // report: the fact itself, or something its terms need.
            let missing = |goal: &Proposition, side_condition: bool| {
                UNESTABLISHED_INTERFACE_GOAL.with(|unestablished| {
                    *unestablished.borrow_mut() = Some(UnestablishedInterfaceGoal {
                        fact: 0,
                        arm: 0,
                        goal: goal.clone(),
                        side_condition,
                    });
                });
            };
            let Some(proved) = prove(&path.proposition, None) else {
                missing(&path.proposition, false);
                return None;
            };
            let mut proofs = vec![proved];
            for fact in &path.facts {
                let definition = CheckedInterfaceLoadDefinition::check(fact.proposition());
                let Some(proved) = prove(fact.proposition(), definition.as_ref()) else {
                    missing(fact.proposition(), true);
                    return None;
                };
                proofs.push(proved);
            }
            for obligation in &path.obligations {
                let Some(proved) = prove(obligation.proposition(), None) else {
                    missing(obligation.proposition(), true);
                    return None;
                };
                proofs.push(proved);
            }
            Some(Self {
                spec: Arc::new(spec.clone()),
                snapshot: state.clone(),
                reference: reference_state.clone(),
                facts: facts.clone(),
                path: Arc::new(path),
                proofs: Arc::new(proofs),
            })
        })
    }
}

/// An index over the explicitly exported, already ownership-checked resource
/// clauses. Building it is output-sized; no ambient resource/fact scan occurs
/// per interface judgment. Equal bases retain the largest constant extent.
#[derive(Default)]
struct InterfaceReadPremises {
    by_base: std::collections::BTreeMap<
        (crate::kernel::CMemory, crate::kernel::Pointer),
        (u32, Proposition),
    >,
}

impl InterfaceReadPremises {
    fn new(premises: impl IntoIterator<Item = Proposition>) -> Self {
        let mut index = Self::default();
        for premise in premises {
            crate::instrumentation::record_deterministic_work(1);
            let Proposition::CMemoryLoadable {
                memory,
                base,
                bytes,
                wide: false,
            } = &premise
            else {
                continue;
            };
            let Some(width) = bytes.as_const() else {
                continue;
            };
            let key = (memory.clone(), base.clone());
            if index.by_base.get(&key).is_none_or(|(old, _)| *old < width) {
                index.by_base.insert(key, (width, premise));
            }
        }
        index
    }

    fn for_goal(&self, goal: &Proposition) -> Option<&Proposition> {
        let Proposition::CMemoryLoadable { memory, base, .. } = goal else {
            return None;
        };
        crate::instrumentation::record_deterministic_work(1);
        self.by_base
            .get(&(memory.clone(), base.clone()))
            .map(|(_, premise)| premise)
    }
}

pub(super) fn interface_read_is_subrange(goal: &Proposition, premise: &Proposition) -> bool {
    let (
        Proposition::CMemoryLoadable {
            memory,
            base,
            bytes,
            wide: false,
        },
        Proposition::CMemoryLoadable {
            memory: source_memory,
            base: source_base,
            bytes: source_bytes,
            wide: false,
        },
    ) = (goal, premise)
    else {
        return false;
    };
    memory == source_memory
        && base == source_base
        && bytes
            .as_const()
            .zip(source_bytes.as_const())
            .is_some_and(|(width, source_width)| width <= source_width)
}

/// An exact registered load identity. The witness cannot be supplied by the
/// surface or inferred merely from a reserved variable's spelling.
pub(super) struct CheckedInterfaceLoadDefinition {
    proposition: Proposition,
}

impl CheckedInterfaceLoadDefinition {
    fn check(proposition: &Proposition) -> Option<Self> {
        let Proposition::ConditionIs(
            crate::kernel::ConditionTerm::Bitvector32Equal(left, right),
            true,
        ) = proposition
        else {
            return None;
        };
        let (Bitvector32Term::Variable(variable), load @ Bitvector32Term::MemoryLoad(_, _, _)) =
            (left.as_ref(), right.as_ref())
        else {
            return None;
        };
        // The registered load, kind included, is the definition.
        let defined = crate::kernel::registered_load_term_for_variable(variable)?;
        (&defined == load).then(|| Self {
            proposition: proposition.clone(),
        })
    }

    /// Exact equality against the one load definition this record carries.
    /// Named so the package 15 `\.proves(` audit grep over `src/kernel/`
    /// does not have to distinguish it from the relocated prover.
    pub(super) fn matches_goal_exactly(&self, goal: &Proposition) -> bool {
        &self.proposition == goal
    }
}

/// One path retained from a complete kernel C-condition evaluation.
#[derive(Clone)]
pub(crate) struct CheckedBranchPath {
    outcome: CConditionOutcome,
    facts: crate::kernel::ExecutionFacts,
    obligations: Vec<crate::kernel::ProofObligation>,
    theorem: Theorem,
}

impl CheckedBranchPath {
    pub(crate) fn outcome(&self) -> &CConditionOutcome {
        &self.outcome
    }

    pub(crate) fn facts(&self) -> &crate::kernel::ExecutionFacts {
        &self.facts
    }

    pub(crate) fn obligations(&self) -> &[crate::kernel::ProofObligation] {
        &self.obligations
    }

    pub(crate) fn theorem(&self) -> &Theorem {
        &self.theorem
    }
}

/// Kernel-issued complete evaluation of one C branch condition at one exact
/// checked proof-fact root.
///
/// This retains every symbolic path, including paths later proved infeasible
/// and error outcomes. Only [`Self::validates_exhaustive_join`] converts it
/// into arm-coverage authority, after checking the original state, condition,
/// fact root, path prerequisites, and one-for-one feasible theorem coverage.
#[derive(Clone)]
pub(crate) struct CheckedBranchSplit {
    state: CState,
    branch_statement: CStatement,
    continuation: Option<CStatement>,
    condition: CExpression,
    root_facts: ProofFacts,
    paths: Vec<CheckedBranchPath>,
}

pub(crate) enum CheckedBranchSplitError {
    Limit(ExecutionLimit),
    InvalidEvidence,
}

/// A complete, kernel-checked direct call with exactly one feasible normal
/// successor and one feasible exceptional successor. Individual statement
/// theorems prove each arm; this witness proves that neither arm was omitted.
/// Its source and fact root are exact, so it cannot authorize a fork at a
/// different call or after the proof context has changed.
#[derive(Clone)]
pub(crate) struct CheckedCallOutcomeSplit {
    state: CState,
    statement: CStatement,
    root_facts: ProofFacts,
    normal: CStatementOutcome,
    exceptional: CStatementOutcome,
}

#[derive(Debug)]
pub(crate) enum CheckedCallOutcomeSplitError {
    InvalidEvidence,
}

impl CheckedCallOutcomeSplit {
    /// Builds the exhaustive call-outcome witness from the two transitions
    /// already certified by the statement evaluator.  This is deliberately
    /// not another evaluator entry point: the caller has retained the
    /// evaluator's complete two-transition result and supplies both checked
    /// theorem conclusions here.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn from_certified_transitions(
        state: CState,
        statement: CStatement,
        root_facts: &ProofFacts,
        normal_theorem: &Theorem,
        normal: &CStatementOutcome,
        normal_path_facts: &[Proposition],
        normal_obligations: &[crate::kernel::ProofObligation],
        exceptional_theorem: &Theorem,
        exceptional: &CStatementOutcome,
        exceptional_path_facts: &[Proposition],
        exceptional_obligations: &[crate::kernel::ProofObligation],
    ) -> Result<Self, CheckedCallOutcomeSplitError> {
        if !matches!(
            statement,
            CStatement::Call { .. } | CStatement::CallAssign { .. }
        ) || !matches!(normal, CStatementOutcome::Normal(_))
            || !matches!(exceptional, CStatementOutcome::Throw { .. })
        {
            return Err(CheckedCallOutcomeSplitError::InvalidEvidence);
        }
        let validates_arm =
            |theorem: &Theorem,
             expected: &CStatementOutcome,
             path_facts: &[Proposition],
             obligations: &[crate::kernel::ProofObligation]| {
                let Proposition::CStatementVerifies {
                    state: proved_state,
                    statement: proved_statement,
                    outcome,
                } = crate::kernel::api::proof_evidence_conclusion(theorem)
                else {
                    return false;
                };
                if **proved_state != state
                    || **proved_statement != statement
                    || outcome != expected
                    || path_facts
                        .iter()
                        .any(|fact| root_facts.directly_conflicts_with(fact))
                {
                    return false;
                }
                let mut facts = root_facts.clone();
                for fact in path_facts {
                    facts = facts.with_kernel_checked_fact(fact.clone());
                }
                obligations.iter().all(|obligation| {
                    checked_branch_fact_is_available(&facts, obligation.proposition())
                })
            };
        if !validates_arm(
            normal_theorem,
            normal,
            normal_path_facts,
            normal_obligations,
        ) || !validates_arm(
            exceptional_theorem,
            exceptional,
            exceptional_path_facts,
            exceptional_obligations,
        ) {
            return Err(CheckedCallOutcomeSplitError::InvalidEvidence);
        }
        Ok(Self {
            state,
            statement,
            root_facts: root_facts.clone(),
            normal: normal.clone(),
            exceptional: exceptional.clone(),
        })
    }

    pub(crate) fn validates(
        &self,
        state: &CState,
        statement: &CStatement,
        root_facts: &ProofFacts,
        normal: &Theorem,
        exceptional: &Theorem,
    ) -> bool {
        if &self.state != state
            || &self.statement != statement
            || !self
                .root_facts
                .introduced_since(root_facts)
                .is_some_and(|delta| delta.is_empty())
            || !root_facts
                .introduced_since(&self.root_facts)
                .is_some_and(|delta| delta.is_empty())
        {
            return false;
        }
        [
            (normal, &self.normal),
            (exceptional, &self.exceptional),
        ]
        .iter()
        .all(|(theorem, expected)| {
            matches!(
                crate::kernel::api::proof_evidence_conclusion(theorem),
                Proposition::CStatementVerifies {
                    state: proved_state,
                    statement: proved_statement,
                    outcome,
                } if **proved_state == *state && **proved_statement == *statement && outcome == *expected
            )
        })
    }
}

impl CheckedBranchSplit {
    pub(crate) fn check(
        state: CState,
        branch_statement: CStatement,
        continuation: Option<CStatement>,
        root_facts: &ProofFacts,
    ) -> Result<Self, CheckedBranchSplitError> {
        let CStatement::If { condition, .. } = &branch_statement else {
            return Err(CheckedBranchSplitError::InvalidEvidence);
        };
        let condition = condition.clone();
        let evaluation = crate::kernel::prove_symbolic_c_condition_evaluation(
            state.clone(),
            condition.clone(),
            root_facts.assumptions().clone(),
        );
        if let Some(limit) = evaluation.limit() {
            return Err(CheckedBranchSplitError::Limit(limit));
        }
        let paths = evaluation
            .paths()
            .iter()
            .filter_map(|path| {
                let mut conclusion = path.theorem().proposition();
                while let Proposition::Implies(_, body) = conclusion {
                    conclusion = body;
                }
                let Proposition::CConditionEvaluates {
                    state: proved_state,
                    condition: proved_condition,
                    outcome,
                } = conclusion
                else {
                    return None;
                };
                if **proved_state != state || proved_condition != &condition {
                    return None;
                }
                Some(CheckedBranchPath {
                    outcome: outcome.clone(),
                    facts: path.facts().clone(),
                    obligations: path.obligations().to_vec(),
                    theorem: path.theorem().clone(),
                })
            })
            .collect::<Vec<_>>();
        if paths.len() != evaluation.paths().len() {
            return Err(CheckedBranchSplitError::InvalidEvidence);
        }
        Ok(Self {
            state,
            branch_statement,
            continuation,
            condition,
            root_facts: root_facts.clone(),
            paths,
        })
    }

    pub(crate) fn paths(&self) -> &[CheckedBranchPath] {
        &self.paths
    }

    fn has_exact_root(&self, root_facts: &ProofFacts) -> bool {
        self.root_facts
            .introduced_since(root_facts)
            .is_some_and(|delta| delta.is_empty())
            && root_facts
                .introduced_since(&self.root_facts)
                .is_some_and(|delta| delta.is_empty())
    }

    pub(crate) fn validates_exhaustive_join(
        &self,
        state: &CState,
        condition: &CExpression,
        root_facts: &ProofFacts,
        arm_theorems: [Option<&Theorem>; 2],
        arm_facts: [Option<&ProofFacts>; 2],
    ) -> bool {
        if &self.state != state || &self.condition != condition || !self.has_exact_root(root_facts)
        {
            return false;
        }
        let mut required = [None, None];
        for path in &self.paths {
            let infeasible = path
                .facts
                .iter()
                .any(|fact| root_facts.directly_conflicts_with(fact.proposition()));
            if infeasible {
                continue;
            }
            let CConditionOutcome::Value(value) = path.outcome else {
                return false;
            };
            let arm_index = usize::from(!value);
            let Some(arm_facts) = arm_facts[arm_index] else {
                return false;
            };
            if arm_facts.introduced_since(root_facts).is_none()
                || path
                    .facts
                    .iter()
                    .any(|fact| !arm_facts.contains(fact.proposition()))
                || path.obligations.iter().any(|obligation| {
                    !checked_branch_fact_is_available(arm_facts, obligation.proposition())
                })
            {
                return false;
            }
            let slot = &mut required[arm_index];
            if slot.replace(&path.theorem).is_some() {
                return false;
            }
        }
        required == arm_theorems
    }
}

/// One checked execution path's current semantic frontier.
#[derive(Clone, Default)]
pub(crate) struct ExecutionFrontier {
    pub(crate) position: FrontierPosition,
    pub(crate) region: ExecutionRegionKind,
    pub(crate) execution_start_state: Option<CState>,
    /// A checked member exchange or proof interface has materialized the
    /// function entry before its first C statement. The first step must use
    /// that checked successor instead of binding the arguments again.
    pub(crate) entry_member_prefix: bool,
    pub(crate) next_statement_index: usize,
    pub(crate) continuations: PersistentSequence<ProofExecutionContinuation>,
    /// Whether this frontier executes inside one loop-body region, directly
    /// or through a bounded branch arm of it. A `break` or `continue` here
    /// belongs to that loop, which no continuation of this frontier holds:
    /// the enclosing loop rule consumes it at the region boundary.
    pub(crate) in_loop_body: bool,
    /// How this path reached the loop body's boundary, once it has.
    pub(crate) loop_control: LoopControlExit,
    /// A proof-only natural cycle's source back edge, when this frontier is
    /// executing that loop body. Matching `goto` evidence reaches the typed
    /// body boundary instead of reopening the source target.
    pub(crate) natural_backedge_target: Option<crate::kernel::CControlTargetId>,
    /// A proof-only natural cycle's checked forward exit, when this frontier
    /// is executing that loop body.
    pub(crate) natural_exit_target: Option<crate::kernel::CControlTargetId>,
}

impl ExecutionFrontier {
    /// Whether two frontiers that split from one stand at the same program
    /// point: the same statement to run next, in the same region, with the
    /// same enclosing continuations still owed.
    pub(crate) fn at_same_program_point(&self, other: &Self) -> bool {
        self.region == other.region
            && self.entry_member_prefix == other.entry_member_prefix
            && self.next_statement_index == other.next_statement_index
            && self.in_loop_body == other.in_loop_body
            && self.loop_control == other.loop_control
            && self.natural_backedge_target == other.natural_backedge_target
            && self.natural_exit_target == other.natural_exit_target
            && self.continuations.len() == other.continuations.len()
            && match (&self.position, &other.position) {
                (FrontierPosition::FunctionEntry, FrontierPosition::FunctionEntry)
                | (FrontierPosition::RegionBoundary, FrontierPosition::RegionBoundary) => true,
                (
                    FrontierPosition::StatementEntry { remaining: left },
                    FrontierPosition::StatementEntry { remaining: right },
                ) => Arc::ptr_eq(left, right) || left == right,
                _ => false,
            }
    }
}

/// One entered `try` body tracked for evidence order validation: the
/// handler to resume at if unwinding reaches it, and the source tail after
/// the `try` for normal completion.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct EvidenceTryFrame {
    pub(crate) binding: String,
    pub(crate) handler: Arc<CStatement>,
    pub(crate) tail_after_try: Option<Arc<CStatement>>,
    pub(crate) cleanup_unwind: bool,
}

#[derive(Clone)]
pub(crate) struct ProofExecutionContinuation {
    pub(crate) remaining: Option<Arc<CStatement>>,
    pub(crate) next_statement_index: usize,
    /// The source statement index immediately after the loop. A `break`
    /// consumes the loop continuation and resumes here; `continue` resumes
    /// at `next_statement_index`, the loop head itself.
    pub(crate) loop_exit_statement_index: usize,
    /// The exceptional successor of an entered `try` body. On a `Throw`
    /// outcome while this continuation is on top, the path abandons its
    /// remaining statements and resumes at the handler entry with the
    /// payload bound. Normal completion pops this continuation like any
    /// other, discarding the handler without running it.
    pub(crate) exceptional: Option<ExceptionalContinuation>,
}

/// The handler a `Throw` inside an entered `try` body resumes at. Only the
/// typed C++ frontend produces `TryCatchInt32`, so C execution never
/// carries one of these.
#[derive(Clone)]
pub(crate) struct ExceptionalContinuation {
    pub(crate) binding: String,
    pub(crate) handler: Arc<CStatement>,
    pub(crate) handler_first_index: usize,
    pub(crate) cleanup_unwind: bool,
}

/// A returned path of a summarized loop, already checked while the loop's
/// continuing successor keeps advancing.
///
/// The trace forks from the open trace at the loop statement and completes
/// with the loop rule's `Return` theorem; it is appended to the completed
/// trace set only at the function boundary. The outcome and facts are the
/// candidate the surface publishes for it there, and `pure_facts` is the
/// proof's fact base on that path: the facts available at the loop plus the
/// returned path's own, so nothing established after the loop on the
/// continuing path is cited on it.
#[derive(Clone)]
pub(crate) struct PendingLoopReturnPath {
    /// Position among the return outcomes exported by this loop rule.
    pub(crate) return_index: usize,
    trace: PersistentSequence<CheckedExecutionEvent>,
    /// The source loop whose rule returned this path, for the point its
    /// premises are read at.
    pub(crate) loop_index: Option<usize>,
    pub(crate) outcome: CFunctionOutcome,
    pub(crate) execution_facts: ExecutionFacts,
    pub(crate) obligations: Vec<crate::kernel::ProofObligation>,
    pub(crate) pure_facts: ProofFacts,
    pub(crate) loan_evidence: crate::kernel::loans::CheckedLoanCallEvidenceSequence,
}

/// Surface-independent execution state owned by a checked proof branch.
///
/// Language lowering and certificate capture wrap this value with their own
/// path-local records. The kernel core contains only C state, checked facts
/// and rules, typed frontier state, and semantic freshness/region flags.
#[derive(Clone)]
pub(crate) struct ExecutionProofCore {
    pub(crate) state: SharedValue<CState>,
    initial_match_scope: SharedValue<CState>,
    /// Context of the logical frontier cases admitted by the kernel, in
    /// split order. Forks share the prefix; a join restores the parent's.
    /// Other case producers use the ordinary local-context construction.
    checked_step_cases: (usize, PureFactContext),
    /// The admitted case delta, shared by every returned descendant. Retain
    /// it at the split, before terminal joins could copy it into every path.
    publication_case_facts: ExecutionFacts,
    /// Every variable `initial_match_scope` mentions, built once and shared by
    /// every branch forked from this region. A constructor witness introduced
    /// anywhere in the region must avoid these; everything the kernel has
    /// issued since lies in this execution's issued range, which the same
    /// freshness probe checks without a second scan.
    initial_match_reserved: Arc<std::sync::OnceLock<std::collections::BTreeSet<Variable>>>,
    /// The state the retained evidence has reached on the open trace: the
    /// outcome of the last recorded theorem, observation, rewrite, or
    /// join. `None` until the first is recorded, when the theorem starts
    /// from the function entry bound from `state`. Once set, the checks
    /// read this and never `state`: the chain is validated from the
    /// theorems alone.
    pub(crate) evidence_state: Option<CState>,
    /// The open trace has completed with a returning or diverging theorem
    /// or an outcome fork; only post-execution case arms may follow.
    pub(crate) evidence_completed: bool,
    /// The source the retained evidence has yet to consume, advanced with
    /// each recorded theorem or join: a statement's tail, a condition's
    /// selected arm (or loop body followed by the loop head) before the
    /// tail. Meaningful once `evidence_state` is set; `None` then means
    /// the source is exhausted. Checks read this and never the driver's
    /// frontier once it is set.
    pub(crate) evidence_source: Option<Arc<CStatement>>,
    /// Entered `try` bodies the evidence chain is descending into, innermost
    /// last. Pushed when an interior theorem is accepted against a `Try`
    /// head, popped when the body completes normally (offered matches the
    /// tail) or when handler entry is accepted. Only the typed C++ frontend
    /// produces `TryCatchInt32`, so C evidence never carries one of these.
    /// Each entry is derived solely from validated theorems and expected
    /// source, never from driver-provided pushes.
    pub(crate) evidence_try_stack: Vec<EvidenceTryFrame>,
    pub(crate) frontier: ExecutionFrontier,
    pub(crate) effect_facts: ExecutionFacts,
    /// One append-only evidence trace per operational outcome represented by
    /// this frontier. Ordinary in-flight execution has one trace; a single C
    /// operation with several return outcomes can complete several traces at
    /// once. Forked proofs share every unchanged trace prefix.
    pub(crate) execution_evidence:
        super::PersistentVector<PersistentSequence<CheckedExecutionEvent>>,
    /// Returned paths of summarized loops, already proved while each loop's
    /// continuing successor keeps advancing. They are appended to the
    /// completed trace set only at the function boundary, so ordinary
    /// frontier operations still own exactly one active trace and never
    /// mutate a terminal sibling. Once appended, `pending_loop_return_start`
    /// says where they begin among this execution's paths.
    pending_loop_returns: PersistentSequence<PendingLoopReturnPath>,
    completed_pending_loop_returns: Option<Arc<Vec<PendingLoopReturnPath>>>,
    pending_loop_return_start: Option<usize>,
    /// Stable-view call evidence retained along the focused execution path.
    /// This is kept beside the checked event trace so loop planning can pass
    /// the exact path evidence into its exit candidates.
    pub(crate) loan_evidence: crate::kernel::loans::CheckedLoanCallEvidenceSequence,
    /// One kernel publication shared by post-return proofs on each path.
    return_proof_contexts: crate::persistent::PersistentMap<usize, Arc<CheckedReturnContext>>,
    /// Completed pure proofs awaiting a resource exchange that needs them.
    return_pending_propositions: crate::persistent::PersistentMap<
        usize,
        PersistentSequence<(super::CheckedProposition, ProofFacts)>,
    >,
    /// Post-return exchanges indexed by the selected outcome. Forking a
    /// focused outcome must not copy or modify its sibling traces.
    return_resource_rewrites:
        crate::persistent::PersistentMap<usize, PersistentSequence<CheckedExecutionEvent>>,
    /// Events on the current unjoined path. A branch join restores its
    /// parent's set; finalization collects all retained arm events by walking
    /// the output trace once.
    checked_call_events: CheckedCallEvents,
    pub(crate) function_entry: Option<Arc<CheckedFunctionEntry>>,
    /// The proof's facts at the checked entry, whose context the entry was
    /// checked under. A retained return proof's facts descend from it, so
    /// completion checks only what the proof introduced since.
    entry_facts: Option<ProofFacts>,
    pub(crate) frontier_loop_rules: PersistentSequence<CVerifiedLoopRule>,
    pub(crate) execution_abstraction: bool,
    pub(crate) concrete_loop_execution: bool,
    /// Kernel theorems whose conclusions justify the facts a resource
    /// observation introduces (its count and quantity witnesses).
    pub(crate) function_entry_derivations: PersistentOrderedSet<Theorem>,
    pub(crate) region_invariants_close_requested: bool,
    /// Complete lowerings prepared for this exact execution and premise store.
    pub(crate) checked_invariant_lowerings: Option<Arc<CheckedLoopInvariantLowerings>>,
    pub(crate) next_opaque_call: u64,
    /// This execution's one fresh-variable counter, as an offset from
    /// [`ExecutionBudget::KERNEL_VARIABLE_BASE`] -- the representation
    /// [`ExecutionBudget::continuing_from`] takes and
    /// [`ExecutionBudget::next_kernel_variable`] returns. Every identity the
    /// kernel has issued for this execution lies below it.
    ///
    /// The field is private on purpose: within one execution the counter only
    /// moves forward, and only the kernel moves it. A caller reads it with
    /// [`Self::kernel_variable_mark`] and can only move it with
    /// [`Self::advance_kernel_variable_mark`], which refuses a rewind. A
    /// rewound counter re-issues an identity something live still carries,
    /// which is a false-theorem hazard, not merely wasted identities.
    next_kernel_variable: u64,
    pub(crate) has_empty_execution_branch_leaf: bool,
    pub(crate) has_structured_branch_history: bool,
    pub(crate) unfolded_predicates: SharedVec<String>,
}

#[cfg_attr(test, derive(Clone))]
pub(crate) struct CheckedLoopInvariantLowerings {
    pub(super) body: Option<super::object::CheckedInvariantBody>,
    pub(super) snapshot: SharedValue<CState>,
    pub(super) checks: Vec<crate::kernel::CLoopInvariantCheck>,
    /// The loop's declared `decreases` components, whose back-edge members
    /// the retained body also closed. Validation compares them exactly, so a
    /// body checked before a `decreases` clause existed cannot be reused.
    pub(super) ranking_measures: Vec<crate::kernel::CRankingComponent>,
    pub(super) facts: super::ProofFacts,
    pub(super) effects: crate::kernel::ExecutionFacts,
}

#[cfg(test)]
impl CheckedLoopInvariantLowerings {
    pub(crate) fn checks(&self) -> &[crate::kernel::CLoopInvariantCheck] {
        &self.checks
    }
    pub(crate) fn snapshot(&self) -> &SharedValue<CState> {
        &self.snapshot
    }
}

/// One checked execution branch combines kernel semantic state with an opaque
/// language presentation record. The kernel can validate the semantic
/// frontier without depending on Surface Click data; language code can carry
/// that data without treating it as evidence.
#[derive(Clone)]
pub(crate) struct ProofExecutionState<S> {
    pub(crate) core: ExecutionProofCore,
    pub(crate) presentation: S,
}

impl<S> ProofExecutionState<S> {
    pub(crate) fn new(core: ExecutionProofCore, presentation: S) -> Self {
        Self { core, presentation }
    }
}

impl<S> Deref for ProofExecutionState<S> {
    type Target = S;

    fn deref(&self) -> &Self::Target {
        &self.presentation
    }
}

impl<S> DerefMut for ProofExecutionState<S> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.presentation
    }
}

fn checked_evidence_conclusion(theorem: &Theorem) -> &Proposition {
    let mut conclusion = theorem.proposition();
    while let Proposition::Implies(_, body) = conclusion {
        conclusion = body;
    }
    conclusion
}

fn statement_call_havoc_views(theorem: &Theorem) -> Vec<crate::kernel::SharedCMemory> {
    let (before, outcome) = match checked_evidence_conclusion(theorem) {
        Proposition::CStatementExecutes { state, outcome, .. }
        | Proposition::CStatementVerifies { state, outcome, .. } => (state.memory(), outcome),
        _ => return Vec::new(),
    };
    let after = match outcome {
        CStatementOutcome::Normal(state)
        | CStatementOutcome::Break(state)
        | CStatementOutcome::Continue(state)
        | CStatementOutcome::Jump { state, .. }
        | CStatementOutcome::Return { state, .. }
        | CStatementOutcome::Throw { state, .. } => state.memory(),
        CStatementOutcome::VerificationDiverges
        | CStatementOutcome::UndefinedBehavior(_)
        | CStatementOutcome::RuntimeError(_) => return Vec::new(),
    };
    let before = crate::kernel::intern_c_memory_ref(before);
    let mut current = crate::kernel::intern_c_memory_ref(after);
    let mut calls = Vec::new();
    while current != before {
        let Some(derivation) = current.derivation() else {
            return Vec::new();
        };
        if matches!(
            derivation.as_ref(),
            crate::kernel::CMemoryDerivation::CallHavoc { .. }
        ) {
            calls.push(current.clone());
        }
        current = derivation.base().clone();
    }
    calls.reverse();
    calls
}

fn register_recomputed_call_views(
    events: &CheckedCallEvents,
    running: &CMemory,
    recomputed: &CMemory,
    assumptions: &PureFactContext,
) {
    let Some(pairs) =
        crate::kernel::api::contract_certification::matching_recomputed_call_havoc_views(
            running,
            recomputed,
            assumptions,
        )
    else {
        return;
    };
    for (running_view, recomputed_view) in pairs {
        for event in events.events_for_view(&running_view) {
            events.register_view(&event, recomputed_view.clone());
        }
        for event in events.events_for_view(&recomputed_view) {
            events.register_view(&event, running_view.clone());
        }
    }
}

/// The tactics a retained trace applied, including in its branch arms.
fn collect_applied_tactics(
    events: &[CheckedExecutionEvent],
    tactics: &mut std::collections::BTreeSet<String>,
) {
    for event in events {
        match event {
            CheckedExecutionEvent::TacticApplication(application) => {
                tactics.insert(application.name.clone());
            }
            CheckedExecutionEvent::Branch(branch) => {
                for arm in &branch.arms {
                    collect_applied_tactics(&arm.events, tactics);
                }
            }
            CheckedExecutionEvent::ProofCaseJoin(join) => {
                for events in join.live_arm_events() {
                    collect_applied_tactics(events, tactics);
                }
            }
            _ => {}
        }
    }
}

/// Conservative dependencies of retained checked statements. A summarized
/// statement (including a loop) contributes its whole body; selected branches
/// contribute only their checked arm events. No diagnostic trace is consulted.
fn collect_checked_callees(
    events: &[CheckedExecutionEvent],
    seen: &mut std::collections::HashSet<usize>,
    callees: &mut std::collections::BTreeSet<String>,
) {
    for event in events {
        crate::kernel::termination::charge_termination_work(1);
        match event {
            CheckedExecutionEvent::Statement(theorem) => {
                match checked_evidence_conclusion(theorem) {
                    Proposition::CStatementExecutes { statement, .. }
                    | Proposition::CStatementVerifies { statement, .. } => {
                        crate::kernel::termination::checked_statement_calls(
                            statement, seen, callees,
                        );
                    }
                    _ => unreachable!("checked statement evidence has a statement conclusion"),
                }
            }
            CheckedExecutionEvent::Branch(branch) => {
                for arm in &branch.arms {
                    collect_checked_callees(&arm.events, seen, callees);
                }
            }
            CheckedExecutionEvent::ProofCaseJoin(join) => {
                for events in join.live_arm_events() {
                    collect_checked_callees(events, seen, callees);
                }
            }
            // Conditions contain no calls in kernel C: calls are statements.
            // Tactic dependencies are retained separately in applied_tactics.
            _ => {}
        }
    }
}

fn collect_retained_call_events(
    events: &[CheckedExecutionEvent],
    call_events: &mut CheckedCallEvents,
) {
    for event in events {
        match event {
            CheckedExecutionEvent::Call(call) => call_events.insert(call),
            CheckedExecutionEvent::Branch(branch) => {
                for arm in &branch.arms {
                    collect_retained_call_events(&arm.events, call_events);
                }
            }
            CheckedExecutionEvent::ProofCaseJoin(join) => {
                for events in join.live_arm_events() {
                    collect_retained_call_events(events, call_events);
                }
            }
            CheckedExecutionEvent::Statement(_)
            | CheckedExecutionEvent::Condition(_)
            | CheckedExecutionEvent::Context(_)
            | CheckedExecutionEvent::StatementEffects(_)
            | CheckedExecutionEvent::ProofCase(_)
            | CheckedExecutionEvent::ResourceObservation(_)
            | CheckedExecutionEvent::AutomaticLifetimeEnd(_)
            | CheckedExecutionEvent::ReturnProposition(_)
            | CheckedExecutionEvent::ResourceRewrite(_)
            | CheckedExecutionEvent::PopulationAuthorityRewrite(_)
            | CheckedExecutionEvent::PopulationMemberRewrite(_)
            | CheckedExecutionEvent::IteratedStep(_)
            | CheckedExecutionEvent::TacticApplication(_) => {}
        }
    }
}

/// Check only a literal int32 comparison, without folding expressions or
/// consulting a context. Signed order interprets the stored bits as int32.
fn ground_comparison_premise_holds(premise: &Proposition) -> bool {
    use crate::kernel::ConditionTerm;
    let Proposition::ConditionIs(condition, expected) = premise else {
        return false;
    };
    let (left, right) = match condition {
        ConditionTerm::Bitvector32SignedLessThan(left, right)
        | ConditionTerm::Bitvector32SignedLessEqual(left, right)
        | ConditionTerm::Bitvector32SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector32Equal(left, right) => (left, right),
        _ => return false,
    };
    let (Some(left), Some(right)) = (left.as_const(), right.as_const()) else {
        return false;
    };
    let (left, right) = (left as i32, right as i32);
    let actual = match condition {
        ConditionTerm::Bitvector32SignedLessThan(..) => left < right,
        ConditionTerm::Bitvector32SignedLessEqual(..) => left <= right,
        ConditionTerm::Bitvector32SignedGreaterThan(..) => left > right,
        ConditionTerm::Bitvector32SignedGreaterEqual(..) => left >= right,
        ConditionTerm::Bitvector32Equal(..) => left == right,
        _ => unreachable!("comparison shape was checked above"),
    };
    actual == *expected
}

/// Branch evidence names its exact arm context. Do not derive a missing
/// prerequisite from other facts at the join. Literal comparisons and
/// integer reflexivity are context-free rules, not premise search.
pub(crate) fn checked_branch_fact_is_available(facts: &ProofFacts, fact: &Proposition) -> bool {
    crate::instrumentation::record_deterministic_work(1);
    facts.contains(fact)
        || facts.assumptions().proves_exact(fact)
        || ground_comparison_premise_holds(fact)
        || matches!(fact,
            Proposition::ConditionIs(crate::kernel::ConditionTerm::Bitvector32Equal(left, right), true)
                if left == right)
}

/// The pointer congruence fragment may give a field read another spelling
/// in the same checked arm. This normalizes just the named positive equality;
/// it neither searches premises nor proves a missing read/safety obligation.
pub(super) fn checked_interface_pointer_equality(facts: &ProofFacts, goal: &Proposition) -> bool {
    matches!(
        goal,
        Proposition::ConditionIs(
            crate::kernel::ConditionTerm::PointerEqual(_, _)
                | crate::kernel::ConditionTerm::PointerOffsetEqual(_, _),
            true
        )
    ) && super::fact_reasoning::normalize_using_conditions(goal, &[], facts).is_ok()
}

#[cfg(test)]
fn checked_evidence_premises_hold(theorem: &Theorem, facts: &ProofFacts) -> bool {
    checked_evidence_premises_hold_in(theorem, facts.assumptions())
}

#[cfg(test)]
fn checked_evidence_premises_hold_in(theorem: &Theorem, context: &PureFactContext) -> bool {
    let mut proposition = theorem.proposition();
    while let Proposition::Implies(premise, body) = proposition {
        if !context.proves_exact(premise) && !ground_comparison_premise_holds(premise) {
            return false;
        }
        proposition = body;
    }
    true
}

/// Whether a retained theorem's premises hold where it stands in a trace.
///
/// A premise holds under the facts the stretch ended with, or under the fact
/// context recorded right after the theorem, which is the context it was
/// proved under. Facts are not only added along a path: folding and
/// unfolding replace facts a later state no longer has, so a premise that
/// held at the theorem can be gone from the stretch's final facts.
///
/// One kind of premise comes from neither: comparing two pointers records
/// that the state holds both of their owners, as a resource composition
/// read off the state the comparison ran in. That premise holds when the
/// state the walk has reached holds every resource it names.
fn checked_evidence_premises_hold_at(
    theorem: &Theorem,
    recorded: Option<&PureFactContext>,
    facts: &ProofFacts,
    state: &CState,
) -> bool {
    let mut proposition = theorem.proposition();
    while let Proposition::Implies(premise, body) = proposition {
        let held = facts.assumptions().proves_exact(premise)
            || recorded.is_some_and(|context| context.proves_exact(premise))
            || ground_comparison_premise_holds(premise)
            || matches!(
                premise.as_ref(),
                Proposition::CResourceComposition(resources)
                    if resources.facts().iter().all(|fact| {
                        state
                            .resources()
                            .satisfies_fact(fact, recorded.unwrap_or(facts.assumptions()))
                    })
            );
        if !held {
            return false;
        }
        proposition = body;
    }
    true
}

fn split_checked_evidence_statement(statement: CStatement) -> (CStatement, Option<CStatement>) {
    match statement {
        CStatement::Seq(first, second) => {
            let (head, first_tail) = split_checked_evidence_statement(Arc::unwrap_or_clone(first));
            let tail = match first_tail {
                Some(first_tail) => CStatement::Seq(Arc::new(first_tail), second),
                None => Arc::unwrap_or_clone(second),
            };
            (head, Some(tail))
        }
        statement => (statement, None),
    }
}

/// `split_checked_evidence_statement` without taking the source: the head
/// is borrowed and the tail shares every statement after it.
fn split_shared_source(
    source: &CStatement,
) -> (std::borrow::Cow<'_, CStatement>, Option<Arc<CStatement>>) {
    match source {
        CStatement::Seq(first, second) => {
            let (head, first_tail) = split_shared_source(first);
            let tail = match first_tail {
                Some(first_tail) => Arc::new(CStatement::Seq(first_tail, second.clone())),
                None => second.clone(),
            };
            (head, Some(tail))
        }
        statement => (std::borrow::Cow::Borrowed(statement), None),
    }
}

fn prepend_shared_source(
    statement: Arc<CStatement>,
    tail: Option<Arc<CStatement>>,
) -> Arc<CStatement> {
    match tail {
        Some(tail) => Arc::new(CStatement::Seq(statement, tail)),
        None => statement,
    }
}

fn prepend_checked_evidence_statement(
    statement: CStatement,
    tail: Option<CStatement>,
) -> CStatement {
    match tail {
        Some(tail) => CStatement::Seq(Arc::new(statement), Arc::new(tail)),
        None => statement,
    }
}

/// Finds the current loop head in the validated source tail after a control
/// statement. The tail may contain the rest of the current body first; a
/// nested loop also needs the enclosing loop's continuation after its own
/// head, so returning the suffix at the matching head preserves both.
fn loop_head_source(
    mut source: Option<Arc<CStatement>>,
    loop_head: &CStatement,
) -> Option<Arc<CStatement>> {
    while let Some(current) = source {
        let (head, tail) = split_shared_source(&current);
        if statements_have_same_source(&head, loop_head) {
            return Some(current);
        }
        source = tail;
    }
    None
}

/// Whether two statements are the same C source. A proof binds loop
/// clauses into the `while` statements at its frontier, so the theorem it
/// records names the annotated statement while the proof object holds the
/// plain source; the invariant and effect annotations do not change what
/// the C executes, only what the theorem additionally checks.
fn statements_have_same_source(left: &CStatement, right: &CStatement) -> bool {
    fn flatten<'a>(statement: &'a CStatement, output: &mut Vec<&'a CStatement>) {
        match statement {
            CStatement::Seq(first, second) => {
                flatten(first, output);
                flatten(second, output);
            }
            statement => output.push(statement),
        }
    }
    match (left, right) {
        (CStatement::Seq(..), _) | (_, CStatement::Seq(..)) => {
            let mut left_statements = Vec::new();
            flatten(left, &mut left_statements);
            let mut right_statements = Vec::new();
            flatten(right, &mut right_statements);
            left_statements.len() == right_statements.len()
                && left_statements
                    .iter()
                    .zip(&right_statements)
                    .all(|(left, right)| statements_have_same_source(left, right))
        }
        (
            CStatement::If {
                condition: left_condition,
                then_branch: left_then,
                else_branch: left_else,
            },
            CStatement::If {
                condition: right_condition,
                then_branch: right_then,
                else_branch: right_else,
            },
        ) => {
            left_condition == right_condition
                && statements_have_same_source(left_then, right_then)
                && statements_have_same_source(left_else, right_else)
        }
        (
            CStatement::While {
                condition: left_condition,
                body: left_body,
                ..
            },
            CStatement::While {
                condition: right_condition,
                body: right_body,
                ..
            },
        ) => {
            left_condition == right_condition && statements_have_same_source(left_body, right_body)
        }
        (left, right) => left == right,
    }
}

/// `statement_sequence_is_prefix` up to loop annotations.
fn statement_sequence_has_same_source_prefix(
    expected_prefix: &Option<CStatement>,
    actual: Option<&CStatement>,
) -> bool {
    fn flatten<'a>(statement: &'a CStatement, output: &mut Vec<&'a CStatement>) {
        match statement {
            CStatement::Seq(first, second) => {
                flatten(first, output);
                flatten(second, output);
            }
            statement => output.push(statement),
        }
    }

    let Some(expected_prefix) = expected_prefix else {
        return true;
    };
    let Some(actual) = actual else {
        return false;
    };
    let mut expected_statements = Vec::new();
    flatten(expected_prefix, &mut expected_statements);
    let mut actual_statements = Vec::new();
    flatten(actual, &mut actual_statements);
    expected_statements.len() <= actual_statements.len()
        && expected_statements
            .iter()
            .zip(&actual_statements)
            .all(|(expected, actual)| statements_have_same_source(expected, actual))
}

fn statement_sequence_is_prefix(
    expected_prefix: &Option<CStatement>,
    actual: &Option<CStatement>,
) -> bool {
    fn flatten<'a>(statement: &'a CStatement, output: &mut Vec<&'a CStatement>) {
        match statement {
            CStatement::Seq(first, second) => {
                flatten(first, output);
                flatten(second, output);
            }
            statement => output.push(statement),
        }
    }

    let Some(expected_prefix) = expected_prefix else {
        return true;
    };
    let Some(actual) = actual else {
        return false;
    };
    let mut expected_statements = Vec::new();
    let mut actual_statements = Vec::new();
    flatten(expected_prefix, &mut expected_statements);
    flatten(actual, &mut actual_statements);
    actual_statements.starts_with(&expected_statements)
}

/// Whether a statement theorem's statement is the C source statement it is
/// checked against.
///
/// A summarized loop's theorem names the loop with the proof's own clauses
/// attached: the `loop { ... }` tactic re-annotates the C loop at the frontier
/// before its rule is certified. A `branch` arm is checked against the C source
/// captured when the branch split, which still carries that loop bare. The two
/// are the same C program — same condition, same body, same `do`-ness — and the
/// annotated theorem is the stronger claim, since every attached clause was
/// discharged to obtain it. So a bare source loop accepts its annotated proof.
///
/// A source loop that already carries clauses of its own must match exactly, so
/// this can never drop an obligation the source asked for.
fn checked_source_statement_matches(proved: &CStatement, source: &CStatement) -> bool {
    if proved == source {
        return true;
    }
    let (
        CStatement::While {
            condition: proved_condition,
            do_while: proved_do_while,
            body: proved_body,
            ..
        },
        CStatement::While {
            condition: source_condition,
            invariant,
            invariant_checks,
            effect_checks,
            resource_specs,
            ranking_measures,
            structural_measure,
            do_while: source_do_while,
            body: source_body,
            ..
        },
    ) = (proved, source)
    else {
        return false;
    };
    invariant.is_empty()
        && invariant_checks.is_empty()
        && effect_checks.is_empty()
        && resource_specs.is_empty()
        && ranking_measures.is_empty()
        && structural_measure.is_none()
        && proved_condition == source_condition
        && proved_do_while == source_do_while
        && proved_body == source_body
}

fn checked_statement_event(
    theorem: &Theorem,
    recorded: Option<&PureFactContext>,
    facts: &ProofFacts,
    state: &CState,
    statement: &CStatement,
) -> Option<CStatementOutcome> {
    if !checked_evidence_premises_hold_at(theorem, recorded, facts, state) {
        return None;
    }
    let (proved_state, proved_statement, outcome) = match checked_evidence_conclusion(theorem) {
        Proposition::CStatementExecutes {
            state,
            statement,
            outcome,
        }
        | Proposition::CStatementVerifies {
            state,
            statement,
            outcome,
        } => (state, statement, outcome),
        _ => return None,
    };
    (**proved_state == *state && checked_source_statement_matches(proved_statement, statement))
        .then(|| outcome.clone())
}

fn checked_condition_event(
    theorem: &Theorem,
    recorded: Option<&PureFactContext>,
    facts: &ProofFacts,
    state: &CState,
    statement: CStatement,
    tail: Option<CStatement>,
) -> Option<Option<CStatement>> {
    if !checked_evidence_premises_hold_at(theorem, recorded, facts, state) {
        return None;
    }
    let (proved_state, proved_condition, value) = match checked_evidence_conclusion(theorem) {
        Proposition::CConditionEvaluates {
            state,
            condition,
            outcome: CConditionOutcome::Value(value),
        } => (state, condition, *value),
        _ => return None,
    };
    if **proved_state != *state {
        return None;
    }
    let selected = match statement {
        CStatement::If {
            condition,
            then_branch,
            else_branch,
        } if &condition == proved_condition => {
            if value {
                *then_branch
            } else {
                *else_branch
            }
        }
        CStatement::While {
            condition,
            invariant,
            invariant_checks,
            effect_checks,
            resource_specs,
            ranking_measures,
            structural_measure,
            body,
            ..
        } if &condition == proved_condition => {
            if value {
                let loop_head = CStatement::While {
                    condition,
                    invariant,
                    invariant_checks,
                    effect_checks,
                    resource_specs,
                    ranking_measures,
                    structural_measure,
                    do_while: false,
                    backedge_target: None,
                    natural_exit_target: None,
                    body: body.clone(),
                };
                prepend_checked_evidence_statement(*body, Some(loop_head))
            } else {
                CStatement::Skip
            }
        }
        _ => return None,
    };
    Some(if matches!(selected, CStatement::Skip) {
        tail
    } else {
        Some(prepend_checked_evidence_statement(selected, tail))
    })
}

struct CheckedEvidenceProgress {
    state: CState,
    remaining: Option<CStatement>,
    completed: Option<CStatementOutcome>,
    /// Where the walk saw memory change, in order.
    memory_steps: Vec<CheckedMemoryStep>,
}

/// One change of memory a walk of checked events passed through: the
/// snapshot before an event and the one after it.
///
/// `may_write` is false for an event that only rewrites what the proof holds
/// (a fold, an unfold, an observation, the end of an automatic lifetime).
/// Such an event changes which values a snapshot caches, never a byte a
/// pointer can reach, and it leaves no effect fact.
#[derive(Clone)]
struct CheckedMemoryStep {
    before: CMemory,
    after: CMemory,
    may_write: bool,
    /// For a statement, how many memory effects its recorder appended.
    statement_effects: Option<usize>,
}

/// Checks a retained event tree by following kernel theorem conclusions
/// through an exact source tree. This does not evaluate a C operation.
fn check_evidence_events(
    events: &[CheckedExecutionEvent],
    facts: &ProofFacts,
    state: CState,
    remaining: Option<CStatement>,
) -> Option<CheckedEvidenceProgress> {
    check_evidence_events_with_call_events(
        events,
        facts,
        state,
        remaining,
        CheckedCallEvents::default(),
    )
}

fn check_evidence_events_with_call_events(
    events: &[CheckedExecutionEvent],
    facts: &ProofFacts,
    mut state: CState,
    mut remaining: Option<CStatement>,
    mut call_events: CheckedCallEvents,
) -> Option<CheckedEvidenceProgress> {
    let mut completed = None;
    let mut current_facts = facts.clone();
    let mut memory_steps = Vec::new();
    let mut step_memory = state.memory().clone();
    let mut step_may_write = false;
    // The step of the statement last walked, for its effect count to land on.
    let mut statement_step: Option<usize> = None;
    let mut after_statement = false;
    for (position, event) in events.iter().enumerate() {
        if state.memory() != &step_memory {
            if after_statement {
                statement_step = Some(memory_steps.len());
            }
            memory_steps.push(CheckedMemoryStep {
                before: std::mem::replace(&mut step_memory, state.memory().clone()),
                after: state.memory().clone(),
                may_write: step_may_write,
                statement_effects: None,
            });
        }
        match event {
            CheckedExecutionEvent::Statement(_) => {
                statement_step = None;
                after_statement = true;
            }
            CheckedExecutionEvent::StatementEffects(count) => {
                match statement_step.take() {
                    Some(step) => memory_steps[step].statement_effects = Some(*count),
                    // The statement left memory as it was. Its effects, if
                    // any, are still the next ones on the list.
                    None if *count > 0 => memory_steps.push(CheckedMemoryStep {
                        before: step_memory.clone(),
                        after: step_memory.clone(),
                        may_write: true,
                        statement_effects: Some(*count),
                    }),
                    None => {}
                }
                after_statement = false;
                continue;
            }
            CheckedExecutionEvent::Context(_) | CheckedExecutionEvent::Call(_) => {}
            _ => after_statement = false,
        }
        step_may_write = matches!(
            event,
            CheckedExecutionEvent::Statement(_)
                | CheckedExecutionEvent::Condition(_)
                | CheckedExecutionEvent::Call(_)
                | CheckedExecutionEvent::Branch(_)
                | CheckedExecutionEvent::ProofCaseJoin(_)
        );
        // The fact context recorded right after a theorem is the one it was
        // proved under.
        let recorded = match events.get(position + 1) {
            Some(CheckedExecutionEvent::Context(context)) => Some(context),
            _ => None,
        };
        if let Some(CStatementOutcome::Return {
            state: returned, ..
        }) = &mut completed
            && let CheckedExecutionEvent::ResourceRewrite(rewrite) = event
        {
            current_facts = rewrite.advance_checked(returned, &current_facts, &call_events)?;
            **returned = rewrite.after_state.clone();
            continue;
        }
        if let Some(CStatementOutcome::Return {
            state: returned, ..
        }) = &mut completed
            && let CheckedExecutionEvent::PopulationAuthorityRewrite(rewrite) = event
        {
            current_facts = rewrite.advance_checked(returned, &current_facts)?;
            **returned = rewrite.after_state.clone();
            continue;
        }
        if let CheckedExecutionEvent::AutomaticLifetimeEnd(end) = event {
            if let Some(outcome) = &mut completed {
                let returned = match outcome {
                    CStatementOutcome::Normal(state)
                    | CStatementOutcome::Break(state)
                    | CStatementOutcome::Continue(state)
                    | CStatementOutcome::Return { state, .. }
                    | CStatementOutcome::Throw { state, .. } => state,
                    _ => return None,
                };
                **returned = end.advance_checked(returned)?;
            } else {
                state = end.advance_checked(&state)?;
            }
            continue;
        }
        if completed.is_some() {
            return None;
        }
        match event {
            CheckedExecutionEvent::ReturnProposition(_) => return None,
            CheckedExecutionEvent::ProofCase(arm) => {
                if !arm.is_valid() {
                    return None;
                }
                current_facts = arm.facts.clone();
                continue;
            }
            CheckedExecutionEvent::ProofCaseJoin(join) => {
                remaining = join.advance_checked(&state, &remaining, &call_events)?;
                state = join.joined_state().clone();
                // The walk runs under the facts its own path ends with, which
                // extend whatever the join left. Only a walk that began
                // before those facts existed takes the join's.
                if let Some(successor_facts) = join.interface_successor_facts()
                    && current_facts.introduced_since(successor_facts).is_none()
                {
                    current_facts = successor_facts.clone();
                }
                continue;
            }
            CheckedExecutionEvent::ResourceObservation(observation) => {
                current_facts =
                    observation.advance_checked(&state, &current_facts, &call_events)?;
                state = observation.after_state.clone();
                continue;
            }
            CheckedExecutionEvent::ResourceRewrite(rewrite) => {
                current_facts = rewrite.advance_checked(&state, &current_facts, &call_events)?;
                state = rewrite.after_state.clone();
                continue;
            }
            CheckedExecutionEvent::PopulationAuthorityRewrite(rewrite) => {
                current_facts = rewrite.advance_checked(&state, &current_facts)?;
                state = rewrite.after_state.clone();
                continue;
            }
            CheckedExecutionEvent::PopulationMemberRewrite(rewrite) => {
                current_facts = rewrite.advance_checked(&state, &current_facts)?;
                state = rewrite.after_state.clone();
                continue;
            }
            // A checked iterated step does not advance an existing trace: the
            // authority ledger records its events, so the trace is checked
            // again from the start.
            CheckedExecutionEvent::IteratedStep(_) => return None,
            CheckedExecutionEvent::TacticApplication(application) => {
                current_facts = application.advance_checked(&state, &current_facts)?;
                state = application.after_state.clone();
                continue;
            }
            // The retained context of the preceding theorem; the arm check
            // above already holds the arm's own facts.
            CheckedExecutionEvent::Context(_) | CheckedExecutionEvent::StatementEffects(_) => {
                continue;
            }
            CheckedExecutionEvent::Call(call) => {
                call_events.insert(call);
                continue;
            }
            CheckedExecutionEvent::AutomaticLifetimeEnd(_) => {
                unreachable!("handled before source advance")
            }
            CheckedExecutionEvent::Statement(_)
            | CheckedExecutionEvent::Condition(_)
            | CheckedExecutionEvent::Branch(_) => {}
        }
        // A `Skip` theorem consumes a `Skip` at the head of the source when
        // there is one and otherwise nothing, exactly as when it was
        // recorded: the empty arm a condition selected is not kept in the
        // source, but a proof may still step it.
        if let CheckedExecutionEvent::Statement(theorem) = event
            && matches!(
                checked_evidence_conclusion(theorem),
                Proposition::CStatementExecutes { statement, .. }
                | Proposition::CStatementVerifies { statement, .. }
                    if matches!(**statement, CStatement::Skip)
            )
            && !remaining
                .as_ref()
                .is_some_and(|source| matches!(*split_shared_source(source).0, CStatement::Skip))
        {
            let CStatementOutcome::Normal(next_state) = checked_statement_event(
                theorem,
                recorded,
                &current_facts,
                &state,
                &CStatement::Skip,
            )?
            else {
                return None;
            };
            state = *next_state;
            continue;
        }
        let source = remaining.take()?;
        let (next_statement, tail) = split_checked_evidence_statement(source);
        match event {
            CheckedExecutionEvent::Statement(theorem) => {
                match checked_statement_event(
                    theorem,
                    recorded,
                    &current_facts,
                    &state,
                    &next_statement,
                )? {
                    CStatementOutcome::Normal(next_state) => {
                        state = *next_state;
                        remaining = tail;
                    }
                    outcome @ (CStatementOutcome::Break(_)
                    | CStatementOutcome::Continue(_)
                    | CStatementOutcome::Return { .. }
                    | CStatementOutcome::Throw { .. }
                    | CStatementOutcome::VerificationDiverges) => {
                        if tail.is_some() {
                            return None;
                        }
                        completed = Some(outcome);
                    }
                    CStatementOutcome::UndefinedBehavior(_)
                    | CStatementOutcome::RuntimeError(_)
                    | CStatementOutcome::Jump { .. } => return None,
                }
            }
            CheckedExecutionEvent::Condition(theorem) => {
                remaining = checked_condition_event(
                    theorem,
                    recorded,
                    &current_facts,
                    &state,
                    next_statement,
                    tail,
                )?;
            }
            CheckedExecutionEvent::Branch(branch) => {
                let CStatement::If { .. } = &next_statement else {
                    return None;
                };
                if !branch.matches_source(&state, &next_statement, &tail) {
                    return None;
                }
                let full_source = prepend_checked_evidence_statement(next_statement, tail.clone());
                for arm_index in 0..2 {
                    let arm = check_evidence_events_with_call_events(
                        branch.arm_events(arm_index),
                        branch.arm_facts(arm_index),
                        state.clone(),
                        Some(full_source.clone()),
                        call_events.clone(),
                    )?;
                    if arm.completed.is_some()
                        || arm.remaining != tail
                        || (branch.interface_successor_facts().is_none()
                            && arm.state != *branch.joined_state())
                    {
                        return None;
                    }
                }
                state = branch.joined_state().clone();
                remaining = tail;
                if let Some(successor_facts) = branch.interface_successor_facts() {
                    current_facts = successor_facts.clone();
                }
            }
            CheckedExecutionEvent::ProofCase(_)
            | CheckedExecutionEvent::ProofCaseJoin(_)
            | CheckedExecutionEvent::Context(_)
            | CheckedExecutionEvent::StatementEffects(_) => {
                unreachable!("handled before source advance")
            }
            CheckedExecutionEvent::Call(_) => unreachable!("handled before source advance"),
            CheckedExecutionEvent::AutomaticLifetimeEnd(_)
            | CheckedExecutionEvent::ResourceObservation(_) => {
                unreachable!("handled before source advance")
            }
            CheckedExecutionEvent::ReturnProposition(_)
            | CheckedExecutionEvent::ResourceRewrite(_)
            | CheckedExecutionEvent::PopulationAuthorityRewrite(_)
            | CheckedExecutionEvent::PopulationMemberRewrite(_)
            | CheckedExecutionEvent::IteratedStep(_)
            | CheckedExecutionEvent::TacticApplication(_) => {
                unreachable!("handled before source advance")
            }
        }
    }
    if state.memory() != &step_memory {
        memory_steps.push(CheckedMemoryStep {
            before: step_memory,
            after: state.memory().clone(),
            may_write: step_may_write,
            statement_effects: None,
        });
    }
    Some(CheckedEvidenceProgress {
        state,
        remaining,
        completed,
        memory_steps,
    })
}

/// A completed trace's completing outcome, the context its completing
/// theorem was proved under (every fact the proof had established on the
/// path), and the interface facts of the branches it joined. A trace that
/// does not complete, continues past its completion, or completes in an
/// error outcome yields nothing.
/// Extends an already checked completion context by genuinely new facts.
/// A typed producer can also carry a load bridge beyond its proposition.
fn retain_completed_path_fact(
    assumptions: PureFactContext,
    fact: &ExecutionPureFact,
) -> PureFactContext {
    crate::instrumentation::record_deterministic_work(1);
    if assumptions.contains_assumed_exact(fact.proposition())
        && (!fact.is_certified() || fact.generated_load_binding().is_none())
    {
        return assumptions;
    }
    crate::kernel::reasoning::path_facts::count_context_rebuild_entries(1);
    assumptions.assume_execution_pure_fact(fact)
}

fn trace_completion(
    function: &CFunction,
    events: &[CheckedExecutionEvent],
    assumptions: &PureFactContext,
    checked_void_fallthrough: bool,
) -> Result<
    (
        CStatementOutcome,
        PureFactContext,
        crate::kernel::ExecutionFacts,
    ),
    &'static str,
> {
    trace_completion_from_entry(
        function,
        events,
        assumptions,
        checked_void_fallthrough,
        None,
    )
}

/// As [`trace_completion`], where `entry_facts` are the facts the checked
/// entry was checked under. A return proof's facts that the entry already
/// held are the proof's assumptions, not path facts, so only the facts it
/// introduced since are checked against the path.
fn trace_completion_from_entry(
    function: &CFunction,
    events: &[CheckedExecutionEvent],
    assumptions: &PureFactContext,
    checked_void_fallthrough: bool,
    entry_facts: Option<&ProofFacts>,
) -> Result<
    (
        CStatementOutcome,
        PureFactContext,
        crate::kernel::ExecutionFacts,
    ),
    &'static str,
> {
    if !events_use_the_function_definitions(function, events) {
        return Err("a retained resource event was checked under other composite definitions");
    }
    let mut completed: Option<(CStatementOutcome, PureFactContext)> = None;
    let mut return_origin = None;
    let mut return_context: Option<&Arc<CheckedReturnContext>> = None;
    let mut proposition_base: Option<&ProofFacts> = None;
    let mut fallthrough = None;
    let mut interface_execution_facts: crate::kernel::ExecutionFacts = Vec::new().into();
    for (index, event) in events.iter().enumerate() {
        match event {
            CheckedExecutionEvent::Statement(theorem) => {
                if completed.is_some() {
                    return Err("a trace continues past its completing theorem");
                }
                let Proposition::CStatementVerifies { outcome, .. } =
                    checked_evidence_conclusion(theorem)
                else {
                    return Err("retained statement evidence has a non-statement conclusion");
                };
                match outcome {
                    CStatementOutcome::Normal(state) => {
                        let context = match events.get(index + 1) {
                            Some(CheckedExecutionEvent::Context(context)) => context.clone(),
                            _ => {
                                crate::kernel::api::proof_evidence_assumptions(theorem, assumptions)
                            }
                        };
                        fallthrough = Some((
                            CStatementOutcome::Return {
                                value: CValue::Void,
                                state: state.clone(),
                            },
                            context,
                        ));
                    }
                    CStatementOutcome::Break(_)
                    | CStatementOutcome::Continue(_)
                    | CStatementOutcome::Jump { .. } => {
                        fallthrough = None;
                    }
                    CStatementOutcome::Throw { .. }
                        if events[index + 2..]
                            .iter()
                            .any(|event| matches!(event, CheckedExecutionEvent::Statement(_))) =>
                    {
                        // A caught throw is followed by the synthetic
                        // handler-binding/cleanup trace. It is an internal
                        // control transfer, not this execution path's final
                        // function outcome.
                    }
                    CStatementOutcome::Return { .. }
                    | CStatementOutcome::Throw { .. }
                    | CStatementOutcome::VerificationDiverges => {
                        // The path completes under the context its final
                        // theorem was proved under, recorded right after it.
                        let executed_under = match events.get(index + 1) {
                            Some(CheckedExecutionEvent::Context(context)) => context.clone(),
                            _ => {
                                crate::kernel::api::proof_evidence_assumptions(theorem, assumptions)
                            }
                        };
                        return_origin = Some(outcome.clone());
                        completed = Some((outcome.clone(), executed_under));
                    }
                    CStatementOutcome::UndefinedBehavior(_)
                    | CStatementOutcome::RuntimeError(_) => {
                        return Err("a trace completes in an error outcome");
                    }
                }
            }
            CheckedExecutionEvent::Branch(branch) => {
                fallthrough = None;
                if completed.is_some() {
                    return Err("a trace continues past its completing theorem");
                }
                if branch.interface_successor_facts().is_some() {
                    for fact in branch.interface_execution_facts() {
                        if !interface_execution_facts
                            .iter()
                            .any(|retained| retained.proposition() == fact.proposition())
                        {
                            interface_execution_facts.push(fact.clone());
                        }
                    }
                }
            }
            CheckedExecutionEvent::PopulationAuthorityRewrite(rewrite) => {
                fallthrough = None;
                if let Some((outcome, _)) = &mut completed {
                    let CStatementOutcome::Return { state, .. } = outcome else {
                        return Err("population authority rewrite requires a returned state");
                    };
                    rewrite
                        .advance_checked(state, &rewrite.before_facts)
                        .ok_or("population authority rewrite failed certificate check")?;
                    **state = rewrite.after_state.clone();
                }
            }
            CheckedExecutionEvent::PopulationMemberRewrite(_) => {
                fallthrough = None;
                if completed.is_some() {
                    return Err("population member rewrite must precede function exit");
                }
            }
            CheckedExecutionEvent::TacticApplication(_) => {
                fallthrough = None;
                if completed.is_some() {
                    return Err("a tactic application must precede function exit");
                }
            }
            CheckedExecutionEvent::ReturnProposition(retained) => {
                let Some((CStatementOutcome::Return { state, .. }, executed_under)) =
                    &mut completed
                else {
                    return Err("return proof requires a returning path");
                };
                if return_origin.as_ref() != Some(&retained.context.origin) {
                    return Err("return proof belongs to a different execution path");
                }
                if let Some(previous) = return_context {
                    if !Arc::ptr_eq(previous, &retained.context) {
                        return Err("return proofs have different publication contexts");
                    }
                } else {
                    // Import this path's kernel-produced effects and resource
                    // observations once, before consuming any logical proof.
                    for fact in retained
                        .context
                        .facts
                        .facts_not_assumed_by(executed_under)
                        .into_iter()
                        .chain(retained.context.facts.producer_facts().filter(|fact| {
                            fact.is_certified() && fact.generated_load_binding().is_some()
                        }))
                    {
                        *executed_under =
                            retain_completed_path_fact(std::mem::take(executed_under), fact);
                    }
                    let CFunctionOutcome::Return {
                        state: published, ..
                    } = &retained.context.published
                    else {
                        return Err("return proof has no published return");
                    };
                    for fact in published
                        .resources()
                        .observable_facts_assuming_valid(executed_under)
                    {
                        *executed_under = std::mem::take(executed_under).assume_proposition(fact);
                    }
                    // Relations describe the definition's footprint, not an
                    // unchecked assertion about the current invariant value.
                    let definitions: BTreeMap<_, _> = function
                        .composite_resource_definitions()
                        .iter()
                        .map(|definition| (definition.name(), std::slice::from_ref(definition)))
                        .collect();
                    for held in published.resources().facts() {
                        let CResource::Composite { name, .. } = held.resource() else {
                            continue;
                        };
                        let Some(definition) = definitions.get(name.as_str()) else {
                            continue;
                        };
                        if !(held.is_view() || held.has_proven_positive_quantity(executed_under)) {
                            continue;
                        }
                        let authority = CResourceFact::own(held.resource().clone());
                        // Immutable argument facts of an ordinary held resource
                        // survive a return. Instantiate with no memory, resources,
                        // or ambient read premises so this cannot import a mutable
                        // invariant from an unchecked current snapshot.
                        if !definition[0].is_authorized()
                            && let Some(facts) = crate::kernel::functions::evaluate_composite_resource_fact_propositions(
                                &authority, definition, &CMemory::new(), &ResourceContext::new(),
                                &PureFactContext::new().require_owned_expression_loads()) {
                            for fact in facts {
                                *executed_under = std::mem::take(executed_under).assume_proposition(fact);
                            }
                        }
                        if let Some(facts) = crate::kernel::functions::evaluate_composite_resource_relation_propositions(
                            &authority, definition, published.memory(), executed_under) {
                            for fact in facts {
                                *executed_under = std::mem::take(executed_under).assume_proposition(fact);
                            }
                        }
                        if let Some(facts) = crate::kernel::functions::evaluate_composite_resource_loadable_propositions(
                            held, definition, published.memory(), executed_under) {
                            for fact in facts {
                                *executed_under = std::mem::take(executed_under).assume_proposition(fact);
                            }
                        }
                    }
                    return_context = Some(&retained.context);
                }
                let proof = &retained.proof;
                let delta = match proposition_base {
                    Some(base) => retained
                        .base
                        .introduced_since(base)
                        .ok_or("return proof belongs to a different fact lineage")?,
                    None => {
                        match entry_facts.and_then(|entry| retained.base.introduced_since(entry)) {
                            Some(delta) => delta,
                            None => retained.base.to_vec(),
                        }
                    }
                };
                let extra = proof
                    .root_assumptions()
                    .introduced_since(&retained.base)
                    .ok_or("return proof has a different root context")?;
                for fact in delta.iter().chain(extra.iter()) {
                    crate::instrumentation::record_deterministic_work(1);
                    if executed_under.proves_exact(fact) {
                        continue;
                    }
                    // A store materializes its exact cell in this snapshot.
                    // This is read validity, not ownership or a value equality;
                    // no ambient range search or cross-snapshot transport occurs.
                    let materialized_read = matches!(fact,
                        Proposition::CMemoryLoadable { memory, base, bytes, wide: false }
                            if bytes.as_const().is_some_and(|width|
                                width > 0 && memory.is_loadable_concretely(base, width)));
                    if !materialized_read
                        && !matches!(fact, Proposition::CMemoryReadDefined { .. }
                            if crate::kernel::c_state_justifies_loadability_obligation(
                                state, fact, executed_under))
                        && !executed_under.settles_exactly(fact)
                        && !resource_composition_is_supported_by(
                            fact,
                            state.resources(),
                            executed_under,
                        )
                        && !matches!(fact, Proposition::CResourceComposition(resources)
                            if ResourceContext::new()
                                .try_compose_with_facts(resources.facts().iter().cloned(), executed_under)
                                .is_ok())
                    {
                        return Err("return proof assumes an unjustified path fact");
                    }
                    *executed_under =
                        std::mem::take(executed_under).assume_proposition(fact.clone());
                }
                *executed_under =
                    std::mem::take(executed_under).assume_proposition(proof.proposition().clone());
                proposition_base = Some(&retained.base);
            }
            CheckedExecutionEvent::ResourceRewrite(rewrite) => {
                fallthrough = None;
                if let Some((outcome, executed_under)) = &mut completed {
                    let CStatementOutcome::Return { state, .. } = outcome else {
                        return Err("resource rewriting requires a returned state");
                    };
                    if **state != rewrite.before_state {
                        return Err("post-return resource rewrite has a different input state");
                    }
                    if let Some(instance) = &rewrite.instance
                        && rewrite.definition.condition().is_some()
                    {
                        let path_case = crate::kernel::functions::instance_body_guard_case(
                            state,
                            instance,
                            &rewrite.definition,
                            executed_under,
                        );
                        let selected_case = crate::kernel::functions::instance_body_guard_case(
                            state,
                            instance,
                            &rewrite.definition,
                            rewrite.before_facts.assumptions(),
                        );
                        if path_case.is_none() || path_case != selected_case {
                            return Err(
                                "return fold guard is not justified on this execution path",
                            );
                        }
                    }
                    if let Some(instance) = &rewrite.instance {
                        if rewrite.definition.matched.is_some() {
                            let path_case = crate::kernel::functions::selected_instance_match_arm(
                                instance,
                                &rewrite.definition,
                                function.composite_resource_definitions(),
                                executed_under,
                            )
                            .map(|(arm, _)| &arm.variant);
                            let selected_case =
                                crate::kernel::functions::selected_instance_match_arm(
                                    instance,
                                    &rewrite.definition,
                                    function.composite_resource_definitions(),
                                    rewrite.before_facts.assumptions(),
                                )
                                .map(|(arm, _)| &arm.variant);
                            if path_case.is_err() || path_case != selected_case {
                                return Err(
                                    "return fold constructor is not justified on this execution path",
                                );
                            }
                        }
                        let unfold = state
                            .resources()
                            .owned_instance(instance.identity())
                            .is_some();
                        let checked = crate::kernel::rewrite_resource_instance_selecting_children(
                            state,
                            instance,
                            &rewrite.definition,
                            function.composite_resource_definitions(),
                            executed_under,
                            unfold,
                            rewrite.selected_children.as_deref(),
                        )
                        .map_err(|_| "return fold body is not justified on this execution path")?;
                        let checked_state = checked.state;
                        if !checked_state
                            .resources
                            .same_exchange_from(&rewrite.after_state.resources, &state.resources)
                            || !checked_state.instance_field_scope.same_exchange_from(
                                &rewrite.after_state.instance_field_scope,
                                &state.instance_field_scope,
                            )
                            || checked_state.population_effects.creation
                                != rewrite.after_state.population_effects.creation
                        {
                            return Err(
                                "return fold does not match this path's checked resource exchange",
                            );
                        }
                        for fact in checked.semantic_facts {
                            *executed_under =
                                std::mem::take(executed_under).assume_proposition(fact);
                        }
                    }
                    **state = rewrite.after_state.clone();
                    // Only the rechecked exchange's semantic facts enter this
                    // path, never a proof snapshot's entire assumption context.
                }
            }
            CheckedExecutionEvent::AutomaticLifetimeEnd(end) => {
                if let Some((outcome, _)) = completed.as_mut().or(fallthrough.as_mut()) {
                    let state = match outcome {
                        CStatementOutcome::Return { state, .. }
                        | CStatementOutcome::Throw { state, .. } => state,
                        _ => return Err("lifetime end follows a stateless outcome"),
                    };
                    **state = end
                        .advance_checked(state)
                        .ok_or("lifetime end has mismatched state")?;
                }
            }
            CheckedExecutionEvent::ProofCaseJoin(join) => {
                fallthrough = None;
                if completed.is_some() {
                    return Err("a trace continues past its completing theorem");
                }
                for fact in join.interface_execution_facts() {
                    if !interface_execution_facts
                        .iter()
                        .any(|retained| retained.proposition() == fact.proposition())
                    {
                        interface_execution_facts.push(fact.clone());
                    }
                }
            }
            CheckedExecutionEvent::Condition(_)
            | CheckedExecutionEvent::ResourceObservation(_)
            | CheckedExecutionEvent::IteratedStep(_) => {
                fallthrough = None;
                if completed.is_some() {
                    return Err("a trace continues past its completing theorem");
                }
            }
            // A post-execution case split records its arm after the path's
            // returning statement; it changes only the assumed facts.
            CheckedExecutionEvent::ProofCase(arm) => {
                if !arm.is_valid() {
                    return Err("invalid post-execution proof case");
                }
                if let Some((_, executed_under)) = &mut completed {
                    *executed_under = arm.facts.assumptions().clone();
                }
            }
            CheckedExecutionEvent::Context(_)
            | CheckedExecutionEvent::StatementEffects(_)
            | CheckedExecutionEvent::Call(_) => {}
        }
    }
    let Some((outcome, executed_under)) =
        completed.or_else(|| checked_void_fallthrough.then_some(fallthrough).flatten())
    else {
        return Err("a trace does not reach a return");
    };
    Ok((outcome, executed_under, interface_execution_facts))
}

/// Whether every resource observation, rewrite, and interface join in the
/// events, and in every joined branch's arms, was checked under the
/// composite resource definitions of `function`.
fn events_use_the_function_definitions(
    function: &CFunction,
    events: &[CheckedExecutionEvent],
) -> bool {
    fn check(
        function: &CFunction,
        events: &[CheckedExecutionEvent],
        checked_entries: &mut std::collections::HashSet<usize>,
    ) -> bool {
        let definitions = function.composite_resource_definitions();
        events.iter().all(|event| match event {
            CheckedExecutionEvent::ResourceObservation(observation) => observation
                .definition()
                .is_none_or(|definition| definitions.contains(definition)),
            CheckedExecutionEvent::PopulationAuthorityRewrite(_) => true,
            // The application was checked against the environment's own
            // verified rule; the rule carries the definitions it was
            // certified under, and the same run installed both.
            CheckedExecutionEvent::TacticApplication(_) => true,
            CheckedExecutionEvent::PopulationMemberRewrite(rewrite) => {
                definitions.contains(&rewrite.definition)
            }
            CheckedExecutionEvent::ResourceRewrite(rewrite) => {
                definitions.contains(rewrite.definition())
                    && rewrite.consumption_contract.as_ref().is_none_or(|entry| {
                        !checked_entries.insert(Arc::as_ptr(entry) as usize)
                            || entry.function.as_ref() == function
                    })
            }
            CheckedExecutionEvent::Branch(branch) => {
                branch.matches_interface_resource_definitions(function)
                    && (0..2).all(|arm_index| {
                        check(function, branch.arm_events(arm_index), checked_entries)
                    })
            }
            CheckedExecutionEvent::ProofCaseJoin(join) => {
                join.matches_interface_resource_definitions(function)
                    && join
                        .live_arm_events()
                        .all(|events| check(function, events, checked_entries))
            }
            CheckedExecutionEvent::AutomaticLifetimeEnd(_)
            | CheckedExecutionEvent::IteratedStep(_)
            | CheckedExecutionEvent::Statement(_)
            | CheckedExecutionEvent::Call(_)
            | CheckedExecutionEvent::Condition(_)
            | CheckedExecutionEvent::Context(_)
            | CheckedExecutionEvent::StatementEffects(_)
            | CheckedExecutionEvent::ProofCase(_)
            | CheckedExecutionEvent::ReturnProposition(_) => true,
        })
    }
    check(function, events, &mut std::collections::HashSet::new())
}

/// Why a record call refused the evidence offered to it. `reason` names
/// the judgment that failed; the statements and premise, when the judgment
/// concerned them, let the driver's diagnostic say what the proof object
/// expected and what it was offered.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct EvidenceRefusal {
    pub(crate) reason: &'static str,
    /// The source statement the evidence had to consume next.
    pub(crate) expected: Option<CStatement>,
    /// The statement the offered theorem proves.
    pub(crate) proved: Option<CStatement>,
    /// The premise the offered theorem assumes that nothing retains.
    pub(crate) premise: Option<Proposition>,
}

impl From<&'static str> for EvidenceRefusal {
    fn from(reason: &'static str) -> Self {
        Self {
            reason,
            expected: None,
            proved: None,
            premise: None,
        }
    }
}

fn validate_checked_event_shapes(events: &[CheckedExecutionEvent]) -> Result<(), &'static str> {
    let mut pending_call_views = Vec::new();
    for event in events {
        let (theorem, statement) = match event {
            CheckedExecutionEvent::Statement(theorem) => {
                pending_call_views = statement_call_havoc_views(theorem);
                (theorem, true)
            }
            CheckedExecutionEvent::Condition(theorem) => {
                pending_call_views.clear();
                (theorem, false)
            }
            CheckedExecutionEvent::Branch(branch) => {
                pending_call_views.clear();
                for arm in &branch.arms {
                    validate_checked_event_shapes(&arm.events)?;
                }
                continue;
            }
            CheckedExecutionEvent::ProofCaseJoin(join) => {
                pending_call_views.clear();
                for events in join.live_arm_events() {
                    validate_checked_event_shapes(events)?;
                }
                continue;
            }
            CheckedExecutionEvent::Context(_) | CheckedExecutionEvent::StatementEffects(_) => {
                continue;
            }
            CheckedExecutionEvent::Call(call) => {
                let Some(index) = pending_call_views
                    .iter()
                    .position(|view| view == &call.canonical_view())
                else {
                    return Err(
                        "retained checked-call event is not introduced by its preceding statement",
                    );
                };
                pending_call_views.remove(index);
                continue;
            }
            CheckedExecutionEvent::ProofCase(arm) => {
                pending_call_views.clear();
                if !arm.is_valid() {
                    return Err("retained proof-case evidence has an invalid checked arm");
                }
                continue;
            }
            CheckedExecutionEvent::AutomaticLifetimeEnd(_)
            | CheckedExecutionEvent::ResourceObservation(_)
            | CheckedExecutionEvent::ReturnProposition(_)
            | CheckedExecutionEvent::ResourceRewrite(_)
            | CheckedExecutionEvent::PopulationAuthorityRewrite(_)
            | CheckedExecutionEvent::PopulationMemberRewrite(_)
            | CheckedExecutionEvent::IteratedStep(_)
            | CheckedExecutionEvent::TacticApplication(_) => {
                pending_call_views.clear();
                continue;
            }
        };
        let right_shape = if statement {
            matches!(
                checked_evidence_conclusion(theorem),
                Proposition::CStatementExecutes { .. } | Proposition::CStatementVerifies { .. }
            )
        } else {
            matches!(
                checked_evidence_conclusion(theorem),
                Proposition::CConditionEvaluates { .. }
            )
        };
        if !right_shape {
            return Err(if statement {
                "retained statement evidence has a non-statement conclusion"
            } else {
                "retained condition evidence has a non-condition conclusion"
            });
        }
    }
    Ok(())
}

impl ExecutionProofCore {
    pub(crate) fn register_current_call_views(&self, assumptions: &PureFactContext) {
        let Some(evidence_state) = &self.evidence_state else {
            return;
        };
        if evidence_state.memory() == self.state.memory() {
            return;
        }
        register_recomputed_call_views(
            &self.checked_call_events,
            evidence_state.memory(),
            self.state.memory(),
            assumptions,
        );
    }

    pub(crate) fn checked_call_events(&self) -> CheckedCallEvents {
        self.checked_call_events.clone()
    }

    fn retained_checked_callees(&self) -> Option<Arc<std::collections::BTreeSet<String>>> {
        if self.execution_evidence.is_empty() {
            return None;
        }
        let mut callees = std::collections::BTreeSet::new();
        let mut seen = std::collections::HashSet::new();
        for trace in &self.execution_evidence {
            collect_checked_callees(&trace.to_vec(), &mut seen, &mut callees);
        }
        Some(Arc::new(callees))
    }

    fn retained_applied_tactics(&self) -> std::collections::BTreeSet<String> {
        let mut tactics = std::collections::BTreeSet::new();
        for trace in &self.execution_evidence {
            collect_applied_tactics(&trace.to_vec(), &mut tactics);
        }
        tactics
    }

    fn retained_call_events(&self) -> CheckedCallEvents {
        let mut call_events = CheckedCallEvents::default();
        for trace in &self.execution_evidence {
            collect_retained_call_events(&trace.to_vec(), &mut call_events);
        }
        call_events
    }

    pub(crate) fn at_entry(state: CState, frontier: ExecutionFrontier) -> Self {
        let state: SharedValue<CState> = state.into();
        Self {
            initial_match_scope: state.clone(),
            checked_step_cases: (0, PureFactContext::new()),
            publication_case_facts: ExecutionFacts::new(),
            initial_match_reserved: Arc::new(std::sync::OnceLock::new()),
            state,
            evidence_state: None,
            evidence_completed: false,
            evidence_source: None,
            evidence_try_stack: Vec::new(),
            frontier,
            effect_facts: Default::default(),
            execution_evidence: vec![PersistentSequence::default()].into(),
            pending_loop_returns: Default::default(),
            completed_pending_loop_returns: None,
            pending_loop_return_start: None,
            loan_evidence: crate::kernel::loans::empty_checked_loan_evidence_sequence(),
            return_resource_rewrites: Default::default(),
            return_proof_contexts: Default::default(),
            return_pending_propositions: Default::default(),
            checked_call_events: CheckedCallEvents::new(),
            function_entry: None,
            entry_facts: None,
            frontier_loop_rules: Default::default(),
            execution_abstraction: false,
            concrete_loop_execution: false,
            function_entry_derivations: Default::default(),
            region_invariants_close_requested: false,
            checked_invariant_lowerings: None,
            next_opaque_call: 0,
            next_kernel_variable: 0,
            has_empty_execution_branch_leaf: false,
            has_structured_branch_history: false,
            unfolded_predicates: Default::default(),
        }
    }

    /// Checks the function entry under `facts` and keeps them as the lineage
    /// the proof's later facts descend from.
    pub(crate) fn record_checked_function_entry_with_facts(
        &mut self,
        function: &CFunction,
        arguments: &[CExpression],
        expected_entry_state: &CState,
        facts: &ProofFacts,
    ) -> Result<(), CRuntimeError> {
        self.record_checked_function_entry(
            function,
            arguments,
            expected_entry_state,
            facts.assumptions().clone(),
        )?;
        self.entry_facts = Some(facts.clone());
        Ok(())
    }

    /// The entry facts while the proof has not left its checked entry.
    pub(crate) fn entry_facts_at_entry(&self) -> Option<&ProofFacts> {
        (self.frontier.is_at_function_entry()
            && self.execution_evidence.len() == 1
            && self.execution_evidence[0].is_empty())
        .then_some(self.entry_facts.as_ref())
        .flatten()
    }

    pub(crate) fn record_checked_function_entry(
        &mut self,
        function: &CFunction,
        arguments: &[CExpression],
        expected_entry_state: &CState,
        assumptions: PureFactContext,
    ) -> Result<(), CRuntimeError> {
        if !self.frontier.is_at_function_entry()
            || self.execution_evidence.len() != 1
            || !self.execution_evidence[0].is_empty()
        {
            return Err(CRuntimeError::FunctionContract(
                "function entry must be checked before executing its body".into(),
            ));
        }
        let entry = CheckedFunctionEntry::check(
            &self.state,
            function,
            arguments,
            expected_entry_state,
            assumptions,
        )?;
        self.function_entry = Some(entry);
        Ok(())
    }

    /// Appends a checked statement's effects to the proof's effect list and
    /// returns how many of them are memory effects. A fact the list already
    /// holds is not appended and not counted.
    fn append_statement_effects(
        &mut self,
        execution_facts: &(impl ExecutionFactSource + ?Sized),
    ) -> usize {
        let mut memory_effects = 0;
        for fact in execution_facts.fact_iter() {
            let memory_effect = is_memory_effect(fact.proposition());
            if (memory_effect || fact.is_certified()) && !self.effect_facts.contains(fact) {
                self.effect_facts.push(fact.clone());
                memory_effects += usize::from(memory_effect);
            }
        }
        memory_effects
    }

    /// Records one statement theorem and the fact context it was proved
    /// under on the single open trace, once the theorem is checked to
    /// advance this frontier (`check_statement_evidence`).
    pub(crate) fn record_statement_transition(
        &mut self,
        function: &CFunction,
        arguments: &[CExpression],
        theorem: Theorem,
        context: PureFactContext,
        execution_facts: &(impl ExecutionFactSource + ?Sized),
        obligations: &[crate::kernel::ProofObligation],
    ) -> Result<(), EvidenceRefusal> {
        self.record_statement_transition_with_loan_evidence(
            function,
            arguments,
            theorem,
            context,
            execution_facts,
            obligations,
            &crate::kernel::loans::empty_checked_loan_evidence_sequence(),
        )
    }

    /// Records a statement theorem and appends the exact stable-view evidence
    /// emitted by the checked evaluator for that transition.
    pub(crate) fn record_statement_transition_with_loan_evidence(
        &mut self,
        function: &CFunction,
        arguments: &[CExpression],
        theorem: Theorem,
        context: PureFactContext,
        execution_facts: &(impl ExecutionFactSource + ?Sized),
        obligations: &[crate::kernel::ProofObligation],
        loan_evidence: &crate::kernel::loans::CheckedLoanCallEvidenceSequence,
    ) -> Result<(), EvidenceRefusal> {
        debug_assert_eq!(self.execution_evidence.len(), 1);
        let (outcome, source_after) = self.check_statement_evidence(
            function,
            arguments,
            &theorem,
            &context,
            execution_facts,
            obligations,
        )?;
        self.loan_evidence =
            crate::kernel::loans::concat_checked_loan_evidence(&self.loan_evidence, loan_evidence);
        let call_events = statement_call_havoc_views(&theorem)
            .into_iter()
            .map(|view| self.checked_call_events.new_event(view))
            .collect::<Vec<_>>();
        let memory_effects = self.append_statement_effects(execution_facts);
        for trace in self.execution_evidence.iter_mut() {
            trace.push(CheckedExecutionEvent::Statement(theorem.clone()));
            trace.push(CheckedExecutionEvent::Context(context.clone()));
            for call in &call_events {
                trace.push(CheckedExecutionEvent::Call(call.clone()));
            }
            trace.push(CheckedExecutionEvent::StatementEffects(memory_effects));
        }
        self.evidence_source = matches!(&outcome, CStatementOutcome::Normal(_))
            .then_some(source_after.clone())
            .flatten();
        // A `break` or `continue` this frontier's own region owns, rather
        // than one belonging to a concretely executed loop it contains.
        let region_loop_control = if self.frontier.continuations.is_empty()
            && (self.frontier.in_loop_body
                || matches!(self.frontier.region, ExecutionRegionKind::LoopBody))
        {
            match &outcome {
                CStatementOutcome::Break(_) => Some(LoopControlExit::Break),
                CStatementOutcome::Continue(_) => Some(LoopControlExit::Continue),
                _ => None,
            }
        } else {
            None
        };
        if let CStatementOutcome::Throw { .. } = &outcome
            && let Some(exceptional) = self
                .frontier
                .continuations
                .iter()
                .filter_map(|continuation| continuation.exceptional.as_ref())
                .next_back()
            && self
                .evidence_try_stack
                .last()
                .is_none_or(|frame| frame.binding != exceptional.binding)
        {
            self.evidence_try_stack.push(EvidenceTryFrame {
                binding: exceptional.binding.clone(),
                handler: exceptional.handler.clone(),
                tail_after_try: self
                    .frontier
                    .continuations
                    .iter()
                    .filter(|continuation| continuation.exceptional.is_some())
                    .rfind(|continuation| continuation.exceptional.is_some())
                    .and_then(|continuation| continuation.remaining.clone()),
                cleanup_unwind: exceptional.cleanup_unwind,
            });
        }
        match outcome {
            CStatementOutcome::Normal(next_state) => self.evidence_state = Some(*next_state),
            CStatementOutcome::Throw { state, .. }
                if self
                    .frontier
                    .continuations
                    .iter()
                    .any(|continuation| continuation.exceptional.is_some()) =>
            {
                // A throw inside a checked try body is an internal control
                // transfer. Keep the trace open while the surface executor
                // records the handler binding and moves the frontier there;
                // only an uncaught throw completes this execution evidence.
                self.evidence_state = Some(*state);
                self.evidence_completed = false;
            }
            CStatementOutcome::Return { state, .. } | CStatementOutcome::Throw { state, .. } => {
                self.evidence_state = Some(*state);
                self.evidence_completed = true;
            }
            CStatementOutcome::Break(state) | CStatementOutcome::Continue(state)
                if region_loop_control.is_some() =>
            {
                // A loop-preservation proof executes one body iteration in a
                // bounded region. Both controls reach that region's typed
                // boundary, and the path stops there: the enclosing loop rule
                // consumes the distinction, certifying a `break` as an exit
                // and a `continue` as the back edge. A continuation on this
                // frontier means the innermost loop is a concretely executed
                // one this region contains, which is resumed below instead.
                self.frontier.loop_control =
                    region_loop_control.expect("the guard matched a loop control");
                self.frontier.position = FrontierPosition::RegionBoundary;
                self.evidence_state = Some(*state);
                self.evidence_completed = true;
            }
            CStatementOutcome::Break(state) => {
                let source_after = self.advance_loop_control(false, source_after)?;
                self.evidence_source = source_after;
                self.evidence_state = Some(*state);
                self.evidence_completed = false;
            }
            CStatementOutcome::Continue(state) => {
                let source_after = self.advance_loop_control(true, source_after)?;
                self.evidence_source = source_after;
                self.evidence_state = Some(*state);
                self.evidence_completed = false;
            }
            CStatementOutcome::Jump { target, state } => {
                if self.frontier.natural_backedge_target == Some(target)
                    && self.frontier.in_loop_body
                {
                    self.frontier.position = FrontierPosition::RegionBoundary;
                    self.frontier.loop_control = LoopControlExit::BodyEnd;
                    self.evidence_state = Some(*state);
                    self.evidence_completed = true;
                    return Ok(());
                }
                if self.frontier.natural_exit_target == Some(target) && self.frontier.in_loop_body {
                    self.frontier.position = FrontierPosition::RegionBoundary;
                    self.frontier.loop_control = LoopControlExit::NaturalExit(target);
                    self.evidence_state = Some(*state);
                    self.evidence_completed = true;
                    return Ok(());
                }
                let target = function
                    .control_target(target)
                    .ok_or_else(|| EvidenceRefusal::from("goto target is not in its function"))?;
                self.frontier.next_statement_index = target.statement_index;
                self.frontier.position = FrontierPosition::StatementEntry {
                    remaining: target.remaining.clone(),
                };
                self.evidence_source = Some(target.remaining.clone());
                self.evidence_state = Some(*state);
                self.evidence_completed = false;
            }
            // An error outcome is recorded so the driver reports it; it
            // completes the trace without a state a later theorem could
            // start from, and completion will not accept it as a path.
            CStatementOutcome::VerificationDiverges
            | CStatementOutcome::UndefinedBehavior(_)
            | CStatementOutcome::RuntimeError(_) => self.evidence_completed = true,
        }
        Ok(())
    }

    /// Consumes the innermost concrete-loop continuation for a checked
    /// `break`/`continue`. The ordinary statement theorem proves only the
    /// control statement itself; this frontier movement supplies the exact
    /// source that the next condition or statement theorem must consume.
    ///
    /// The continuation holds the source the driver's frontier saw when it
    /// entered the loop: the loop head followed by the rest of the region
    /// that contains the loop. For a loop nested in another concretely
    /// executed loop that region is the enclosing body alone; the enclosing
    /// loop head and everything after it live in the next continuation
    /// down. The frontier resumes from that body tail, as it does when the
    /// loop exits at its head. The evidence source is the kernel's own:
    /// `validated_source_after`, the source left after the control
    /// statement's theorem, still holds the rest of this body, this loop
    /// head and whatever follows the head, so the source the next theorem
    /// must consume is read from it at the head, never from the
    /// continuation's shorter view.
    fn advance_loop_control(
        &mut self,
        continue_statement: bool,
        validated_source_after: Option<Arc<CStatement>>,
    ) -> Result<Option<Arc<CStatement>>, EvidenceRefusal> {
        let continuation = self
            .frontier
            .continuations
            .pop()
            .ok_or_else(|| EvidenceRefusal::from("loop control has no enclosing loop"))?;
        let Some(loop_source) = continuation.remaining else {
            return Err(EvidenceRefusal::from(
                "loop control has an empty enclosing-loop continuation",
            ));
        };
        let (loop_head, frontier_tail) = split_shared_source(&loop_source);
        let (next_statement_index, source_after) = if continue_statement {
            // The validated tail still contains the rest of the source body
            // before the loop head. Preserve the exact loop head (and any
            // enclosing-loop suffix after it) rather than treating that body
            // tail as the next frontier statement.
            let source_after =
                loop_head_source(validated_source_after, &loop_head).or(Some(loop_source.clone()));
            self.frontier.position = FrontierPosition::StatementEntry {
                remaining: loop_source.clone(),
            };
            (continuation.next_statement_index, source_after)
        } else {
            // A `break` leaves the loop: the source after it is what follows
            // this loop head in the validated tail. The continuation's own
            // tail is the fallback when the head is not found there, and is
            // what the driver's frontier resumes from either way.
            let source_after = loop_head_source(validated_source_after, &loop_head)
                .map(|from_head| split_shared_source(&from_head).1)
                .unwrap_or_else(|| frontier_tail.clone());
            self.frontier.position = match &frontier_tail {
                Some(remaining) => FrontierPosition::StatementEntry {
                    remaining: remaining.clone(),
                },
                None => FrontierPosition::RegionBoundary,
            };
            (continuation.loop_exit_statement_index, source_after)
        };
        self.frontier.next_statement_index = next_statement_index;
        Ok(source_after)
    }

    /// Forks the single open trace into one trace per outcome theorem, each
    /// recording its theorem and the shared context they were proved under,
    /// once every theorem is checked to advance this frontier.
    pub(crate) fn record_statement_outcomes(
        &mut self,
        function: &CFunction,
        arguments: &[CExpression],
        outcomes: &[(
            Theorem,
            &(impl ExecutionFactSource + ?Sized),
            &[crate::kernel::ProofObligation],
        )],
        context: PureFactContext,
    ) -> Result<(), EvidenceRefusal> {
        debug_assert_eq!(self.execution_evidence.len(), 1);
        for (theorem, execution_facts, obligations) in outcomes {
            let (outcome, _) = self.check_statement_evidence(
                function,
                arguments,
                theorem,
                &context,
                execution_facts,
                obligations,
            )?;
            if matches!(outcome, CStatementOutcome::Normal(_)) {
                return Err("an outcome fork records only completing outcomes".into());
            }
        }
        let prefix = self.execution_evidence.first().cloned().unwrap_or_default();
        let mut traces = Vec::with_capacity(outcomes.len());
        for (theorem, _, _) in outcomes {
            let mut trace = prefix.clone();
            trace.push(CheckedExecutionEvent::Statement(theorem.clone()));
            trace.push(CheckedExecutionEvent::Context(context.clone()));
            for view in statement_call_havoc_views(theorem) {
                let event = self.checked_call_events.new_event(view);
                trace.push(CheckedExecutionEvent::Call(event));
            }
            traces.push(trace);
        }
        self.execution_evidence = traces.into();
        self.evidence_state = None;
        self.evidence_source = None;
        self.evidence_completed = true;
        Ok(())
    }

    /// Retains one returned path of a summarized loop while this core follows
    /// the loop's continuing successor.
    ///
    /// `parent` is this core as it was before the loop's continuing theorem
    /// was recorded: the returned path forks from that single open trace.
    /// The `Return` theorem is checked against the parent exactly as a
    /// recorded transition would be, so it proves the loop statement the
    /// frontier was about to run, from the state it was in, under the
    /// retained premises. The published outcome is checked again at
    /// completion against the trace, like every other path's.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_pending_loop_return(
        &mut self,
        parent: &Self,
        function: &CFunction,
        arguments: &[CExpression],
        theorem: &Theorem,
        context: &PureFactContext,
        execution_facts: &(impl ExecutionFactSource + ?Sized),
        obligations: &[crate::kernel::ProofObligation],
        outcome: CFunctionOutcome,
        completed_execution_facts: ExecutionFacts,
        completed_obligations: Vec<crate::kernel::ProofObligation>,
        pure_facts: ProofFacts,
        loan_evidence: crate::kernel::loans::CheckedLoanCallEvidenceSequence,
        loop_index: Option<usize>,
        return_index: usize,
    ) -> Result<(), EvidenceRefusal> {
        if parent.execution_evidence.len() != 1
            || self.execution_evidence.len() != 1
            || parent.evidence_completed
            || self.evidence_completed
            || parent.completed_pending_loop_returns.is_some()
            || self.execution_evidence[0]
                .suffix_since(&parent.execution_evidence[0])
                .is_none()
        {
            return Err(
                "a loop's returned path does not fork from the step's single open trace".into(),
            );
        }
        let mut probe = parent.clone();
        let (statement_outcome, _) = probe.check_statement_evidence(
            function,
            arguments,
            theorem,
            context,
            execution_facts,
            obligations,
        )?;
        if !matches!(statement_outcome, CStatementOutcome::Return { .. }) {
            return Err("a loop's retained terminal path does not return".into());
        }
        if !matches!(
            outcome,
            CFunctionOutcome::Return { .. }
                | CFunctionOutcome::RuntimeError(_)
                | CFunctionOutcome::UndefinedBehavior(_)
        ) {
            return Err("a loop's returned path was published with a non-returning outcome".into());
        }
        let mut trace = parent.execution_evidence[0].clone();
        trace.push(CheckedExecutionEvent::Statement(theorem.clone()));
        trace.push(CheckedExecutionEvent::Context(context.clone()));
        for view in statement_call_havoc_views(theorem) {
            let event = self.checked_call_events.new_event(view);
            trace.push(CheckedExecutionEvent::Call(event));
        }
        self.pending_loop_returns.push(PendingLoopReturnPath {
            return_index,
            trace,
            loop_index,
            outcome,
            execution_facts: completed_execution_facts,
            obligations: completed_obligations,
            pure_facts,
            loan_evidence,
        });
        Ok(())
    }

    /// Already checked returns retained while the continuing path advances.
    pub(crate) fn pending_loop_returns(&self) -> impl Iterator<Item = &PendingLoopReturnPath> {
        self.pending_loop_returns.iter()
    }

    /// Appends each retained returned path once, after the live successor
    /// completes, in the same order as its checked trace.
    pub(crate) fn complete_pending_loop_returns(&mut self) -> Vec<PendingLoopReturnPath> {
        if self.pending_loop_returns.is_empty() || self.completed_pending_loop_returns.is_some() {
            return Vec::new();
        }
        self.pending_loop_return_start = Some(self.execution_evidence.len());
        let pending = self.pending_loop_returns.to_vec();
        self.completed_pending_loop_returns = Some(Arc::new(pending.clone()));
        for path in &pending {
            self.execution_evidence.push(path.trace.clone());
        }
        pending
    }

    /// The proof's fact base on a completed returned path of a summarized
    /// loop, by its index among this execution's paths; `None` for every
    /// other path, whose base is the proof's own facts.
    pub(crate) fn pending_loop_return_pure_facts(&self, path_index: usize) -> Option<&ProofFacts> {
        let start = self.pending_loop_return_start?;
        path_index
            .checked_sub(start)
            .and_then(|index| self.completed_pending_loop_returns.as_ref()?.get(index))
            .map(|path| &path.pure_facts)
    }

    /// The source loop and rule-return ordinal of a completed pending path.
    pub(crate) fn pending_loop_return_origin(&self, path_index: usize) -> Option<(usize, usize)> {
        let index = path_index.checked_sub(self.pending_loop_return_start?)?;
        let path = self.completed_pending_loop_returns.as_ref()?.get(index)?;
        Some((path.loop_index?, path.return_index))
    }

    pub(crate) fn pending_loop_return_loop_index(&self, path_index: usize) -> Option<usize> {
        let start = self.pending_loop_return_start?;
        path_index
            .checked_sub(start)
            .and_then(|index| self.completed_pending_loop_returns.as_ref()?.get(index))
            .and_then(|path| path.loop_index)
    }

    /// Forgets retained returned paths: a join that rebuilt this core's paths
    /// from its arms has already carried each arm's completed paths over.
    pub(crate) fn clear_pending_loop_returns(&mut self) {
        self.pending_loop_returns = Default::default();
        self.completed_pending_loop_returns = None;
        self.pending_loop_return_start = None;
    }

    /// The value and state a trace this frontier completed with a `return`
    /// returned, read from the theorem that completed it and the state the
    /// evidence reached after it (automatic lifetimes the `return` ended
    /// included). `None` for an open frontier or one completed otherwise.
    pub(crate) fn completed_return_outcome(&self) -> Option<(CValue, CState)> {
        if !self.evidence_completed || self.execution_evidence.len() != 1 {
            return None;
        }
        let state = self.evidence_state.clone()?;
        let theorem = self.execution_evidence[0]
            .iter()
            .rev()
            .find_map(|event| match event {
                CheckedExecutionEvent::Statement(theorem) => Some(theorem),
                _ => None,
            })?;
        match checked_evidence_conclusion(theorem) {
            Proposition::CStatementVerifies {
                outcome: CStatementOutcome::Return { value, .. },
                ..
            } => Some((value.clone(), state)),
            _ => None,
        }
    }

    /// The source the evidence has yet to consume: the kernel-held source
    /// once evidence is recorded, and before that the driver's frontier
    /// (the function body at entry). `None` when the source is exhausted,
    /// or at the driver's function exit or region boundary before any
    /// evidence.
    fn current_source<'a>(&'a self, function: &'a CFunction) -> Option<&'a CStatement> {
        if self.evidence_state.is_some() {
            return self.evidence_source.as_deref();
        }
        match &self.frontier.position {
            FrontierPosition::FunctionEntry => Some(function.body()),
            FrontierPosition::StatementEntry { remaining } => Some(remaining),
            FrontierPosition::FunctionExit { .. } | FrontierPosition::RegionBoundary => None,
        }
    }

    /// `current_source`, shared, for keeping it as it is.
    fn current_source_shared(&self, function: &CFunction) -> Option<Arc<CStatement>> {
        if self.evidence_state.is_some() {
            return self.evidence_source.clone();
        }
        match &self.frontier.position {
            FrontierPosition::FunctionEntry => Some(Arc::new(function.body().clone())),
            FrontierPosition::StatementEntry { remaining } => Some(remaining.clone()),
            FrontierPosition::FunctionExit { .. } | FrontierPosition::RegionBoundary => None,
        }
    }

    /// The next source statement, the head of the current source with
    /// leading `Skip`s passed over, and the shared tail after it. The head
    /// is borrowed from the source unless a `Skip` was passed over.
    fn next_source_statement_and_tail<'a>(
        &'a self,
        function: &'a CFunction,
    ) -> Option<(std::borrow::Cow<'a, CStatement>, Option<Arc<CStatement>>)> {
        use std::borrow::Cow;
        let source = self.current_source(function)?;
        let (mut head, mut tail) = split_shared_source(source);
        while matches!(*head, CStatement::Skip) {
            let Some(rest) = tail else {
                return Some((head, None));
            };
            let (rest_head, rest_tail) = split_shared_source(&rest);
            head = Cow::Owned(rest_head.into_owned());
            tail = rest_tail;
        }
        Some((head, tail))
    }

    /// The source left after a branch join consumes the parent's next `if`:
    /// the branch must split that `if`, and its shared continuation must
    /// be a prefix of the parent's tail, which the joined core continues.
    fn source_after_branch(
        &self,
        function: &CFunction,
        branch: &CheckedExecutionBranch,
    ) -> Result<Option<Arc<CStatement>>, &'static str> {
        let Some((statement, tail)) = self.next_source_statement_and_tail(function) else {
            return Err("a branch join was recorded with no source statement remaining");
        };
        if !statements_have_same_source(&statement, branch.start_statement()) {
            return Err("the branch split is not the parent's next source statement");
        }
        if !statement_sequence_has_same_source_prefix(branch.continuation(), tail.as_deref()) {
            return Err("the branch continuation does not begin the parent's remaining source");
        }
        Ok(tail)
    }

    /// Called only after the kernel admitted this logical frontier case.
    pub(in crate::kernel::proof) fn retain_step_case(&mut self, fact: Proposition) {
        self.checked_step_cases.0 += 1;
        crate::kernel::reasoning::path_facts::count_context_rebuild_entries(1);
        self.publication_case_facts
            .push(ExecutionPureFact::new(fact.clone()));
        self.checked_step_cases.1 = self.checked_step_cases.1.clone().assume_proposition(fact);
    }

    pub(crate) fn publication_case_prefix(&self) -> ExecutionFacts {
        self.publication_case_facts.clone()
    }

    /// Candidate publication retains the admitted case prefix and appends
    /// only this statement's own evidence. This carries no theorem authority.
    pub(crate) fn completed_path_facts(&self, delta: &ExecutionFacts) -> ExecutionFacts {
        let mut facts = self.publication_case_facts.clone();
        let delta = delta.filtered(|fact| !facts.contains(fact));
        facts.extend_shared(&delta);
        facts
    }

    /// A local context for a presentation containing exactly these admitted
    /// cases. The caller still checks every selected premise against its
    /// ProofFacts; presentation never supplies semantic authority.
    pub(crate) fn checked_step_case_context(&self, count: usize) -> Option<PureFactContext> {
        (self.checked_step_cases.0 == count).then(|| self.checked_step_cases.1.clone())
    }

    /// The state the retained evidence has reached, or the core's state
    /// before any evidence is recorded.
    pub(crate) fn reached_state(&self) -> &CState {
        self.evidence_state.as_ref().unwrap_or(&self.state)
    }

    pub(crate) fn loan_evidence(&self) -> &crate::kernel::loans::CheckedLoanCallEvidenceSequence {
        &self.loan_evidence
    }

    /// The state the frontier's next theorem must start from: the state the
    /// evidence has reached. Before any evidence, at function entry, the
    /// core holds the caller-side state (resource observations and
    /// rewrites recorded there keep that form, and the trace holds their
    /// entry-bound states); the theorem starts from binding the arguments
    /// in it, as the recorded observations were bound.
    fn running_state(
        &self,
        function: &CFunction,
        arguments: &[CExpression],
    ) -> Result<std::borrow::Cow<'_, CState>, EvidenceRefusal> {
        use std::borrow::Cow;
        if self.evidence_completed {
            return Err("evidence was recorded after the trace completed".into());
        }
        if let Some(state) = &self.evidence_state {
            return Ok(Cow::Borrowed(state));
        }
        if !matches!(self.frontier.position, FrontierPosition::FunctionEntry) {
            return Ok(Cow::Borrowed(&self.state));
        }
        crate::kernel::c_function_entry_state(&self.state, function, arguments)
            .map(Cow::Owned)
            .ok_or_else(|| EvidenceRefusal::from("the function's arguments do not bind at entry"))
    }

    /// Materialize the already checked function entry before a proof-only
    /// interface split. Its arms and successor must use the same bound state
    /// as the retained trace, even though no C statement has run yet.
    pub(crate) fn materialize_function_entry(&mut self) -> Result<(), &'static str> {
        if !self.frontier.is_at_function_entry() || self.frontier.entry_member_prefix {
            return Ok(());
        }
        let entry = self
            .function_entry
            .as_ref()
            .ok_or("an entry interface requires a checked function entry")?;
        let caller = entry.caller_state().clone();
        let bound =
            crate::kernel::c_function_entry_state(&self.state, &entry.function, &entry.arguments)
                .ok_or("the interface could not bind function arguments")?;
        let source = Arc::new(entry.function.body().clone());
        if self
            .evidence_state
            .as_ref()
            .is_some_and(|state| state != &bound)
        {
            return Err("the entry interface does not follow its retained state");
        }
        self.state = bound.clone().into();
        self.evidence_state = Some(bound);
        self.frontier.execution_start_state = Some(caller);
        self.frontier.entry_member_prefix = true;
        self.evidence_source = Some(source);
        Ok(())
    }

    /// Advances evidence tracking across an entered `try` where linear
    /// matching fails. Each rule fires only where the linear rules below
    /// would refuse, so existing green behavior is unchanged:
    /// - descent: the expected head is a `Try` node and the offered theorem
    ///   proves its body head. Pushes the handler frame and continues into
    ///   the body. Whole-`try` theorems still match linearly above and never
    ///   reach this rule.
    /// - handler binding: the offered theorem declares or assigns the top
    ///   frame's handler binding. These micro-steps are not in any source
    ///   tree, so the source is left unchanged for the handler body.
    /// - handler entry: the offered theorem proves the top frame's handler
    ///   head. Pops the frame and continues into the handler.
    /// - normal exit: no source remains, a frame is open, and the offered
    ///   theorem proves the frame's tail head. Pops the frame and continues
    ///   past the `try`.
    ///
    /// Returns the new source after the offered theorem, or `None` when no try
    /// rule applies (the caller then runs the linear rules unchanged). Only
    /// the typed C++ frontend produces `TryCatchInt32`, so C evidence never
    /// takes these branches.
    fn try_evidence_source_after(
        &mut self,
        function: &CFunction,
        proved_statement: &CStatement,
    ) -> Option<Option<Arc<CStatement>>> {
        let next_tail = self.next_source_statement_and_tail(function);
        // Binding micro-steps and handler heads are meaningful only while
        // a `try` frame is open; without one there is nothing to route to.
        let frame_binding_matches = |frame: &EvidenceTryFrame| match proved_statement {
            CStatement::Declare { name, .. } | CStatement::Assign { name, .. } => {
                *name == frame.binding
            }
            _ => false,
        };
        if let Some(frame) = self.evidence_try_stack.last()
            && frame_binding_matches(frame)
        {
            return Some(self.evidence_source.clone());
        }
        // A routed C++ cleanup handler can begin with synthetic `skip`
        // nodes. Its user-visible destructor is still an internal handler
        // statement, so consume that handler source one statement at a time
        // while the surface frontier remains outside the original source.
        if next_tail.is_none() {
            if self.evidence_try_stack.last().is_some_and(|frame| {
                frame.cleanup_unwind
                    && matches!(
                        split_shared_source(&frame.handler).0.as_ref(),
                        CStatement::Throw(_)
                    )
                    && !matches!(proved_statement, CStatement::Throw(_))
            }) {
                self.evidence_try_stack.pop();
                return self.try_evidence_source_after(function, proved_statement);
            }
            let mut handler_source = self.evidence_try_stack.last()?.handler.clone();
            loop {
                let (head, tail) = split_shared_source(&handler_source);
                if matches!(head.as_ref(), CStatement::Skip) {
                    let Some(next) = tail else { break };
                    handler_source = next;
                    continue;
                }
                if statements_have_same_source(&head, proved_statement) {
                    if let Some(frame) = self.evidence_try_stack.last_mut() {
                        if let Some(tail) = tail {
                            frame.handler = tail;
                        } else {
                            self.evidence_try_stack.pop();
                        }
                    }
                    return Some(self.evidence_source.clone());
                }
                break;
            }
        }
        if let Some((next, tail)) = &next_tail {
            let next: &CStatement = next;
            // Never shadow linear matching: an offered theorem the linear
            // rules accept must keep going through them (including whole-
            // `try` theorems and ordinary declares inside `try` bodies).
            if statements_have_same_source(next, proved_statement) {
                // A body theorem can be the first statement after a nested
                // try. Linear matching is still authoritative for the
                // source advance, but consuming that tail also closes the
                // nested evidence frame; otherwise the following outer
                // handler/return sees a stale frame and reports no source.
                if let Some(frame) = self.evidence_try_stack.last()
                    && let Some(tail_after) = &frame.tail_after_try
                {
                    let (tail_head, _) = split_shared_source(tail_after);
                    if statements_have_same_source(&tail_head, proved_statement) {
                        self.evidence_try_stack.pop();
                    }
                }
                return None;
            }
            if let CStatement::TryCatchInt32 {
                try_body,
                binding,
                handler,
                cleanup_unwind,
            } = next
            {
                let (body_head, body_tail) = split_shared_source(try_body);
                if statements_have_same_source(&body_head, proved_statement) {
                    self.evidence_try_stack.push(EvidenceTryFrame {
                        binding: binding.clone(),
                        handler: Arc::new((**handler).clone()),
                        tail_after_try: tail.clone(),
                        cleanup_unwind: *cleanup_unwind,
                    });
                    return Some(body_tail);
                }
            }
            if let Some(frame) = self.evidence_try_stack.last() {
                let (handler_head, handler_tail) = split_shared_source(&frame.handler);
                if statements_have_same_source(&handler_head, proved_statement) {
                    let frame = self
                        .evidence_try_stack
                        .last()
                        .expect("handler frame just matched");
                    let cleanup_rethrows = frame.cleanup_unwind
                        && handler_tail.as_ref().is_some_and(|tail| {
                            let (tail_head, tail_tail) = split_shared_source(tail);
                            matches!(tail_head.as_ref(), CStatement::Throw(_))
                                && tail_tail.is_none()
                        });
                    self.evidence_try_stack.pop();
                    if cleanup_rethrows {
                        return Some(self.evidence_source.clone());
                    }
                    return Some(handler_tail);
                }
            }
            return None;
        }
        // No source remains: a normal `try` exit pops the open frame when
        // the offered theorem proves its tail head. Anything else keeps the
        // existing no-source error below.
        if let Some(frame) = self.evidence_try_stack.last()
            && let Some(tail_after) = &frame.tail_after_try
        {
            let (tail_head, tail_tail) = split_shared_source(tail_after);
            if statements_have_same_source(&tail_head, proved_statement) {
                self.evidence_try_stack.pop();
                return Some(tail_tail);
            }
        }
        None
    }

    /// Checks that a statement theorem advances this frontier: it proves
    /// the frontier's next source statement (a `Skip` theorem consumes
    /// nothing) from the running state, modulo definitionally equal
    /// resource representation (and, before the first C operation of a
    /// checked entry, the representation-only change resource scopes
    /// make), and every premise it assumes is retained by the context it
    /// was proved under, the step's execution facts and obligations, the
    /// effect facts recorded so far, the running resources, or the checked
    /// entry's relation facts. Definitional comparisons run under the
    /// entry assumptions plus the theorem's own premises, as the
    /// end-of-proof walk runs them. This is that walk's judgment, made at
    /// the step.
    fn check_statement_evidence(
        &mut self,
        function: &CFunction,
        arguments: &[CExpression],
        theorem: &Theorem,
        context: &PureFactContext,
        execution_facts: &(impl ExecutionFactSource + ?Sized),
        obligations: &[crate::kernel::ProofObligation],
    ) -> Result<(CStatementOutcome, Option<Arc<CStatement>>), EvidenceRefusal> {
        // Owned (not borrowed) so try-evidence advancement below can take
        // `&mut self`; `CState` clones are persistent-structure shares.
        let running_state = self.running_state(function, arguments)?.into_owned();
        let (proved_state, proved_statement, outcome) =
            match crate::kernel::api::proof_evidence_conclusion(theorem) {
                Proposition::CStatementVerifies {
                    state,
                    statement,
                    outcome,
                } => (state, statement, outcome),
                _ => {
                    return Err("retained statement evidence has a non-statement conclusion".into());
                }
            };
        match (&**proved_statement, outcome) {
            (
                CStatement::Goto { target: expected },
                CStatementOutcome::Jump { target: actual, .. },
            ) if expected == actual && function.control_target(*actual).is_some() => {}
            (CStatement::Goto { .. }, _) => {
                return Err("goto evidence does not carry its checked function target".into());
            }
            (
                CStatement::While {
                    backedge_target: Some(_),
                    natural_exit_target: Some(expected),
                    ..
                },
                CStatementOutcome::Jump { target: actual, .. },
            ) if expected == actual && function.control_target(*actual).is_some() => {}
            (_, CStatementOutcome::Jump { .. }) => {
                return Err("non-goto evidence carries a control-flow jump".into());
            }
            _ => {}
        }
        // The source left after the theorem: a `Skip` theorem consumes a
        // `Skip` at the head of the source when there is one and otherwise
        // nothing; another theorem consumes its statement after the
        // `Skip`s before it.
        let source_after = if matches!(&**proved_statement, CStatement::Skip) {
            match self.current_source(function) {
                Some(source) => {
                    let (head, tail) = split_shared_source(source);
                    if matches!(*head, CStatement::Skip) {
                        tail
                    } else {
                        self.current_source_shared(function)
                    }
                }
                None => None,
            }
        } else if matches!(&**proved_statement, CStatement::Seq(..))
            && self
                .current_source(function)
                .is_some_and(|source| *source == **proved_statement)
        {
            // A checked sequence may cover the entire remaining source. This
            // is exact structural identity, not a search through the suffix.
            // In particular an executes proof checks call + return together.
            None
        } else {
            // Try-evidence rules (descent into `try` bodies, handler-entry
            // binding and handler heads, normal `try` exits) fire only
            // where the linear rules below would refuse — the helper
            // returns `None` whenever normal matching, the `do`-`while`
            // rule, or the existing errors apply — so existing green
            // behavior is unchanged. Only the typed C++ frontend produces
            // `TryCatchInt32`, so C evidence never resolves here.
            if let Some(source_after) = self.try_evidence_source_after(function, proved_statement) {
                source_after
            } else {
                let Some((next, tail)) = self.next_source_statement_and_tail(function) else {
                    return Err(
                        "statement evidence was recorded with no source statement remaining".into(),
                    );
                };
                let do_while_initial_body = match &*next {
                    CStatement::While {
                        condition,
                        invariant,
                        invariant_checks,
                        effect_checks,
                        resource_specs,
                        ranking_measures,
                        structural_measure,
                        do_while: true,
                        backedge_target: None,
                        natural_exit_target: None,
                        body,
                    } if !matches!(&**proved_statement, CStatement::While { .. }) => {
                        let (body_head, body_tail) = split_shared_source(body);
                        if !statements_have_same_source(&body_head, proved_statement) {
                            return Err(EvidenceRefusal {
                                reason: "statement evidence does not prove the frontier's next source statement",
                                expected: Some(next.into_owned()),
                                proved: Some(*proved_statement.clone()),
                                premise: None,
                            });
                        }
                        let loop_head = CStatement::While {
                            condition: condition.clone(),
                            invariant: invariant.clone(),
                            invariant_checks: invariant_checks.clone(),
                            effect_checks: effect_checks.clone(),
                            resource_specs: resource_specs.clone(),
                            ranking_measures: ranking_measures.clone(),
                            structural_measure: structural_measure.clone(),
                            do_while: false,
                            backedge_target: None,
                            natural_exit_target: None,
                            body: body.clone(),
                        };
                        let loop_continuation =
                            prepend_shared_source(Arc::new(loop_head), tail.clone());
                        Some(match body_tail {
                            Some(body_tail) => {
                                prepend_shared_source(body_tail, Some(loop_continuation))
                            }
                            None => loop_continuation,
                        })
                    }
                    _ => None,
                };
                if !statements_have_same_source(&next, proved_statement)
                    && do_while_initial_body.is_none()
                {
                    return Err(EvidenceRefusal {
                        reason: "statement evidence does not prove the frontier's next source statement",
                        expected: Some(next.into_owned()),
                        proved: Some(*proved_statement.clone()),
                        premise: None,
                    });
                }
                do_while_initial_body.or(tail)
            }
        };
        self.check_evidence_state_and_premises(
            function,
            &running_state,
            theorem,
            context,
            proved_state,
            execution_facts,
            obligations,
        )?;
        Ok((outcome.clone(), source_after))
    }

    /// Checks that a condition theorem decides the frontier's next `if` or
    /// `while` (a loop head re-entered from its body is the frontier's next
    /// statement again) from the running state, under retained premises:
    /// the statement judgment for the theorem that selects an arm or a
    /// loop iteration.
    fn check_condition_evidence(
        &self,
        function: &CFunction,
        arguments: &[CExpression],
        theorem: &Theorem,
        context: &PureFactContext,
        path_facts: &[Proposition],
        obligations: &[crate::kernel::ProofObligation],
    ) -> Result<(CState, Option<Arc<CStatement>>), EvidenceRefusal> {
        let running_state = self.running_state(function, arguments)?;
        let (proved_state, proved_condition, value) =
            match crate::kernel::api::proof_evidence_conclusion(theorem) {
                Proposition::CConditionEvaluates {
                    state,
                    condition,
                    outcome: CConditionOutcome::Value(value),
                } => (state, condition, *value),
                _ => return Err("retained condition evidence has a non-value conclusion".into()),
            };
        let Some((mut next, mut tail)) = self.next_source_statement_and_tail(function) else {
            return Err(
                "condition evidence was recorded with no source statement remaining".into(),
            );
        };
        // A `do`-`while` runs its body before its condition is read, so a
        // condition decided at its head belongs to the body's first
        // statement, never to the loop: the source is the body followed by
        // an ordinary loop head, as for a statement theorem.
        while let CStatement::While {
            condition,
            invariant,
            invariant_checks,
            effect_checks,
            resource_specs,
            ranking_measures,
            structural_measure,
            do_while: true,
            backedge_target,
            natural_exit_target,
            body,
        } = &*next
        {
            if backedge_target.is_some() || natural_exit_target.is_some() {
                return Err(EvidenceRefusal {
                    reason: "condition evidence does not decide the frontier's next `if` or `while`",
                    expected: Some(next.into_owned()),
                    proved: None,
                    premise: None,
                });
            }
            let loop_head = CStatement::While {
                condition: condition.clone(),
                invariant: invariant.clone(),
                invariant_checks: invariant_checks.clone(),
                effect_checks: effect_checks.clone(),
                resource_specs: resource_specs.clone(),
                ranking_measures: ranking_measures.clone(),
                structural_measure: structural_measure.clone(),
                do_while: false,
                backedge_target: None,
                natural_exit_target: None,
                body: body.clone(),
            };
            let unrolled = prepend_shared_source(
                Arc::new((**body).clone()),
                Some(prepend_shared_source(Arc::new(loop_head), tail)),
            );
            let (mut head, mut rest) = split_shared_source(&unrolled);
            while matches!(*head, CStatement::Skip) {
                let Some(following) = rest else {
                    break;
                };
                let (following_head, following_rest) = split_shared_source(&following);
                head = std::borrow::Cow::Owned(following_head.into_owned());
                rest = following_rest;
            }
            next = std::borrow::Cow::Owned(head.into_owned());
            tail = rest;
        }
        let decided = match &*next {
            CStatement::If { condition, .. } | CStatement::While { condition, .. } => condition,
            _ => {
                return Err(EvidenceRefusal {
                    reason: "condition evidence does not decide the frontier's next `if` or `while`",
                    expected: Some(next.into_owned()),
                    proved: None,
                    premise: None,
                });
            }
        };
        if decided != proved_condition {
            return Err(EvidenceRefusal {
                reason: "condition evidence does not decide the frontier's next source condition",
                expected: Some(next.clone().into_owned()),
                proved: None,
                premise: None,
            });
        }
        // The source left after the decision: the selected arm, or the loop
        // body followed by the loop head again, before the tail.
        let source_after = match &*next {
            CStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                let selected: &CStatement = if value { then_branch } else { else_branch };
                if matches!(selected, CStatement::Skip) {
                    tail
                } else {
                    Some(prepend_shared_source(Arc::new(selected.clone()), tail))
                }
            }
            CStatement::While {
                condition,
                invariant,
                invariant_checks,
                effect_checks,
                resource_specs,
                ranking_measures,
                structural_measure,
                body,
                ..
            } => {
                if value {
                    let loop_head = CStatement::While {
                        condition: condition.clone(),
                        invariant: invariant.clone(),
                        invariant_checks: invariant_checks.clone(),
                        effect_checks: effect_checks.clone(),
                        resource_specs: resource_specs.clone(),
                        ranking_measures: ranking_measures.clone(),
                        structural_measure: structural_measure.clone(),
                        do_while: false,
                        backedge_target: None,
                        natural_exit_target: None,
                        body: body.clone(),
                    };
                    let body_then_head = Arc::new(CStatement::Seq(
                        Arc::new((**body).clone()),
                        Arc::new(loop_head),
                    ));
                    Some(prepend_shared_source(body_then_head, tail))
                } else {
                    tail
                }
            }
            _ => tail,
        };
        let path_facts = path_facts
            .iter()
            .cloned()
            .map(ExecutionPureFact::new)
            .collect::<Vec<_>>();
        self.check_evidence_state_and_premises(
            function,
            &running_state,
            theorem,
            context,
            proved_state,
            &path_facts,
            obligations,
        )?;
        // A condition on a pending `malloc` result decides that allocation's
        // outcome: the reached state resolves the pending allocation from
        // the decided facts, the kernel rule execution applies right after
        // the condition.
        let mut reached = proved_state.clone();
        if reached.memory().has_pending_heap_allocation() {
            let no_assumptions = PureFactContext::new();
            let entry_assumptions = self
                .function_entry
                .as_ref()
                .map_or(&no_assumptions, |entry| entry.assumptions());
            let theorem_assumptions =
                crate::kernel::api::proof_evidence_assumptions(theorem, entry_assumptions);
            *reached =
                crate::kernel::resolve_pending_heap_allocations(&reached, &theorem_assumptions);
        }
        if let Some(pending) = &reached.pending_thread_create {
            let no_assumptions = PureFactContext::new();
            let entry_assumptions = self
                .function_entry
                .as_ref()
                .map_or(&no_assumptions, |entry| entry.assumptions());
            let theorem_assumptions =
                crate::kernel::api::proof_evidence_assumptions(theorem, entry_assumptions);
            let decided_assumptions =
                crate::kernel::reasoning::path_facts::assumptions_with_path_context(
                    &theorem_assumptions,
                    &path_facts,
                    obligations,
                );
            if let Some(resolved) = pending.resolve(&reached, &decided_assumptions) {
                *reached = resolved;
            }
        }
        // Likewise a condition on an acquire load's value keeps or exchanges
        // the subscriber right that load read through.
        if reached.resources.has_observed_publication_rights() {
            let no_assumptions = PureFactContext::new();
            let entry_assumptions = self
                .function_entry
                .as_ref()
                .map_or(&no_assumptions, |entry| entry.assumptions());
            let theorem_assumptions =
                crate::kernel::api::proof_evidence_assumptions(theorem, entry_assumptions);
            let decided_assumptions =
                crate::kernel::reasoning::path_facts::assumptions_with_path_context(
                    &theorem_assumptions,
                    &path_facts,
                    obligations,
                );
            *reached = crate::kernel::publication::resolve_observed_publications(
                &reached,
                &decided_assumptions,
            );
        }
        Ok((*reached, source_after))
    }

    /// The part of the evidence judgment shared by statement and condition
    /// theorems: the theorem starts from the running state, and every
    /// premise it assumes is retained.
    #[allow(clippy::too_many_arguments)]
    fn check_evidence_state_and_premises(
        &self,
        function: &CFunction,
        running_state: &CState,
        theorem: &Theorem,
        context: &PureFactContext,
        proved_state: &CState,
        execution_facts: &(impl ExecutionFactSource + ?Sized),
        obligations: &[crate::kernel::ProofObligation],
    ) -> Result<(), EvidenceRefusal> {
        let no_assumptions = PureFactContext::new();
        let entry_assumptions = self
            .function_entry
            .as_ref()
            .map_or(&no_assumptions, |entry| entry.assumptions());
        // The representation-only change before the first operation is
        // allowed against the checked entry state itself: once the trace
        // holds an observation or rewrite, the theorem follows its state.
        let at_checked_entry = matches!(self.frontier.position, FrontierPosition::FunctionEntry)
            && self.function_entry.is_some()
            && self.execution_evidence.iter().all(|trace| trace.is_empty());
        // A theorem lists the whole context it executed under as premises,
        // so the assumption set it needs for a definitional comparison is
        // built only when the states are not identical.
        let states_match = *running_state == *proved_state
            || if at_checked_entry {
                crate::kernel::api::function_entry_representation_states_match(
                    function,
                    running_state,
                    proved_state,
                    entry_assumptions,
                )
            } else {
                let theorem_assumptions =
                    crate::kernel::api::proof_evidence_assumptions(theorem, entry_assumptions);
                crate::kernel::api::execution_evidence_states_match(
                    function,
                    running_state,
                    proved_state,
                    &theorem_assumptions,
                )
            };
        let states_match = states_match
            || proved_state
                .pending_thread_create
                .as_ref()
                .is_some_and(|pending| {
                    let theorem_assumptions =
                        crate::kernel::api::proof_evidence_assumptions(theorem, entry_assumptions);
                    pending
                        .resolve(proved_state, &theorem_assumptions)
                        .is_some_and(|resolved| resolved == *running_state)
                });
        if !states_match {
            return Err("evidence does not start from the running state".into());
        }
        // Premise availability is a set question. Retain both ordered streams
        // by their persistent roots; the premise checker deduplicates only if
        // a theorem actually needs its fallback set. Do not rebuild the whole
        // effect history before every statement's ordinary context check.
        let mut retained_execution_facts = execution_facts.persistent_facts();
        retained_execution_facts.extend_shared(&self.effect_facts);
        let entry_relation_facts = self
            .function_entry
            .as_ref()
            .and_then(|entry| entry.relation_facts());
        if let Some(premise) = crate::kernel::api::proof_evidence_unretained_premise(
            theorem,
            entry_assumptions,
            Some(context),
            &retained_execution_facts,
            obligations,
            running_state,
            entry_relation_facts,
        ) {
            return Err(EvidenceRefusal {
                reason: "evidence assumes a premise the proof did not retain",
                expected: None,
                proved: None,
                premise: Some(premise),
            });
        }
        if running_state.memory() != proved_state.memory() {
            let theorem_assumptions =
                crate::kernel::api::proof_evidence_assumptions(theorem, entry_assumptions);
            register_recomputed_call_views(
                &self.checked_call_events,
                running_state.memory(),
                proved_state.memory(),
                &theorem_assumptions,
            );
        }
        Ok(())
    }

    /// Records one condition theorem and the fact context it was proved
    /// under on the single open trace, once the theorem is checked to
    /// decide the frontier's next `if` or `while`
    /// (`check_condition_evidence`). `path_facts` are the kernel-issued
    /// facts of the path the decision selects; the theorem may assume
    /// them.
    pub(crate) fn record_condition_transition(
        &mut self,
        function: &CFunction,
        arguments: &[CExpression],
        theorem: Theorem,
        context: PureFactContext,
        path_facts: &[Proposition],
        obligations: &[crate::kernel::ProofObligation],
    ) -> Result<(), EvidenceRefusal> {
        debug_assert_eq!(self.execution_evidence.len(), 1);
        let (reached, source_after) = self.check_condition_evidence(
            function,
            arguments,
            &theorem,
            &context,
            path_facts,
            obligations,
        )?;
        for trace in self.execution_evidence.iter_mut() {
            trace.push(CheckedExecutionEvent::Condition(theorem.clone()));
            trace.push(CheckedExecutionEvent::Context(context.clone()));
        }
        for fact in path_facts {
            let fact = ExecutionPureFact::new(fact.clone());
            if !self.publication_case_facts.contains(&fact) {
                self.publication_case_facts.push(fact);
            }
        }
        self.evidence_state = Some(reached);
        self.evidence_source = source_after;
        Ok(())
    }

    pub(crate) fn record_proof_case_arm(
        &mut self,
        partition: Arc<CheckedProofCasePartition>,
        arm_index: usize,
        facts: ProofFacts,
    ) -> bool {
        // A generative constructor witness belongs to the exact state its
        // partition was issued against: no C step may run between the split
        // and its arms. Recorded evidence before the split is no obstacle —
        // the witnesses were checked fresh against the whole region.
        if partition
            .witness_scope
            .as_ref()
            .is_some_and(|scope| !self.state.shares_storage_with(scope))
        {
            return false;
        }
        let arm = CheckedProofCaseArm {
            partition,
            arm_index,
            facts,
        };
        if !arm.is_valid() {
            return false;
        }
        for trace in self.execution_evidence.iter_mut() {
            trace.push(CheckedExecutionEvent::ProofCase(arm.clone()));
        }
        true
    }

    /// Rejoins the live arms of the partition they entered and continues
    /// this core, a copy of `parent`, from their one state. Returns the
    /// facts the proof holds after the join (the partition's root facts plus
    /// what every live arm established) and whether any arm advanced the C
    /// program or changed the state. `arms` has one entry per case of the
    /// partition, `None` for an excluded one.
    pub(crate) fn record_proof_case_join(
        &mut self,
        parent: &ExecutionProofCore,
        arms: &[(&ExecutionProofCore, &ProofFacts)],
        function: &CFunction,
        arguments: &[CExpression],
        successor_facts: &ProofFacts,
    ) -> Result<bool, &'static str> {
        let join = CheckedProofCaseJoin::check(parent, arms, function, arguments, successor_facts)?;
        let changed_execution = join.arms_changed_execution();
        let first = arms[0].0;
        let mut trace = parent.execution_evidence[0].clone();
        let joined_state = join.joined_state().clone();
        trace.push(CheckedExecutionEvent::ProofCaseJoin(join));
        self.execution_evidence = vec![trace].into();
        self.checked_call_events = parent.checked_call_events.clone();
        self.evidence_state = Some(joined_state);
        // An arm that ran no C has recorded no source of its own yet; what
        // remains for it is what its frontier says.
        self.evidence_source = first.current_source_shared(function);
        self.evidence_try_stack = first.evidence_try_stack.clone();
        self.evidence_completed = false;
        Ok(changed_execution)
    }

    /// Rejoins two arms that ended in different states through an explicit
    /// interface, and continues this core, a copy of `parent`, from
    /// `joined_state`. Returns the effect facts the join certifies across
    /// both arms. The kernel recomputes the abstraction, so it installs the
    /// fresh-variable counter the abstraction left.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_interface_proof_case_join(
        &mut self,
        parent: &ExecutionProofCore,
        root_facts: &ProofFacts,
        arms: [(&ExecutionProofCore, &ProofFacts); 2],
        function: &CFunction,
        arguments: &[CExpression],
        stable_join_locals: &BTreeMap<String, CValue>,
        interface_specs: &[SpecProposition],
        interface_resource_specs: &[CResourceSpec],
        arm_effect_facts: [&(impl ExecutionFactSource + ?Sized); 2],
        joined_state: &CState,
        successor_facts: &ProofFacts,
        old_reference: Option<&CState>,
    ) -> Result<crate::kernel::ExecutionFacts, &'static str> {
        let join = CheckedProofCaseJoin::check_interface(
            parent,
            root_facts,
            arms,
            function,
            arguments,
            stable_join_locals,
            interface_specs,
            interface_resource_specs,
            arm_effect_facts,
            joined_state,
            successor_facts,
            old_reference,
        )?;
        let interface = join
            .interface
            .as_ref()
            .expect("an interface join retains its interface");
        let effect_facts = interface.effect_facts.clone();
        self.advance_kernel_variable_mark(interface.next_kernel_variable)?;
        let mut trace = parent.execution_evidence[0].clone();
        trace.push(CheckedExecutionEvent::ProofCaseJoin(join));
        self.execution_evidence = vec![trace].into();
        self.checked_call_events = parent.checked_call_events.clone();
        self.evidence_state = Some(joined_state.clone());
        // An arm that ran no C has recorded no source of its own yet; what
        // remains for it is what its frontier says.
        self.evidence_source = arms[0].0.current_source_shared(function);
        self.evidence_try_stack = arms[0].0.evidence_try_stack.clone();
        self.evidence_completed = false;
        Ok(effect_facts)
    }

    /// This execution's fresh-variable counter, execution-relative: the
    /// offset an [`ExecutionBudget`] is built from and reports back.
    pub(crate) fn kernel_variable_mark(&self) -> u64 {
        self.next_kernel_variable
    }

    /// The first identity this execution has not issued, as a `Variable` id.
    ///
    /// [`Self::kernel_variable_mark`] is execution-relative, so a freshness
    /// probe against a candidate identity must add the range base back before
    /// comparing: the identities this execution has issued are exactly
    /// `KERNEL_VARIABLE_BASE .. issued_kernel_variable_bound()`.
    pub(crate) fn issued_kernel_variable_bound(&self) -> u64 {
        ExecutionBudget::KERNEL_VARIABLE_BASE + self.next_kernel_variable
    }

    /// Moves this execution's counter forward to `mark`.
    ///
    /// This is the only way anything outside this module changes the counter,
    /// and it refuses a rewind. A lower mark would re-issue identities that
    /// loop havocs, opaque call results, heap allocations, join abstractions
    /// and resource model fields are still using, which is how two unrelated
    /// things come to be the same `Variable`.
    pub(crate) fn advance_kernel_variable_mark(&mut self, mark: u64) -> Result<(), &'static str> {
        if mark < self.next_kernel_variable {
            return Err("an execution's fresh-variable counter cannot move backwards");
        }
        self.next_kernel_variable = mark;
        Ok(())
    }

    /// Every variable the region this proof started in already mentions,
    /// built once and shared by every branch forked from it. This is the
    /// frontier-independent half of a constructor witness's freshness: the
    /// other half is [`Self::issued_kernel_variable_bound`], which closes the
    /// range holding everything the kernel has issued since, so no later
    /// frontier rescans the state.
    fn initial_match_reserved_variables(&self) -> &std::collections::BTreeSet<Variable> {
        self.initial_match_reserved.get_or_init(|| {
            use crate::kernel::CFunctionOutcome;
            #[cfg(test)]
            MATCH_SCOPE_INDEX_BUILDS.with(|count| count.set(count.get() + 1));
            let mut reserved = std::collections::BTreeSet::new();
            crate::kernel::reasoning::collect_c_state_bitvector_variables(
                &self.initial_match_scope,
                &mut reserved,
            );
            crate::kernel::reasoning::collect_c_state_bound_variables(
                &self.initial_match_scope,
                &mut reserved,
            );
            if let Some(entry) = self.function_entry.as_ref() {
                reserved.extend(crate::kernel::proposition_variables(
                    &Proposition::CFunctionExecutes {
                        state: Box::new(entry.caller_state.clone()),
                        function: Box::new(entry.function.as_ref().clone()),
                        arguments: entry.arguments.clone(),
                        outcome: CFunctionOutcome::Return {
                            value: CValue::Void,
                            state: Box::new(entry.entry_state.clone()),
                        },
                    },
                ));
            }
            reserved
        })
    }

    /// Constructor elimination at any frontier this proof has reached: a
    /// function entry, a loop body, or a point after checked C steps.
    ///
    /// The witnesses are fresh against everything the region can name. Its
    /// entry state (and, at a function entry, the entry theorem) is reserved
    /// once by [`Self::initial_match_reserved_variables`]; every variable the
    /// kernel has issued since lies in
    /// `KERNEL_VARIABLE_BASE .. issued_kernel_variable_bound()`, so the probe
    /// is one range test rather than a rescan of the current state. The
    /// environment, the scrutinee, and the persistent fact index are queried
    /// per candidate as before.
    pub(crate) fn algebraic_case_partition(
        &self,
        facts: &ProofFacts,
        value: &crate::kernel::AlgebraicTerm,
        environment: &crate::kernel::CExecutionEnvironment,
        definitions: &[crate::kernel::CCompositeResourceDefinition],
        matched_resource_field: Option<&crate::kernel::ResourceFieldProjection>,
        first_variable: u64,
        stride: u64,
    ) -> Option<(
        Arc<CheckedProofCasePartition>,
        Vec<Vec<(Variable, crate::kernel::Sort)>>,
        u64,
    )> {
        use crate::kernel::Term;
        if stride == 0 {
            return None;
        }
        // D7 in reverse, at the frontier the cases are taken from. A path
        // fact that refutes an arm's own fact says the folded instance's
        // model is not that constructor, and the body of a loop learns that
        // about a child it unfolded earlier only here: the `unfold` ran
        // before the cursor moved, and the loop head spoke about the frame
        // above (A26, gap 57b). The refutation is scoped to the scrutinee's
        // own instance, so the cost is that one instance's arms.
        let facts =
            &self.model_arm_refutations_for(facts, value, definitions, matched_resource_field);
        let reserved = self.initial_match_reserved_variables();
        // The identities this execution has issued are exactly
        // `KERNEL_VARIABLE_BASE .. issued_kernel_variable_bound()`.
        // `next_kernel_variable` is execution-relative, so comparing a
        // candidate's absolute id against it directly was comparing an
        // identity with an offset: the probe read as `candidate >= issued`
        // but `issued` was a few dozen, and every candidate cleared it.
        let issued = ExecutionBudget::KERNEL_VARIABLE_BASE..self.issued_kernel_variable_bound();
        let environment_variables =
            crate::kernel::reasoning::execution_environment_variable_index(environment);
        let value_variables = crate::kernel::proposition_variables(&Proposition::Equal(
            Term::Algebraic(value.clone()),
            Term::Algebraic(value.clone()),
        ));
        let mut next = first_variable;
        let mut overflow = false;
        let equations =
            crate::kernel::api::algebraic_constructor_case_equations(value, &mut || {
                loop {
                    let candidate = Variable(next);
                    #[cfg(test)]
                    MATCH_FRESHNESS_PROBES.with(|count| count.set(count.get() + 1));
                    if let Some(successor) = next.checked_add(stride) {
                        next = successor;
                    } else {
                        overflow = true;
                        return candidate;
                    }
                    if !issued.contains(&candidate.0)
                        && !reserved.contains(&candidate)
                        && !environment_variables.contains(&candidate)
                        && !value_variables.contains(&candidate)
                        && !facts.reserves_variable(candidate)
                    {
                        return candidate;
                    }
                }
            })?;
        if overflow {
            return None;
        }
        let (case_facts, bindings): (Vec<_>, Vec<_>) = equations.into_iter().unzip();
        let (arm_additions, arm_body_clauses): (Vec<_>, Vec<_>) = case_facts
            .iter()
            .map(|case| {
                let mut arm_facts = facts.with_fact(case.clone());
                // A concrete scrutinee already names its payload. Relate each
                // fresh pattern binding to that payload by checked constructor
                // injectivity, so resource unfolds and the written arm refer
                // to the same pointers and models.
                if let Some(fields) =
                    crate::kernel::assumptions::algebraic_constructor_field_equalities(case)
                {
                    for field in fields {
                        // Resource arms interpret pointer payloads at a proved
                        // program spelling. Publish that same one-hop transport
                        // here: constructor injectivity gives left = right and
                        // the existing exact alias gives left = spelling.
                        if let Proposition::ConditionIs(
                            crate::kernel::ConditionTerm::PointerEqual(left, right),
                            true,
                        ) = &field
                            && let Some(spelling) =
                                crate::kernel::functions::arm_pointer_program_spelling(
                                    left,
                                    facts.assumptions(),
                                )
                        {
                            arm_facts = arm_facts.with_fact(Proposition::ConditionIs(
                                crate::kernel::ConditionTerm::pointer_equal(
                                    spelling,
                                    (**right).clone(),
                                ),
                                true,
                            ));
                        }
                        arm_facts = arm_facts.with_fact(field);
                    }
                }
                let mut body_clauses = Vec::new();
                if let (
                    Some(projection),
                    Proposition::Equal(Term::Algebraic(model), Term::Algebraic(constructor)),
                ) = (matched_resource_field, case)
                {
                    body_clauses = crate::kernel::functions::matched_resource_instance_case_clauses(
                        &self.state,
                        projection,
                        model,
                        constructor,
                        definitions,
                        arm_facts.assumptions(),
                    );
                    for clause in &body_clauses {
                        arm_facts = arm_facts.with_fact(clause.proposition.clone());
                    }
                }
                // The surface binds pointer payloads at the same checked
                // program spelling as resource bodies and preserves existing
                // algebraic variables carried by a concrete constructor. Retain its
                // equation in that spelling too, so explicit rewrites of the
                // written match equation remain exact premises.
                if matches!(
                    value.node,
                    crate::kernel::AlgebraicTermNode::Constructor { .. }
                ) && let Proposition::Equal(left, Term::Algebraic(constructor)) = case
                    && let crate::kernel::AlgebraicTermNode::Constructor { variant, fields } =
                        &constructor.node
                {
                    let spelled_fields = fields
                        .iter()
                        .enumerate()
                        .map(|(index, field)| match field {
                            crate::kernel::AlgebraicValue::C(value) => {
                                crate::kernel::AlgebraicValue::C(
                                    crate::kernel::functions::arm_binding_program_spelling(
                                        value,
                                        arm_facts.assumptions(),
                                    )
                                    .unwrap_or_else(|| value.clone()),
                                )
                            }
                            crate::kernel::AlgebraicValue::Algebraic(_) => {
                                crate::kernel::arm_algebraic_payload_spelling(value, variant, index)
                                    .map(|payload| {
                                        crate::kernel::AlgebraicValue::Algebraic(payload.clone())
                                    })
                                    .unwrap_or_else(|| field.clone())
                            }
                            _ => field.clone(),
                        })
                        .collect::<Vec<_>>();
                    if spelled_fields != *fields {
                        let spelled = crate::kernel::AlgebraicTerm {
                            algebraic_type: constructor.algebraic_type.clone(),
                            node: crate::kernel::AlgebraicTermNode::Constructor {
                                variant: variant.clone(),
                                fields: spelled_fields,
                            },
                        };
                        arm_facts = arm_facts
                            .with_fact(Proposition::Equal(left.clone(), Term::Algebraic(spelled)));
                    }
                }
                (
                    arm_facts.introduced_since(facts).unwrap_or_default(),
                    body_clauses,
                )
            })
            .unzip();
        Some((
            Arc::new(CheckedProofCasePartition {
                identity: Arc::new(()),
                root_facts: facts.clone(),
                excluded: vec![None; case_facts.len()],
                case_facts,
                arm_additions,
                arm_body_clauses,
                witness_scope: Some(self.state.clone()),
            }),
            bindings,
            next,
        ))
    }

    /// `facts` together with the model facts this frontier's premises force
    /// on the instance whose model is `value`.
    ///
    /// This is [`crate::kernel::publish_instance_arms`]' refutation applied at
    /// one frontier rather than at contract lowering, a loop head, a back
    /// edge, or an `unfold`. Only the instance the case split is about is
    /// visited, and only when its model is still a symbolic variable, so the
    /// work is that instance's own arms and nothing else. Nothing is
    /// concluded that the refutation rule would not publish at those sites.
    fn model_arm_refutations_for(
        &self,
        facts: &ProofFacts,
        value: &crate::kernel::AlgebraicTerm,
        definitions: &[crate::kernel::CCompositeResourceDefinition],
        matched_resource_field: Option<&crate::kernel::ResourceFieldProjection>,
    ) -> ProofFacts {
        let crate::kernel::AlgebraicTermNode::Variable(variable) = value.node else {
            return facts.clone();
        };
        if definitions.is_empty() {
            return facts.clone();
        }
        let state: &crate::kernel::CState = &self.state;
        let assumptions = facts.assumptions();
        let mut extended = facts.clone();
        if let Some(projection) = matched_resource_field {
            if !projection.children.is_empty() {
                return extended;
            }
            let Some(instance) = state.owned_resource_instance(projection.identity) else {
                return extended;
            };
            if instance
                .fields()
                .get(projection.field_index)
                .is_some_and(|field| {
                    matches!(
                        field,
                        crate::kernel::AlgebraicValue::Algebraic(model) if model == value
                    )
                })
            {
                for published in crate::kernel::functions::instance_arm_model_facts(
                    instance,
                    definitions,
                    state,
                    assumptions,
                ) {
                    extended = extended.with_fact(published);
                }
            }
            return extended;
        }
        for fact in state.resources().facts() {
            let crate::kernel::CResource::Instance(instance) = fact.resource() else {
                continue;
            };
            if !instance.fields().iter().any(|field| {
                matches!(
                    field,
                    crate::kernel::AlgebraicValue::Algebraic(model)
                        if model.node == crate::kernel::AlgebraicTermNode::Variable(variable)
                )
            }) {
                continue;
            }
            for published in crate::kernel::functions::instance_arm_model_facts(
                instance,
                definitions,
                state,
                assumptions,
            ) {
                extended = extended.with_fact(published);
            }
        }
        extended
    }

    /// Forks the per-path evidence traces the way a post-execution case
    /// split forks the candidate paths: `plan[i]` keeps path `i`'s trace or
    /// splits it into two traces that each record one arm of a checked
    /// partition. The traces come out in the candidates' order (a kept
    /// trace, or the then-arm followed by the else-arm), so they stay
    /// zipped with the paths. A plan that does not cover every trace, or an
    /// arm whose facts do not extend the partition's root by exactly that
    /// arm's case fact, is rejected and changes nothing.
    pub(crate) fn fork_outcome_evidence(
        &mut self,
        plan: &[OutcomeEvidenceFork],
    ) -> Result<(), &'static str> {
        if plan.len() != self.execution_evidence.len() {
            return Err("outcome evidence fork plan does not cover every trace");
        }
        let mut traces = Vec::with_capacity(plan.len() * 2);
        fn append(
            trace: &PersistentSequence<CheckedExecutionEvent>,
            fork: &OutcomeEvidenceFork,
            traces: &mut Vec<PersistentSequence<CheckedExecutionEvent>>,
        ) -> Result<(), &'static str> {
            match fork {
                OutcomeEvidenceFork::Keep => traces.push(trace.clone()),
                OutcomeEvidenceFork::Split {
                    partition,
                    arm_facts,
                }
                | OutcomeEvidenceFork::NestedSplit {
                    partition,
                    arm_facts,
                    ..
                } => {
                    for (arm_index, facts) in arm_facts.iter().enumerate() {
                        let arm = CheckedProofCaseArm {
                            partition: partition.clone(),
                            arm_index,
                            facts: facts.clone(),
                        };
                        if !arm.is_valid() {
                            return Err(
                                "outcome evidence fork arm does not extend the partition root by its case fact",
                            );
                        }
                        let mut forked = trace.clone();
                        forked.push(CheckedExecutionEvent::ProofCase(arm));
                        if let OutcomeEvidenceFork::NestedSplit { arms, .. } = fork {
                            append(&forked, &arms[arm_index], traces)?;
                        } else {
                            traces.push(forked);
                        }
                    }
                }
            }
            Ok(())
        }
        for (trace, fork) in self.execution_evidence.iter().zip(plan) {
            append(trace, fork, &mut traces)?;
        }
        if let (Some(start), Some(completed)) = (
            self.pending_loop_return_start,
            self.completed_pending_loop_returns.as_ref(),
        ) {
            // The retained returned paths stay zipped with their traces: the
            // block now starts after every trace the plan produces for the
            // paths before it, and a split path repeats its entry per arm.
            let new_start: usize = plan[..start].iter().map(outcome_fork_count).sum();
            let mut remapped = Vec::with_capacity(completed.len());
            for (offset, fork) in plan[start..].iter().enumerate() {
                let Some(path) = completed.get(offset) else {
                    break;
                };
                for _ in 0..outcome_fork_count(fork) {
                    remapped.push(path.clone());
                }
            }
            self.pending_loop_return_start = Some(new_start);
            self.completed_pending_loop_returns = Some(Arc::new(remapped));
        }
        self.execution_evidence = traces.into();
        Ok(())
    }

    pub(crate) fn record_automatic_lifetime_end(
        &mut self,
        state: &CState,
        names: &[String],
    ) -> Result<CState, CRuntimeError> {
        if names.is_empty() {
            return Ok(state.clone());
        }
        let after_state = crate::kernel::eval::end_scope_automatic_lifetimes(state, names)?;
        if after_state == *state {
            return Ok(after_state);
        }
        if self.reached_state() != state {
            return Err(CRuntimeError::FunctionContract(
                "automatic lifetime end does not start from the running state".into(),
            ));
        }
        let end = CheckedAutomaticLifetimeEnd {
            before_state: state.clone(),
            after_state: after_state.clone(),
            names: names.to_vec(),
        };
        self.evidence_state = Some(after_state.clone());
        for trace in self.execution_evidence.iter_mut() {
            trace.push(CheckedExecutionEvent::AutomaticLifetimeEnd(end.clone()));
        }
        Ok(after_state)
    }

    /// Applies one iterated guarded-ownership step to the running state and
    /// records it. The kernel performs the step; the caller supplies only the
    /// step's operands.
    pub(crate) fn record_iterated_step(
        &mut self,
        before_facts: &ProofFacts,
        step: crate::kernel::IteratedStep,
    ) -> Result<CState, String> {
        if self.evidence_completed {
            return Err("an iterated ownership step was recorded after the trace completed".into());
        }
        // An iterated step regroups owned memory only; it creates, moves or
        // retires no population member, so it applies as is.
        let before_state = self.reached_state().clone();
        let after_state =
            crate::kernel::apply_iterated_step(&before_state, &step, before_facts.assumptions())?;
        let checked = CheckedIteratedStep { before_state };
        if self.evidence_state.is_some() {
            self.evidence_state = Some(after_state.clone());
        }
        for trace in self.execution_evidence.iter_mut() {
            trace.push(CheckedExecutionEvent::IteratedStep(checked.clone()));
        }
        Ok(after_state)
    }

    pub(crate) fn record_resource_observation(
        &mut self,
        function: &CFunction,
        arguments: &[CExpression],
        before_facts: &ProofFacts,
        observed: &CResourceFact,
        after_state: &CState,
        after_facts: &ProofFacts,
    ) -> Result<(), &'static str> {
        if self.evidence_completed {
            return Err("a resource observation was recorded after the trace completed");
        }
        let mut observation = CheckedResourceObservation::check(
            function,
            self.reached_state(),
            before_facts,
            observed,
            after_state,
            after_facts,
            &self.function_entry_derivations,
            &self.checked_call_events,
        )?;
        if self.frontier.is_at_function_entry() && !self.frontier.entry_member_prefix {
            observation.before_state = crate::kernel::c_function_entry_state(
                &observation.before_state,
                function,
                arguments,
            )
            .ok_or("resource observation could not bind the function entry state")?;
            observation.after_state = crate::kernel::c_function_entry_state(
                &observation.after_state,
                function,
                arguments,
            )
            .ok_or("resource observation could not bind its successor entry state")?;
        }
        if self.evidence_state.is_some() {
            self.evidence_state = Some(observation.after_state.clone());
        }
        for trace in self.execution_evidence.iter_mut() {
            trace.push(CheckedExecutionEvent::ResourceObservation(
                observation.clone(),
            ));
        }
        Ok(())
    }

    /// Applies the verified rule of tactic `name` at the reached state and
    /// records the checked application. Returns the successor state and fact
    /// context the proof continues from.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_tactic_application(
        &mut self,
        function: &CFunction,
        function_arguments: &[CExpression],
        before_facts: &ProofFacts,
        name: &str,
        arguments: &[crate::kernel::CValue],
        environment: &crate::kernel::CExecutionEnvironment,
    ) -> Result<(CState, ProofFacts), crate::kernel::functions::TacticApplicationRefusal> {
        use crate::kernel::functions::TacticApplicationRefusal::Refused;
        if self.evidence_completed {
            return Err(Refused(
                "a tactic must be applied before execution reaches function exit".into(),
            ));
        }
        let (mut application, mark) = CheckedTacticApplication::check(
            self.reached_state(),
            before_facts,
            name,
            arguments,
            environment,
            self.kernel_variable_mark(),
        )?;
        self.advance_kernel_variable_mark(mark)
            .map_err(|message| Refused(message.into()))?;
        let result = (
            application.after_state.clone(),
            application.after_facts.clone(),
        );
        // Before any evidence, the core holds the caller-side state and the
        // trace holds entry-bound states, as for a resource rewrite here.
        if self.frontier.is_at_function_entry() && !self.frontier.entry_member_prefix {
            application.before_state = crate::kernel::c_function_entry_state(
                &application.before_state,
                function,
                function_arguments,
            )
            .ok_or_else(|| {
                Refused("a tactic application could not bind the function entry state".into())
            })?;
            application.after_state = crate::kernel::c_function_entry_state(
                &application.after_state,
                function,
                function_arguments,
            )
            .ok_or_else(|| {
                Refused("a tactic application could not bind its successor entry state".into())
            })?;
        }
        if self.evidence_state.is_some() {
            self.evidence_state = Some(application.after_state.clone());
        }
        for trace in self.execution_evidence.iter_mut() {
            trace.push(CheckedExecutionEvent::TacticApplication(
                application.clone(),
            ));
        }
        Ok(result)
    }

    pub(crate) fn record_resource_rewrite(
        &mut self,
        function: &CFunction,
        arguments: &[CExpression],
        before_facts: &ProofFacts,
        selected: &CResourceFact,
        after_state: &CState,
        after_facts: &ProofFacts,
    ) -> Result<(), String> {
        self.record_resource_rewrite_with_children(
            function,
            arguments,
            before_facts,
            selected,
            after_state,
            after_facts,
            None,
        )
    }

    /// Publish one authority establish or retirement only with the opaque
    /// creation witness and its exact resource and state exchange.
    pub(crate) fn record_population_authority_rewrite(
        &mut self,
        before_facts: &ProofFacts,
        selected: &CResourceFact,
        establish: bool,
        witness: &CheckedPopulationAuthorityExchange,
        after_state: &CState,
        after_facts: &ProofFacts,
    ) -> Result<(), String> {
        if self.evidence_completed
            || (self.frontier.is_at_function_entry() && !self.frontier.entry_member_prefix)
        {
            return Err("population authority rewrite requires an active function body".into());
        }
        let rewrite = CheckedPopulationAuthorityRewrite::check(
            self.reached_state(),
            before_facts,
            selected,
            establish,
            witness,
            after_state,
            after_facts,
        )?;
        if self.evidence_state.is_some() {
            self.evidence_state = Some(rewrite.after_state.clone());
        }
        for trace in self.execution_evidence.iter_mut() {
            trace.push(CheckedExecutionEvent::PopulationAuthorityRewrite(
                rewrite.clone(),
            ));
        }
        Ok(())
    }

    pub(crate) fn record_population_member_rewrite(
        &mut self,
        function: &CFunction,
        arguments: &[CExpression],
        before_facts: &ProofFacts,
        selected: &CResourceFact,
        produce: bool,
        witness: &CheckedPopulationMemberExchange,
        after_state: &CState,
        after_facts: &ProofFacts,
    ) -> Result<Option<CState>, String> {
        if self.evidence_completed {
            return Err("population member rewrite requires an active function body".into());
        }
        let rewrite = CheckedPopulationMemberRewrite::check(
            function,
            self.reached_state(),
            before_facts,
            selected,
            produce,
            witness,
            after_state,
            after_facts,
        )?;
        let (rewrite, entry_successor) = if self.frontier.is_at_function_entry()
            && !self.frontier.entry_member_prefix
        {
            let entry = self
                .function_entry
                .as_ref()
                .ok_or("entry member change requires a checked function entry")?;
            // Earlier proof-only resource rewrites at the function entry may
            // have opened the authority wrapper. Bind their checked successor
            // to the callee entry before exchanging the member. The checked
            // rewrite chain must still connect to the original entry.
            let bound_before =
                crate::kernel::c_function_entry_state(self.reached_state(), function, arguments)
                    .ok_or("entry member change could not bind function arguments")?;
            let (bound_after, bound_witness) = bound_before.checked_population_member_exchange(
                selected,
                produce,
                &rewrite.definition,
                before_facts.assumptions(),
            )?;
            let bound_rewrite = CheckedPopulationMemberRewrite::check(
                function,
                &bound_before,
                before_facts,
                selected,
                produce,
                &bound_witness,
                &bound_after,
                after_facts,
            )?;
            self.frontier.execution_start_state = Some(entry.caller_state().clone());
            self.frontier.entry_member_prefix = true;
            self.evidence_source = Some(Arc::new(function.body().clone()));
            (bound_rewrite, Some(bound_after))
        } else {
            (rewrite, None)
        };
        if self.evidence_state.is_some() || entry_successor.is_some() {
            self.evidence_state = Some(rewrite.after_state.clone());
        }
        for trace in self.execution_evidence.iter_mut() {
            trace.push(CheckedExecutionEvent::PopulationMemberRewrite(
                rewrite.clone(),
            ));
        }
        Ok(entry_successor)
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_resource_rewrite_with_children(
        &mut self,
        function: &CFunction,
        arguments: &[CExpression],
        before_facts: &ProofFacts,
        selected: &CResourceFact,
        after_state: &CState,
        after_facts: &ProofFacts,
        selected_children: Option<Arc<[(String, Variable)]>>,
    ) -> Result<(), String> {
        if self.evidence_completed {
            return Err("a resource rewrite was recorded after the trace completed".to_string());
        }
        let mut rewrite = CheckedResourceRewrite::check_with_children(
            function,
            self.reached_state(),
            before_facts,
            selected,
            after_state,
            after_facts,
            &self.checked_call_events,
            selected_children,
        )?;
        if self.frontier.is_at_function_entry() && !self.frontier.entry_member_prefix {
            rewrite.before_state =
                crate::kernel::c_function_entry_state(&rewrite.before_state, function, arguments)
                    .ok_or_else(|| {
                    "resource rewrite could not bind the function entry state".to_string()
                })?;
            rewrite.after_state =
                crate::kernel::c_function_entry_state(&rewrite.after_state, function, arguments)
                    .ok_or("resource rewrite could not bind its successor entry state")?;
        }
        if self.evidence_state.is_some() {
            self.evidence_state = Some(rewrite.after_state.clone());
        }
        for trace in self.execution_evidence.iter_mut() {
            trace.push(CheckedExecutionEvent::ResourceRewrite(rewrite.clone()));
        }
        Ok(())
    }

    /// A logical resource exchange after the returning C statement. This
    /// cannot execute C, change the result, or bypass the checked body rule.
    #[cfg(test)]
    pub(crate) fn record_return_resource_rewrite(
        &mut self,
        function: &CFunction,
        path_index: usize,
        before_facts: &ProofFacts,
        selected: &CResourceFact,
        after_facts: &ProofFacts,
    ) -> Result<(), String> {
        self.record_return_resource_rewrite_with_children(
            function,
            path_index,
            before_facts,
            selected,
            after_facts,
            false,
            None,
        )
    }

    pub(crate) fn record_return_proposition(
        &mut self,
        path_index: usize,
        proof: super::CheckedProposition,
        base: &ProofFacts,
    ) -> Result<(), String> {
        // Contract refinements also use outcome goals, but their proofs are
        // certified by the refinement rule rather than a retained C trace.
        if !self.evidence_completed {
            return Ok(());
        }
        if self.execution_evidence.get(path_index).is_none() {
            return Err("return proof selected an unknown path".into());
        }
        let mut pending = self
            .return_pending_propositions
            .get(&path_index)
            .cloned()
            .unwrap_or_default();
        pending.push((proof, base.clone()));
        self.return_pending_propositions = self
            .return_pending_propositions
            .with_inserted(path_index, pending);
        Ok(())
    }

    fn flush_return_propositions(&mut self, path_index: usize) -> Result<(), String> {
        let Some(pending) = self.return_pending_propositions.get(&path_index).cloned() else {
            return Ok(());
        };
        let context = if let Some(context) = self.return_proof_contexts.get(&path_index) {
            context.clone()
        } else {
            let candidates = self
                .frontier
                .execution()
                .ok_or("return proof has no published execution")?;
            let candidate = candidates
                .paths()
                .get(path_index)
                .ok_or("return proof selected an unknown path")?;
            let mut source = self.execution_evidence[path_index].clone();
            let origin = loop {
                match source.pop() {
                    Some(CheckedExecutionEvent::Statement(theorem)) => {
                        let Proposition::CStatementVerifies { outcome, .. } =
                            checked_evidence_conclusion(&theorem)
                        else {
                            return Err("return proof has no completing statement".into());
                        };
                        break outcome.clone();
                    }
                    Some(
                        CheckedExecutionEvent::Context(_)
                        | CheckedExecutionEvent::StatementEffects(_)
                        | CheckedExecutionEvent::Call(_)
                        | CheckedExecutionEvent::ProofCase(_),
                    ) => {}
                    _ => return Err("return proof has no completing statement".into()),
                }
            };
            let context = Arc::new(CheckedReturnContext::from_candidate(origin, candidate));
            self.return_proof_contexts = self
                .return_proof_contexts
                .with_inserted(path_index, context.clone());
            context
        };
        let mut trace = self
            .return_resource_rewrites
            .get(&path_index)
            .unwrap_or(&self.execution_evidence[path_index])
            .clone();
        for (proof, base) in pending.iter() {
            trace.push(CheckedExecutionEvent::ReturnProposition(
                CheckedReturnProposition::check(proof.clone(), base, context.clone())?,
            ));
        }
        self.return_resource_rewrites = self
            .return_resource_rewrites
            .with_inserted(path_index, trace);
        self.return_pending_propositions =
            self.return_pending_propositions.without_key(&path_index);
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_return_resource_rewrite_with_children(
        &mut self,
        function: &CFunction,
        path_index: usize,
        before_facts: &ProofFacts,
        selected: &CResourceFact,
        after_facts: &ProofFacts,
        unfold: bool,
        selected_children: Option<Arc<[(String, Variable)]>>,
    ) -> Result<(), String> {
        self.flush_return_propositions(path_index)?;
        if !self.evidence_completed {
            return Err("return resource rewrite requires completed execution".to_string());
        }
        let CResource::Instance(instance) = selected.resource() else {
            return Err("return rewrite requires a named instance".to_string());
        };
        let definition = function
            .composite_resource_definition(instance.name())
            .ok_or_else(|| "instance definition is not registered on the function".to_string())?;
        let mut trace = self
            .return_resource_rewrites
            .get(&path_index)
            .or_else(|| self.execution_evidence.get(path_index))
            .cloned()
            .ok_or_else(|| "return resource rewrite selected an unknown path".to_string())?;
        // Read only the completing suffix. Persistent pop does not copy the
        // path's earlier history, and no sibling path is inspected.
        let before_state = loop {
            match trace.pop() {
                Some(CheckedExecutionEvent::ResourceRewrite(rewrite)) => {
                    break rewrite.after_state;
                }
                Some(CheckedExecutionEvent::Statement(theorem)) => {
                    let Proposition::CStatementVerifies {
                        outcome: CStatementOutcome::Return { state, .. },
                        ..
                    } = checked_evidence_conclusion(&theorem)
                    else {
                        return Err("return resource rewrite requires a returning path".to_string());
                    };
                    break *state.clone();
                }
                Some(
                    CheckedExecutionEvent::Context(_)
                    | CheckedExecutionEvent::StatementEffects(_)
                    | CheckedExecutionEvent::Call(_)
                    | CheckedExecutionEvent::ProofCase(_)
                    | CheckedExecutionEvent::ReturnProposition(_),
                ) => {}
                _ => {
                    return Err("return resource rewrite has no completing theorem".to_string());
                }
            }
        };
        // Compute the exchange in the retained C-body state, not the
        // caller-side projection used by postcondition expressions.
        let after_state = crate::kernel::rewrite_resource_instance_selecting_children(
            &before_state,
            instance,
            definition,
            function.composite_resource_definitions(),
            before_facts.assumptions(),
            unfold,
            selected_children.as_deref(),
        )
        .map_err(|refusal| refusal.describe())?
        .state;
        let rewrite = CheckedResourceRewrite::check_with_children(
            function,
            &before_state,
            before_facts,
            selected,
            &after_state,
            after_facts,
            &self.checked_call_events,
            selected_children,
        )?;
        let mut trace = self
            .return_resource_rewrites
            .get(&path_index)
            .unwrap_or(&self.execution_evidence[path_index])
            .clone();
        trace.push(CheckedExecutionEvent::ResourceRewrite(rewrite));
        self.return_resource_rewrites = self
            .return_resource_rewrites
            .with_inserted(path_index, trace);
        Ok(())
    }

    /// Checks and retains an ordinary wrapper exchange on a completed path.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_return_transfer_wrapper_rewrite(
        &mut self,
        function: &CFunction,
        path_index: usize,
        before_facts: &ProofFacts,
        selected: &CResourceFact,
        presented_before_state: &CState,
        after_state: &CState,
        after_facts: &ProofFacts,
    ) -> Result<(), String> {
        self.flush_return_propositions(path_index)?;
        if !self.evidence_completed {
            return Err("return resource rewrite requires completed execution".into());
        }
        let mut trace = self
            .return_resource_rewrites
            .get(&path_index)
            .or_else(|| self.execution_evidence.get(path_index))
            .cloned()
            .ok_or_else(|| "return resource rewrite selected an unknown path".to_string())?;
        // Read only the completing suffix. Persistent pop does not copy the
        // path's earlier history, and no sibling path is inspected.
        let before_state = loop {
            match trace.pop() {
                Some(CheckedExecutionEvent::ResourceRewrite(rewrite)) => {
                    break rewrite.after_state;
                }
                Some(CheckedExecutionEvent::Statement(theorem)) => {
                    let Proposition::CStatementVerifies {
                        outcome: CStatementOutcome::Return { state, .. },
                        ..
                    } = checked_evidence_conclusion(&theorem)
                    else {
                        return Err("return resource rewrite requires a returning path".to_string());
                    };
                    break *state.clone();
                }
                Some(
                    CheckedExecutionEvent::Context(_)
                    | CheckedExecutionEvent::StatementEffects(_)
                    | CheckedExecutionEvent::Call(_)
                    | CheckedExecutionEvent::ProofCase(_)
                    | CheckedExecutionEvent::ReturnProposition(_),
                ) => {}
                _ => {
                    return Err("return resource rewrite has no completing theorem".to_string());
                }
            }
        };
        // The expression-facing outcome has already projected local bindings.
        // Validate both representations and retain the C-body snapshot.
        CheckedResourceRewrite::check_with_children(
            function,
            presented_before_state,
            before_facts,
            selected,
            after_state,
            after_facts,
            &self.checked_call_events,
            None,
        )?;
        // An ordinary family refolded on the outcome is not retained on the
        // path, which still holds its body. Unfolding it again leaves the
        // retained path as it is: the exchange is checked above, and the
        // path never held the folded head it would remove.
        if matches!(selected.resource(), CResource::Composite { name, .. }
                if function
                    .composite_resource_definition(name)
                    .is_some_and(|definition| !definition.reaches_population()))
            && before_state
                .resources()
                .directly_supporting_fact(selected, before_facts.assumptions())
                .is_none()
        {
            return Ok(());
        }
        let retained_after_state = before_state
            .clone()
            .with_resource_context(after_state.resources().clone());
        let rewrite = CheckedResourceRewrite::check_with_children(
            function,
            &before_state,
            before_facts,
            selected,
            &retained_after_state,
            after_facts,
            &self.checked_call_events,
            None,
        )?;
        let mut trace = self
            .return_resource_rewrites
            .get(&path_index)
            .unwrap_or(&self.execution_evidence[path_index])
            .clone();
        trace.push(CheckedExecutionEvent::ResourceRewrite(rewrite));
        self.return_resource_rewrites = self
            .return_resource_rewrites
            .with_inserted(path_index, trace);
        Ok(())
    }

    /// Records a branch node only after [`CheckedExecutionBranch::check`]
    /// has validated exact source coverage, both persistent arm suffixes,
    /// the common continuation, and the joined state.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_exhaustive_branch_join(
        &mut self,
        split: CheckedBranchSplit,
        root_facts: &ProofFacts,
        arm_theorems: [&Theorem; 2],
        arm_facts: [&ProofFacts; 2],
        parent: &ExecutionProofCore,
        arms: [&ExecutionProofCore; 2],
        function: &CFunction,
        arguments: &[CExpression],
        arm_effect_facts: [&(impl ExecutionFactSource + ?Sized); 2],
    ) -> Result<crate::kernel::ExecutionFacts, &'static str> {
        let parent_trace = match parent.execution_evidence.as_slice() {
            [trace] => trace,
            _ => return Err("the branch parent does not have one execution trace"),
        };
        let branch = CheckedExecutionBranch::check(
            split,
            root_facts,
            arm_theorems,
            arm_facts,
            parent,
            arms,
            function,
            arguments,
            arm_effect_facts,
        )?;
        let interface_effect_facts = branch.interface_effect_facts().clone();
        let joined_state = branch.joined_state().clone();
        let source = parent.source_after_branch(function, &branch)?;
        let mut trace = parent_trace.clone();
        trace.push(CheckedExecutionEvent::Branch(branch));
        self.execution_evidence = vec![trace].into();
        self.checked_call_events = parent.checked_call_events.clone();
        self.evidence_state = Some(joined_state);
        self.evidence_source = source;
        self.evidence_completed = false;
        Ok(interface_effect_facts)
    }

    /// Records a two-arm `branch ensuring` only after the kernel has checked
    /// both source traces, the deterministic abstraction, every retained
    /// interface fact, and whole-context resource availability in both arms.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_interface_branch_join(
        &mut self,
        split: CheckedBranchSplit,
        root_facts: &ProofFacts,
        arm_theorems: [&Theorem; 2],
        arm_facts: [&ProofFacts; 2],
        parent: &ExecutionProofCore,
        arms: [&ExecutionProofCore; 2],
        function: &CFunction,
        arguments: &[CExpression],
        stable_join_locals: &BTreeMap<String, CValue>,
        interface_specs: &[SpecProposition],
        interface_resource_specs: &[CResourceSpec],
        arm_effect_facts: [&(impl ExecutionFactSource + ?Sized); 2],
        joined_state: &CState,
        successor_facts: &ProofFacts,
        old_reference: Option<&CState>,
    ) -> Result<crate::kernel::ExecutionFacts, &'static str> {
        let parent_trace = match parent.execution_evidence.as_slice() {
            [trace] => trace,
            _ => return Err("the interface parent does not have one execution trace"),
        };
        let branch = CheckedExecutionBranch::check_interface(
            split,
            root_facts,
            arm_theorems,
            arm_facts,
            parent,
            arms,
            function,
            arguments,
            stable_join_locals,
            interface_specs,
            interface_resource_specs,
            arm_effect_facts,
            joined_state,
            successor_facts,
            old_reference,
        )?;
        let interface_effect_facts = branch.interface_effect_facts().clone();
        let joined_state = branch.joined_state().clone();
        // The kernel recomputed the abstraction, so it also knows where the
        // abstraction left the counter. Installing that mark here is what
        // makes the successor's counter kernel-owned: a caller cannot take
        // the joined state and keep a counter that knows nothing about the
        // identities the join spent. It only ever moves the counter forward --
        // the mark is above both arms', which are above the parent's.
        let join_mark = branch
            .interface_next_kernel_variable()
            .ok_or("the checked interface join did not report its fresh-variable counter")?;
        self.advance_kernel_variable_mark(join_mark)?;
        let source = parent.source_after_branch(function, &branch)?;
        let mut trace = parent_trace.clone();
        trace.push(CheckedExecutionEvent::Branch(branch));
        self.execution_evidence = vec![trace].into();
        self.checked_call_events = parent.checked_call_events.clone();
        self.evidence_state = Some(joined_state);
        self.evidence_source = source;
        self.evidence_completed = false;
        Ok(interface_effect_facts)
    }

    /// The checked whole-function execution a completed proof yields: one
    /// path per retained trace, each its trace's completing theorem under
    /// the contract's exit rule, stating everything the proof established
    /// on the path. Every step of every trace was checked when it was
    /// recorded, so this composes the traces without re-executing the body.
    /// A single traversal collects conservative call dependencies.
    /// `candidates` is the driver's publication of the paths, which must
    /// name the traces' outcomes in order.
    pub(crate) fn checked_function_execution(
        &self,
        candidates: &CFunctionExecutionCandidates,
        checked_function: &CFunction,
        assumptions: PureFactContext,
        environment: crate::kernel::CExecutionEnvironment,
        execution_semantics: crate::kernel::CExecutionSemantics,
        mode: crate::kernel::CFunctionContractExecutionMode,
    ) -> Result<crate::kernel::CCheckedFunctionExecution, &'static str> {
        // A function that declares an expression `decreases` measure owes a
        // descent obligation at each self-call, and the environment's anchor
        // is what makes the call step emit one. The proof stepped under the
        // environment it publishes here, so refusing an environment without
        // the anchor refuses exactly the executions in which those
        // obligations were never raised.
        if checked_function
            .contract_interface()
            .recursion_measure()
            .is_some()
            && environment
                .recursion_anchor()
                .is_none_or(|anchor| anchor.function() != checked_function.name())
        {
            return Err(
                "the checked execution of a function with a `decreases` measure carries no \
                 recursion anchor for it",
            );
        }
        // The same requirement for the loops this execution summarized. A
        // verified loop rule answers for its body, so a rule whose loop calls
        // the anchored function and whose own body was stepped without the
        // anchor is a summary that swallowed the descent. Applying such a
        // rule is already refused; naming it here says why, instead of
        // leaving a step that found no applicable rule.
        if !environment.verified_loop_rules_answer_for_recursion() {
            return Err(
                "a verified loop rule of a function with a `decreases` measure calls that \
                 function but was certified without its recursion anchor",
            );
        }
        let (paths, has_checked_entry, deferred_contract_exits, deferred_contract_exit_errors) =
            self.checked_execution_paths(candidates, checked_function, &assumptions, None)?;
        let path_count = paths.len();
        Ok(crate::kernel::CCheckedFunctionExecution {
            state: candidates.state().clone(),
            function: checked_function.clone(),
            arguments: candidates.arguments().to_vec(),
            assumptions,
            environment,
            execution_semantics,
            mode,
            execution: crate::kernel::SymbolicCExecution { paths, limit: None },
            checked_resource_claims: vec![Vec::new(); path_count],
            checked_resource_transitions: vec![false; path_count],
            deferred_contract_exits,
            deferred_contract_exit_errors,
            // Empty conclusion placeholders; checked resource clauses replace
            // them before any live resource query.
            checked_returned_resources: vec![crate::kernel::ResourceContext::new(); path_count],
            entry_representation_origin: has_checked_entry
                .then_some(self.function_entry.as_ref())
                .flatten()
                .map(|entry| entry.caller_state().clone()),
            boundary_transfer: has_checked_entry
                .then_some(self.function_entry.as_ref())
                .flatten()
                .and_then(|entry| entry.boundary_transfer.clone()),
            checked_call_events: self.retained_call_events(),
            applied_tactics: self.retained_applied_tactics(),
            checked_callees: self.retained_checked_callees(),
        })
    }

    /// One path theorem, not an assertion of whole-function coverage.
    pub(crate) fn checked_return_path(
        &self,
        candidates: &CFunctionExecutionCandidates,
        function: &CFunction,
        assumptions: &PureFactContext,
        path_index: usize,
    ) -> Result<crate::kernel::SymbolicCExecutionPath, &'static str> {
        self.checked_execution_paths(candidates, function, assumptions, Some(path_index))?
            .0
            .pop()
            .ok_or("return fold selected an unknown path")
    }

    /// Whether this path retains a kernel-checked exchange after its C return.
    pub(crate) fn has_checked_return_resource_rewrite(&self, path_index: usize) -> bool {
        self.return_resource_rewrites.get(&path_index).is_some()
    }

    /// Collect a finished outcome's exchange without copying sibling traces.
    pub(crate) fn collect_return_resource_rewrites(
        &mut self,
        source: &Self,
        path_index: usize,
    ) -> Result<(), &'static str> {
        let base = self
            .execution_evidence
            .get(path_index)
            .ok_or("return fold selected an unknown path")?;
        let source_base = source
            .execution_evidence
            .get(path_index)
            .ok_or("return fold selected an unknown source path")?;
        if !base.shares_tail_with(source_base) {
            return Err("return folds belong to a different execution path");
        }
        let rewritten = source
            .return_resource_rewrites
            .get(&path_index)
            .ok_or("selected path has no checked return folds")?;
        self.return_resource_rewrites = self
            .return_resource_rewrites
            .with_inserted(path_index, rewritten.clone());
        Ok(())
    }

    fn checked_execution_paths(
        &self,
        candidates: &CFunctionExecutionCandidates,
        checked_function: &CFunction,
        assumptions: &PureFactContext,
        selected: Option<usize>,
    ) -> Result<
        (
            Vec<crate::kernel::SymbolicCExecutionPath>,
            bool,
            Vec<bool>,
            Vec<Option<crate::kernel::CRuntimeError>>,
        ),
        &'static str,
    > {
        if candidates.paths().len() != self.execution_evidence.len() {
            return Err("the published paths do not match the retained traces one to one");
        }
        if selected.is_none()
            && !crate::kernel::api::proof_case_partitions_are_exhaustive(&self.execution_evidence)
        {
            return Err("a proof-case partition is not exhausted by the retained traces");
        }
        if !crate::kernel::api::proof_evidence_function_refines_same_source(
            candidates.function(),
            checked_function,
        ) {
            return Err("the checked function does not refine the published function's source");
        }
        let function = checked_function;
        let range = match selected {
            Some(index) if index < candidates.paths().len() => index..index + 1,
            Some(_) => return Err("return fold selected an unknown path"),
            None => 0..candidates.paths().len(),
        };
        // The checked entry vouches for the published function's entry only
        // when it was checked for that function and those arguments, and
        // either every trace starts at its entry state or that state
        // rebases onto the published caller state. Checked loop annotations
        // may refine the function without changing its source or entry
        // contract; those annotations do not invalidate its checked entry.
        let has_checked_entry = self.function_entry.as_ref().is_some_and(|entry| {
            match entry.trace_entry_state(candidates.function(), candidates.arguments()) {
                None => false,
                Some(trace_entry) => {
                    self.execution_evidence[range.clone()].iter().all(|trace| {
                        crate::kernel::api::proof_evidence_initial_state(&trace.to_vec())
                            == Some(trace_entry)
                    }) || entry
                        .entry_state_for(
                            candidates.state(),
                            candidates.function(),
                            candidates.arguments(),
                            assumptions,
                        )
                        .is_some()
                }
            }
        });
        if !has_checked_entry {
            crate::kernel::c_function_entry_state(
                candidates.state(),
                function,
                candidates.arguments(),
            )
            .ok_or("the published arguments do not bind at entry")?;
        }
        let mut paths = Vec::with_capacity(range.len());
        let mut deferred_contract_exits = Vec::with_capacity(range.len());
        let mut deferred_contract_exit_errors = Vec::with_capacity(range.len());
        for path_index in range {
            let candidate = &candidates.paths()[path_index];
            let trace = self
                .return_resource_rewrites
                .get(&path_index)
                .unwrap_or(&self.execution_evidence[path_index]);
            let events = trace.to_vec();
            let (completed, statement_assumptions, interface_execution_facts) =
                trace_completion_from_entry(
                    function,
                    &events,
                    assumptions,
                    function.return_type() == crate::kernel::CType::Void
                        && self.evidence_source.is_none()
                        && self.frontier.region == ExecutionRegionKind::Function,
                    self.entry_facts.as_ref(),
                )?;
            // Publication precedes post-return logical folds. Check its
            // original C outcome against the trace before those exchanges;
            // the final exit rule below still checks the folded ownership.
            let publication_end = events
                .iter()
                .rposition(|event| {
                    !matches!(
                        event,
                        CheckedExecutionEvent::ReturnProposition(_)
                            | CheckedExecutionEvent::ResourceRewrite(_)
                            | CheckedExecutionEvent::PopulationAuthorityRewrite(_)
                            | CheckedExecutionEvent::PopulationMemberRewrite(_)
                    )
                })
                .map_or(0, |index| index + 1);
            let publication_completed = if publication_end < events.len() {
                trace_completion(
                    function,
                    &events[..publication_end],
                    assumptions,
                    function.return_type() == crate::kernel::CType::Void
                        && self.evidence_source.is_none()
                        && self.frontier.region == ExecutionRegionKind::Function,
                )?
                .0
            } else {
                completed.clone()
            };
            let (outcome, obligations) = crate::kernel::c_function_outcome_from_statement_outcome(
                candidates.state(),
                function,
                publication_completed,
                candidate.obligations().to_vec(),
                &statement_assumptions,
            );
            if !outcome.equal_up_to_unused_creation_ledgers(candidate.outcome()) {
                return Err("a published path outcome is not its trace's outcome");
            }
            // The published outcome is the body's. The path's theorem states
            // the function's: the body's after the contract's exit rule, the
            // same resource transfer or population transition an independent
            // execution applies at return. A contract the body violates at
            // exit ends the path in that runtime error.
            let body_outcome = candidate.outcome().clone();
            let retain_post_context = function.resource_requires().is_empty();
            let mut boundary_assumptions = statement_assumptions.clone();
            for fact in candidate
                .facts()
                .facts_not_assumed_by(&boundary_assumptions)
            {
                crate::instrumentation::record_deterministic_work(1);
                crate::kernel::reasoning::path_facts::count_context_rebuild_entries(1);
                boundary_assumptions =
                    boundary_assumptions.assume_proposition(fact.proposition().clone());
            }
            let typed_candidate_facts = candidate.facts().producer_facts().filter(|fact| {
                retain_post_context
                    && fact.is_certified()
                    && fact.generated_load_binding().is_some()
            });
            let (
                outcome,
                obligations,
                loan_evidence,
                deferred_contract_exit,
                deferred_contract_exit_error,
            ) = match crate::kernel::functions::checked_contract_exit_outcome_with_boundary_transfer(
                if has_checked_entry {
                    self.function_entry
                        .as_ref()
                        .expect("checked entry exists")
                        .caller_state()
                } else {
                    candidates.state()
                },
                if has_checked_entry {
                    self.function_entry
                        .as_ref()
                        .expect("checked entry exists")
                        .function
                        .as_ref()
                } else {
                    function
                },
                candidates.arguments(),
                completed,
                body_outcome.clone(),
                obligations,
                &boundary_assumptions,
                &mut ExecutionBudget::beside_live_state(),
                // This is the enclosing function's boundary. Retained
                // call evidence belongs to calls inside its body; it does
                // not mean the function lent its own inputs at entry.
                crate::kernel::functions::ResourceTransitionPurpose::FunctionBoundary,
                if has_checked_entry {
                    self.function_entry
                        .as_ref()
                        .and_then(|entry| entry.boundary_transfer.as_deref())
                } else {
                    None
                },
            ) {
                Ok(Ok(exit)) => exit,
                Ok(Err(error)) => (
                    crate::kernel::CFunctionOutcome::RuntimeError(error),
                    candidate.obligations().to_vec(),
                    None,
                    false,
                    None,
                ),
                Err(_) => return Err("the contract's exit rule hit an execution limit"),
            };
            let loan_evidence = match loan_evidence {
                Some(evidence) => crate::kernel::loans::concat_checked_loan_evidence(
                    candidate.loan_evidence(),
                    &crate::kernel::loans::append_checked_loan_evidence(
                        &crate::kernel::loans::empty_checked_loan_evidence_sequence(),
                        Some(evidence),
                    ),
                ),
                None => candidate.loan_evidence().clone(),
            };
            let proposition = Proposition::CFunctionVerifies {
                state: Box::new(candidates.state().clone()),
                function: Box::new(function.clone()),
                arguments: candidates.arguments().to_vec(),
                outcome,
            };
            // The path states everything the proof established on it: the
            // candidate's execution facts, the interface facts of joined
            // branches, and the facts of the context its final theorem was
            // proved under (a `have` in one arm that both arms share, say).
            let mut facts = candidate.facts().clone();
            let mut post_assumptions = boundary_assumptions;
            for fact in interface_execution_facts {
                if retain_post_context {
                    post_assumptions = retain_completed_path_fact(post_assumptions, &fact);
                }
                if !facts
                    .iter()
                    .any(|retained| retained.proposition() == fact.proposition())
                {
                    facts.push(fact);
                }
            }
            facts.append_context(&statement_assumptions.execution_fact_projection);
            // Preserve the typed-load bridges that the former certification
            // import installed, including private memory-effect evidence.
            if retain_post_context {
                for fact in typed_candidate_facts
                    .into_iter()
                    .chain(candidate.effect_facts())
                {
                    post_assumptions = retain_completed_path_fact(post_assumptions, fact);
                }
            }
            let theorem = Theorem::new(crate::kernel::reasoning::wrap_proof_facts(
                proposition,
                assumptions,
                &facts,
                candidate.obligations(),
            ));
            paths.push(crate::kernel::SymbolicCExecutionPath {
                completion_origin: Some(candidate.outcome().clone()),
                assumptions: assumptions.clone(),
                post_assumptions: retain_post_context.then_some(post_assumptions),
                facts,
                effect_facts: candidate.effect_facts().clone(),
                obligations,
                theorem,
                loan_evidence,
            });
            deferred_contract_exits.push(deferred_contract_exit);
            deferred_contract_exit_errors.push(deferred_contract_exit_error);
        }
        #[cfg(test)]
        ExecutionFacts::record_published_storage(
            true,
            paths.len(),
            paths
                .iter()
                .flat_map(|path| [&path.facts, &path.effect_facts]),
        );
        Ok((
            paths,
            has_checked_entry,
            deferred_contract_exits,
            deferred_contract_exit_errors,
        ))
    }

    /// Checks that every retained event carries the kernel judgment its tag
    /// promises. This is intentionally cheaper than executing any C: it only
    /// inspects the conclusions of already-issued theorem objects.
    pub(crate) fn validate_execution_evidence_shapes(&self) -> Result<(), &'static str> {
        for trace in &self.execution_evidence {
            validate_checked_event_shapes(&trace.to_vec())?;
        }
        Ok(())
    }
}

#[derive(Clone, Default)]
pub(crate) enum FrontierPosition {
    #[default]
    FunctionEntry,
    StatementEntry {
        remaining: Arc<CStatement>,
    },
    FunctionExit {
        execution: CFunctionExecutionCandidates,
    },
    /// A bounded region exhausted its own statement tree without an enclosing
    /// continuation. Advancing past this typed boundary is unrepresentable.
    RegionBoundary,
}

impl ExecutionFrontier {
    pub(crate) fn is_at_function_exit(&self) -> bool {
        matches!(self.position, FrontierPosition::FunctionExit { .. })
    }

    pub(crate) fn is_at_function_entry(&self) -> bool {
        matches!(self.position, FrontierPosition::FunctionEntry)
    }

    pub(crate) fn is_at_region_boundary(&self) -> bool {
        matches!(self.position, FrontierPosition::RegionBoundary)
    }

    pub(crate) fn execution(&self) -> Option<&CFunctionExecutionCandidates> {
        match &self.position {
            FrontierPosition::FunctionEntry
            | FrontierPosition::StatementEntry { .. }
            | FrontierPosition::RegionBoundary => None,
            FrontierPosition::FunctionExit { execution } => Some(execution),
        }
    }

    pub(crate) fn execution_start_state<'a>(&'a self, current_state: &'a CState) -> &'a CState {
        self.execution_start_state.as_ref().unwrap_or(current_state)
    }
}

/// Resolves the named function-entry state used by `old(...)`, falling back
/// to the current region's start state when the proof has no entry snapshot.
pub(crate) fn old_reference_state<'a>(
    function_entry_state: Option<&'a CState>,
    frontier: &'a ExecutionFrontier,
    current_state: &'a CState,
) -> &'a CState {
    match function_entry_state {
        Some(entry_state) => entry_state,
        None => frontier.execution_start_state(current_state),
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn numeric_load_does_not_establish_pointer_designation() {
        use crate::kernel::{CPointerValue, CType, Pointer, PointerDesignation, PointerOffsetTerm};
        let slot = Pointer::symbolic(Variable(983_100));
        let load = Bitvector32Term::Variable(Variable(983_101));
        let address = Pointer {
            block: slot.block.clone(),
            offset: PointerOffsetTerm::Int32Scaled {
                value: load.clone().into(),
                byte_width: 4,
            },
        };
        let pointer = CPointerValue::new(address, CType::Int32Pointer);
        assert!(cell_value_is_exactly_load(
            &CValue::Pointer(pointer.clone()),
            &load,
            &slot
        ));
        let designated =
            pointer.with_designation(PointerDesignation::Unresolved(Variable(983_102)));
        assert!(!cell_value_is_exactly_load(
            &CValue::Pointer(designated),
            &load,
            &slot
        ));
    }

    #[test]
    fn authority_nonoverflow_uses_selected_exact_scalar_equality_without_dropping_a_premise() {
        let read = Bitvector32Term::Variable(Variable(983_110));
        let count = Bitvector32Term::Variable(Variable(983_111));
        let amount = Bitvector32Term::Variable(Variable(983_112));
        let equality =
            Proposition::ConditionIs(ConditionTerm::equal(read.clone(), count.clone()), true);
        let nonoverflow = Proposition::ConditionIs(
            ConditionTerm::signed_add_overflows(read, amount.clone()),
            false,
        );
        let goal =
            Proposition::ConditionIs(ConditionTerm::signed_add_overflows(count, amount), false);
        for missing in 0..=2 {
            let facts = [equality.clone(), nonoverflow.clone()]
                .into_iter()
                .enumerate()
                .filter(|(index, _)| *index != missing)
                .fold(PureFactContext::new(), |facts, (_, fact)| {
                    facts.assume_proposition(fact)
                });
            assert_eq!(
                super::authority_control_evaluation_condition_proven(&facts, &goal),
                missing == 2
            );
        }
        let wrong = Proposition::ConditionIs(
            ConditionTerm::signed_add_overflows(
                Bitvector32Term::Variable(Variable(983_113)),
                Bitvector32Term::Variable(Variable(983_112)),
            ),
            false,
        );
        let facts = PureFactContext::new()
            .assume_proposition(equality)
            .assume_proposition(nonoverflow);
        assert!(!super::authority_control_evaluation_condition_proven(
            &facts, &wrong
        ));
        let baseline = crate::instrumentation::measure_deterministic_work(|| {
            super::authority_control_evaluation_condition_proven(&facts, &goal)
        });
        for unrelated in [16u64, 128, 1024] {
            let facts = (0..unrelated).fold(facts.clone(), |facts, index| {
                facts.assume_condition(
                    ConditionTerm::signed_add_overflows(
                        Bitvector32Term::Variable(Variable(984_000 + 2 * index)),
                        Bitvector32Term::Variable(Variable(984_001 + 2 * index)),
                    ),
                    false,
                )
            });
            let (proven, work) = crate::instrumentation::measure_deterministic_work(|| {
                super::authority_control_evaluation_condition_proven(&facts, &goal)
            });
            assert!(proven);
            assert!(
                work <= baseline.1 + 16,
                "unrelated conditions changed selected transport: {} -> {work}",
                baseline.1
            );
        }
    }

    #[test]
    fn balanced_unit_sum_domain_requires_all_three_original_domains() {
        use crate::kernel::ConditionTerm;
        let a = Bitvector32Term::Variable(Variable(100));
        let b = Bitvector32Term::Variable(Variable(101));
        let one = Bitvector32Term::Constant(1);
        let guards = [
            ConditionTerm::signed_add_overflows(a.clone(), b.clone()),
            ConditionTerm::signed_add_overflows(a.clone(), one.clone()),
            ConditionTerm::signed_subtract_overflows(b.clone(), one.clone()),
        ];
        let goal = Proposition::ConditionIs(
            ConditionTerm::signed_add_overflows(
                Bitvector32Term::add(a.clone(), one.clone()),
                Bitvector32Term::subtract(b.clone(), one.clone()),
            ),
            false,
        );
        for missing in 0..=3 {
            let facts = guards
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != missing)
                .fold(PureFactContext::new(), |facts, (_, condition)| {
                    facts.assume_condition(condition.clone(), false)
                });
            assert_eq!(
                super::authority_control_evaluation_condition_proven(&facts, &goal),
                missing == 3
            );
        }
        // Return reverses the two original summands. Commutativity must
        // preserve the check without dropping either child-domain premise.
        let reversed_guards = [
            ConditionTerm::signed_add_overflows(b.clone(), a.clone()),
            guards[1].clone(),
            guards[2].clone(),
        ];
        for missing in 0..=3 {
            let facts = reversed_guards
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != missing)
                .fold(PureFactContext::new(), |facts, (_, condition)| {
                    facts.assume_condition(condition.clone(), false)
                });
            assert_eq!(
                super::authority_control_evaluation_condition_proven(&facts, &goal),
                missing == 3
            );
        }
        // The original sum fits, but the increment wraps at MAX, or the
        // predecessor wraps at MIN. Modular equality must not certify either.
        for (left, right) in [(i32::MAX, 0), (0, i32::MIN)] {
            assert!(left.checked_add(right).is_some());
            assert!(
                left.checked_add(1)
                    .and_then(|x| right.checked_sub(1).and_then(|y| x.checked_add(y)))
                    .is_none()
            );
        }
    }

    #[test]
    fn balanced_unit_sum_domain_uses_only_indexed_related_bounds() {
        use crate::kernel::ConditionTerm;
        let a = Bitvector32Term::Variable(Variable(200));
        let b = Bitvector32Term::Variable(Variable(201));
        let one = Bitvector32Term::Constant(1);
        let goal = Proposition::ConditionIs(
            ConditionTerm::signed_add_overflows(
                Bitvector32Term::add(a.clone(), one.clone()),
                Bitvector32Term::subtract(b.clone(), one),
            ),
            false,
        );
        let mut measurements = Vec::new();
        for n in [8, 32, 128, 512] {
            let mut facts = PureFactContext::new()
                .assume_condition(
                    ConditionTerm::signed_add_overflows(a.clone(), b.clone()),
                    false,
                )
                .assume_condition(
                    ConditionTerm::signed_less_than(
                        a.clone(),
                        Bitvector32Term::Constant(i32::MAX as u32),
                    ),
                    true,
                )
                .assume_condition(
                    ConditionTerm::signed_greater_equal(b.clone(), Bitvector32Term::Constant(1)),
                    true,
                );
            for i in 0..n {
                facts = facts.assume_condition(
                    ConditionTerm::signed_less_equal(
                        Bitvector32Term::Variable(Variable(1000 + i)),
                        Bitvector32Term::Constant(100),
                    ),
                    true,
                );
            }
            let (valid, work) = crate::instrumentation::measure_deterministic_work(|| {
                super::authority_control_evaluation_condition_proven(&facts, &goal)
            });
            assert!(valid);
            // Removing the old domain must fail without searching the frame.
            let missing_old = PureFactContext::new().assume_condition(
                ConditionTerm::signed_less_than(
                    a.clone(),
                    Bitvector32Term::Constant(i32::MAX as u32),
                ),
                true,
            );
            assert!(!super::authority_control_evaluation_condition_proven(
                &missing_old,
                &goal
            ));
            measurements.push(work);
        }
        assert!(
            measurements
                .iter()
                .all(|work| *work <= measurements[0] + 16),
            "{measurements:?}"
        );
    }

    #[test]
    fn named_cell_check_rejects_removals_and_ignores_unchanged_cells() {
        use crate::kernel::{CMemory, Pointer, PointerBlock, PointerOffsetTerm};
        let target = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let mut samples = Vec::new();
        for count in [8, 32, 128, 512] {
            let mut before = CMemory::new();
            for index in 0..count {
                before = before.store(
                    Pointer {
                        block: PointerBlock::Heap(index),
                        offset: PointerOffsetTerm::Constant(0),
                    },
                    CValue::Int32(Bitvector32Term::Constant(7)),
                );
            }
            let name = crate::kernel::canonical_form_of_load(
                crate::kernel::intern_c_memory(before.clone()),
                target.clone(),
                crate::kernel::LoadKind::Bits32,
            );
            let after = before
                .clone()
                .materialize_named_cell(target.clone(), CValue::Int32(name));
            let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
                super::memory_only_adds_named_cells(&before, &after)
            });
            checked.unwrap();
            samples.push(work);
            assert!(super::memory_only_adds_named_cells(&after, &before).is_err());
        }
        assert!(
            samples.windows(2).all(|pair| pair[1] <= pair[0] + 32),
            "{samples:?}"
        );
    }

    use super::*;
    // The proposition search is Surface planning now; see
    // `src/surface/planning/proposition_search.rs`. Only these tests reach
    // it from inside the kernel.
    use crate::kernel::{
        Bitvector32Term, CComparisonOperator, CCompositeResourceDefinition, CMemory,
        CResourceAccessMode, CResourceFact, CResourceSpec, CType, CValue, Pointer, PointerBlock,
        PointerOffsetTerm, SpecExpression, c_function, int32,
    };
    use crate::surface::planning::proposition_search::PropositionSearch;

    /// One arm state holding a checked view rooted in a fresh loan.
    fn arm_holding_a_view(name: &str) -> (CState, crate::kernel::loans::LoanViewBinding) {
        let support_fact = CResourceFact::own_token(format!("{name}_support"), Vec::new());
        let viewed = CResourceFact::view_token(format!("{name}_view"), Vec::new());
        let resources = crate::kernel::ResourceContext::new()
            .unchecked_with_facts([support_fact.clone(), viewed.clone()]);
        let support = resources.owned_occurrences_for_fact(&support_fact)[0];
        let occurrence = resources.occurrences_for_fact(&viewed)[0];
        let ledger = crate::kernel::loans::LoanLedger::new();
        let owner = ledger.fresh_participant().expect("owner identity");
        let reader = ledger.fresh_participant().expect("reader identity");
        let opening = ledger
            .lend(owner, reader, support, support_fact)
            .expect("the arm's view is backed by a fresh loan");
        let binding = crate::kernel::loans::LoanViewBinding {
            loan: opening.loan,
            scope: opening.scope,
            share: opening.root_share,
            support,
            viewed,
            hold: None,
        };
        let state = CState::new()
            .with_loan_ledger(Some(ledger))
            .with_loan_participant(Some(reader))
            .with_resource_context_and_loan_dependencies(
                resources,
                [(occurrence, binding.clone())],
            );
        (state, binding)
    }

    #[test]
    fn frame_exchange_retains_the_exits_exact_stable_view_dependency() {
        let (state, binding) = arm_holding_a_view("loop_exit");
        let body = state.resources();
        let original = body.occurrences_for_fact(&binding.viewed)[0];
        let (exit, inserted) = body
            .clone()
            .without_bound_view_occurrence(original, &binding)
            .unwrap()
            .unchecked_with_facts_and_occurrences([binding.viewed.clone()]);
        let final_occurrence = inserted[0].1;
        let exit = exit.with_loan_dependency(final_occurrence, binding.clone());
        let outside = CResourceFact::own_composite("outside".into(), Vec::new());
        let frame = body.clone().unchecked_with_fact(outside.clone());
        let restored = exit
            .restore_frame_after_exchange(body, &frame, &PureFactContext::new())
            .unwrap();
        assert!(restored.contains_exact_representation(&outside));
        assert_eq!(restored.loan_dependency(final_occurrence), Some(&binding));
        assert!(restored.loan_dependency(original).is_none());
        assert!(restored.view_fact_at_occurrence(original).is_none());
    }

    fn successor_carrying(binding: &crate::kernel::loans::LoanViewBinding) -> CState {
        let resources =
            crate::kernel::ResourceContext::new().unchecked_with_facts([binding.viewed.clone()]);
        let occurrence = resources.occurrences_for_fact(&binding.viewed)[0];
        // A fresh interface context: the occurrence is new, so only the
        // binding's own content can connect it to an arm's authority.
        CState::new()
            .with_resource_context_and_loan_dependencies(resources, [(occurrence, binding.clone())])
    }

    #[test]
    fn an_interface_successor_may_only_carry_a_loan_an_arm_held() {
        let (left, left_binding) = arm_holding_a_view("left");
        let (right, right_binding) = arm_holding_a_view("right");

        // No claimed authority at all is always inherited.
        assert!(interface_successor_loans_are_inherited(
            &CState::new(),
            [&left, &right]
        ));
        // Either arm's own root is, whichever arm held it.
        assert!(interface_successor_loans_are_inherited(
            &successor_carrying(&left_binding),
            [&left, &right]
        ));
        assert!(interface_successor_loans_are_inherited(
            &successor_carrying(&right_binding),
            [&left, &right]
        ));
        // A root neither arm reached is not admitted by the join.
        let (_, outside) = arm_holding_a_view("outside");
        assert!(!interface_successor_loans_are_inherited(
            &successor_carrying(&outside),
            [&left, &right]
        ));
        // Nor is one arm's root once that arm is not part of the join.
        assert!(!interface_successor_loans_are_inherited(
            &successor_carrying(&right_binding),
            [&left, &left]
        ));
    }

    fn constructor_partition_fixture(
        width: usize,
    ) -> (ExecutionProofCore, crate::kernel::AlgebraicTerm) {
        constructor_partition_fixture_with_type(width, CType::Int32)
    }

    fn constructor_partition_fixture_with_type(
        width: usize,
        payload_type: CType,
    ) -> (ExecutionProofCore, crate::kernel::AlgebraicTerm) {
        use crate::kernel::{
            AlgebraicSchemas, AlgebraicTerm, AlgebraicTermNode, AlgebraicType, AlgebraicValueType,
            AlgebraicVariantType,
        };
        let variants: Arc<[AlgebraicVariantType]> = (0..width)
            .map(|index| AlgebraicVariantType {
                name: format!("C{index}"),
                fields: vec![AlgebraicValueType::C(payload_type)],
            })
            .collect::<Vec<_>>()
            .into();
        let key = AlgebraicValueType::Algebraic {
            name: "Cases".into(),
            arguments: vec![],
        };
        let value = AlgebraicTerm {
            algebraic_type: AlgebraicType {
                rigid: false,
                name: "Cases".into(),
                arguments: vec![],
                variants: variants.clone(),
                schemas: Arc::new(AlgebraicSchemas::new(BTreeMap::from([(key, variants)]))),
            },
            node: AlgebraicTermNode::Variable(Variable(8)),
        };
        let state = CState::new();
        let function = c_function(
            CType::Int32,
            "entry",
            vec![],
            CStatement::Return(CExpression::Value(CValue::Int32(
                Bitvector32Term::Variable(Variable(4_000_000)),
            ))),
        );
        let mut core = ExecutionProofCore::at_entry(state.clone(), ExecutionFrontier::default());
        assert!(
            core.record_checked_function_entry(&function, &[], &state, PureFactContext::new())
                .is_ok()
        );
        (core, value)
    }

    #[test]
    fn constructor_partition_transports_pointer_payloads_without_scanning_ambient_facts() {
        let (core, mut value) = constructor_partition_fixture_with_type(2, CType::Int32Pointer);
        let payload = Pointer::symbolic(Variable(7_000_000));
        let program = Pointer::symbolic(Variable(1_000_001));
        value.node = crate::kernel::AlgebraicTermNode::Constructor {
            variant: "C0".into(),
            fields: vec![crate::kernel::AlgebraicValue::C(CValue::typed_pointer(
                payload.clone(),
                CType::Int32Pointer,
            ))],
        };
        let alias = Proposition::ConditionIs(
            crate::kernel::ConditionTerm::pointer_equal(payload.clone(), program.clone()),
            true,
        );
        let env = crate::kernel::CExecutionEnvironment::new();
        let mut samples = Vec::new();
        for size in [8, 32, 128] {
            let mut facts = ProofFacts::default().with_fact(alias.clone());
            for index in 0..size {
                facts = facts.with_fact(Proposition::Predicate {
                    name: format!("unrelated_{index}"),
                    arguments: vec![],
                });
            }
            let ((partition, fields, _), work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    core.algebraic_case_partition(
                        &facts,
                        &value,
                        &env,
                        &[],
                        None,
                        4_000_000,
                        65_536,
                    )
                    .unwrap()
                });
            let witness = Pointer::symbolic(fields[0][0].0);
            let transported = Proposition::ConditionIs(
                crate::kernel::ConditionTerm::pointer_equal(program.clone(), witness),
                true,
            );
            assert!(partition.facts_for_case(0).unwrap().contains(&transported));
            assert!(!partition.facts_for_case(1).unwrap().contains(&transported));
            assert!(!facts.contains(&transported));
            let (unrelated, _, _) = core
                .algebraic_case_partition(
                    &ProofFacts::default(),
                    &value,
                    &env,
                    &[],
                    None,
                    4_000_000,
                    65_536,
                )
                .unwrap();
            assert!(!unrelated.facts_for_case(0).unwrap().contains(&transported));
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|pair| pair[1] <= pair[0] + 16),
            "{samples:?}"
        );
    }

    #[test]
    fn constructor_partition_checks_complete_coverage_and_exact_scopes() {
        for width in [1, 2, 4, 16] {
            let (core, value) = constructor_partition_fixture(width);
            let root = ProofFacts::default();
            let (partition, fields, _) = core
                .algebraic_case_partition(
                    &root,
                    &value,
                    &crate::kernel::CExecutionEnvironment::new(),
                    &[],
                    None,
                    4_000_000,
                    65_536,
                )
                .unwrap();
            assert_eq!(fields.len(), width);
            let mut traces = Vec::new();
            for index in 0..width {
                let mut arm = core.clone();
                assert!(arm.record_proof_case_arm(
                    partition.clone(),
                    index,
                    root.with_fact(partition.case_fact(index).unwrap().clone())
                ));
                traces.push(arm.execution_evidence[0].clone());
            }
            assert!(crate::kernel::api::proof_case_partitions_are_exhaustive(
                &traces
            ));
            if width > 1 {
                assert!(!crate::kernel::api::proof_case_partitions_are_exhaustive(
                    &traces[1..]
                ));
            }
            let mut wrong = core.clone();
            assert!(!wrong.record_proof_case_arm(partition.clone(), width, root.clone()));
            assert!(!wrong.record_proof_case_arm(partition.clone(), 0, root.clone()));
            let facts = root.with_fact(partition.case_fact(0).unwrap().clone());
            let extra = facts.with_fact(Proposition::Predicate {
                name: "unjustified".into(),
                arguments: vec![],
            });
            assert!(!wrong.record_proof_case_arm(partition.clone(), 0, extra));
            wrong.state = CState::new().with_local("changed", int32(1)).into();
            // A witness belongs to the exact state its partition was issued
            // against, so the moved frontier cannot take an arm of the old one.
            assert!(!wrong.record_proof_case_arm(partition.clone(), 0, facts));
            // It can issue its own, though: a proof `match` runs at any
            // frontier the proof has reached, not only at an unchanged entry.
            let (moved, _, _) = wrong
                .algebraic_case_partition(
                    &root,
                    &value,
                    &crate::kernel::CExecutionEnvironment::new(),
                    &[],
                    None,
                    4_000_000,
                    65_536,
                )
                .expect("a frontier that has moved still issues its partition");
            let moved_facts = root.with_fact(moved.case_fact(0).unwrap().clone());
            assert!(wrong.record_proof_case_arm(moved, 0, moved_facts));
        }
    }

    #[test]
    fn constructor_partition_exclusion_requires_its_exact_contradiction() {
        let (core, mut value) = constructor_partition_fixture(2);
        value.node = crate::kernel::AlgebraicTermNode::Constructor {
            variant: "C0".into(),
            fields: vec![crate::kernel::AlgebraicValue::C(int32(11))],
        };
        let root = ProofFacts::default();
        let (partition, _, _) = core
            .algebraic_case_partition(
                &root,
                &value,
                &crate::kernel::CExecutionEnvironment::new(),
                &[],
                None,
                4_000_000,
                65_536,
            )
            .unwrap();
        let live = partition.case_fact(0).unwrap().clone();
        let dead = partition.case_fact(1).unwrap().clone();
        assert!(
            partition
                .excluding_constructor_case(0, live.clone())
                .is_none()
        );
        assert!(
            partition
                .excluding_constructor_case(1, live.clone())
                .is_none()
        );
        assert!(
            partition
                .excluding_constructor_case(2, dead.clone())
                .is_none()
        );
        let excluded = partition.excluding_constructor_case(1, dead).unwrap();
        assert!(!Arc::ptr_eq(&partition.identity, &excluded.identity));
        let mut old_arm = core.clone();
        let live_facts = partition.facts_for_case(0).unwrap();
        assert!(old_arm.record_proof_case_arm(partition, 0, live_facts));
        assert!(!crate::kernel::api::proof_case_partitions_are_exhaustive(
            &old_arm.execution_evidence
        ));
        let mut live_arm = core;
        let live_facts = excluded.facts_for_case(0).unwrap();
        assert!(live_arm.record_proof_case_arm(excluded, 0, live_facts));
        assert!(crate::kernel::api::proof_case_partitions_are_exhaustive(
            &live_arm.execution_evidence
        ));
        // New exclusion evidence cannot discharge an old partition's missing arm.
        assert!(!crate::kernel::api::proof_case_partitions_are_exhaustive(
            &[
                old_arm.execution_evidence[0].clone(),
                live_arm.execution_evidence[0].clone(),
            ]
        ));
    }

    #[test]
    fn constructor_partition_witnesses_avoid_source_facts_and_previous_matches() {
        let (core, value) = constructor_partition_fixture(2);
        let occupied = Variable(4_065_536);
        let root = ProofFacts::from_ordered(&[Proposition::Equal(
            crate::kernel::Term::CValue(CValue::Int32(Bitvector32Term::Variable(occupied))),
            crate::kernel::Term::CValue(int32(0)),
        )]);
        let env = crate::kernel::CExecutionEnvironment::new();
        let (partition, fields, next) = core
            .algebraic_case_partition(&root, &value, &env, &[], None, 4_000_000, 65_536)
            .unwrap();
        assert!(fields.iter().flatten().all(|(var, _)| var.0 > occupied.0));
        let facts = root.with_fact(partition.case_fact(0).unwrap().clone());
        let (_, later, _) = core
            .algebraic_case_partition(&facts, &value, &env, &[], None, next, 65_536)
            .unwrap();
        assert!(later.iter().flatten().all(|(var, _)| var.0 >= next));
        assert!(
            core.algebraic_case_partition(&root, &value, &env, &[], None, u64::MAX, 1)
                .is_none()
        );
        assert!(
            core.algebraic_case_partition(&root, &value, &env, &[], None, 0, 0)
                .is_none()
        );
    }

    /// A frontier that is not a function entry reserves the region's own entry
    /// state and everything the kernel has issued since, so a witness can
    /// neither name a value the region started with nor one issued inside it.
    #[test]
    fn constructor_partition_witnesses_avoid_the_region_state_and_issued_variables() {
        let (_, value) = constructor_partition_fixture(2);
        let occupied = Variable(4_000_000);
        let state =
            CState::new().with_local("cursor", CValue::Int32(Bitvector32Term::Variable(occupied)));
        let core = ExecutionProofCore::at_entry(state, ExecutionFrontier::default());
        let root = ProofFacts::default();
        let env = crate::kernel::CExecutionEnvironment::new();
        let (_, fields, _) = core
            .algebraic_case_partition(&root, &value, &env, &[], None, 4_000_000, 65_536)
            .expect("a loop-body frontier issues its partition");
        assert!(fields.iter().flatten().all(|(var, _)| *var != occupied));

        // `next_kernel_variable` is execution-relative, so an execution that
        // has issued 200_000 identities occupies
        // `1_000_000 .. 1_200_000` and a probe starting inside that range
        // must walk out of it. The field used to be set here as if it were an
        // absolute id, which is how the comparison against it stayed vacuous:
        // the partition's own candidates start at 4_000_000, above every
        // identity an execution can issue.
        let mut issued = core.clone();
        issued
            .advance_kernel_variable_mark(200_000)
            .expect("the counter moves forward");
        assert_eq!(issued.issued_kernel_variable_bound(), 1_200_000);
        let (_, fields, _) = issued
            .algebraic_case_partition(&root, &value, &env, &[], None, 1_000_000, 65_536)
            .expect("a partition skips the issued range");
        assert!(fields.iter().flatten().all(|(var, _)| var.0 >= 1_200_000));
        // The same probe at the range the surface actually uses is unaffected:
        // 4_000_000 is above `KERNEL_VARIABLE_CEILING`, so range separation
        // already covers it and the first candidate is taken.
        let (_, fields, _) = issued
            .algebraic_case_partition(&root, &value, &env, &[], None, 4_065_536, 65_536)
            .expect("a partition above the execution range is unconstrained by it");
        assert!(fields.iter().flatten().any(|(var, _)| var.0 == 4_065_536));
    }

    /// The counter is the kernel's: it moves forward through
    /// [`ExecutionProofCore::advance_kernel_variable_mark`] and a rewind is
    /// refused rather than silently re-issuing identities a live value carries.
    #[test]
    fn an_execution_counter_cannot_be_rewound() {
        let mut core = ExecutionProofCore::at_entry(CState::new(), ExecutionFrontier::default());
        assert_eq!(core.kernel_variable_mark(), 0);
        assert_eq!(
            core.issued_kernel_variable_bound(),
            ExecutionBudget::KERNEL_VARIABLE_BASE
        );
        assert!(core.advance_kernel_variable_mark(12).is_ok());
        assert!(core.advance_kernel_variable_mark(12).is_ok());
        assert!(core.advance_kernel_variable_mark(30).is_ok());
        assert_eq!(
            core.advance_kernel_variable_mark(29),
            Err("an execution's fresh-variable counter cannot move backwards")
        );
        assert_eq!(core.kernel_variable_mark(), 30);
        assert_eq!(
            core.issued_kernel_variable_bound(),
            ExecutionBudget::KERNEL_VARIABLE_BASE + 30
        );
    }

    #[test]
    fn constructor_partition_reserves_algebraic_variables_in_opaque_environment_terms() {
        use crate::kernel::{AlgebraicTermNode, CExecutionEnvironment, PureFunctionArgument};
        let (core, mut value) = constructor_partition_fixture(2);
        value.node = AlgebraicTermNode::Variable(Variable(4_065_536));
        let function = c_function(
            CType::Int32,
            "opaque_environment",
            vec![],
            CStatement::Return(CExpression::Value(CValue::Int32(
                Bitvector32Term::ClickFunctionApplication {
                    name: "opaque".into(),
                    arguments: vec![PureFunctionArgument::Algebraic(value.clone())],
                },
            ))),
        );
        let environment = CExecutionEnvironment::new().with_function(function);
        value.node = AlgebraicTermNode::Variable(Variable(8));
        let (_, fields, _) = core
            .algebraic_case_partition(
                &ProofFacts::default(),
                &value,
                &environment,
                &[],
                None,
                4_000_000,
                65_536,
            )
            .unwrap();
        assert!(fields.iter().flatten().all(|(var, _)| var.0 > 4_065_536));
    }

    #[test]
    fn concrete_constructor_payload_spelling_is_checked_and_indexed() {
        use crate::kernel::{
            AlgebraicSchemas, AlgebraicTerm, AlgebraicTermNode, AlgebraicType, AlgebraicValue,
            AlgebraicValueType, AlgebraicVariantType, Term,
        };
        let (core, mut payload) = constructor_partition_fixture(2);
        payload.node = AlgebraicTermNode::Variable(Variable(4_065_536));
        let inner_key = AlgebraicValueType::Algebraic {
            name: "Cases".into(),
            arguments: vec![],
        };
        let variants: Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
            name: "Pair".into(),
            fields: vec![inner_key.clone(), inner_key.clone()],
        }]
        .into();
        let mut sibling = payload.clone();
        sibling.node = AlgebraicTermNode::Variable(Variable(4_131_072));
        let value = AlgebraicTerm {
            algebraic_type: AlgebraicType {
                rigid: false,
                name: "Wrapper".into(),
                arguments: vec![],
                variants: variants.clone(),
                schemas: Arc::new(AlgebraicSchemas::new(BTreeMap::from([
                    (inner_key, payload.algebraic_type.variants.clone()),
                    (
                        AlgebraicValueType::Algebraic {
                            name: "Wrapper".into(),
                            arguments: vec![],
                        },
                        variants,
                    ),
                ]))),
            },
            node: AlgebraicTermNode::Constructor {
                variant: "Pair".into(),
                fields: vec![
                    AlgebraicValue::Algebraic(payload.clone()),
                    AlgebraicValue::Algebraic(sibling.clone()),
                ],
            },
        };
        assert_eq!(
            crate::kernel::arm_algebraic_payload_spelling(&value, "Pair", 0),
            Some(&payload)
        );
        assert_eq!(
            crate::kernel::arm_algebraic_payload_spelling(&value, "Pair", 1),
            Some(&sibling)
        );
        assert!(crate::kernel::arm_algebraic_payload_spelling(&value, "Other", 0).is_none());
        assert!(crate::kernel::arm_algebraic_payload_spelling(&value, "Pair", 2).is_none());
        assert!(crate::kernel::arm_algebraic_payload_spelling(&payload, "Pair", 0).is_none());
        let environment = crate::kernel::CExecutionEnvironment::new();
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let facts = ProofFacts::from_ordered(
                &(0..size)
                    .map(|index| Proposition::Predicate {
                        name: format!("ambient{index}"),
                        arguments: vec![],
                    })
                    .collect::<Vec<_>>(),
            );
            let ((partition, witnesses, _), work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    core.algebraic_case_partition(
                        &facts,
                        &value,
                        &environment,
                        &[],
                        None,
                        4_000_000,
                        65_536,
                    )
                    .unwrap()
                });
            // Reusing the spelling must not reuse existential witness identities.
            assert!(
                witnesses
                    .iter()
                    .flatten()
                    .all(|(variable, _)| variable.0 > 4_131_072)
            );
            let spelled = Proposition::Equal(
                Term::Algebraic(value.clone()),
                Term::Algebraic(value.clone()),
            );
            assert!(partition.facts_for_case(0).unwrap().contains(&spelled));
            samples.push(work);
        }
        assert!(samples.iter().all(|work| *work > 0));
        assert!(
            samples[2] <= samples[0] * 2,
            "ambient facts must not cause a scan: {samples:?}"
        );
    }

    #[test]
    fn constructor_partition_freshness_is_indexed_and_output_linear() {
        for size in [16, 64, 256] {
            let (core, value) = constructor_partition_fixture(2);
            let mut facts = ProofFacts::from_ordered(
                &(0..size)
                    .map(|index| Proposition::Predicate {
                        name: format!("ambient{index}"),
                        arguments: vec![],
                    })
                    .collect::<Vec<_>>(),
            );
            let environment = crate::kernel::CExecutionEnvironment::new();
            let builds = MATCH_SCOPE_INDEX_BUILDS.with(std::cell::Cell::get);
            let probes = MATCH_FRESHNESS_PROBES.with(std::cell::Cell::get);
            let mut next = 4_000_000;
            for _ in 0..size {
                let (partition, fields, successor) = core
                    .algebraic_case_partition(&facts, &value, &environment, &[], None, next, 65_536)
                    .unwrap();
                assert_eq!(fields.iter().map(Vec::len).sum::<usize>(), 2);
                facts = facts.with_fact(partition.case_fact(0).unwrap().clone());
                next = successor;
            }
            assert_eq!(
                MATCH_SCOPE_INDEX_BUILDS.with(std::cell::Cell::get) - builds,
                1
            );
            assert_eq!(
                MATCH_FRESHNESS_PROBES.with(std::cell::Cell::get) - probes,
                2 * size + 1
            );
        }
    }

    fn returned_proposition_trace(
        state: &CState,
        facts: &ProofFacts,
    ) -> (CFunction, Vec<CheckedExecutionEvent>) {
        let statement = CStatement::Return(CExpression::Value(int32(0)));
        let function = c_function(CType::Int32, "test", vec![], statement.clone());
        let events = vec![
            CheckedExecutionEvent::Statement(Theorem::new(Proposition::CStatementVerifies {
                state: Box::new(state.clone()),
                statement: Box::new(statement),
                outcome: CStatementOutcome::Return {
                    value: int32(0),
                    state: Box::new(state.clone()),
                },
            })),
            CheckedExecutionEvent::Context(facts.assumptions().clone()),
        ];
        (function, events)
    }

    #[test]
    fn return_proof_publication_shares_candidate_fact_and_effect_objects() {
        for size in [4, 64, 1024] {
            let facts: ExecutionFacts = (0..size)
                .map(|index| {
                    ExecutionPureFact::new(Proposition::ConditionIs(
                        crate::kernel::ConditionTerm::equal(
                            crate::kernel::Bitvector32Term::Variable(crate::kernel::Variable(
                                index,
                            )),
                            crate::kernel::Bitvector32Term::Constant(0),
                        ),
                        false,
                    ))
                })
                .collect();
            let state = CState::new();
            let effects: ExecutionFacts = [ExecutionPureFact::certified(
                Proposition::CMemoryMutatesOnly {
                    before: state.memory().clone(),
                    after: state.memory().clone(),
                    writes: vec![],
                },
            )]
            .into();
            let candidate = crate::kernel::CFunctionExecutionCandidate {
                data: Arc::new(crate::kernel::CFunctionExecutionCandidateData {
                    outcome: Arc::new(CFunctionOutcome::Return {
                        value: int32(0),
                        state: Box::new(state.clone()),
                    }),
                    facts: facts.clone(),
                    effect_facts: effects.clone(),
                    effects_public_first: true,
                    obligations: Arc::new(vec![]),
                    loan_evidence: crate::kernel::loans::empty_checked_loan_evidence_sequence(),
                }),
            };
            let context = CheckedReturnContext::from_candidate(
                CStatementOutcome::Return {
                    value: int32(0),
                    state: Box::new(state),
                },
                &candidate,
            );
            assert_eq!(context.facts.len(), size as usize + 1);
            for (original, retained) in facts.iter().zip(&context.facts) {
                assert!(std::ptr::eq(original, retained));
            }
            assert!(std::ptr::eq(&effects[0], &context.facts[size as usize]));
            assert!(context.facts[size as usize].is_certified());
            drop(candidate);
            drop(facts);
            drop(effects);
            assert_eq!(context.facts.len(), size as usize + 1);
        }
    }

    fn returned_proposition_context(state: &CState) -> Arc<CheckedReturnContext> {
        Arc::new(CheckedReturnContext {
            origin: CStatementOutcome::Return {
                value: int32(0),
                state: Box::new(state.clone()),
            },
            published: CFunctionOutcome::Return {
                value: int32(0),
                state: Box::new(state.clone()),
            },
            facts: ExecutionFacts::new(),
        })
    }

    fn returned_proposition_event(
        context: &Arc<CheckedReturnContext>,
        state: &CState,
        base: &ProofFacts,
        roots: &ProofFacts,
        proposition: Proposition,
    ) -> CheckedExecutionEvent {
        CheckedExecutionEvent::ReturnProposition(CheckedReturnProposition {
            base: base.clone(),
            context: context.clone(),
            proof: super::super::CheckedProposition::new(
                proposition,
                roots.clone(),
                Some(super::super::OutcomeProofCore {
                    identity: super::super::OutcomeIdentity::fresh(),
                    result: Arc::new(int32(0)),
                    state: state.clone().into(),
                    store_consequences_available: false,
                    is_exceptional: false,
                    effect_facts: Arc::new(ExecutionFacts::new()),
                }),
                None,
            ),
        })
    }

    #[test]
    fn return_proposition_rejects_sibling_assumptions_and_other_memory() {
        let fact = Proposition::ConditionIs(
            crate::kernel::ConditionTerm::equal(
                Bitvector32Term::Variable(Variable(42)),
                Bitvector32Term::Constant(0),
            ),
            true,
        );
        let state = CState::new();
        let empty = ProofFacts::default();
        let sibling = empty.clone().with_fact(fact.clone());
        let (function, original) = returned_proposition_trace(&state, &empty);
        let context = returned_proposition_context(&state);
        for base in [&empty, &sibling] {
            let mut events = original.clone();
            events.push(returned_proposition_event(
                &context,
                &state,
                base,
                &sibling,
                fact.clone(),
            ));
            assert_eq!(
                trace_completion(&function, &events, empty.assumptions(), false).err(),
                Some("return proof assumes an unjustified path fact")
            );
        }
        let (function, mut events) = returned_proposition_trace(&state, &sibling);
        let mut other_state = state.clone();
        other_state.memory = CMemory::new().with_block("other_snapshot", 4);
        let other_context = returned_proposition_context(&other_state);
        let wrong_snapshot =
            returned_proposition_event(&other_context, &other_state, &sibling, &sibling, fact);
        let CheckedExecutionEvent::ReturnProposition(retained) = &wrong_snapshot else {
            unreachable!()
        };
        assert!(
            CheckedReturnProposition::check(retained.proof.clone(), &sibling, context,).is_err()
        );
        events.push(wrong_snapshot);
        assert_eq!(
            trace_completion(&function, &events, sibling.assumptions(), false).err(),
            Some("return proof belongs to a different execution path")
        );
    }

    #[test]
    fn return_proposition_checks_resource_compositions_without_granting_ownership() {
        let state = CState::new();
        let base = ProofFacts::default();
        let context = returned_proposition_context(&state);
        for overlaps in [false, true] {
            let pointer = crate::kernel::Pointer::symbolic(Variable(42));
            let fact =
                Proposition::CResourceComposition(ResourceContext::new().unchecked_with_facts([
                    CResourceFact::own_memory(crate::kernel::CMemoryRange::new(
                        pointer.clone(),
                        0.into(),
                        1.into(),
                    )),
                    CResourceFact::own_memory(crate::kernel::CMemoryRange::new(
                        pointer,
                        if overlaps { 0.into() } else { 1.into() },
                        2.into(),
                    )),
                ]));
            let roots = base.clone().with_fact(fact.clone());
            let (function, mut events) = returned_proposition_trace(&state, &base);
            events.push(returned_proposition_event(
                &context, &state, &base, &roots, fact,
            ));
            let result = trace_completion(&function, &events, base.assumptions(), false);
            if overlaps {
                assert_eq!(
                    result.err(),
                    Some("return proof assumes an unjustified path fact")
                );
            } else {
                let (CStatementOutcome::Return { state: after, .. }, _, _) = result.unwrap() else {
                    panic!("expected a returned state");
                };
                assert_eq!(after.resources(), state.resources());
            }
        }
    }

    #[test]
    fn return_proposition_accepts_materialized_reads_without_widening_or_value_facts() {
        let pointer = Pointer::symbolic(Variable(42));
        let memory = CMemory::new().store(pointer.clone(), int32(7));
        let state = CState::new().with_memory(memory.clone());
        let empty = ProofFacts::default();
        let (function, original) = returned_proposition_trace(&state, &empty);
        let context = returned_proposition_context(&state);
        let read = |memory, base, bytes| Proposition::CMemoryLoadable {
            memory,
            base,
            bytes,
            wide: false,
        };
        let valid = read(
            memory.clone(),
            pointer.clone(),
            Bitvector32Term::Constant(4),
        );
        let bad_value = Proposition::ConditionIs(
            crate::kernel::ConditionTerm::equal(
                Bitvector32Term::Variable(Variable(43)),
                Bitvector32Term::Constant(7),
            ),
            true,
        );
        let cases = [
            (valid, true),
            (
                read(
                    memory.clone(),
                    pointer.clone(),
                    Bitvector32Term::Constant(8),
                ),
                false,
            ),
            (
                read(
                    memory.clone(),
                    Pointer::symbolic(Variable(44)),
                    Bitvector32Term::Constant(4),
                ),
                false,
            ),
            (
                read(
                    CMemory::new(),
                    pointer.clone(),
                    Bitvector32Term::Constant(4),
                ),
                false,
            ),
            (
                read(
                    memory.without_local_block(&pointer.block),
                    pointer,
                    Bitvector32Term::Constant(4),
                ),
                false,
            ),
            (bad_value, false),
        ];
        let typed = |memory, pointer, value_type| Proposition::CMemoryReadDefined {
            memory,
            pointer,
            value_type,
        };
        let pointer = Pointer::symbolic(Variable(42));
        let typed_cases = [
            (
                typed(state.memory().clone(), pointer.clone(), CType::Int32),
                true,
            ),
            (
                typed(state.memory().clone(), pointer.clone(), CType::Int64),
                false,
            ),
            (typed(CMemory::new(), pointer.clone(), CType::Int32), false),
            (
                typed(
                    state.memory().clone(),
                    Pointer::symbolic(Variable(44)),
                    CType::Int32,
                ),
                false,
            ),
            (
                typed(
                    CMemory::new().with_uninitialized_block(pointer.block.clone(), 4),
                    pointer,
                    CType::Int32,
                ),
                false,
            ),
        ];
        let cases = cases.into_iter().chain(typed_cases);
        for (fact, accepted) in cases {
            let roots = empty.clone().with_fact(fact.clone());
            let mut events = original.clone();
            events.push(returned_proposition_event(
                &context, &state, &empty, &roots, fact,
            ));
            let result = trace_completion(&function, &events, empty.assumptions(), false);
            assert_eq!(result.is_ok(), accepted);
            if let Ok((CStatementOutcome::Return { state: after, .. }, _, _)) = result {
                assert_eq!(after.resources(), state.resources());
                assert_eq!(after.memory(), state.memory());
            }
        }
    }

    #[test]
    fn return_materialized_reads_scale_with_the_selected_cells() {
        let samples = [16, 32, 64, 128].map(|size| {
            let mut memory = CMemory::new();
            let pointers: Vec<_> = (0..size).map(|i| Pointer::symbolic(Variable(i))).collect();
            for pointer in &pointers {
                memory = memory.store(pointer.clone(), int32(7));
            }
            let state = CState::new().with_memory(memory.clone());
            let mut base = ProofFacts::default();
            let (function, mut events) = returned_proposition_trace(&state, &base);
            let initial = base.clone();
            let context = returned_proposition_context(&state);
            for pointer in pointers {
                let fact = Proposition::CMemoryLoadable {
                    memory: memory.clone(),
                    base: pointer,
                    bytes: Bitvector32Term::Constant(4),
                    wide: false,
                };
                let roots = base.with_fact(fact.clone());
                events.push(returned_proposition_event(
                    &context, &state, &base, &roots, fact,
                ));
                base = roots;
            }
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                assert!(trace_completion(&function, &events, initial.assumptions(), false).is_ok());
            });
            work
        });
        assert!(samples[0] > 0);
        assert!(
            samples.windows(2).all(|pair| pair[1] <= 2 * pair[0] + 8),
            "materialized reads rescanned their context: {samples:?}"
        );
    }

    #[test]
    fn return_argument_facts_require_an_ordinary_positive_or_viewed_resource() {
        use crate::kernel::{
            CComparisonOperator, SpecExpression, SpecProposition, c_parameter, c_variable,
        };
        let value = CValue::Int32(Bitvector32Term::Variable(Variable(42)));
        let fact = Proposition::ConditionIs(
            crate::kernel::ConditionTerm::signed_less_equal(
                1.into(),
                Bitvector32Term::Variable(Variable(42)),
            ),
            true,
        );
        let definition = CCompositeResourceDefinition::new(
            "positive",
            vec![c_parameter("n", CType::Int32)],
            None,
            false,
            vec![],
            vec![SpecProposition::Comparison {
                left: SpecExpression::Value(int32(1)),
                operator: CComparisonOperator::LessEqual,
                right: SpecExpression::CExpression(c_variable("n")),
            }],
        );
        let owned = CResourceFact::own_composite("positive".into(), vec![value.clone()]);
        let viewed = CResourceFact::view_composite("positive".into(), vec![value]);
        let zero = CResourceFact::Own(owned.resource().clone(), Box::new(0.into()));
        for (resource, authorized, accepted) in [
            (Some(owned.clone()), false, true),
            (Some(viewed), false, true),
            (Some(zero), false, false),
            (None, false, false),
            (Some(owned), true, false),
        ] {
            let resources = resource
                .into_iter()
                .fold(ResourceContext::new(), |r, fact| {
                    r.unchecked_with_fact(fact)
                });
            let state = CState::new().with_resource_context(resources);
            let empty = ProofFacts::default();
            let roots = empty.with_fact(fact.clone());
            let (function, mut events) = returned_proposition_trace(&state, &empty);
            let function = function.with_composite_resource_definitions(vec![
                definition.clone().with_authorized(authorized),
            ]);
            let context = returned_proposition_context(&state);
            events.push(returned_proposition_event(
                &context,
                &state,
                &empty,
                &roots,
                fact.clone(),
            ));
            let result = trace_completion(&function, &events, empty.assumptions(), false);
            assert_eq!(result.is_ok(), accepted);
            if let Ok((CStatementOutcome::Return { state: after, .. }, _, _)) = result {
                assert_eq!(after.resources(), state.resources());
            }
        }
    }

    #[test]
    fn return_argument_facts_do_not_project_mutable_memory_invariants() {
        use crate::kernel::{
            CComparisonOperator, CMemorySegment, SpecExpression, SpecProposition, c_index,
            c_int32_literal, c_parameter, c_variable,
        };
        let pointer = Pointer::symbolic(Variable(42));
        let held = CResourceFact::own_composite(
            "cell".into(),
            vec![CValue::typed_pointer(pointer.clone(), CType::Int32Pointer)],
        );
        let definition = CCompositeResourceDefinition::new(
            "cell",
            vec![c_parameter("p", CType::Int32Pointer)],
            None,
            false,
            vec![CResourceSpec::owned_memory(CMemorySegment::new(
                c_variable("p"),
                c_int32_literal(0),
                c_int32_literal(1),
            ))],
            vec![SpecProposition::Comparison {
                left: SpecExpression::CExpression(c_index(c_variable("p"), c_int32_literal(0))),
                operator: CComparisonOperator::Equal,
                right: SpecExpression::Value(int32(7)),
            }],
        );
        assert!(
            crate::kernel::functions::evaluate_composite_resource_fact_propositions(
                &held,
                std::slice::from_ref(&definition),
                &CMemory::new(),
                &ResourceContext::new(),
                &PureFactContext::new().require_owned_expression_loads()
            )
            .is_none()
        );
        let state = CState::new()
            .with_memory(CMemory::new().store(pointer, int32(9)))
            .with_resource_context(ResourceContext::new().unchecked_with_fact(held));
        let empty = ProofFacts::default();
        let false_fact = Proposition::ConditionIs(
            crate::kernel::ConditionTerm::equal(9.into(), 7.into()),
            true,
        );
        let roots = empty.with_fact(false_fact.clone());
        let (function, mut events) = returned_proposition_trace(&state, &empty);
        let function = function.with_composite_resource_definitions(vec![definition]);
        let context = returned_proposition_context(&state);
        events.push(returned_proposition_event(
            &context, &state, &empty, &roots, false_fact,
        ));
        assert!(trace_completion(&function, &events, empty.assumptions(), false).is_err());
    }

    #[test]
    fn return_proposition_context_validation_scales_with_introductions() {
        let samples = [16, 32, 64, 128].map(|size| {
            let state = CState::new();
            let mut base = ProofFacts::default();
            let premises: Vec<_> = (0..size)
                .map(|i| {
                    Proposition::ConditionIs(
                        crate::kernel::ConditionTerm::equal(
                            Bitvector32Term::Variable(Variable(i)),
                            Bitvector32Term::Constant(i as u32),
                        ),
                        true,
                    )
                })
                .collect();
            for fact in &premises {
                base = base.with_fact(fact.clone());
            }
            let (function, mut events) = returned_proposition_trace(&state, &base);
            let initial = base.clone();
            let context = returned_proposition_context(&state);
            for fact in premises {
                let goal = Proposition::And(Box::new(fact.clone()), Box::new(fact));
                events.push(returned_proposition_event(
                    &context,
                    &state,
                    &base,
                    &base,
                    goal.clone(),
                ));
                base = base.with_fact(goal);
            }
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                assert!(trace_completion(&function, &events, initial.assumptions(), false).is_ok());
            });
            work
        });
        assert!(samples[0] > 0);
        assert!(
            samples.windows(2).all(|pair| pair[1] <= 2 * pair[0] + 8),
            "return proofs rescanned their growing ambient contexts: {samples:?}"
        );
    }

    #[test]
    fn return_instance_guard_and_body_cannot_use_sibling_assumptions() {
        use crate::kernel::{
            AlgebraicSchemas, AlgebraicTerm, AlgebraicTermNode, AlgebraicType, AlgebraicValue,
            AlgebraicValueType, AlgebraicVariantType, CResourceMatchArm, CResourceMatchBody,
            ConditionTerm, ResourceFieldSchema, ResourceFieldType, ResourceInstance, Term,
            Variable,
        };
        let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![
            AlgebraicVariantType {
                name: "Left".into(),
                fields: vec![],
            },
            AlgebraicVariantType {
                name: "Right".into(),
                fields: vec![],
            },
        ]
        .into();
        let ty = AlgebraicType {
            name: "Case".into(),
            arguments: vec![],
            rigid: false,
            variants: variants.clone(),
            schemas: std::sync::Arc::new(AlgebraicSchemas::new(std::collections::BTreeMap::from(
                [(
                    AlgebraicValueType::Algebraic {
                        name: "Case".into(),
                        arguments: vec![],
                    },
                    variants,
                )],
            ))),
        };
        let model = AlgebraicTerm {
            algebraic_type: ty.clone(),
            node: AlgebraicTermNode::Variable(Variable(43)),
        };
        let schema = ResourceFieldSchema::new(vec![
            ("value".into(), ResourceFieldType::C(CType::Int32)),
            ("model".into(), ResourceFieldType::Algebraic(ty.clone())),
        ])
        .unwrap();
        let instance = ResourceInstance::new(
            Variable(1),
            "cell".into(),
            vec![].into(),
            schema.clone(),
            vec![int32(7).into(), AlgebraicValue::Algebraic(model.clone())].into(),
        )
        .unwrap();
        let word = Bitvector32Term::Variable(Variable(42));
        let guard = ConditionTerm::equal(word.clone(), Bitvector32Term::Constant(0));
        let condition = SpecProposition::Comparison {
            left: SpecExpression::Value(CValue::Int32(word)),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::Value(int32(0)),
        };
        for mode in 0..3 {
            let guarded = mode == 0;
            let matched = mode == 2;
            let definition = CCompositeResourceDefinition::new(
                "cell",
                vec![],
                guarded.then(|| condition.clone()),
                false,
                vec![],
                if guarded || matched {
                    vec![]
                } else {
                    vec![condition.clone()]
                },
            )
            .with_instance_schema(Some(schema.clone()))
            .with_resource_match_body(matched.then(|| {
                CResourceMatchBody {
                    field_index: 1,
                    algebraic_type: ty.clone(),
                    arms: ["Left", "Right"]
                        .into_iter()
                        .map(|variant| CResourceMatchArm {
                            children: vec![],
                            variant: variant.into(),
                            bindings: vec![],
                            binding_types: vec![],
                            binding_variables: vec![],
                            contains: vec![],
                            facts: vec![],
                        })
                        .collect(),
                }
            }));
            let selected = CResourceFact::own(CResource::Instance(instance.clone()));
            let before = CState::new().with_resource_context(
                ResourceContext::new().unchecked_with_fact(selected.clone()),
            );
            let case_fact = |variant: &str| {
                Proposition::Equal(
                    Term::Algebraic(model.clone()),
                    Term::Algebraic(AlgebraicTerm {
                        algebraic_type: ty.clone(),
                        node: AlgebraicTermNode::Constructor {
                            variant: variant.into(),
                            fields: vec![],
                        },
                    }),
                )
            };
            let left = ProofFacts::default().with_fact(if matched {
                case_fact("Left")
            } else {
                Proposition::ConditionIs(guard.clone(), true)
            });
            let right = ProofFacts::default().with_fact(if matched {
                case_fact("Right")
            } else {
                Proposition::ConditionIs(guard.clone(), false)
            });
            let (open, _) = crate::kernel::rewrite_resource_instance(
                &before,
                &instance,
                &definition,
                left.assumptions(),
                true,
            )
            .unwrap();
            let statement = CStatement::Return(CExpression::Value(int32(0)));
            let function = c_function(CType::Int32, "test", vec![], statement.clone())
                .with_composite_resource_definitions(vec![definition]);
            let mut core = ExecutionProofCore::at_entry(before, ExecutionFrontier::default());
            let mut trace = PersistentSequence::default();
            trace.push(CheckedExecutionEvent::Statement(Theorem::new(
                Proposition::CStatementVerifies {
                    state: Box::new(open.clone()),
                    statement: Box::new(statement),
                    outcome: CStatementOutcome::Return {
                        value: int32(0),
                        state: Box::new(open),
                    },
                },
            )));
            let (path_facts, rewrite_facts) = if guarded {
                (&left, &right)
            } else {
                (&right, &left)
            };
            trace.push(CheckedExecutionEvent::Context(
                path_facts.assumptions().clone(),
            ));
            core.execution_evidence = vec![trace].into();
            core.evidence_completed = true;
            // Even when both guard arms have identical memory, a rewrite checked
            // under a sibling's case cannot certify this path.
            core.record_return_resource_rewrite(
                &function,
                0,
                rewrite_facts,
                &selected,
                rewrite_facts,
            )
            .unwrap();
            let events = core.return_resource_rewrites.get(&0).unwrap().to_vec();
            let expected = if matched {
                "return fold constructor is not justified on this execution path"
            } else if guarded {
                "return fold guard is not justified on this execution path"
            } else {
                "return fold body is not justified on this execution path"
            };
            assert_eq!(
                trace_completion(&function, &events, path_facts.assumptions(), false).err(),
                Some(expected)
            );
        }
    }

    #[test]
    fn return_instance_folds_are_indexed_and_do_not_copy_sibling_traces() {
        use crate::kernel::{ResourceFieldSchema, ResourceFieldType, ResourceInstance, Variable};
        let schema =
            ResourceFieldSchema::new(vec![("value".into(), ResourceFieldType::C(CType::Int32))])
                .unwrap();
        let instance = ResourceInstance::new(
            Variable(1),
            "cell".into(),
            vec![].into(),
            schema.clone(),
            vec![int32(7).into()].into(),
        )
        .unwrap();
        let definition = CCompositeResourceDefinition::new(
            "cell",
            vec![],
            None,
            false,
            vec![crate::kernel::CResourceSpec::owned_memory(
                crate::kernel::CMemorySegment {
                    base: CExpression::Value(CValue::pointer(crate::kernel::Pointer::symbolic(
                        Variable(100),
                    ))),
                    start: CExpression::Value(int32(0)),
                    end: CExpression::Value(int32(1)),
                    element_width: 4,
                    guard: None,
                },
            )],
            vec![],
        )
        .with_instance_schema(Some(schema));
        let statement = CStatement::Return(CExpression::Value(int32(7)));
        let function = c_function(CType::Int32, "test", vec![], statement.clone())
            .with_composite_resource_definitions(vec![definition.clone()]);
        let selected = CResourceFact::own(CResource::Instance(instance.clone()));
        let folded = CState::new()
            .with_resource_context(ResourceContext::new().unchecked_with_fact(selected.clone()));
        let facts = ProofFacts::default();
        let (open, _) = crate::kernel::rewrite_resource_instance(
            &folded,
            &instance,
            &definition,
            facts.assumptions(),
            true,
        )
        .unwrap();
        let trace = |state: CState| {
            let mut trace = PersistentSequence::default();
            trace.push(CheckedExecutionEvent::Statement(Theorem::new(
                Proposition::CStatementVerifies {
                    state: Box::new(state.clone()),
                    statement: Box::new(statement.clone()),
                    outcome: CStatementOutcome::Return {
                        value: int32(7),
                        state: Box::new(state),
                    },
                },
            )));
            trace.push(CheckedExecutionEvent::Context(PureFactContext::new()));
            trace
        };
        let mut work_samples = Vec::new();
        for size in [16, 32, 64, 128] {
            let mut core =
                ExecutionProofCore::at_entry(folded.clone(), ExecutionFrontier::default());
            core.execution_evidence = (0..size)
                .map(|index| {
                    // A sibling lacks the body ownership. Its state cannot be used
                    // to satisfy this path's fold, or vice versa.
                    trace(if index == size - 1 {
                        CState::new()
                    } else {
                        open.clone()
                    })
                })
                .collect::<Vec<_>>()
                .into();
            core.evidence_completed = true;
            let base = core.clone();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                core.record_return_resource_rewrite(&function, size / 2, &facts, &selected, &facts)
                    .unwrap();
            });
            work_samples.push(work);
            for index in 0..size {
                assert!(
                    core.execution_evidence[index]
                        .shares_tail_with(&base.execution_evidence[index])
                );
                assert_eq!(
                    core.return_resource_rewrites.get(&index).is_some(),
                    index == size / 2
                );
            }
            assert!(
                core.record_return_resource_rewrite(&function, size - 1, &facts, &selected, &facts)
                    .is_err()
            );
            assert!(
                core.record_return_resource_rewrite(&function, size, &facts, &selected, &facts)
                    .is_err()
            );
            assert!(
                core.record_return_resource_rewrite(&function, size / 2, &facts, &selected, &facts)
                    .is_err()
            );
            let events = core
                .return_resource_rewrites
                .get(&(size / 2))
                .unwrap()
                .to_vec();
            let (outcome, _, _) =
                trace_completion(&function, &events, facts.assumptions(), false).unwrap();
            // The fold publishes read authority for the cells it consumed;
            // apart from that observation the state is the folded one.
            let CStatementOutcome::Return { value, state } = outcome else {
                panic!("the completion returns");
            };
            assert_eq!(value, int32(7));
            let resources = state
                .resources()
                .clone()
                .without_owned_instance_read_views();
            assert_eq!(state.with_resource_context(resources), folded);
            // Copying an event to a different path with a different body
            // state is rejected during final certification.
            let mut forged = base.execution_evidence[size - 1].clone();
            forged.push(events.last().unwrap().clone());
            assert!(
                trace_completion(&function, &forged.to_vec(), facts.assumptions(), false).is_err()
            );
            let mut collected = base.clone();
            collected
                .collect_return_resource_rewrites(&core, size / 2)
                .unwrap();
            let extra = Proposition::ConditionIs(
                crate::kernel::ConditionTerm::equal(
                    Bitvector32Term::Variable(Variable(1000)),
                    Bitvector32Term::Constant(9),
                ),
                true,
            );
            let snapshot_facts = facts.with_fact(extra.clone());
            let mut snapshot = base.clone();
            snapshot
                .record_return_resource_rewrite(
                    &function,
                    0,
                    &snapshot_facts,
                    &selected,
                    &snapshot_facts,
                )
                .unwrap();
            let (_, retained, _) = trace_completion(
                &function,
                &snapshot.return_resource_rewrites.get(&0).unwrap().to_vec(),
                facts.assumptions(),
                false,
            )
            .unwrap();
            assert!(
                !retained.proves(&extra),
                "a fold must not publish unrelated snapshot assumptions"
            );
            let mut unrelated = base;
            unrelated.execution_evidence[size / 2] = trace(open.clone());
            assert!(
                unrelated
                    .collect_return_resource_rewrites(&core, size / 2)
                    .is_err()
            );
        }
        for pair in work_samples.windows(2) {
            assert!(
                pair[1] <= pair[0] + 128,
                "path-local fold work: {work_samples:?}"
            );
        }
    }

    #[test]
    fn instance_rewrite_certificate_rejects_unrelated_state_and_fact_changes() {
        use crate::kernel::{ResourceFieldSchema, ResourceFieldType, ResourceInstance, Variable};
        let schema =
            ResourceFieldSchema::new(vec![("value".into(), ResourceFieldType::C(CType::Int32))])
                .unwrap();
        let instance = ResourceInstance::new(
            Variable(1),
            "cell".into(),
            vec![].into(),
            schema.clone(),
            vec![int32(7).into()].into(),
        )
        .unwrap();
        let definition =
            CCompositeResourceDefinition::new("cell", vec![], None, false, vec![], vec![])
                .with_instance_schema(Some(schema));
        let function = c_function(
            CType::Void,
            "test",
            vec![],
            CStatement::Return(CExpression::Value(CValue::Void)),
        )
        .with_composite_resource_definitions(vec![definition.clone()]);
        let selected = CResourceFact::own(CResource::Instance(instance.clone()));
        let before = CState::new()
            .with_resource_context(ResourceContext::new().unchecked_with_fact(selected.clone()));
        let facts = ProofFacts::default();
        let (opened, _) = crate::kernel::rewrite_resource_instance(
            &before,
            &instance,
            &definition,
            facts.assumptions(),
            true,
        )
        .unwrap();
        let calls = CheckedCallEvents::default();
        CheckedResourceRewrite::check(
            &function, &before, &facts, &selected, &opened, &facts, &calls,
        )
        .unwrap();
        let forged = opened.clone().with_resource_context(
            opened
                .resources()
                .clone()
                .unchecked_with_fact(CResourceFact::own_token("forged".into(), vec![])),
        );
        assert!(
            CheckedResourceRewrite::check(
                &function, &before, &facts, &selected, &forged, &facts, &calls
            )
            .is_err()
        );
        let forged = opened
            .clone()
            .with_memory(CMemory::new().with_block("invented", 4));
        assert!(
            CheckedResourceRewrite::check(
                &function, &before, &facts, &selected, &forged, &facts, &calls
            )
            .is_err()
        );
        let mut forged = opened.clone();
        forged.instance_field_scope = ResourceContext::new().unchecked_with_fact(selected.clone());
        assert!(
            CheckedResourceRewrite::check(
                &function, &before, &facts, &selected, &forged, &facts, &calls,
            )
            .is_err(),
            "a rewrite cannot retain scratch field bindings as a handle"
        );
        let forged_facts = facts.with_fact(Proposition::ConditionIs(
            crate::kernel::ConditionTerm::Constant(false),
            true,
        ));
        assert!(
            CheckedResourceRewrite::check(
                &function,
                &before,
                &facts,
                &selected,
                &opened,
                &forged_facts,
                &calls
            )
            .is_err()
        );
        let (closed, _) = crate::kernel::rewrite_resource_instance(
            &opened,
            &instance,
            &definition,
            facts.assumptions(),
            false,
        )
        .unwrap();
        CheckedResourceRewrite::check(
            &function, &opened, &facts, &selected, &closed, &facts, &calls,
        )
        .unwrap();
        let mut samples = Vec::new();
        for size in [16, 32, 64, 128] {
            let mut state = before.clone();
            for identity in 2..=size {
                let mut unrelated = instance.clone();
                unrelated.identity = Variable(identity);
                state.resources = state
                    .resources
                    .unchecked_with_fact(CResourceFact::own(CResource::Instance(unrelated)));
            }
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let (open, _) = crate::kernel::rewrite_resource_instance(
                    &state,
                    &instance,
                    &definition,
                    facts.assumptions(),
                    true,
                )
                .unwrap();
                CheckedResourceRewrite::check(
                    &function, &state, &facts, &selected, &open, &facts, &calls,
                )
                .unwrap();
                let (closed, _) = crate::kernel::rewrite_resource_instance(
                    &open,
                    &instance,
                    &definition,
                    facts.assumptions(),
                    false,
                )
                .unwrap();
                CheckedResourceRewrite::check(
                    &function, &open, &facts, &selected, &closed, &facts, &calls,
                )
                .unwrap();
            });
            samples.push(work);
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1] <= pair[0] + 256,
                "certificate must inspect only its exchange: {samples:?}"
            );
        }
        assert!(
            CheckedResourceRewrite::check(
                &function,
                &CState::new(),
                &facts,
                &selected,
                &before,
                &facts,
                &calls
            )
            .is_err()
        );
    }

    fn condition_event(
        state: &CState,
        condition: &CExpression,
        value: bool,
    ) -> CheckedExecutionEvent {
        CheckedExecutionEvent::Condition(Theorem::new(Proposition::CConditionEvaluates {
            state: Box::new(state.clone()),
            condition: condition.clone(),
            outcome: CConditionOutcome::Value(value),
        }))
    }

    #[test]
    fn checked_call_event_must_name_a_call_introduced_by_its_statement() {
        let assumptions = PureFactContext::new();
        let pointer = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let range = CMemoryRange::new(
            pointer,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        );
        let before = CState::new().with_memory(CMemory::new().with_block("arg-memory", 4));
        let after = before
            .clone()
            .with_memory(before.memory().clone().with_call_memory_havoc(
                crate::kernel::Variable(700),
                std::slice::from_ref(&range),
                &assumptions,
                None,
            ));
        let theorem = Theorem::new(Proposition::CStatementVerifies {
            state: Box::new(before.clone()),
            statement: Box::new(CStatement::Skip),
            outcome: CStatementOutcome::Normal(Box::new(after)),
        });
        let views = statement_call_havoc_views(&theorem);
        let [view] = views.as_slice() else {
            panic!("expected one checked call view");
        };
        let valid = CheckedCallEvent::new(view.clone());
        assert!(
            validate_checked_event_shapes(&[
                CheckedExecutionEvent::Statement(theorem.clone()),
                CheckedExecutionEvent::Context(PureFactContext::new()),
                CheckedExecutionEvent::Call(valid),
            ])
            .is_ok()
        );

        let unrelated = before.memory().clone().with_call_memory_havoc(
            crate::kernel::Variable(701),
            std::slice::from_ref(&range),
            &assumptions,
            None,
        );
        let unrelated = CheckedCallEvent::new(crate::kernel::intern_c_memory(unrelated));
        assert_eq!(
            validate_checked_event_shapes(&[
                CheckedExecutionEvent::Statement(theorem),
                CheckedExecutionEvent::Context(PureFactContext::new()),
                CheckedExecutionEvent::Call(unrelated),
            ]),
            Err("retained checked-call event is not introduced by its preceding statement")
        );
    }

    #[test]
    fn checked_call_authority_is_path_local_across_forks() {
        let ancestor_view = crate::kernel::intern_c_memory(CMemory::new());
        let sibling_view = crate::kernel::intern_c_memory(
            CMemory::new().with_block_without_derivation("local:sibling", 4),
        );
        let mut ancestor = CheckedCallEvents::default();
        ancestor.new_event(ancestor_view);
        let mut left_arm = ancestor.clone();
        let right_arm = ancestor;
        let left_only = left_arm.new_event(sibling_view.clone());

        assert!(left_arm.contains(&left_only));
        assert!(left_arm.contains_view(&left_only, &sibling_view));
        assert!(
            !right_arm.contains(&left_only),
            "a registry shared for indexing must not make a sibling event active",
        );
    }

    #[test]
    fn checked_call_view_lookup_does_not_scan_unrelated_events() {
        for event_count in [1usize, 64, 1024] {
            let mut events = CheckedCallEvents::new();
            let mut selected = None;
            for index in 0..event_count {
                let view = crate::kernel::intern_c_memory(
                    CMemory::new().with_block_without_derivation(format!("local:call-{index}"), 4),
                );
                let event = events.new_event(view.clone());
                if index + 1 == event_count {
                    selected = Some((event, view));
                }
            }
            let (selected_event, selected_view) = selected.expect("the corpus is nonempty");
            CheckedCallEvents::reset_lookup_candidates_for_test();
            let found = events.events_for_view(&selected_view);
            assert_eq!(found.len(), 1);
            assert!(found[0].same_authority(&selected_event));
            assert_eq!(
                CheckedCallEvents::lookup_candidates_for_test(),
                1,
                "exact-view lookup should visit only its indexed event at size {event_count}",
            );
        }
    }

    #[test]
    fn interface_pointer_congruence_preserves_scope_and_read_obligations() {
        let a = Pointer::symbolic(Variable(95_700));
        let b = Pointer::symbolic(Variable(95_701));
        let c = Pointer::symbolic(Variable(95_702));
        let equal = |a: Pointer, b: Pointer| {
            Proposition::ConditionIs(crate::kernel::ConditionTerm::pointer_equal(a, b), true)
        };
        let parent = ProofFacts::from_ordered(&[equal(a.clone(), b.clone())]);
        let arm = parent.with_fact(equal(b, c.clone()));
        let goal = equal(a.clone(), c.clone());
        assert!(checked_interface_pointer_equality(&arm, &goal));
        assert!(!checked_interface_pointer_equality(&parent, &goal));
        assert!(!checked_interface_pointer_equality(
            &arm,
            &equal(a.offset_by_bytes(8), c.offset_by_bytes(16))
        ));
        assert!(!checked_interface_pointer_equality(
            &arm,
            &Proposition::And(Box::new(goal.clone()), Box::new(goal))
        ));
        assert!(!checked_interface_pointer_equality(
            &arm,
            &Proposition::CMemoryLoadable {
                memory: CMemory::new(),
                base: a,
                bytes: Bitvector32Term::Constant(8),
                wide: false,
            }
        ));
    }

    #[test]
    fn entry_interface_materialization_retains_source_and_does_not_rebind() {
        let caller = CState::new();
        let function = c_function(
            CType::Int32,
            "entry_interface",
            vec![crate::kernel::c_parameter("n", CType::Int32)],
            CStatement::Return(crate::kernel::c_variable("n")),
        );
        let arguments = [CExpression::Value(int32(7))];
        let bound = crate::kernel::c_function_entry_state(&caller, &function, &arguments).unwrap();
        let mut core = ExecutionProofCore::at_entry(caller.clone(), ExecutionFrontier::default());
        assert!(core.materialize_function_entry().is_err());
        core.record_checked_function_entry(&function, &arguments, &bound, PureFactContext::new())
            .unwrap();
        let mut unrelated = core.clone();
        unrelated.evidence_state = Some(CState::new().with_local("different", int32(1)));
        assert!(unrelated.materialize_function_entry().is_err());
        core.materialize_function_entry().unwrap();
        assert_eq!(&*core.state, &bound);
        assert_eq!(core.reached_state(), &bound);
        assert_eq!(core.current_source(&function), Some(function.body()));
        assert_eq!(core.frontier.execution_start_state.as_ref(), Some(&caller));
        assert!(core.frontier.is_at_function_entry());
        core.materialize_function_entry().unwrap();
        assert_eq!(&*core.state, &bound);
        assert_eq!(core.reached_state(), &bound);
        assert!(core.execution_evidence.iter().all(|trace| trace.is_empty()));
    }

    #[test]
    fn checked_entry_accepts_only_body_annotations_with_identical_entry_metadata() {
        let returned = CStatement::Return(CExpression::Value(CValue::Void));
        let condition = CExpression::Value(int32(1));
        let function = c_function(
            CType::Void,
            "entry_annotations",
            Vec::new(),
            crate::kernel::api::c_while(condition.clone(), Vec::new(), returned.clone()),
        );
        let caller = CState::new();
        let state = crate::kernel::c_function_entry_state(&caller, &function, &[]).unwrap();
        let entry =
            CheckedFunctionEntry::check(&caller, &function, &[], &state, PureFactContext::new())
                .unwrap();
        let annotated = function.clone().with_body(crate::kernel::api::c_while(
            condition.clone(),
            vec![Proposition::ConditionIs(
                crate::kernel::ConditionTerm::Constant(true),
                true,
            )],
            returned.clone(),
        ));
        assert_ne!(annotated, function);
        assert_eq!(entry.trace_entry_state(&annotated, &[]), Some(&state));
        assert!(
            entry
                .trace_entry_state(&annotated, std::slice::from_ref(&condition))
                .is_none()
        );
        for changed in [
            annotated.clone().with_source_body(returned),
            annotated
                .clone()
                .with_recursion_measure(crate::kernel::CRankingComponent::CExpression(condition)),
            annotated.with_global_variables(vec![crate::kernel::CGlobal::new(
                "g",
                CType::Int32,
                int32(7),
            )]),
        ] {
            assert!(entry.trace_entry_state(&changed, &[]).is_none());
        }
    }

    #[test]
    fn checked_function_entry_rebase_rejects_semantic_memory_and_population_changes() {
        let function = c_function(
            CType::Void,
            "checked_entry",
            Vec::new(),
            CStatement::Return(CExpression::Value(CValue::Void)),
        )
        .with_composite_resource_definitions(vec![
            CCompositeResourceDefinition::authority_control(
                "item",
                Vec::new(),
                None,
                Vec::new(),
                Vec::new(),
            ),
        ]);
        let pointer = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let caller = CState::new()
            .with_memory(
                CMemory::new().store(pointer.clone(), CValue::Int32(Bitvector32Term::Constant(1))),
            )
            .with_observed_population_family("item");
        let entry_state = crate::kernel::c_function_entry_state(&caller, &function, &[])
            .expect("the empty argument list should bind");
        let checked = CheckedFunctionEntry::check(
            &caller,
            &function,
            &[],
            &entry_state,
            PureFactContext::new(),
        )
        .expect("the exact kernel-computed entry should check");
        let assumptions = PureFactContext::new();

        assert_eq!(
            checked.entry_state_for(&caller, &function, &[], &assumptions),
            Some(entry_state)
        );

        let changed_memory = caller.clone().with_memory(
            CMemory::new().store(pointer, CValue::Int32(Bitvector32Term::Constant(2))),
        );
        assert!(
            checked
                .entry_state_for(&changed_memory, &function, &[], &assumptions)
                .is_none(),
            "a resource rebase must not authorize a changed C memory value"
        );

        let changed_population = caller.with_observed_population_family("other");
        assert!(
            checked
                .entry_state_for(&changed_population, &function, &[], &assumptions)
                .is_none(),
            "a resource rebase must not authorize a changed population observation"
        );
    }

    #[test]
    fn resource_read_evidence_pins_range_lifetime_and_completed_goal() {
        let pointer = Pointer {
            block: "region".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = CMemory::new().with_block("region", 8);
        let written = memory.clone().store(pointer.clone(), int32(7));
        let read = |memory: CMemory, base: Pointer, bytes| Proposition::CMemoryLoadable {
            memory,
            base,
            bytes,
            wide: false,
        };
        let source = read(
            memory.clone(),
            pointer.clone(),
            Bitvector32Term::Constant(4),
        );
        let goal = read(written, pointer.clone(), Bitvector32Term::Constant(4));
        let index = ResourceDeltaPremises::new(std::slice::from_ref(&source));
        let mut retained = index.prove(&goal).unwrap();
        assert!(retained.matches_completed_goal());
        retained.source = None;
        assert!(!retained.matches_completed_goal());
        retained.source = Some(source.clone());
        assert!(ResourceDeltaPremises::new(&[]).prove(&goal).is_none());
        for wrong in [
            read(
                memory.clone(),
                pointer.clone(),
                Bitvector32Term::Constant(8),
            ),
            read(
                memory.clone(),
                Pointer {
                    block: "other".into(),
                    offset: PointerOffsetTerm::Constant(0),
                },
                Bitvector32Term::Constant(4),
            ),
            read(
                memory.clone().with_block("region", 2),
                pointer.clone(),
                Bitvector32Term::Constant(4),
            ),
            read(
                memory.without_local_block(&pointer.block),
                pointer.clone(),
                Bitvector32Term::Constant(4),
            ),
        ] {
            assert!(index.prove(&wrong).is_none());
            retained.goal = wrong;
            assert!(!retained.matches_completed_goal());
        }
        // External allocations keep their broad block on free: a block-only
        // check would unsoundly transport this read past retirement.
        let external = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let live = CMemory::new()
            .with_heap_allocation_claim(external.clone(), Bitvector32Term::Constant(8))
            .unwrap();
        let freed = live
            .clone()
            .free_heap_block(&external, &PureFactContext::new())
            .unwrap();
        let live_read = read(live, external.clone(), Bitvector32Term::Constant(4));
        let dead_read = read(freed.clone(), external, Bitvector32Term::Constant(4));
        assert!(!resource_read_preserves_range(&live_read, &dead_read));
        assert!(!resource_read_preserves_range(&dead_read, &live_read));
        let survivor = freed.with_block("region", 8);
        let source = read(
            survivor.clone(),
            pointer.clone(),
            Bitvector32Term::Constant(4),
        );
        let target = read(
            survivor.store(pointer.clone(), int32(9)),
            pointer,
            Bitvector32Term::Constant(4),
        );
        assert!(
            ResourceDeltaPremises::new(&[source])
                .prove(&target)
                .unwrap()
                .matches_completed_goal(),
            "shared nonempty retirement metadata still permits writes to a surviving range"
        );
    }

    #[test]
    fn resource_read_alias_retains_only_an_exact_named_equality() {
        let pointer = |i| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(Bitvector32Term::Variable(Variable(i))),
                byte_width: 4,
            },
        };
        let read = |i| Proposition::CMemoryLoadable {
            memory: CMemory::new(),
            base: pointer(i),
            bytes: Bitvector32Term::Constant(4),
            wide: false,
        };
        let source = read(20);
        let goal = read(21);
        let index = ResourceDeltaPremises::new(std::slice::from_ref(&source));
        let equality = resource_delta_pointer_equality(&source, &goal).unwrap();
        let facts = PureFactContext::new().assume_proposition(equality.clone());
        assert!(index.prove(&goal).is_none());
        let mut retained = index.prove_with_facts(&goal, &facts).unwrap();
        assert!(retained.matches_completed_goal());
        assert!(retained.equality.as_ref() == Some(&equality));
        retained.equality = None;
        assert!(!retained.matches_completed_goal());
        assert!(!resource_delta_uses_exact_equality(
            &source,
            &equality,
            &read(22)
        ));
        assert!(
            ResourceDeltaPremises::new(&[source.clone(), read(22)])
                .prove_with_facts(&goal, &facts)
                .is_none(),
            "ambiguous body reads must not launch pair search"
        );
        // Duplicate exact ranges are interchangeable, not ambiguity.
        assert!(
            ResourceDeltaPremises::new(&[source.clone(), source])
                .prove_with_facts(&goal, &facts)
                .is_some()
        );
        let contains = |i, end| Proposition::CResourceContains {
            parent: Box::new(
                CResourceFact::own_composite("cell".into(), Vec::new())
                    .resource()
                    .clone(),
            ),
            child: Box::new(CResource::Memory(crate::kernel::CMemoryRange::new(
                pointer(i),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(end),
            ))),
        };
        let relation_index = ResourceDeltaPremises::new(&[contains(20, 1)]);
        assert!(relation_index.prove(&contains(21, 1)).is_none());
        assert!(
            relation_index
                .prove_with_facts(&contains(21, 1), &facts)
                .unwrap()
                .matches_completed_goal()
        );
        assert!(
            relation_index
                .prove_with_facts(&contains(21, 2), &facts)
                .is_none()
        );
        let wrong_parent = Proposition::CResourceContains {
            parent: Box::new(
                CResourceFact::own_composite("other".into(), Vec::new())
                    .resource()
                    .clone(),
            ),
            child: Box::new(CResource::Memory(crate::kernel::CMemoryRange::new(
                pointer(21),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            ))),
        };
        assert!(
            relation_index
                .prove_with_facts(&wrong_parent, &facts)
                .is_none()
        );
        let samples = [16, 32, 64, 128].map(|size| {
            let mut context = facts.clone();
            for i in 0..size {
                context = context.assume_proposition(Proposition::Predicate {
                    name: format!("unrelated_{i}"),
                    arguments: vec![],
                });
            }
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                assert!(
                    index
                        .prove_with_facts(&goal, &context)
                        .unwrap()
                        .matches_completed_goal()
                );
                assert!(
                    relation_index
                        .prove_with_facts(&contains(21, 1), &context)
                        .unwrap()
                        .matches_completed_goal()
                );
            });
            work
        });
        assert!(
            samples.windows(2).all(|pair| pair[1] <= pair[0] + 8),
            "exact alias evidence inspected unrelated premises: {samples:?}"
        );
    }

    #[test]
    fn resource_read_evidence_scales_with_explicit_premises_not_memory_contents() {
        let pointer = Pointer {
            block: "selected".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let mut samples = Vec::new();
        for size in [16, 32, 64, 128] {
            let mut memory = CMemory::new().with_block("selected", 8);
            for i in 0..size {
                memory = memory.with_block(format!("unrelated_{i}"), 8);
            }
            let source = Proposition::CMemoryLoadable {
                memory: memory.clone(),
                base: pointer.clone(),
                bytes: Bitvector32Term::Variable(Variable(42)),
                wide: false,
            };
            let goal = Proposition::CMemoryLoadable {
                memory: memory.store(pointer.clone(), int32(7)),
                base: pointer.clone(),
                bytes: Bitvector32Term::Variable(Variable(42)),
                wide: false,
            };
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let index = ResourceDeltaPremises::new(std::slice::from_ref(&source));
                assert!(index.prove(&goal).unwrap().matches_completed_goal());
            });
            samples.push(work);
        }
        assert!(samples.iter().all(|work| *work > 0));
        assert!(
            samples.windows(2).all(|pair| pair[1] <= pair[0] + 8),
            "read transport inspected unrelated memory: {samples:?}"
        );
        let samples = [16, 32, 64, 128].map(|size| {
            let allowed = (0..size)
                .map(|i| Proposition::CMemoryLoadable {
                    memory: CMemory::new(),
                    base: Pointer {
                        block: format!("range_{i}").into(),
                        offset: PointerOffsetTerm::Constant(0),
                    },
                    bytes: Bitvector32Term::Constant(4),
                    wide: false,
                })
                .collect::<Vec<_>>();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let index = ResourceDeltaPremises::new(&allowed);
                for goal in &allowed {
                    assert!(index.prove(goal).unwrap().matches_completed_goal());
                }
            });
            work
        });
        assert!(
            samples.windows(2).all(|pair| pair[1] <= pair[0] * 2 + 16),
            "explicit read premise index: {samples:?}"
        );
    }

    #[test]
    fn checked_composite_events_reject_forged_resources_facts_memory_and_definitions() {
        let child_spec = CResourceSpec::token(
            CResourceAccessMode::Own,
            "child".to_string(),
            Vec::new(),
            Vec::new(),
        );
        let definition = CCompositeResourceDefinition::new(
            "bundle",
            Vec::new(),
            None,
            false,
            vec![child_spec],
            Vec::new(),
        );
        let function = c_function(
            CType::Void,
            "resource_events",
            Vec::new(),
            CStatement::Return(CExpression::Value(CValue::Void)),
        )
        .with_composite_resource_definitions(vec![definition.clone()]);
        let selected = CResourceFact::own_composite("bundle".to_string(), Vec::new());
        let child = CResourceFact::own_token("child".to_string(), Vec::new());
        let child_view = CResourceFact::view_token("child".to_string(), Vec::new());
        let before = CState::new()
            .with_resource_context(ResourceContext::new().unchecked_with_fact(selected.clone()));
        let facts = ProofFacts::default();

        let observed = before.clone().with_resource_context(
            before
                .resources()
                .clone()
                .unchecked_with_supported_facts(&selected, [child_view.clone()]),
        );
        let observation = CheckedResourceObservation::check(
            &function,
            &before,
            &facts,
            &selected,
            &observed,
            &facts,
            &PersistentOrderedSet::default(),
            &CheckedCallEvents::default(),
        )
        .expect("the exact one-layer child view should check");

        let untracked_observation = before.clone().with_resource_context(
            before
                .resources()
                .clone()
                .unchecked_with_fact(child_view.clone()),
        );
        assert!(
            CheckedResourceObservation::check(
                &function,
                &before,
                &facts,
                &selected,
                &untracked_observation,
                &facts,
                &PersistentOrderedSet::default(),
                &CheckedCallEvents::default(),
            )
            .is_err(),
            "observation evidence must retain the owned support relation"
        );

        let forged_resource = observed.clone().with_resource_context(
            observed
                .resources()
                .clone()
                .unchecked_with_fact(CResourceFact::view_token("forged".to_string(), Vec::new())),
        );
        assert!(
            CheckedResourceObservation::check(
                &function,
                &before,
                &facts,
                &selected,
                &forged_resource,
                &facts,
                &PersistentOrderedSet::default(),
                &CheckedCallEvents::default(),
            )
            .is_err(),
            "observation must not invent an unrelated child view"
        );
        let forged_fact = facts.with_fact(Proposition::ConditionIs(
            crate::kernel::ConditionTerm::Constant(false),
            true,
        ));
        assert!(
            CheckedResourceObservation::check(
                &function,
                &before,
                &facts,
                &selected,
                &observed,
                &forged_fact,
                &PersistentOrderedSet::default(),
                &CheckedCallEvents::default(),
            )
            .is_err(),
            "observation must not invent an unrelated pure fact"
        );
        let pointer = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let changed_memory = observed.clone().with_memory(
            CMemory::new().store(pointer, CValue::Int32(Bitvector32Term::Constant(1))),
        );
        assert!(
            CheckedResourceObservation::check(
                &function,
                &before,
                &facts,
                &selected,
                &changed_memory,
                &facts,
                &PersistentOrderedSet::default(),
                &CheckedCallEvents::default(),
            )
            .is_err(),
            "observation must not change C memory"
        );

        let unfolded = before
            .clone()
            .with_resource_context(ResourceContext::new().unchecked_with_fact(child.clone()));
        CheckedResourceRewrite::check(
            &function,
            &before,
            &facts,
            &selected,
            &unfolded,
            &facts,
            &CheckedCallEvents::default(),
        )
        .expect("the exact folded-to-body representation change should check");
        let variable = Bitvector32Term::Variable(Variable(400));
        let strong = Proposition::ConditionIs(
            crate::kernel::ConditionTerm::signed_greater_than(
                variable.clone(),
                Bitvector32Term::Constant(0),
            ),
            true,
        );
        let weak = Proposition::ConditionIs(
            crate::kernel::ConditionTerm::signed_greater_equal(
                variable,
                Bitvector32Term::Constant(0),
            ),
            true,
        );
        let premise = facts.with_fact(strong);
        let derivable_delta = premise.with_fact(weak.clone());
        assert!(premise.assumptions().proves(&weak));
        assert!(!premise.assumptions().proves_exact(&weak));
        assert!(
            CheckedResourceObservation::check(
                &function,
                &before,
                &premise,
                &selected,
                &observed,
                &derivable_delta,
                &PersistentOrderedSet::default(),
                &CheckedCallEvents::default(),
            )
            .is_err(),
            "observation must not discover an unrecorded implication"
        );
        assert!(
            CheckedResourceRewrite::check(
                &function,
                &before,
                &premise,
                &selected,
                &unfolded,
                &derivable_delta,
                &CheckedCallEvents::default(),
            )
            .is_err(),
            "rewrite must not discover an unrecorded implication"
        );
        let forged_unfold = unfolded.clone().with_resource_context(
            unfolded
                .resources()
                .clone()
                .unchecked_with_fact(CResourceFact::own_token("forged".to_string(), Vec::new())),
        );
        assert!(
            CheckedResourceRewrite::check(
                &function,
                &before,
                &facts,
                &selected,
                &forged_unfold,
                &facts,
                &CheckedCallEvents::default(),
            )
            .is_err(),
            "rewrite must not invent an unrelated owned resource"
        );

        let changed_definition = c_function(
            CType::Void,
            "resource_events",
            Vec::new(),
            CStatement::Return(CExpression::Value(CValue::Void)),
        )
        .with_composite_resource_definitions(vec![CCompositeResourceDefinition::new(
            "bundle",
            Vec::new(),
            None,
            false,
            Vec::new(),
            Vec::new(),
        )]);
        assert!(
            !changed_definition
                .composite_resource_definitions()
                .contains(
                    observation
                        .definition()
                        .expect("legacy body observation has a definition")
                ),
            "a retained observation must remain tied to its checked definition"
        );
    }

    #[test]
    fn interface_abstraction_work_scales_with_unrelated_locals_and_memory() {
        let mut samples = Vec::new();
        for size in [64_u32, 128, 256, 512] {
            let mut memory = CMemory::new();
            let mut then_state = CState::new().with_local("changed", int32(1));
            let mut stable_locals = BTreeMap::new();
            for index in 0..size {
                let name = format!("stable_{index}");
                let value = int32(index);
                then_state = then_state.with_local(name.clone(), value.clone());
                stable_locals.insert(name, value);
                memory = memory.store(
                    Pointer {
                        block: PointerBlock::ExternalArgument,
                        offset: PointerOffsetTerm::Constant(i64::from(index * 4)),
                    },
                    int32(index),
                );
            }
            then_state = then_state.with_memory(memory);
            let else_state = then_state.clone().with_local("changed", int32(2));
            let siblings = [&then_state, &else_state];
            let ((then_join, else_join), work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    (
                        crate::kernel::abstract_c_state_for_interface_join_across(
                            &then_state,
                            &siblings,
                            &stable_locals,
                            0,
                        )
                        .expect("the then arm should abstract"),
                        crate::kernel::abstract_c_state_for_interface_join_across(
                            &else_state,
                            &siblings,
                            &stable_locals,
                            0,
                        )
                        .expect("the else arm should abstract"),
                    )
                });
            assert_eq!(then_join, else_join);
            samples.push((size, work));
        }
        assert!(samples[0].1 > 0);
        for pair in samples.windows(2) {
            assert!(
                pair[1].1 <= pair[0].1 * 3,
                "interface abstraction work grew superlinearly: {samples:?}"
            );
        }
    }

    #[test]
    fn checked_join_effects_require_exact_arm_deltas_and_summarize_alternatives() {
        let before = CState::new();
        let left_pointer = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let right_pointer = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(4),
        };
        let left = before.clone().with_memory(
            before
                .memory()
                .clone()
                .store(left_pointer.clone(), crate::kernel::int64(1)),
        );
        let right = before.clone().with_memory(
            before
                .memory()
                .clone()
                .store(right_pointer.clone(), int32(2)),
        );
        let left_effect = ExecutionPureFact::certified(Proposition::CMemoryMutatesOnly {
            before: before.memory().clone(),
            after: left.memory().clone(),
            writes: vec![(left_pointer.clone(), 8)],
        });
        let right_effect = ExecutionPureFact::certified(Proposition::CMemoryMutatesOnly {
            before: before.memory().clone(),
            after: right.memory().clone(),
            writes: vec![(right_pointer.clone(), 4)],
        });
        let parent = ExecutionProofCore::at_entry(before.clone(), ExecutionFrontier::default());
        let mut left_core = parent.clone();
        left_core.state = left.clone().into();
        left_core.effect_facts.push(left_effect.clone());
        let mut right_core = parent.clone();
        right_core.state = right.clone().into();
        right_core.effect_facts.push(right_effect.clone());

        assert!(!arm_effect_deltas_are_exact(
            &parent,
            [&left_core, &right_core],
            [&[], &[]],
        ));
        let supplied = [
            std::slice::from_ref(&left_effect),
            std::slice::from_ref(&right_effect),
        ];
        assert!(arm_effect_deltas_are_exact(
            &parent,
            [&left_core, &right_core],
            supplied,
        ));

        let joined = crate::kernel::abstract_c_state_for_interface_join_across(
            &left,
            &[&left, &right],
            &BTreeMap::new(),
            0,
        )
        .expect("alternative memories should have one deterministic abstraction")
        .state;
        let facts = ProofFacts::default();
        let summaries = checked_interface_effect_facts(
            &before,
            &joined,
            [&left_core, &right_core],
            [&facts, &facts],
            supplied,
        )
        .expect("the two exact alternative stores should summarize");
        assert!(matches!(
            summaries.to_vec().as_slice(),
            [fact] if matches!(
                fact.proposition(),
                Proposition::CMemoryMutatesOnly { before: effect_before, after, writes }
                    if effect_before == before.memory()
                        && after == joined.memory()
                        && writes == &vec![(left_pointer, 8), (right_pointer, 4)]
            )
        ));
    }

    #[test]
    fn checked_interface_effects_reject_uncertified_memory_effects() {
        let before = CState::new();
        let pointer = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let after = before
            .clone()
            .with_memory(before.memory().clone().store(pointer.clone(), int32(1)));
        let effect = ExecutionPureFact::new(Proposition::CMemoryMutatesOnly {
            before: before.memory().clone(),
            after: after.memory().clone(),
            writes: vec![(pointer, 4)],
        });
        let parent = ExecutionProofCore::at_entry(before.clone(), ExecutionFrontier::default());
        let mut changed_core = parent.clone();
        changed_core.state = after.clone().into();
        changed_core.effect_facts.push(effect.clone());

        assert_eq!(
            checked_interface_effect_facts(
                &before,
                &after,
                [&changed_core, &parent],
                [&ProofFacts::default(), &ProofFacts::default()],
                [std::slice::from_ref(&effect), &[]],
            ),
            Err("an interface arm contains an uncertified memory effect")
        );
    }

    #[test]
    fn checked_interface_effects_require_memory_diff_coverage() {
        let before = CState::new();
        let changed_pointer = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(4),
        };
        let declared_pointer = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let after = before.clone().with_memory(
            before
                .memory()
                .clone()
                .store(changed_pointer.clone(), int32(1)),
        );
        let parent = ExecutionProofCore::at_entry(before.clone(), ExecutionFrontier::default());

        let mutation = ExecutionPureFact::certified(Proposition::CMemoryMutatesOnly {
            before: before.memory().clone(),
            after: after.memory().clone(),
            writes: vec![(declared_pointer.clone(), 4)],
        });
        let mut mutation_core = parent.clone();
        mutation_core.state = after.clone().into();
        mutation_core.effect_facts.push(mutation.clone());
        assert_eq!(
            checked_interface_effect_facts(
                &before,
                &after,
                [&mutation_core, &parent],
                [&ProofFacts::default(), &ProofFacts::default()],
                [std::slice::from_ref(&mutation), &[]],
            ),
            Err("an interface arm memory effect does not cover its memory diff")
        );

        let summary = ExecutionPureFact::certified(Proposition::CMemoryEffectSummary {
            before: before.memory().clone(),
            after: after.memory().clone(),
            mutable_ranges: vec![CMemoryRange::new(
                declared_pointer.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )],
        });
        let mut summary_core = parent.clone();
        summary_core.state = after.clone().into();
        summary_core.effect_facts.push(summary.clone());
        assert_eq!(
            checked_interface_effect_facts(
                &before,
                &after,
                [&summary_core, &parent],
                [&ProofFacts::default(), &ProofFacts::default()],
                [std::slice::from_ref(&summary), &[]],
            ),
            Err("an interface arm memory effect does not cover its memory diff")
        );

        let erased_before =
            CState::new().with_memory(CMemory::new().store(changed_pointer.clone(), int32(1)));
        let erased_after = erased_before.clone().with_memory(
            erased_before
                .memory()
                .clone()
                .without_cell(&changed_pointer),
        );
        let erased_parent =
            ExecutionProofCore::at_entry(erased_before.clone(), ExecutionFrontier::default());
        let erased_summary = ExecutionPureFact::certified(Proposition::CMemoryEffectSummary {
            before: erased_before.memory().clone(),
            after: erased_after.memory().clone(),
            mutable_ranges: vec![CMemoryRange::new(
                declared_pointer.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )],
        });
        let mut erased_core = erased_parent.clone();
        erased_core.state = erased_after.clone().into();
        erased_core.effect_facts.push(erased_summary.clone());
        assert_eq!(
            checked_interface_effect_facts(
                &erased_before,
                &erased_after,
                [&erased_core, &erased_parent],
                [&ProofFacts::default(), &ProofFacts::default()],
                [std::slice::from_ref(&erased_summary), &[]],
            ),
            Err("an interface arm memory effect does not cover its memory diff")
        );
    }

    #[test]
    fn conditional_heap_free_is_checked_as_a_guarded_lifetime_join() {
        let allocation_base = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let before = CState::new().with_memory(
            CMemory::new()
                .with_heap_allocation_claim(allocation_base.clone(), 16)
                .expect("the allocation claim should be fresh"),
        );
        let freed = before.clone().with_memory(
            before
                .memory()
                .clone()
                .free_heap_block(&allocation_base, &PureFactContext::new())
                .expect("the freed arm should retire the allocation"),
        );
        let retained = before.clone();
        let parent = ExecutionProofCore::at_entry(before.clone(), ExecutionFrontier::default());
        let free_effect = ExecutionPureFact::certified(Proposition::CHeapAllocationFreed {
            before: before.memory().clone(),
            after: freed.memory().clone(),
            allocation_base: allocation_base.clone(),
            bytes: Bitvector32Term::Constant(16),
        });
        let mut freed_core = parent.clone();
        freed_core.state = freed.clone().into();
        freed_core.effect_facts.push(free_effect.clone());
        let retained_core = parent.clone();
        let siblings = [&freed, &retained];
        let joined = crate::kernel::abstract_c_state_for_interface_join_across(
            &freed,
            &siblings,
            &BTreeMap::new(),
            0,
        )
        .expect("the conditional heap states should abstract")
        .state;
        let facts = ProofFacts::default();
        let summaries = checked_interface_effect_facts(
            &before,
            &joined,
            [&freed_core, &retained_core],
            [&facts, &facts],
            [std::slice::from_ref(&free_effect), &[]],
        )
        .expect("a conditional free should be checked at the branch boundary");
        assert!(summaries.is_empty());

        let function = c_function(
            CType::Void,
            "conditional_heap_free",
            Vec::new(),
            CStatement::Return(CExpression::Value(CValue::Void)),
        );
        let free_facts = [
            Vec::new(),
            vec![CResourceFact::own_allocation(allocation_base.clone(), 16)],
        ];
        let states = [&freed, &retained];
        assert!(interface_resources_guard_heap_frees(
            &function,
            &free_facts,
            states,
            [&facts, &facts],
            &conditional_heap_frees([std::slice::from_ref(&free_effect), &[],]),
        ));
        assert!(!interface_resources_guard_heap_frees(
            &function,
            &[Vec::new(), Vec::new()],
            states,
            [&facts, &facts],
            &conditional_heap_frees([std::slice::from_ref(&free_effect), &[],]),
        ));
    }

    #[test]
    fn ground_comparison_premises_check_signed_literals_and_both_polarities() {
        use crate::kernel::ConditionTerm;
        for left in [i32::MIN, -1, 0, 1, i32::MAX] {
            for right in [i32::MIN, -1, 0, 1, i32::MAX] {
                let l = Box::new(Bitvector32Term::Constant(left as u32));
                let r = Box::new(Bitvector32Term::Constant(right as u32));
                for (condition, actual) in [
                    (
                        ConditionTerm::Bitvector32SignedLessThan(l.clone(), r.clone()),
                        left < right,
                    ),
                    (
                        ConditionTerm::Bitvector32SignedLessEqual(l.clone(), r.clone()),
                        left <= right,
                    ),
                    (
                        ConditionTerm::Bitvector32SignedGreaterThan(l.clone(), r.clone()),
                        left > right,
                    ),
                    (
                        ConditionTerm::Bitvector32SignedGreaterEqual(l.clone(), r.clone()),
                        left >= right,
                    ),
                    (
                        ConditionTerm::Bitvector32Equal(l.clone(), r.clone()),
                        left == right,
                    ),
                ] {
                    assert!(ground_comparison_premise_holds(&Proposition::ConditionIs(
                        condition.clone(),
                        actual
                    )));
                    assert!(!ground_comparison_premise_holds(&Proposition::ConditionIs(
                        condition, !actual
                    )));
                }
            }
        }
        // Literal sums canonicalize when constructed; a symbolic operand
        // keeps this an actual compound term at the checking boundary.
        let symbolic_expression = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::Add(
                    Box::new(Bitvector32Term::Variable(crate::kernel::Variable(990))),
                    Box::new(Bitvector32Term::Constant(1)),
                )),
                Box::new(Bitvector32Term::Constant(1)),
            ),
            true,
        );
        assert!(!ground_comparison_premise_holds(&symbolic_expression));
    }

    #[test]
    fn checked_event_premises_require_exact_facts_or_ground_comparisons() {
        use crate::kernel::{ConditionTerm, Variable};
        let theorem = |premise| {
            Theorem::new(Proposition::Implies(
                Box::new(premise),
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::Constant(true),
                    true,
                )),
            ))
        };
        let required = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedGreaterEqual(
                Box::new(Bitvector32Term::Variable(Variable(991))),
                Box::new(Bitvector32Term::Constant(0)),
            ),
            true,
        );
        let stronger = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedGreaterThan(
                Box::new(Bitvector32Term::Variable(Variable(991))),
                Box::new(Bitvector32Term::Constant(0)),
            ),
            true,
        );
        let empty = ProofFacts::default();
        assert!(!checked_evidence_premises_hold(
            &theorem(required.clone()),
            &empty
        ));
        assert!(checked_evidence_premises_hold(
            &theorem(required.clone()),
            &empty.with_fact(required.clone())
        ));
        let derived = empty.with_fact(stronger);
        assert!(
            derived.assumptions().proves(&required),
            "the retired fallback would find this proof"
        );
        assert!(!checked_evidence_premises_hold(
            &theorem(required.clone()),
            &derived
        ));
        let unrelated = empty.with_fact(Proposition::ConditionIs(
            ConditionTerm::Variable(Variable(992)),
            true,
        ));
        assert!(!checked_evidence_premises_hold(
            &theorem(required),
            &unrelated
        ));
        for (left, right, accepted) in [(1, 1, true), (0, 1, false)] {
            let premise = Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedGreaterEqual(
                    Box::new(Bitvector32Term::Constant(left)),
                    Box::new(Bitvector32Term::Constant(right)),
                ),
                true,
            );
            assert_eq!(
                checked_evidence_premises_hold(&theorem(premise), &empty),
                accepted
            );
        }
    }

    #[test]
    fn checked_condition_evidence_preserves_the_tail_for_empty_if_arms() {
        let state = CState::new();
        let condition = CExpression::Variable("x".to_string());
        let branch = CStatement::If {
            condition: condition.clone(),
            then_branch: Box::new(CStatement::Skip),
            else_branch: Box::new(CStatement::Skip),
        };
        let tail = CStatement::Return(CExpression::Variable("x".to_string()));
        let source = prepend_checked_evidence_statement(branch, Some(tail.clone()));

        for value in [true, false] {
            let progress = check_evidence_events(
                &[condition_event(&state, &condition, value)],
                &ProofFacts::default(),
                state.clone(),
                Some(source.clone()),
            )
            .expect("a checked empty arm should advance directly to the shared tail");
            assert_eq!(progress.state, state);
            assert_eq!(progress.remaining, Some(tail.clone()));
            assert!(progress.completed.is_none());
        }
    }

    #[test]
    fn checked_condition_evidence_rejects_a_different_source_condition() {
        let state = CState::new();
        let source_condition = CExpression::Variable("x".to_string());
        let theorem_condition = CExpression::Variable("y".to_string());
        let source = CStatement::If {
            condition: source_condition,
            then_branch: Box::new(CStatement::Skip),
            else_branch: Box::new(CStatement::Skip),
        };
        assert!(
            check_evidence_events(
                &[condition_event(&state, &theorem_condition, true)],
                &ProofFacts::default(),
                state,
                Some(source),
            )
            .is_none()
        );
    }

    #[test]
    fn a_summarized_loop_matches_only_a_less_annotated_source_loop() {
        fn loop_statement(invariant: Vec<Proposition>, body: CStatement) -> CStatement {
            CStatement::While {
                condition: CExpression::Variable("c".to_string()),
                invariant,
                invariant_checks: Vec::new(),
                effect_checks: Vec::new(),
                resource_specs: Vec::new(),
                ranking_measures: Vec::new(),
                structural_measure: None,
                do_while: false,
                backedge_target: None,
                natural_exit_target: None,
                body: Box::new(body),
            }
        }
        let clause = Proposition::ConditionIs(
            crate::kernel::ConditionTerm::Bitvector32SignedGreaterEqual(
                Box::new(Bitvector32Term::Constant(0)),
                Box::new(Bitvector32Term::Constant(0)),
            ),
            true,
        );
        let body = CStatement::Skip;
        let bare = loop_statement(Vec::new(), body.clone());
        let annotated = loop_statement(vec![clause], body.clone());

        // The `loop { ... }` tactic's own clauses may be added to a source
        // loop that carries none: the C program is the same and the theorem
        // discharged more.
        assert!(checked_source_statement_matches(&annotated, &bare));
        assert!(checked_source_statement_matches(&bare, &bare));
        assert!(checked_source_statement_matches(&annotated, &annotated));
        // The reverse would drop an obligation the source asked for.
        assert!(!checked_source_statement_matches(&bare, &annotated));
        // The C itself is still exact.
        assert!(!checked_source_statement_matches(
            &loop_statement(Vec::new(), CStatement::Break),
            &bare
        ));
        let mut other_condition = bare.clone();
        if let CStatement::While { condition, .. } = &mut other_condition {
            *condition = CExpression::Variable("d".to_string());
        }
        assert!(!checked_source_statement_matches(&other_condition, &bare));
        let mut do_while = bare.clone();
        if let CStatement::While { do_while: flag, .. } = &mut do_while {
            *flag = true;
        }
        assert!(!checked_source_statement_matches(&do_while, &bare));
        // Only loops have proof clauses; nothing else relaxes.
        assert!(!checked_source_statement_matches(
            &CStatement::Skip,
            &CStatement::Break
        ));
    }

    #[test]
    fn checked_branch_join_accepts_empty_arms_only_at_the_artifact_tail() {
        let function = c_function(
            CType::Void,
            "branch",
            Vec::new(),
            CStatement::Return(CExpression::Value(CValue::Void)),
        );
        let state = CState::new();
        let condition = CExpression::Variable("x".to_string());
        let branch_statement = CStatement::If {
            condition: condition.clone(),
            then_branch: Box::new(CStatement::Skip),
            else_branch: Box::new(CStatement::Skip),
        };
        let continuation = Some(CStatement::Return(CExpression::Variable("x".to_string())));
        let then_theorem = match condition_event(&state, &condition, true) {
            CheckedExecutionEvent::Condition(theorem) => theorem,
            _ => unreachable!(),
        };
        let else_theorem = match condition_event(&state, &condition, false) {
            CheckedExecutionEvent::Condition(theorem) => theorem,
            _ => unreachable!(),
        };
        let root_facts = ProofFacts::default();
        let split = CheckedBranchSplit {
            state: state.clone(),
            branch_statement,
            continuation,
            condition,
            root_facts: root_facts.clone(),
            paths: vec![
                CheckedBranchPath {
                    outcome: CConditionOutcome::Value(true),
                    facts: Vec::new().into(),
                    obligations: Vec::new(),
                    theorem: then_theorem.clone(),
                },
                CheckedBranchPath {
                    outcome: CConditionOutcome::Value(false),
                    facts: Vec::new().into(),
                    obligations: Vec::new(),
                    theorem: else_theorem.clone(),
                },
            ],
        };
        let parent = ExecutionProofCore::at_entry(state.clone(), ExecutionFrontier::default());
        let at_branch = FrontierPosition::StatementEntry {
            remaining: Arc::new(crate::kernel::c_seq(
                split.branch_statement.clone(),
                split.continuation.clone().expect("a continuation"),
            )),
        };
        let mut then_arm = parent.clone();
        then_arm.frontier.position = at_branch.clone();
        then_arm
            .record_condition_transition(
                &function,
                &[],
                then_theorem.clone(),
                PureFactContext::new(),
                &[],
                &[],
            )
            .expect("the then condition decides the frontier's `if`");
        then_arm.frontier.region = ExecutionRegionKind::BranchArm;
        then_arm.frontier.position = FrontierPosition::RegionBoundary;
        let mut else_arm = parent.clone();
        else_arm.frontier.position = at_branch;
        else_arm
            .record_condition_transition(
                &function,
                &[],
                else_theorem.clone(),
                PureFactContext::new(),
                &[],
                &[],
            )
            .expect("the else condition decides the frontier's `if`");
        else_arm.frontier.region = ExecutionRegionKind::BranchArm;
        else_arm.frontier.position = FrontierPosition::RegionBoundary;

        let checked = CheckedExecutionBranch::check(
            split.clone(),
            &root_facts,
            [&then_theorem, &else_theorem],
            [&root_facts, &root_facts],
            &parent,
            [&then_arm, &else_arm],
            &function,
            &[],
            [&[], &[]],
        )
        .expect("the exact empty arms should join at the retained continuation");
        assert_eq!(checked.joined_state(), &state);
        // Each empty arm records its condition theorem and the context it
        // was proved under.
        assert_eq!(checked.arm_events(0).len(), 2);
        assert_eq!(checked.arm_events(1).len(), 2);

        assert!(
            CheckedExecutionBranch::check(
                split,
                &root_facts,
                [&else_theorem, &then_theorem],
                [&root_facts, &root_facts],
                &parent,
                [&then_arm, &else_arm],
                &function,
                &[],
                [&[], &[]],
            )
            .is_err(),
            "swapped arm evidence must not certify the source partition"
        );
    }

    #[test]
    fn branch_fact_availability_is_exact_and_independent_of_ambient_history() {
        use crate::kernel::ConditionTerm;
        let x = Bitvector32Term::Variable(Variable(910_000));
        let strong = Proposition::ConditionIs(
            ConditionTerm::signed_greater_than(x.clone(), Bitvector32Term::Constant(0)),
            true,
        );
        let weak = Proposition::ConditionIs(
            ConditionTerm::signed_greater_equal(x.clone(), Bitvector32Term::Constant(0)),
            true,
        );
        let reflexive = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(Box::new(x.clone()), Box::new(x)),
            true,
        );
        let mut samples = Vec::new();
        for size in [16, 32, 64, 128] {
            let mut facts = ProofFacts::default().with_fact(strong.clone());
            for index in 0..size {
                facts = facts.with_fact(Proposition::ConditionIs(
                    ConditionTerm::signed_less_than(
                        Bitvector32Term::Variable(Variable(920_000 + index)),
                        Bitvector32Term::Constant(100),
                    ),
                    true,
                ));
            }
            assert!(
                facts.assumptions().proves(&weak),
                "the old general route could derive this missing fact"
            );
            let exact = facts.with_fact(weak.clone());
            let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
                assert!(!checked_branch_fact_is_available(&facts, &weak));
                assert!(checked_branch_fact_is_available(&exact, &weak));
                assert!(checked_branch_fact_is_available(&facts, &reflexive));
                assert!(!checked_branch_fact_is_available(
                    &facts,
                    &Proposition::Not(Box::new(reflexive.clone()))
                ));
            });
            samples.push(work);
        }
        assert!(samples.iter().all(|work| *work > 0));
        assert!(
            samples.windows(2).all(|pair| pair[1] <= pair[0] * 2),
            "branch availability scanned unrelated history: {samples:?}"
        );
    }

    #[test]
    fn branch_split_obligations_require_evidence_on_each_named_arm() {
        use crate::kernel::{ConditionTerm, ProofObligation};
        let state = CState::new();
        let condition = CExpression::Value(int32(1));
        let x = Bitvector32Term::Variable(Variable(930_000));
        let strong = Proposition::ConditionIs(
            ConditionTerm::signed_greater_than(x.clone(), Bitvector32Term::Constant(0)),
            true,
        );
        let required = Proposition::ConditionIs(
            ConditionTerm::signed_greater_equal(x, Bitvector32Term::Constant(0)),
            true,
        );
        let root = ProofFacts::default().with_fact(strong);
        let theorems =
            [true, false].map(|value| match condition_event(&state, &condition, value) {
                CheckedExecutionEvent::Condition(theorem) => theorem,
                _ => unreachable!(),
            });
        let split = CheckedBranchSplit {
            state: state.clone(),
            branch_statement: CStatement::If {
                condition: condition.clone(),
                then_branch: Box::new(CStatement::Skip),
                else_branch: Box::new(CStatement::Skip),
            },
            continuation: None,
            condition: condition.clone(),
            root_facts: root.clone(),
            paths: [true, false]
                .into_iter()
                .enumerate()
                .map(|(index, value)| CheckedBranchPath {
                    outcome: CConditionOutcome::Value(value),
                    facts: Vec::new().into(),
                    obligations: vec![ProofObligation::new(required.clone())],
                    theorem: theorems[index].clone(),
                })
                .collect(),
        };
        let exact = root.with_fact(required);
        let validate = |arms| {
            split.validates_exhaustive_join(
                &state,
                &condition,
                &root,
                [Some(&theorems[0]), Some(&theorems[1])],
                arms,
            )
        };
        assert!(
            !validate([Some(&root), Some(&root)]),
            "general derivability is not retained evidence"
        );
        assert!(
            !validate([Some(&exact), Some(&root)]),
            "then evidence cannot discharge the else obligation"
        );
        assert!(
            !validate([Some(&root), Some(&exact)]),
            "else evidence cannot discharge the then obligation"
        );
        assert!(validate([Some(&exact), Some(&exact)]));
        assert!(
            !validate([Some(&exact), None]),
            "an omitted arm is not exhaustive"
        );
        let unrelated = ProofFacts::default().with_fact(Proposition::ConditionIs(
            ConditionTerm::Constant(true),
            true,
        ));
        assert!(
            !validate([Some(&exact), Some(&unrelated)]),
            "evidence must descend from this split root"
        );
    }

    // Interface re-lowering must use the checked arm's address aliases without
    // acquiring read authority, leaking an arm fact, or scanning its history.
    #[test]
    fn interface_aliased_wide_read_preserves_scope_history_and_scales() {
        use crate::kernel::{CPointerValue, ConditionTerm, SpecMemory};
        let _session = crate::kernel::VerificationSession::enter();
        let owner = Pointer::symbolic(Variable(951_000));
        let alias = Pointer::symbolic(Variable(951_001));
        let value = Bitvector32Term::UInt64Constant(0x1234_5678_9abc_def0);
        let load = SpecExpression::MemoryLoad {
            memory: SpecMemory::Current,
            pointer: Box::new(SpecExpression::Value(CValue::Pointer(CPointerValue::new(
                alias.clone(),
                CType::UInt64Pointer,
            )))),
            value_type: CType::UInt64,
        };
        let spec = SpecProposition::Comparison {
            left: load.clone(),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::Value(CValue::UInt64(value.clone())),
        };
        let mut previous = None;
        for count in [16_u32, 64, 256, 1024] {
            let mut memory = CMemory::new();
            let mut parent = ProofFacts::default();
            for index in 0..count {
                memory = memory.store(owner.offset_by_bytes((index + 1) * 8), int32(index));
                parent = parent.with_fact(Proposition::ConditionIs(
                    ConditionTerm::equal(
                        Bitvector32Term::Variable(Variable(952_000 + u64::from(index))),
                        Bitvector32Term::Constant(index),
                    ),
                    true,
                ));
            }
            memory = memory.store(owner.clone(), CValue::UInt64(value.clone()));
            let state = CState::new().with_memory(memory.clone());
            let arm = parent.with_fact(Proposition::ConditionIs(
                ConditionTerm::pointer_equal(alias.clone(), owner.clone()),
                true,
            ));
            let check = |state: &CState, facts: &ProofFacts, spec: &SpecProposition| {
                CheckedInterfaceLowering::check(
                    spec,
                    state,
                    state,
                    facts,
                    &InterfaceReadPremises::default(),
                )
            };
            let (checked, work) =
                crate::instrumentation::measure_deterministic_work(|| check(&state, &arm, &spec));
            assert!(checked.is_some(), "{count} unrelated cells and premises");
            assert!(checked.unwrap().has_complete_proof());
            if let Some(previous) = previous {
                assert!(work <= previous + 128, "{count}: {work} after {previous}");
            }
            previous = Some(work);
            assert!(
                check(&state, &parent, &spec).is_none(),
                "alias stays in its arm"
            );
            assert!(
                check(&state, &arm, &SpecProposition::Defined(load.clone())).is_none(),
                "logical value evidence does not authorize a C read"
            );
            for (offset, overwrite) in [
                (0, CValue::UInt64(Bitvector32Term::UInt64Constant(7))),
                (4, int32(7)),
            ] {
                let address = owner.offset_by_bytes(offset);
                let changed = memory
                    .without_possible_aliasing_cells(
                        &address,
                        overwrite.byte_width(),
                        arm.assumptions(),
                    )
                    .store(address, overwrite);
                assert!(
                    check(&state.clone().with_memory(changed), &arm, &spec).is_none(),
                    "a full or partial overwrite invalidates the old value"
                );
            }
        }
    }

    #[test]
    fn interface_logical_read_does_not_establish_validity() {
        use crate::kernel::{CPointerValue, SpecMemory};
        let state = CState::new();
        let pointer = crate::kernel::Pointer {
            block: "interface_cell".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let load = SpecExpression::MemoryLoad {
            memory: SpecMemory::Current,
            pointer: Box::new(SpecExpression::Value(CValue::Pointer(CPointerValue::new(
                pointer,
                CType::Int32Pointer,
            )))),
            value_type: CType::Int32,
        };
        let spec = SpecProposition::Comparison {
            left: load.clone(),
            operator: CComparisonOperator::Equal,
            right: load.clone(),
        };
        let path = interface_spec_paths(&spec, &state, &state, &PureFactContext::new())
            .unwrap()
            .remove(0);
        assert!(path.facts.is_empty());
        assert!(path.obligations.is_empty());
        let mut facts = ProofFacts::default().with_fact(path.proposition.clone());
        for fact in &path.facts {
            facts = facts.with_fact(fact.proposition().clone());
        }
        assert!(
            CheckedInterfaceLowering::check(
                &SpecProposition::Defined(load),
                &state,
                &state,
                &facts,
                &InterfaceReadPremises::default(),
            )
            .is_none(),
            "logical reflexivity grants no read validity"
        );
        for obligation in &path.obligations {
            facts = facts.with_fact(obligation.proposition().clone());
        }
        let checked = CheckedInterfaceLowering::check(
            &spec,
            &state,
            &state,
            &facts,
            &InterfaceReadPremises::default(),
        )
        .unwrap();
        assert_eq!(checked.path.as_ref(), &path);
        assert!(checked.has_complete_proof());
        assert_eq!(
            checked.proofs.len(),
            1 + path.facts.len() + path.obligations.len()
        );
        assert!(checked.facts.shares_premises_with(&facts));
        assert_eq!(checked.snapshot, state);
        assert_eq!(checked.reference, state);
        assert_eq!(checked.spec.as_ref(), &spec);
        let copy = checked.clone();
        assert!(Arc::ptr_eq(&copy.path, &checked.path));
        assert!(Arc::ptr_eq(&copy.spec, &checked.spec));
        assert!(Arc::ptr_eq(&copy.proofs, &checked.proofs));
        let mut incomplete = checked.clone();
        incomplete.proofs = Arc::new(checked.proofs[..checked.proofs.len() - 1].to_vec());
        assert!(!incomplete.has_complete_proof());
    }

    #[test]
    fn interface_assertion_requires_an_available_proof_not_derivability() {
        use crate::kernel::ConditionTerm;
        let term = Bitvector32Term::Variable(Variable(949_000));
        let state = CState::new().with_local("x", CValue::Int32(term.clone()));
        let spec = SpecProposition::Comparison {
            left: SpecExpression::CExpression(CExpression::Variable("x".into())),
            operator: CComparisonOperator::GreaterEqual,
            right: SpecExpression::Value(int32(0)),
        };
        let goal = Proposition::ConditionIs(
            ConditionTerm::signed_greater_equal(term.clone(), Bitvector32Term::Constant(0)),
            true,
        );
        let facts = ProofFacts::default().with_fact(Proposition::ConditionIs(
            ConditionTerm::signed_greater_than(term, Bitvector32Term::Constant(0)),
            true,
        ));
        assert!(
            facts.assumptions().proves(&goal),
            "the removed contextual checker could derive this consequence"
        );
        assert!(
            CheckedInterfaceLowering::check(
                &spec,
                &state,
                &state,
                &facts,
                &InterfaceReadPremises::default()
            )
            .is_none()
        );
        let established = facts.with_fact(goal);
        assert!(
            CheckedInterfaceLowering::check(
                &spec,
                &state,
                &state,
                &established,
                &InterfaceReadPremises::default()
            )
            .unwrap()
            .has_complete_proof()
        );
    }

    #[test]
    fn interface_load_definition_rejects_wrong_variable_address_and_snapshot() {
        use crate::kernel::{CMemory, ConditionTerm, Pointer};
        let memory = crate::kernel::intern_c_memory(CMemory::new());
        let pointer = Pointer {
            block: "interface_definition".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let variable = crate::kernel::eval::load_variable_for_cell(
            &memory,
            &pointer,
            crate::kernel::LoadKind::Bits32,
        );
        let equation = |variable, memory, pointer| {
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(
                    Box::new(Bitvector32Term::Variable(variable)),
                    Box::new(Bitvector32Term::MemoryLoad(
                        memory,
                        Box::new(pointer),
                        crate::kernel::LoadKind::Bits32,
                    )),
                ),
                true,
            )
        };
        let correct = equation(variable, memory.clone(), pointer.clone());
        let definition = CheckedInterfaceLoadDefinition::check(&correct).unwrap();
        assert!(definition.matches_goal_exactly(&correct));
        let wrong_variable = equation(Variable(17), memory.clone(), pointer.clone());
        let wrong_address = equation(
            variable,
            memory,
            Pointer {
                block: "other".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
        );
        let wrong_snapshot = equation(
            variable,
            crate::kernel::intern_c_memory(CMemory::new().with_block("different", 4)),
            pointer,
        );
        for wrong in [wrong_variable, wrong_address, wrong_snapshot] {
            assert!(CheckedInterfaceLoadDefinition::check(&wrong).is_none());
            assert!(!definition.matches_goal_exactly(&wrong));
        }
    }

    #[test]
    fn interface_read_premises_are_indexed_and_check_the_exact_range() {
        use crate::kernel::{CMemory, Pointer};
        let memory = CMemory::new();
        let readable = |memory: CMemory, block: String, width| Proposition::CMemoryLoadable {
            memory,
            base: Pointer {
                block: block.into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            bytes: Bitvector32Term::Constant(width),
            wide: false,
        };
        let goal = readable(memory.clone(), "selected".into(), 4);
        let source = readable(memory.clone(), "selected".into(), 8);
        let samples = [16, 32, 64, 128].map(|size| {
            let inputs = (0..size)
                .map(|i| readable(memory.clone(), format!("unrelated_{i}"), 8))
                .chain(std::iter::once(source.clone()))
                .collect::<Vec<_>>();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let index = InterfaceReadPremises::new(inputs);
                let selected = index.for_goal(&goal).unwrap();
                assert_eq!(selected, &source);
                assert!(interface_read_is_subrange(&goal, selected));
                assert!(!interface_read_is_subrange(
                    &readable(memory.clone(), "selected".into(), 9),
                    selected
                ));
                assert!(!interface_read_is_subrange(
                    &readable(memory.clone(), "other".into(), 4),
                    selected
                ));
                assert!(!interface_read_is_subrange(
                    &readable(CMemory::new().with_block("other", 4), "selected".into(), 4),
                    selected
                ));
            });
            work
        });
        assert!(samples.iter().all(|work| *work > 0));
        assert!(
            samples.windows(2).all(|pair| pair[1] <= pair[0] * 2),
            "explicit resource index scaled superlinearly: {samples:?}"
        );
        assert!(InterfaceReadPremises::default().for_goal(&goal).is_none());
    }

    #[test]
    fn interface_lowering_retention_shares_unrelated_history() {
        let spec = SpecProposition::Comparison {
            left: SpecExpression::Value(int32(1)),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::Value(int32(1)),
        };
        let samples = [16, 32, 64, 128].map(|size| {
            let mut facts = ProofFacts::default();
            let mut state = CState::new();
            for index in 0..size {
                facts = facts.with_fact(Proposition::Predicate {
                    name: format!("unrelated_{index}"),
                    arguments: Vec::new(),
                });
                state = state.with_local(format!("unrelated_{index}"), int32(index));
            }
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let checked = CheckedInterfaceLowering::check(
                    &spec,
                    &state,
                    &state,
                    &facts,
                    &InterfaceReadPremises::default(),
                )
                .unwrap();
                let copy = checked.clone();
                assert!(copy.facts.shares_premises_with(&facts));
                assert_eq!(copy.snapshot, state);
                assert_eq!(copy.reference, state);
                assert!(Arc::ptr_eq(&copy.path, &checked.path));
            });
            work
        });
        assert!(samples.iter().all(|work| *work > 0));
        assert!(
            samples.windows(2).all(|pair| pair[1] <= pair[0] * 2),
            "retention scanned unrelated history: {samples:?}"
        );
    }

    #[test]
    fn checked_interface_branch_rejects_unproved_facts_and_unowned_resources() {
        let function = c_function(
            CType::Void,
            "interface",
            Vec::new(),
            CStatement::Return(CExpression::Value(CValue::Void)),
        );
        let state = CState::new()
            .with_local("x", int32(7))
            .with_local("flag", int32(0));
        let condition = CExpression::Variable("flag".to_string());
        let branch_statement = CStatement::If {
            condition: condition.clone(),
            then_branch: Box::new(CStatement::Skip),
            else_branch: Box::new(CStatement::Skip),
        };
        let continuation = Some(CStatement::Return(CExpression::Variable("x".to_string())));
        let then_theorem = match condition_event(&state, &condition, true) {
            CheckedExecutionEvent::Condition(theorem) => theorem,
            _ => unreachable!(),
        };
        let else_theorem = match condition_event(&state, &condition, false) {
            CheckedExecutionEvent::Condition(theorem) => theorem,
            _ => unreachable!(),
        };
        let root_facts = ProofFacts::default();
        let split = CheckedBranchSplit {
            state: state.clone(),
            branch_statement,
            continuation,
            condition,
            root_facts: root_facts.clone(),
            paths: vec![
                CheckedBranchPath {
                    outcome: CConditionOutcome::Value(true),
                    facts: Vec::new().into(),
                    obligations: Vec::new(),
                    theorem: then_theorem.clone(),
                },
                CheckedBranchPath {
                    outcome: CConditionOutcome::Value(false),
                    facts: Vec::new().into(),
                    obligations: Vec::new(),
                    theorem: else_theorem.clone(),
                },
            ],
        };
        let parent = ExecutionProofCore::at_entry(state.clone(), ExecutionFrontier::default());
        let at_branch = FrontierPosition::StatementEntry {
            remaining: Arc::new(crate::kernel::c_seq(
                split.branch_statement.clone(),
                split.continuation.clone().expect("a continuation"),
            )),
        };
        let mut then_arm = parent.clone();
        then_arm.frontier.position = at_branch.clone();
        then_arm
            .record_condition_transition(
                &function,
                &[],
                then_theorem.clone(),
                PureFactContext::new(),
                &[],
                &[],
            )
            .expect("the then condition decides the frontier's `if`");
        then_arm.frontier.region = ExecutionRegionKind::BranchArm;
        then_arm.frontier.position = FrontierPosition::RegionBoundary;
        let mut else_arm = parent.clone();
        else_arm.frontier.position = at_branch;
        else_arm
            .record_condition_transition(
                &function,
                &[],
                else_theorem.clone(),
                PureFactContext::new(),
                &[],
                &[],
            )
            .expect("the else condition decides the frontier's `if`");
        else_arm.frontier.region = ExecutionRegionKind::BranchArm;
        else_arm.frontier.position = FrontierPosition::RegionBoundary;
        let stable_join_locals = state
            .locals()
            .object_values()
            .map(|(name, value)| (name.to_string(), value.clone()))
            .collect::<BTreeMap<_, _>>();
        let spec = SpecProposition::Comparison {
            left: SpecExpression::CExpression(CExpression::Variable("x".to_string())),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::CExpression(CExpression::Variable("x".to_string())),
        };
        let checked_fact = interface_spec_paths(&spec, &state, &state, &PureFactContext::new())
            .expect("the simple interface should lower")
            .remove(0)
            .proposition;
        let successor_facts = root_facts.with_fact(checked_fact.clone());

        let checked = CheckedExecutionBranch::check_interface(
            split.clone(),
            &root_facts,
            [&then_theorem, &else_theorem],
            [&root_facts, &root_facts],
            &parent,
            [&then_arm, &else_arm],
            &function,
            &[],
            &stable_join_locals,
            std::slice::from_ref(&spec),
            &[],
            [&[], &[]],
            &state,
            &successor_facts,
            None,
        )
        .expect("the exact fact-only abstraction should check");
        assert_eq!(checked.interface_lowerings.len(), 1);
        let retained = &checked.interface_lowerings[0];
        assert!(retained[0].facts.shares_premises_with(&root_facts));
        assert!(retained[1].facts.shares_premises_with(&root_facts));
        assert!(retained[2].facts.shares_premises_with(&successor_facts));
        assert!(
            retained
                .iter()
                .all(|lowering| lowering.path.proposition == checked_fact)
        );
        assert!(checked.matches_interface_resource_definitions(&function));
        let mut stale = checked.clone();
        stale.interface_successor_facts = Some(successor_facts.with_fact(Proposition::Predicate {
            name: "stale".into(),
            arguments: Vec::new(),
        }));
        assert!(!stale.matches_interface_resource_definitions(&function));
        assert_eq!(
            checked
                .interface_execution_facts()
                .iter()
                .map(ExecutionPureFact::proposition)
                .collect::<Vec<_>>(),
            vec![&checked_fact],
            "only the validated successor delta gains execution-fact authority"
        );

        let forged_fact = Proposition::ConditionIs(
            crate::kernel::ConditionTerm::signed_less_than(
                Bitvector32Term::Constant(1),
                Bitvector32Term::Constant(0),
            ),
            true,
        );
        assert!(
            CheckedExecutionBranch::check_interface(
                split.clone(),
                &root_facts,
                [&then_theorem, &else_theorem],
                [&root_facts, &root_facts],
                &parent,
                [&then_arm, &else_arm],
                &function,
                &[],
                &stable_join_locals,
                std::slice::from_ref(&spec),
                &[],
                [&[], &[]],
                &state,
                &successor_facts.with_fact(forged_fact),
                None,
            )
            .is_err(),
            "an unrelated successor fact must not gain interface authority"
        );

        let forged_resource = CResourceFact::own_token("missing".to_string(), Vec::new());
        let forged_state = state
            .clone()
            .with_resource_context(ResourceContext::new().unchecked_with_fact(forged_resource));
        assert!(
            CheckedExecutionBranch::check_interface(
                split,
                &root_facts,
                [&then_theorem, &else_theorem],
                [&root_facts, &root_facts],
                &parent,
                [&then_arm, &else_arm],
                &function,
                &[],
                &stable_join_locals,
                std::slice::from_ref(&spec),
                &[],
                [&[], &[]],
                &forged_state,
                &successor_facts,
                None,
            )
            .is_err(),
            "a resource absent from both arms must not gain interface authority"
        );
    }
}

/// Deterministic four-size curves for the loan machinery an interface join
/// and a loop-head havoc run (R32; docs/internals/stable-views.md). Both axes
/// grow with proof length rather than with the selected contract: the binding
/// count grows by one per exposed child per unfold or observe, and the cell
/// and symbolic-loan counts grow with the memory a proof has named. Neither
/// is output the checker must produce, so a quadratic curve here is a scaling
/// defect rather than output-sensitive work. Work is counted with the
/// deterministic counter; host time never decides these tests.
#[cfg(test)]
mod loan_scaling_tests {
    use super::*;
    use crate::kernel::loans::{LoanLedger, LoanViewBinding};
    use crate::kernel::{PointerBlock, PointerOffsetTerm, int32};
    use std::collections::BTreeSet;

    /// The two largest adjacent ratios of a doubling series, the same
    /// near-linear rule `src/surface/tests/scaling_tests.rs` applies.
    fn assert_near_linear(axis: &str, samples: &[(usize, usize)]) {
        assert!(
            samples[0].1 > 0,
            "{axis}: nothing was measured: {samples:?}"
        );
        for pair in samples.windows(2) {
            assert_eq!(pair[1].0, pair[0].0 * 2, "{axis}: {samples:?}");
        }
        for pair in samples.windows(2).skip(samples.len().saturating_sub(3)) {
            assert!(
                pair[1].1 <= pair[0].1.saturating_mul(3),
                "{axis}: deterministic work grows faster than the simple-verification contract: {samples:?}"
            );
        }
    }

    /// One arm state and one interface successor that both carry `count`
    /// occurrence-keyed bindings of a single shared loan. This is the shape a
    /// proof reaches by exposing one child per unfold or observe: the binding
    /// count follows the proof, while the loan and its ledger follow the
    /// contract. The successor's resource context is rebuilt from the
    /// declared clauses, so its occurrences are fresh and only the binding
    /// content can connect it to the arm.
    fn interface_join_states(count: usize) -> (CState, CState) {
        let support_fact = CResourceFact::own_token("shared_support".to_string(), Vec::new());
        let viewed = (0..count)
            .map(|index| CResourceFact::view_token(format!("child_{index}"), Vec::new()))
            .collect::<Vec<_>>();
        let resources = ResourceContext::new().unchecked_with_facts(
            std::iter::once(support_fact.clone()).chain(viewed.iter().cloned()),
        );
        let support = resources.owned_occurrences_for_fact(&support_fact)[0];
        let ledger = LoanLedger::new();
        let owner = ledger.fresh_participant().expect("owner identity");
        let reader = ledger.fresh_participant().expect("reader identity");
        let opening = ledger
            .lend(owner, reader, support, support_fact)
            .expect("one shared loan backs every exposed child");
        let bindings = viewed
            .iter()
            .map(|fact| LoanViewBinding {
                loan: opening.loan,
                scope: opening.scope,
                share: opening.root_share,
                support,
                viewed: fact.clone(),
                hold: None,
            })
            .collect::<Vec<_>>();
        let arm_dependencies = viewed
            .iter()
            .zip(&bindings)
            .map(|(fact, binding)| (resources.occurrences_for_fact(fact)[0], binding.clone()))
            .collect::<Vec<_>>();
        let arm = CState::new()
            .with_loan_ledger(Some(ledger))
            .with_loan_participant(Some(reader))
            .with_resource_context_and_loan_dependencies(resources, arm_dependencies);

        let successor_resources =
            ResourceContext::new().unchecked_with_facts(viewed.iter().cloned());
        let successor_dependencies = viewed
            .iter()
            .zip(&bindings)
            .map(|(fact, binding)| {
                (
                    successor_resources.occurrences_for_fact(fact)[0],
                    binding.clone(),
                )
            })
            .collect::<Vec<_>>();
        let successor = CState::new().with_resource_context_and_loan_dependencies(
            successor_resources,
            successor_dependencies,
        );
        (arm, successor)
    }

    #[test]
    fn interface_binding_inheritance_is_near_linear_in_the_binding_count() {
        let mut samples = Vec::new();
        for count in [8, 16, 32, 64] {
            let (arm, successor) = interface_join_states(count);
            let (inherited, work) = crate::instrumentation::measure_deterministic_work(|| {
                interface_successor_loans_are_inherited(&successor, [&arm, &arm])
            });
            assert!(
                inherited,
                "every successor binding is one the arm held, so the join is admitted"
            );
            samples.push((count, work));
        }
        // 36, 136, 528, 2080 before the membership index; 24, 48, 96, 192
        // after it (both arms folded in, then one lookup per successor
        // binding). The second assertion pins the linear shape itself, so a
        // reintroduced pairwise scan fails here and not only at eight times
        // the size.
        assert_near_linear("interface join binding count", &samples);
        for (count, work) in &samples {
            assert!(
                *work <= 6 * count + 16,
                "interface join binding inheritance stopped being one pass per binding: {samples:?}"
            );
        }
    }

    /// A contract-input view over parameter memory: symbolic base offset, so
    /// it never enters the concrete dyadic index and stays in its block's
    /// unindexed bucket.
    fn parameter_view(variable: u64) -> CResourceFact {
        CResourceFact::view_memory(CMemoryRange::new_with_element_width(
            Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Variable(Variable(variable)),
            },
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
            4,
        ))
    }

    /// `count` live symbolic contract-input loans, all in one block.
    fn symbolic_contract_input_ledger(count: usize) -> LoanLedger {
        let viewed = (0..count as u64).map(parameter_view).collect::<Vec<_>>();
        let resources = ResourceContext::new().unchecked_with_facts(viewed.iter().cloned());
        let mut ledger = LoanLedger::new();
        let holder = ledger.fresh_participant().expect("holder identity");
        for fact in &viewed {
            let support = resources.occurrences_for_fact(fact)[0];
            let opening = ledger
                .borrowed_contract_input(holder, support, fact.clone(), None)
                .expect("a checked symbolic contract input");
            ledger = ledger
                .apply(&opening.transition)
                .expect("the input root applies");
        }
        assert!(ledger.has_active_memory_loans());
        ledger
    }

    /// `count` concrete cells in the same block those loans protect.
    fn cells_in_the_symbolic_block(count: usize) -> CMemory {
        let mut memory = CMemory::new();
        for index in 0..count {
            memory = memory.store(
                Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: PointerOffsetTerm::Constant(4 * index as i64),
                },
                int32(0),
            );
        }
        memory
    }

    #[test]
    fn loop_head_havoc_work_over_cells_and_symbolic_loans() {
        let mut samples = Vec::new();
        for count in [8, 16, 32, 64] {
            let ledger = symbolic_contract_input_ledger(count);
            let memory = cells_in_the_symbolic_block(count);
            let (havoced, work) = crate::instrumentation::measure_deterministic_work(|| {
                memory.with_loop_memory_havoc_preserving_loans(
                    Variable(7),
                    &BTreeSet::new(),
                    None,
                    Some(&ledger),
                )
            });
            // Validity: no cell was proven protected, so the havoc paid the
            // complete query for each one. An early refusal would short the
            // scan and make the curve look better than the checker is.
            for index in 0..count {
                assert!(
                    !havoced.has_known_cell_at(&Pointer {
                        block: PointerBlock::ExternalArgument,
                        offset: PointerOffsetTerm::Constant(4 * index as i64),
                    }),
                    "a cell no loan protects must not survive the havoc"
                );
            }
            samples.push((count, work));
        }
        // Measured, not aspirational: 65, 257, 1025, 4097 -- one query per
        // cell, each walking every symbolic protected range in the block, so
        // the curve is cells x symbolic loans and doubling costs four times
        // as much. Nothing local fixes it: a symbolic base offset cannot
        // enter the dyadic index, the block bucket already holds only the
        // genuinely symbolic entries, and a cell's answer depends on the
        // cell, so per-block hoisting cannot share it. This bound is recorded
        // as a known violation in `docs/internals/verification-efficiency.md`;
        // the assertion pins it from above so no further factor creeps in and
        // so a later indexing change that makes it linear still passes.
        for (count, work) in &samples {
            assert!(
                *work <= count * count + 4 * count + 16,
                "loop-head havoc cells x symbolic loans exceeded its known quadratic bound: {samples:?}"
            );
        }
    }
}

#[cfg(test)]
mod automatic_lifetime_tests {
    use super::*;
    use crate::kernel::int32;

    #[test]
    fn automatic_lifetime_event_rejects_active_local_loan_and_forged_retirement() {
        use crate::kernel::loans::{LoanLedger, plan_stable_view_transfer};
        use crate::kernel::prelude::CCheckedResourceFact;
        use crate::kernel::{CResourceSnapshot, CResourceTransferRole};
        let state = CState::new()
            .with_local("selected", int32(5))
            .with_memory(CMemory::new().with_block("local:selected", 4));
        let pointer = state.locals().slot("selected").unwrap().clone();
        let viewed =
            CResourceFact::view_memory(CMemoryRange::new(pointer.clone(), 0.into(), 1.into()));
        let ledger = LoanLedger::new();
        let caller = ledger.fresh_participant().unwrap();
        let callee = ledger.fresh_participant().unwrap();
        let assumptions = PureFactContext::new();
        let mut plan = plan_stable_view_transfer(
            &ResourceContext::new(),
            &[],
            &assumptions,
            &ledger,
            caller,
            callee,
        )
        .unwrap();
        plan.lend_local_views(
            state.memory(),
            &[CCheckedResourceFact {
                fact: viewed,
                role: CResourceTransferRole::Borrow,
                snapshot: CResourceSnapshot::Entry,
                clause_position: None,
                section_index: None,
                selected_mutex_source: None,
            }],
            &assumptions,
        )
        .unwrap();
        let state = state
            .with_loan_ledger(Some(plan.ledger.clone()))
            .with_loan_participant(Some(caller));
        let names = vec!["selected".to_string()];
        let mut core = ExecutionProofCore::at_entry(state.clone(), ExecutionFrontier::default());
        assert!(core.record_automatic_lifetime_end(&state, &names).is_err());
        let forged = CheckedAutomaticLifetimeEnd {
            before_state: state.clone(),
            names,
            after_state: state
                .clone()
                .with_memory(state.memory().clone().without_local_block(&pointer.block)),
        };
        assert!(forged.advance_checked(&state).is_none());
    }

    #[test]
    fn automatic_lifetime_event_rejects_forged_mutex_storage_retirement() {
        let state = CState::new()
            .with_local("holder", int32(0))
            .with_memory(CMemory::new().with_block("local:holder", 48));
        let address = state.locals().slot("holder").unwrap().offset_by_bytes(8);
        let context = crate::kernel::mutexes::MutexContext::new(state)
            .initialize_empty(address.clone(), 40)
            .unwrap();
        let state = context.state();
        let names = vec!["holder".to_string()];
        let mut core = ExecutionProofCore::at_entry(state.clone(), ExecutionFrontier::default());
        assert!(matches!(
            core.record_automatic_lifetime_end(state, &names),
            Err(CRuntimeError::MutexStorageScopeEnd { .. })
        ));
        let forged = CheckedAutomaticLifetimeEnd {
            before_state: state.clone(),
            names: names.clone(),
            after_state: state
                .clone()
                .with_memory(state.memory().clone().without_local_block(&address.block)),
        };
        assert!(forged.advance_checked(state).is_none());
        assert_eq!(core.reached_state(), state);
        let destroyed = context
            .destroy(&address, &PureFactContext::new())
            .unwrap()
            .into_state();
        let mut core =
            ExecutionProofCore::at_entry(destroyed.clone(), ExecutionFrontier::default());
        let after = core
            .record_automatic_lifetime_end(&destroyed, &names)
            .unwrap();
        let events = core.execution_evidence[0].to_vec();
        let CheckedExecutionEvent::AutomaticLifetimeEnd(event) = &events[0] else {
            panic!("missing scope event")
        };
        assert_eq!(event.advance_checked(&destroyed), Some(after));
    }

    #[test]
    fn automatic_lifetime_end_consumes_only_local_construction_ownership() {
        let mut samples = Vec::new();
        for size in [16, 64, 256, 1024] {
            let pointer = CMemory::local_pointer("selected");
            let owner = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
                pointer,
                0u32.into(),
                16u32.into(),
                1,
            ));
            let mut resources = ResourceContext::new().unchecked_with_fact(owner.clone());
            for i in 0..size {
                resources = resources.unchecked_with_fact(CResourceFact::own_token(
                    format!("unrelated_{i}"),
                    vec![],
                ));
            }
            let state = CState::new()
                .with_local("selected", int32(0))
                .with_memory(CMemory::new().with_block("local:selected", 16))
                .with_resource_context(resources);
            let mut core =
                ExecutionProofCore::at_entry(state.clone(), ExecutionFrontier::default());
            let (after, work) = crate::instrumentation::measure_deterministic_work(|| {
                core.record_automatic_lifetime_end(&state, &["selected".into()])
                    .unwrap()
            });
            assert!(
                !after
                    .resources()
                    .satisfies_fact(&owner, &PureFactContext::new())
            );
            assert!(after.resources().satisfies_fact(
                &CResourceFact::own_token("unrelated_0".into(), vec![]),
                &PureFactContext::new()
            ));
            assert!(!after.memory().has_block(&"local:selected".into()));
            let events = core.execution_evidence[0].to_vec();
            let CheckedExecutionEvent::AutomaticLifetimeEnd(end) = &events[0] else {
                unreachable!()
            };
            assert_eq!(end.advance_checked(&state), Some(after.clone()));
            let mut forged = end.clone();
            forged.after_state = after.with_resource_context(state.resources().clone());
            assert!(forged.advance_checked(&state).is_none());
            samples.push((size, work));
        }
        eprintln!("local construction retirement (N, units): {samples:?}");
        assert!(
            samples.iter().all(|(_, work)| *work <= samples[0].1 + 64),
            "{samples:?}"
        );
    }

    #[test]
    fn automatic_lifetime_event_ignores_unrelated_locals_and_checks_exact_states() {
        let samples = [8, 16, 32, 64].map(|size| {
            let mut state = CState::new()
                .with_local("selected", int32(5))
                .with_memory(CMemory::new().with_block("local:selected", 4));
            for i in 0..size {
                state = state.with_local(format!("other_{i}"), int32(9));
            }
            let mut core =
                ExecutionProofCore::at_entry(state.clone(), ExecutionFrontier::default());
            let (after, work) = crate::instrumentation::measure_deterministic_work(|| {
                core.record_automatic_lifetime_end(&state, &["selected".to_string()])
                    .unwrap()
            });
            assert!(after.locals().get("selected").is_none());
            assert!(!after.memory().has_block(&"local:selected".into()));
            assert_eq!(after.locals().get("other_0"), Some(&int32(9)));
            let events = core.execution_evidence[0].to_vec();
            let CheckedExecutionEvent::AutomaticLifetimeEnd(end) = &events[0] else {
                panic!("missing lifetime evidence")
            };
            assert_eq!(end.advance_checked(&state), Some(after.clone()));
            assert!(end.advance_checked(&after).is_none());
            let mut forged = end.clone();
            forged.after_state = state.clone();
            assert!(forged.advance_checked(&state).is_none());
            work
        });
        assert!(samples[0] > 0);
        assert!(
            samples
                .iter()
                .enumerate()
                .all(|(i, work)| *work <= samples[0] + i),
            "{samples:?}"
        );
    }
}

#[cfg(test)]
mod population_authority_rewrite_tests {
    use super::*;
    use crate::kernel::{CType, c_function};

    #[test]
    fn exact_composition_observation_accepts_retained_views_but_not_foreign_ownership() {
        let (state, _) = source_state();
        let pointer = state.locals.slot("anchor").unwrap().clone();
        let range = CMemoryRange::new(pointer, 0.into(), 1.into());
        let context = ResourceContext::new().unchecked_with_facts([
            CResourceFact::own_memory(range.clone()),
            CResourceFact::view_memory(range),
        ]);
        let assumptions = PureFactContext::default();
        assert!(resource_composition_is_supported_by(
            &Proposition::CResourceComposition(context.clone()),
            &context,
            &assumptions,
        ));
        let framed = context
            .clone()
            .unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
                CMemory::local_pointer("framed_scalar"),
                0.into(),
                1.into(),
            )));
        assert!(resource_composition_is_supported_by(
            &Proposition::CResourceComposition(context.clone()),
            &framed,
            &assumptions,
        ));
        let duplicated = context
            .clone()
            .unchecked_with_fact(context.facts()[0].clone());
        assert!(!resource_composition_is_supported_by(
            &Proposition::CResourceComposition(duplicated),
            &framed,
            &assumptions,
        ));
        let foreign = ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(
            CMemoryRange::new(
                Pointer {
                    block: "local:foreign".into(),
                    offset: crate::kernel::PointerOffsetTerm::Constant(0),
                },
                0.into(),
                1.into(),
            ),
        ));
        assert!(!resource_composition_is_supported_by(
            &Proposition::CResourceComposition(foreign),
            &context,
            &assumptions,
        ));
    }

    fn source_state() -> (CState, CResourceFact) {
        let mut state = CState::new()
            .with_local("anchor", crate::kernel::int32(0))
            .with_population_creation_tracking();
        let pointer = state.locals.slot("anchor").unwrap().clone();
        state.set_memory(CMemory::new().with_block(pointer.block.clone(), 4));
        state.record_population_storage_creation(pointer.block.clone());
        let description = crate::kernel::ResourceDescription::new(
            "reference".into(),
            vec![CValue::pointer(pointer).into()].into(),
            crate::kernel::ResourceFieldSchema::new(vec![]).unwrap(),
        );
        (
            state,
            CResourceFact::own(CResource::PopulationAuthority(description)),
        )
    }

    #[test]
    fn checked_authority_events_reject_forged_deltas() {
        let (before, selected) = source_state();
        let facts = ProofFacts::default();
        let (established, witness) = before
            .checked_population_authority_exchange(&selected, true, facts.assumptions())
            .unwrap();
        let event = CheckedPopulationAuthorityRewrite::check(
            &before,
            &facts,
            &selected,
            true,
            &witness,
            &established,
            &facts,
        )
        .unwrap();
        assert!(event.advance_checked(&before, &facts).is_some());
        let forged_memory = established
            .clone()
            .with_memory(CMemory::new().with_block("local:forged", 4));
        assert!(
            CheckedPopulationAuthorityRewrite::check(
                &before,
                &facts,
                &selected,
                true,
                &witness,
                &forged_memory,
                &facts,
            )
            .is_err()
        );
        let mut forged_event = event.clone();
        forged_event.after_state = forged_memory;
        assert!(forged_event.advance_checked(&before, &facts).is_none());
        let missing_storage_before = before.clone().with_memory(CMemory::new());
        let missing_storage_after = established.clone().with_memory(CMemory::new());
        assert!(
            CheckedPopulationAuthorityRewrite::check(
                &missing_storage_before,
                &facts,
                &selected,
                true,
                &witness,
                &missing_storage_after,
                &facts,
            )
            .is_err()
        );
        let forged_resources = established
            .clone()
            .with_resource_context(ResourceContext::new());
        assert!(
            CheckedPopulationAuthorityRewrite::check(
                &before,
                &facts,
                &selected,
                true,
                &witness,
                &forged_resources,
                &facts,
            )
            .is_err()
        );
        let forged_observation = established
            .clone()
            .with_observed_population_family("reference");
        assert!(
            CheckedPopulationAuthorityRewrite::check(
                &before,
                &facts,
                &selected,
                true,
                &witness,
                &forged_observation,
                &facts,
            )
            .is_err()
        );
        let forged_facts = facts.clone().with_fact(Proposition::ConditionIs(
            crate::kernel::ConditionTerm::Constant(true),
            true,
        ));
        assert!(
            CheckedPopulationAuthorityRewrite::check(
                &before,
                &facts,
                &selected,
                true,
                &witness,
                &established,
                &forged_facts,
            )
            .is_err()
        );
        let (retired, retire_witness) = established
            .checked_population_authority_exchange(&selected, false, facts.assumptions())
            .unwrap();
        assert!(
            CheckedPopulationAuthorityRewrite::check(
                &established,
                &facts,
                &selected,
                false,
                &retire_witness,
                &retired,
                &facts,
            )
            .is_ok()
        );
        assert!(
            CheckedPopulationAuthorityRewrite::check(
                &established,
                &facts,
                &selected,
                false,
                &witness,
                &retired,
                &facts,
            )
            .is_err()
        );
        assert!(
            before
                .checked_population_authority_exchange(&selected, true, facts.assumptions())
                .is_ok()
        );
        assert!(
            retired
                .checked_population_authority_exchange(&selected, true, facts.assumptions())
                .is_err()
        );
    }

    #[test]
    fn checked_member_events_conserve_one_occurrence_and_reject_forged_deltas() {
        let (before, authority) = source_state();
        let facts = ProofFacts::default();
        let (established, _) = before
            .checked_population_authority_exchange(&authority, true, facts.assumptions())
            .unwrap();
        let CResource::PopulationAuthority(description) = authority.resource() else {
            unreachable!()
        };
        let member = CResourceFact::own(CResource::Composite {
            name: description.family().to_owned(),
            arguments: description.arguments().to_vec().into(),
        });
        let function =
            c_function(
                CType::Void,
                "value",
                vec![],
                CStatement::Return(CExpression::Value(CValue::Void)),
            )
            .with_composite_resource_definitions(vec![
                CCompositeResourceDefinition::new("reference", vec![], None, false, vec![], vec![]),
            ]);
        let definition = function.composite_resource_definition("reference").unwrap();
        let (one, birth) = established
            .checked_population_member_exchange(&member, true, definition, facts.assumptions())
            .unwrap();
        let event = CheckedPopulationMemberRewrite::check(
            &function,
            &established,
            &facts,
            &member,
            true,
            &birth,
            &one,
            &facts,
        )
        .unwrap();
        assert!(event.advance_checked(&established, &facts).is_some());
        assert!(
            established
                .checked_population_member_exchange(&member, false, definition, facts.assumptions())
                .is_err()
        );
        assert!(
            one.checked_population_authority_exchange(&authority, false, facts.assumptions())
                .is_err()
        );
        assert!(
            CheckedPopulationMemberRewrite::check(
                &function,
                &established,
                &facts,
                &member,
                true,
                &birth,
                &one.clone().with_resource_context(ResourceContext::new()),
                &facts,
            )
            .is_err()
        );
        assert!(
            CheckedPopulationMemberRewrite::check(
                &function,
                &established,
                &facts,
                &member,
                true,
                &birth,
                &one.clone().with_memory(CMemory::new()),
                &facts,
            )
            .is_err()
        );
        let (zero, death) = one
            .checked_population_member_exchange(&member, false, definition, facts.assumptions())
            .unwrap();
        assert!(
            CheckedPopulationMemberRewrite::check(
                &function, &one, &facts, &member, false, &death, &zero, &facts,
            )
            .is_ok()
        );
        assert!(
            CheckedPopulationMemberRewrite::check(
                &function, &one, &facts, &member, false, &birth, &zero, &facts,
            )
            .is_err()
        );
        assert!(
            zero.checked_population_member_exchange(
                &member,
                false,
                definition,
                facts.assumptions()
            )
            .is_err()
        );
    }

    #[test]
    fn member_exchange_requires_both_external_body_ownership_and_checked_extent() {
        let (state, authority) = source_state();
        let external = crate::kernel::Pointer {
            block: crate::kernel::PointerBlock::ExternalArgument,
            offset: crate::kernel::PointerOffsetTerm::Constant(16),
        };
        let CResource::PopulationAuthority(description) = authority.resource() else {
            unreachable!()
        };
        let member = CResourceFact::own(CResource::Composite {
            name: "reference".into(),
            arguments: description.arguments().to_vec().into(),
        });
        let definition = CCompositeResourceDefinition::new(
            "reference",
            vec![crate::kernel::c_parameter("p", CType::Int32Pointer)],
            None,
            false,
            vec![CResourceSpec::owned_memory(
                crate::kernel::CMemorySegment::new(
                    CExpression::Value(CValue::pointer(external.clone())),
                    crate::kernel::c_int32_literal(0),
                    crate::kernel::c_int32_literal(1),
                ),
            )],
            vec![],
        );
        let function = c_function(CType::Void, "member", vec![], CStatement::Skip)
            .with_composite_resource_definitions(vec![definition.clone()]);
        let (empty, _) = state
            .checked_population_authority_exchange(&authority, true, &PureFactContext::new())
            .unwrap();
        let owned =
            empty
                .clone()
                .with_resource_context(empty.resources().clone().unchecked_with_fact(
                    CResourceFact::own_memory(CMemoryRange::new(
                        external.clone(),
                        0.into(),
                        1.into(),
                    )),
                ));
        assert!(
            owned
                .checked_population_member_exchange(
                    &member,
                    true,
                    &definition,
                    &PureFactContext::new()
                )
                .is_err()
        );
        let extent = |bytes| Proposition::CMemoryLoadable {
            memory: owned.memory().clone(),
            base: external.clone(),
            bytes: Bitvector32Term::Constant(bytes),
            wide: false,
        };
        let small = ProofFacts::default().with_fact(extent(1));
        assert!(
            owned
                .checked_population_member_exchange(&member, true, &definition, small.assumptions())
                .is_err()
        );
        let facts = ProofFacts::default().with_fact(extent(4));
        assert!(
            empty
                .checked_population_member_exchange(&member, true, &definition, facts.assumptions())
                .is_err()
        );
        let (one, witness) = owned
            .checked_population_member_exchange(&member, true, &definition, facts.assumptions())
            .unwrap();
        assert!(
            CheckedPopulationMemberRewrite::check(
                &function, &owned, &facts, &member, true, &witness, &one, &facts
            )
            .is_ok()
        );
        assert!(
            CheckedPopulationMemberRewrite::check(
                &function, &owned, &small, &member, true, &witness, &one, &small
            )
            .is_err()
        );
    }

    #[test]
    fn checked_member_exchange_transfers_exact_contained_resource() {
        for abstract_token in [false, true] {
            let (state, authority) = source_state();
            let facts = ProofFacts::default();
            let CResource::PopulationAuthority(description) = authority.resource() else {
                unreachable!()
            };
            let member = CResourceFact::own(CResource::Composite {
                name: "reference".into(),
                arguments: description.arguments().to_vec().into(),
            });
            let (child, child_spec) = if abstract_token {
                (
                    CResourceFact::own(CResource::Token {
                        name: "payload".into(),
                        arguments: vec![crate::kernel::int32(7).into()].into(),
                    }),
                    CResourceSpec::token(
                        crate::kernel::CResourceAccessMode::Own,
                        "payload".into(),
                        vec![crate::kernel::c_int32_literal(7)],
                        vec![CType::Int32],
                    ),
                )
            } else {
                (
                    CResourceFact::own(CResource::Composite {
                        name: "payload".into(),
                        arguments: description.arguments().to_vec().into(),
                    }),
                    CResourceSpec::composite(
                        crate::kernel::CResourceAccessMode::Own,
                        "payload".into(),
                        vec![crate::kernel::c_variable("p")],
                        vec![CType::Int32Pointer],
                    ),
                )
            };
            let definition = CCompositeResourceDefinition::new(
                "reference",
                vec![crate::kernel::c_parameter("p", CType::Int32Pointer)],
                None,
                false,
                vec![child_spec],
                vec![],
            );
            let function = c_function(
                CType::Void,
                "member",
                vec![],
                CStatement::Return(CExpression::Value(CValue::Void)),
            )
            .with_composite_resource_definitions(vec![definition.clone()]);
            let (empty, _) = state
                .checked_population_authority_exchange(&authority, true, facts.assumptions())
                .unwrap();
            assert!(
                empty
                    .checked_population_member_exchange(
                        &member,
                        true,
                        &definition,
                        facts.assumptions(),
                    )
                    .is_err()
            );
            let empty = empty.clone().with_resource_context(
                empty.resources().clone().unchecked_with_fact(child.clone()),
            );
            let (one, birth) = empty
                .checked_population_member_exchange(&member, true, &definition, facts.assumptions())
                .unwrap();
            assert!(!one.resources().satisfies_fact(&child, facts.assumptions()));
            assert!(one.resources().satisfies_fact(&member, facts.assumptions()));
            let event = CheckedPopulationMemberRewrite::check(
                &function, &empty, &facts, &member, true, &birth, &one, &facts,
            )
            .unwrap();
            assert!(event.advance_checked(&empty, &facts).is_some());
            let duplicated = one
                .clone()
                .with_resource_context(one.resources().clone().unchecked_with_fact(child.clone()));
            assert!(
                CheckedPopulationMemberRewrite::check(
                    &function,
                    &empty,
                    &facts,
                    &member,
                    true,
                    &birth,
                    &duplicated,
                    &facts,
                )
                .is_err()
            );
            assert!(
                one.checked_population_member_exchange(
                    &member,
                    true,
                    &definition,
                    facts.assumptions(),
                )
                .is_err()
            );
            let (zero, death) = one
                .checked_population_member_exchange(
                    &member,
                    false,
                    &definition,
                    facts.assumptions(),
                )
                .unwrap();
            assert!(zero.resources().satisfies_fact(&child, facts.assumptions()));
            assert!(
                !zero
                    .resources()
                    .satisfies_fact(&member, facts.assumptions())
            );
            let event = CheckedPopulationMemberRewrite::check(
                &function, &one, &facts, &member, false, &death, &zero, &facts,
            )
            .unwrap();
            assert!(event.advance_checked(&one, &facts).is_some());
            let missing = zero.clone().with_resource_context(
                zero.resources()
                    .clone()
                    .without_fact_incrementally(&child, facts.assumptions())
                    .unwrap(),
            );
            assert!(
                CheckedPopulationMemberRewrite::check(
                    &function, &one, &facts, &member, false, &death, &missing, &facts,
                )
                .is_err()
            );
        }
    }

    #[test]
    fn private_member_facts_cannot_use_ambient_cell_ownership() {
        use crate::kernel::{CMemorySegment, c_int32_literal, c_parameter, c_variable};
        let (_, authority) = source_state();
        let CResource::PopulationAuthority(description) = authority.resource() else {
            unreachable!()
        };
        let member = CResourceFact::own(CResource::Composite {
            name: "reference".into(),
            arguments: description.arguments().to_vec().into(),
        });
        let [crate::kernel::AlgebraicValue::C(CValue::Pointer(pointer))] = description.arguments()
        else {
            unreachable!()
        };
        let pointer = pointer.pointer();
        let memory = CMemory::new().with_block(pointer.block.clone(), 8).store(
            pointer.offset_by_elements(1.into(), 4),
            crate::kernel::int32(0),
        );
        let resources = ResourceContext::new().unchecked_with_facts([
            CResourceFact::own_memory(CMemoryRange::new(pointer.clone(), 0.into(), 1.into())),
            CResourceFact::own_memory(CMemoryRange::new(pointer.clone(), 1.into(), 2.into())),
        ]);
        let definition = CCompositeResourceDefinition::new(
            "reference",
            vec![c_parameter("p", CType::Int32Pointer)],
            None,
            false,
            vec![CResourceSpec::owned_memory(CMemorySegment::new(
                c_variable("p"),
                c_int32_literal(0),
                c_int32_literal(1),
            ))],
            vec![crate::kernel::SpecProposition::Comparison {
                left: crate::kernel::SpecExpression::CExpression(crate::kernel::c_index(
                    c_variable("p"),
                    c_int32_literal(1),
                )),
                operator: crate::kernel::CComparisonOperator::Equal,
                right: crate::kernel::SpecExpression::Value(crate::kernel::int32(0)),
            }],
        );
        let assumptions = PureFactContext::default();
        assert!(
            crate::kernel::functions::instantiate_composite_resource_facts(
                &member,
                std::slice::from_ref(&definition),
                &memory,
                &resources,
                &assumptions,
            )
            .is_some()
        );
        assert!(
            crate::kernel::functions::instantiate_private_member_body_facts(
                &member,
                &definition,
                &CState::new()
                    .with_population_creation_tracking()
                    .with_memory(memory.clone())
                    .with_resource_context(resources.clone()),
                &assumptions,
            )
            .is_none()
        );
        let work = [8, 32, 128, 512].map(|locals| {
            let mut state = CState::new()
                .with_population_creation_tracking()
                .with_memory(memory.clone())
                .with_resource_context(resources.clone());
            for index in 0..locals {
                state = state.with_local(format!("unrelated_{index}"), crate::kernel::int32(index));
            }
            let (instantiated, work) = crate::persistent::measure_persistent_work(|| {
                crate::kernel::functions::instantiate_private_member_body_facts(
                    &member,
                    &definition,
                    &state,
                    &assumptions,
                )
            });
            assert!(instantiated.is_none());
            work
        });
        assert!(
            work[0] > 0,
            "member fact checking must charge work: {work:?}"
        );
        assert!(
            work.iter().all(|sample| *sample <= work[0] + 128),
            "member fact checking must not visit unrelated caller locals: {work:?}"
        );
    }

    #[test]
    fn member_body_facts_require_checked_birth_and_reject_forged_consumption_facts() {
        let (state, authority) = source_state();
        let facts = ProofFacts::default();
        let (state, _) = state
            .checked_population_authority_exchange(&authority, true, facts.assumptions())
            .unwrap();
        let CResource::PopulationAuthority(description) = authority.resource() else {
            unreachable!()
        };
        let member = CResourceFact::own(CResource::Composite {
            name: "reference".into(),
            arguments: description.arguments().to_vec().into(),
        });
        let definition = |right| {
            CCompositeResourceDefinition::new(
                "reference",
                vec![crate::kernel::c_parameter("p", CType::Int32Pointer)],
                None,
                false,
                vec![],
                vec![crate::kernel::SpecProposition::Comparison {
                    left: crate::kernel::SpecExpression::Value(crate::kernel::int32(1)),
                    operator: crate::kernel::CComparisonOperator::Equal,
                    right: crate::kernel::SpecExpression::Value(crate::kernel::int32(right)),
                }],
            )
        };
        assert!(
            state
                .checked_population_member_exchange(
                    &member,
                    true,
                    &definition(2),
                    facts.assumptions()
                )
                .is_err()
        );
        let definition = definition(1);
        let function = c_function(
            CType::Void,
            "member",
            vec![],
            CStatement::Return(CExpression::Value(CValue::Void)),
        )
        .with_composite_resource_definitions(vec![definition.clone()]);
        let (one, birth) = state
            .checked_population_member_exchange(&member, true, &definition, facts.assumptions())
            .unwrap();
        CheckedPopulationMemberRewrite::check(
            &function, &state, &facts, &member, true, &birth, &one, &facts,
        )
        .unwrap();
        let (zero, death) = one
            .checked_population_member_exchange(&member, false, &definition, facts.assumptions())
            .unwrap();
        let body_facts = crate::kernel::functions::instantiate_composite_resource_facts(
            &member,
            std::slice::from_ref(&definition),
            one.memory(),
            zero.resources(),
            facts.assumptions(),
        )
        .unwrap();
        let mut exposed = facts.clone();
        for fact in body_facts.propositions {
            exposed = exposed.with_fact(fact);
        }
        let event = CheckedPopulationMemberRewrite::check(
            &function, &one, &facts, &member, false, &death, &zero, &exposed,
        )
        .unwrap();
        assert!(event.advance_checked(&one, &facts).is_some());
        let forged_facts = exposed.with_fact(Proposition::ConditionIs(
            crate::kernel::ConditionTerm::Constant(false),
            true,
        ));
        assert!(
            CheckedPopulationMemberRewrite::check(
                &function,
                &one,
                &facts,
                &member,
                false,
                &death,
                &zero,
                &forged_facts
            )
            .is_err()
        );
        let mut forged = event;
        forged.after_facts = forged_facts;
        assert!(forged.advance_checked(&one, &facts).is_none());
    }

    #[test]
    fn checked_member_events_exchange_private_memory_and_reject_duplicate_birth() {
        use crate::kernel::{CMemorySegment, c_int32_literal, c_parameter, c_variable};

        let (before, authority) = source_state();
        let CResource::PopulationAuthority(description) = authority.resource() else {
            unreachable!()
        };
        let member = CResourceFact::own(CResource::Composite {
            name: description.family().to_owned(),
            arguments: description.arguments().to_vec().into(),
        });
        let [crate::kernel::AlgebraicValue::C(CValue::Pointer(pointer))] = description.arguments()
        else {
            unreachable!()
        };
        let memory = CResourceFact::own_memory(CMemoryRange::new(
            pointer.pointer().clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        ));
        let definition = CCompositeResourceDefinition::new(
            "reference",
            vec![c_parameter("p", CType::Int32Pointer)],
            None,
            false,
            vec![CResourceSpec::owned_memory(CMemorySegment::new(
                c_variable("p"),
                c_int32_literal(0),
                c_int32_literal(1),
            ))],
            vec![],
        )
        .with_authorized(true);
        let function = c_function(
            CType::Void,
            "value",
            vec![],
            CStatement::Return(CExpression::Value(CValue::Void)),
        )
        .with_composite_resource_definitions(vec![definition]);
        let definition = function.composite_resource_definition("reference").unwrap();
        let facts = ProofFacts::default();
        let (established, _) = before
            .with_resource_context(ResourceContext::new().unchecked_with_fact(memory.clone()))
            .checked_population_authority_exchange(&authority, true, facts.assumptions())
            .unwrap();
        let (one, birth) = established
            .checked_population_member_exchange(&member, true, definition, facts.assumptions())
            .unwrap();
        assert!(!one.resources().satisfies_fact(&memory, facts.assumptions()));
        assert!(one.resources().satisfies_fact(&member, facts.assumptions()));
        assert!(
            CheckedPopulationMemberRewrite::check(
                &function,
                &established,
                &facts,
                &member,
                true,
                &birth,
                &one,
                &facts,
            )
            .is_ok()
        );
        assert!(
            one.checked_population_member_exchange(&member, true, definition, facts.assumptions())
                .is_err()
        );
        let CResource::Composite { name, arguments } = member.resource() else {
            unreachable!()
        };
        let expanded = crate::kernel::functions::expand_composite_resource_fact(
            &ResourceContext::new().unchecked_with_fact(member.clone()),
            &member,
            std::slice::from_ref(definition),
            one.memory(),
            facts.assumptions(),
        )
        .unwrap();
        let opened = one
            .clone()
            .with_resource_context(
                one.resources()
                    .clone()
                    .try_compose_with_facts_delaying_normalization(
                        expanded.facts().iter().cloned(),
                        facts.assumptions(),
                    )
                    .unwrap(),
            )
            .open_population_body(name.clone(), arguments.clone())
            .unwrap();
        CheckedResourceRewrite::check(
            &function,
            &one,
            &facts,
            &member,
            &opened,
            &facts,
            &CheckedCallEvents::default(),
        )
        .unwrap();
        assert!(
            CheckedResourceRewrite::check(
                &function,
                &one,
                &facts,
                &member,
                &opened.clone().with_memory(CMemory::new()),
                &facts,
                &CheckedCallEvents::default(),
            )
            .is_err()
        );
        assert!(
            CheckedResourceRewrite::check(
                &function,
                &one,
                &facts,
                &member,
                &opened
                    .clone()
                    .with_resource_context(established.resources().clone()),
                &facts,
                &CheckedCallEvents::default(),
            )
            .is_err()
        );
        let closed = opened
            .clone()
            .with_resource_context(
                opened
                    .resources()
                    .clone()
                    .without_fact_incrementally(&expanded.facts()[0], facts.assumptions())
                    .unwrap(),
            )
            .close_population_body(name.clone(), arguments.clone())
            .unwrap();
        CheckedResourceRewrite::check(
            &function,
            &opened,
            &facts,
            &member,
            &closed,
            &facts,
            &CheckedCallEvents::default(),
        )
        .unwrap();
        assert_eq!(closed, one);
        let (zero, death) = one
            .checked_population_member_exchange(&member, false, definition, facts.assumptions())
            .unwrap();
        assert!(
            zero.resources()
                .satisfies_fact(&memory, facts.assumptions())
        );
        assert!(
            CheckedPopulationMemberRewrite::check(
                &function, &one, &facts, &member, false, &death, &zero, &facts,
            )
            .is_ok()
        );
        assert!(
            CheckedPopulationMemberRewrite::check(
                &function,
                &established,
                &facts,
                &member,
                true,
                &birth,
                &one.clone()
                    .with_resource_context(established.resources().clone()),
                &facts,
            )
            .is_err()
        );
    }

    #[test]
    fn authority_count_observation_rejects_unchecked_deltas_and_scales() {
        let work = [16usize, 64, 256].map(|size| {
            let (state, authority) = source_state();
            let facts = ProofFacts::default();
            let (state, _) = state
                .checked_population_authority_exchange(&authority, true, facts.assumptions())
                .unwrap();
            let CResource::PopulationAuthority(description) = authority.resource() else {
                unreachable!()
            };
            let member = CResourceFact::own(CResource::Composite {
                name: "reference".into(),
                arguments: description.arguments().to_vec().into(),
            });
            let definition = CCompositeResourceDefinition::new(
                "reference",
                vec![crate::kernel::c_parameter("p", CType::Int32Pointer)],
                None,
                false,
                vec![],
                vec![],
            )
            .with_authorized(true);
            let (mut state, _) = state
                .checked_population_member_exchange(&member, true, &definition, facts.assumptions())
                .unwrap();
            let mut resources = state.resources().clone();
            for index in 0..size {
                state = state.with_local(
                    format!("unrelated_{index}"),
                    crate::kernel::int32(index as u32),
                );
                resources = resources.unchecked_with_fact(CResourceFact::own_token(
                    format!("unrelated_{index}"),
                    vec![],
                ));
            }
            state = state.with_resource_context(resources);
            let function = c_function(
                CType::Void,
                "observe",
                vec![],
                CStatement::Return(CExpression::Value(CValue::Void)),
            )
            .with_composite_resource_definitions(vec![definition]);
            let bound = crate::kernel::api::checked_owned_resource_count_lower_bound(
                &state,
                &member,
                facts.assumptions(),
            )
            .unwrap();
            let after_facts = facts.with_fact(bound);
            let (_, work) = crate::persistent::measure_persistent_work(|| {
                let observation = CheckedResourceObservation::check(
                    &function,
                    &state,
                    &facts,
                    &member,
                    &state,
                    &after_facts,
                    &PersistentOrderedSet::default(),
                    &CheckedCallEvents::default(),
                )
                .unwrap();
                assert!(observation.definition().is_none());
                assert!(
                    observation
                        .advance_checked(&state, &facts, &CheckedCallEvents::default(),)
                        .is_some()
                );
            });
            let forged_facts = after_facts.with_fact(Proposition::Predicate {
                name: "unproved_body_fact".into(),
                arguments: vec![],
            });
            assert!(
                CheckedResourceObservation::check(
                    &function,
                    &state,
                    &facts,
                    &member,
                    &state,
                    &forged_facts,
                    &PersistentOrderedSet::default(),
                    &CheckedCallEvents::default(),
                )
                .is_err()
            );
            let added_member = state.clone().with_resource_context(
                state
                    .resources()
                    .clone()
                    .unchecked_with_fact(CResourceFact::own_token("forged_child".into(), vec![])),
            );
            assert!(
                CheckedResourceObservation::check(
                    &function,
                    &state,
                    &facts,
                    &member,
                    &added_member,
                    &after_facts,
                    &PersistentOrderedSet::default(),
                    &CheckedCallEvents::default(),
                )
                .is_err()
            );
            for missing in [&member, &authority] {
                let missing = state.clone().with_resource_context(
                    state
                        .resources()
                        .clone()
                        .without_fact_incrementally(missing, facts.assumptions())
                        .unwrap(),
                );
                assert!(
                    CheckedResourceObservation::check(
                        &function,
                        &missing,
                        &facts,
                        &member,
                        &missing,
                        &after_facts,
                        &PersistentOrderedSet::default(),
                        &CheckedCallEvents::default(),
                    )
                    .is_err()
                );
            }
            work
        });
        assert!(
            work[0] > 0,
            "count observation must charge checked work: {work:?}"
        );
        assert!(
            work.iter().all(|sample| *sample <= work[0] + 64),
            "count observation scanned unrelated state: {work:?}"
        );
    }

    #[test]
    fn generic_resource_events_cannot_check_under_authority_history() {
        let (before, _) = source_state();
        let selected = CResourceFact::own_composite("reference".into(), Vec::new());
        let facts = ProofFacts::default();
        let function =
            c_function(
                CType::Void,
                "value",
                vec![],
                CStatement::Return(CExpression::Value(CValue::Void)),
            )
            .with_composite_resource_definitions(vec![
                CCompositeResourceDefinition::new("reference", vec![], None, false, vec![], vec![]),
            ]);
        assert!(
            CheckedResourceRewrite::check(
                &function,
                &before,
                &facts,
                &selected,
                &before,
                &facts,
                &CheckedCallEvents::default(),
            )
            .is_err()
        );
        assert!(
            CheckedResourceObservation::check(
                &function,
                &before,
                &facts,
                &selected,
                &before,
                &facts,
                &PersistentOrderedSet::default(),
                &CheckedCallEvents::default(),
            )
            .is_err()
        );
    }

    #[test]
    fn authority_history_refuses_wildcard_count_evaluation() {
        let (state, _) = source_state();
        let count = crate::kernel::SpecExpression::CountedResourceCount {
            name: "reference".into(),
            arguments: vec![None],
        };
        assert_eq!(
            crate::kernel::spec::evaluate_spec_expression_paths_with_bindings(
                &state,
                &count,
                &PureFactContext::new(),
                &std::collections::BTreeMap::new(),
                &mut crate::kernel::ExecutionBudget::beside_live_state(),
            )
            .err(),
            Some(crate::kernel::ExecutionLimit::AuthorityCountNeedsExactPointer),
        );
    }
}

#[cfg(test)]
mod authority_transfer_wrapper_scaling_tests {
    use super::*;
    use crate::kernel::{CResourceAccessMode, CResourceSpec, CType, c_function, int32};

    #[test]
    #[ignore = "nightly: 6s in the parallel gate"]
    fn ordinary_authority_wrapper_checks_only_its_delta() {
        let definition = CCompositeResourceDefinition::new(
            "held",
            vec![],
            None,
            false,
            vec![CResourceSpec::token(
                CResourceAccessMode::Own,
                "member".into(),
                vec![],
                vec![],
            )],
            vec![],
        );
        let function = c_function(
            CType::Void,
            "wrapper_scaling",
            vec![],
            CStatement::Return(CExpression::Value(CValue::Void)),
        )
        .with_composite_resource_definitions(vec![definition]);
        let selected = CResourceFact::own_composite("held".into(), vec![]);
        let child = CResourceFact::own_token("member".into(), vec![]);
        let samples = [64usize, 256, 1024].map(|size| {
            let mut before = CState::new().with_population_creation_tracking();
            let mut facts = ProofFacts::default();
            let mut memory = CMemory::new();
            let mut resources = ResourceContext::new().unchecked_with_fact(child.clone());
            for index in 0..size {
                let unrelated = CResourceFact::own_token(format!("other_{index}"), vec![]);
                resources = resources.unchecked_with_fact(unrelated);
                before = before.with_local(format!("local_{index}"), int32(index as u32));
                memory = memory.with_block(format!("block_{index}"), 4);
                resources =
                    resources.unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
                        Pointer {
                            block: format!("block_{index}").into(),
                            offset: crate::kernel::PointerOffsetTerm::Constant(0),
                        },
                        0.into(),
                        1.into(),
                    )));
                facts = facts.with_fact(Proposition::ConditionIs(
                    crate::kernel::ConditionTerm::Bitvector32Equal(
                        Box::new(Bitvector32Term::Variable(Variable(index as u64 + 100))),
                        Box::new(Bitvector32Term::Constant(index as u32)),
                    ),
                    true,
                ));
            }
            before = before.with_memory(memory).with_resource_context(resources);
            let folded_resources = before
                .resources()
                .clone()
                .without_fact_incrementally(&child, facts.assumptions())
                .unwrap()
                .try_compose_with_facts_delaying_normalization(
                    std::iter::once(selected.clone()),
                    facts.assumptions(),
                )
                .unwrap();
            let folded = before.clone().with_resource_context(folded_resources);
            let unfolded_resources = folded
                .resources()
                .clone()
                .without_fact_incrementally(&selected, facts.assumptions())
                .unwrap()
                .try_compose_with_facts_delaying_normalization(
                    std::iter::once(child.clone()),
                    facts.assumptions(),
                )
                .unwrap();
            let unfolded = folded.clone().with_resource_context(unfolded_resources);
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for (input, output) in [(&before, &folded), (&folded, &unfolded)] {
                    CheckedResourceRewrite::check(
                        &function,
                        input,
                        &facts,
                        &selected,
                        output,
                        &facts,
                        &CheckedCallEvents::default(),
                    )
                    .expect("one wrapper rewrite preserves its unrelated frame");
                }
            });
            let unrelated = CResourceFact::own_token("other_0".into(), vec![]);
            let forged = folded.clone().with_resource_context(
                folded
                    .resources()
                    .clone()
                    .without_fact_incrementally(&unrelated, facts.assumptions())
                    .unwrap(),
            );
            assert!(
                CheckedResourceRewrite::check(
                    &function,
                    &before,
                    &facts,
                    &selected,
                    &forged,
                    &facts,
                    &CheckedCallEvents::default(),
                )
                .is_err(),
                "the unrelated frame must remain authenticated"
            );
            let unrelated_memory = CResourceFact::own_memory(CMemoryRange::new(
                Pointer {
                    block: "block_0".into(),
                    offset: crate::kernel::PointerOffsetTerm::Constant(0),
                },
                0.into(),
                1.into(),
            ));
            for (input, output) in [(&before, &folded), (&folded, &unfolded)] {
                let forged = output.clone().with_resource_context(
                    output
                        .resources()
                        .clone()
                        .without_fact_incrementally(&unrelated_memory, facts.assumptions())
                        .unwrap(),
                );
                assert!(
                    CheckedResourceRewrite::check(
                        &function,
                        input,
                        &facts,
                        &selected,
                        &forged,
                        &facts,
                        &CheckedCallEvents::default(),
                    )
                    .is_err(),
                    "a wrapper exchange cannot remove unrelated memory"
                );
            }
            work
        });
        assert!(
            samples[0] > 0,
            "the measured checker must charge work: {samples:?}"
        );
        assert!(
            samples.windows(2).all(|pair| pair[1] <= pair[0] + 128),
            "wrapper work must grow at most logarithmically with its unrelated frame: {samples:?}"
        );
    }
    #[test]
    fn authority_named_memory_rewrite_preserves_population_ledger() {
        use crate::kernel::{ResourceFieldSchema, ResourceFieldType, ResourceInstance, Variable};
        let schema =
            ResourceFieldSchema::new(vec![("value".into(), ResourceFieldType::C(CType::Int32))])
                .unwrap();
        let instance = ResourceInstance::new(
            Variable(9_850_001),
            "cell".into(),
            vec![].into(),
            schema.clone(),
            vec![int32(7).into()].into(),
        )
        .unwrap();
        let definition = CCompositeResourceDefinition::new(
            "cell",
            vec![],
            None,
            false,
            vec![crate::kernel::CResourceSpec::owned_memory(
                crate::kernel::CMemorySegment {
                    base: CExpression::Value(CValue::pointer(crate::kernel::Pointer::symbolic(
                        Variable(9_850_002),
                    ))),
                    start: CExpression::Value(int32(0)),
                    end: CExpression::Value(int32(1)),
                    element_width: 4,
                    guard: None,
                },
            )],
            vec![],
        )
        .with_instance_schema(Some(schema));
        let function = c_function(
            CType::Int32,
            "test",
            vec![],
            CStatement::Return(CExpression::Value(int32(7))),
        )
        .with_composite_resource_definitions(vec![definition.clone()]);
        let selected = CResourceFact::own(CResource::Instance(instance.clone()));
        let folded = CState::new()
            .with_population_creation_tracking()
            .with_resource_context(ResourceContext::new().unchecked_with_fact(selected.clone()));
        let facts = ProofFacts::default();
        let (open, introduced) = crate::kernel::rewrite_resource_instance(
            &folded,
            &instance,
            &definition,
            facts.assumptions(),
            true,
        )
        .unwrap();
        let open_facts = introduced
            .into_iter()
            .fold(facts.clone(), |facts, fact| facts.with_fact(fact));
        CheckedResourceRewrite::check(
            &function,
            &folded,
            &facts,
            &selected,
            &open,
            &open_facts,
            &CheckedCallEvents::default(),
        )
        .expect("ordinary named memory is a checked representation exchange");
        let forged_facts = open_facts
            .clone()
            .with_fact(Proposition::CMemoryReadDefined {
                memory: open.memory().clone(),
                pointer: crate::kernel::Pointer::symbolic(Variable(9_850_004)),
                value_type: CType::Int32,
            });
        assert!(
            CheckedResourceRewrite::check(
                &function,
                &folded,
                &facts,
                &selected,
                &open,
                &forged_facts,
                &CheckedCallEvents::default(),
            )
            .is_err(),
            "a named exchange cannot invent definedness of an unrelated cell"
        );
        let mut forged = open.clone();
        Arc::make_mut(&mut forged.population_effects).creation = Some(
            folded
                .population_effects
                .creation
                .as_ref()
                .unwrap()
                .created(crate::kernel::PointerBlock::Heap(9_850_003)),
        );
        assert!(
            CheckedResourceRewrite::check(
                &function,
                &folded,
                &facts,
                &selected,
                &forged,
                &open_facts,
                &CheckedCallEvents::default()
            )
            .is_err(),
            "a named memory exchange cannot alter creation or population evidence"
        );
    }
}

#[cfg(test)]
mod wide_range_reader_tests {
    use super::*;
    use crate::kernel::{CMemorySegment, c_uint64_literal};
    // Containment keys keep the domain, interface liveness stays wide, and
    // changed-cell framing dispatches to the native access rule.
    #[test]
    fn wide_interface_and_memory_effect_readers_preserve_the_range_kind() {
        let base = Pointer::symbolic(Variable(984_600));
        let wide = CMemoryRange::new_wide(
            base.clone(),
            Bitvector32Term::UInt64Constant(0),
            Bitvector32Term::UInt64Constant(1 << 33),
            4,
        );
        let resource = CResourceFact::own_memory(wide.clone());
        let segment = CMemorySegment::new(
            CExpression::Value(CValue::pointer(base.clone())),
            c_uint64_literal(0),
            c_uint64_literal(1 << 33),
        );
        let spec = CResourceSpec::owned_memory(segment);
        let before = CMemory::new().with_block(base.block.clone(), 4);
        let state = CState::new().with_memory(before.clone());
        assert!(matches!(
            interface_resource_intrinsic_fact(&spec, &resource, &state),
            Some(Proposition::CMemoryLoadable { wide: true, .. })
        ));
        let containment = Proposition::CResourceContains {
            parent: Box::new(CResource::Memory(wide.clone())),
            child: Box::new(CResource::Memory(wide.clone())),
        };
        let key = resource_containment_key(&containment).unwrap();
        assert_eq!(key.4, crate::kernel::RangeIndexKind::UInt64);
        let after = before.clone().store(base, CValue::Int32(7u32.into()));
        assert!(memory_diff_is_covered_by_ranges(
            &before,
            &after,
            &[wide],
            &PureFactContext::new()
        ));
    }
}

#[cfg(test)]
mod checked_callee_dependency_tests {
    use super::*;

    /// Reusing a wide summary must visit its syntax once, rather than once
    /// per occurrence. Both the call count and reuse count grow here.
    #[test]
    fn checked_callee_summary_reuse_scales_with_input_not_product() {
        let mut previous = None;
        for size in [16, 64, 256, 1024] {
            let mut body = CStatement::Skip;
            for index in 0..size {
                body = CStatement::Seq(
                    Arc::new(body),
                    Arc::new(crate::kernel::c_call(format!("callee_{index}"), vec![])),
                );
            }
            let summary = crate::kernel::c_while(crate::kernel::c_int32_literal(1), vec![], body);
            let events = (0..size)
                .map(|_| {
                    CheckedExecutionEvent::Statement(Theorem::new(
                        Proposition::CStatementVerifies {
                            state: Box::new(CState::new()),
                            statement: Box::new(summary.clone()),
                            outcome: CStatementOutcome::Normal(Box::new(CState::new())),
                        },
                    ))
                })
                .collect::<Vec<_>>();
            let (calls, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut calls = std::collections::BTreeSet::new();
                collect_checked_callees(&events, &mut Default::default(), &mut calls);
                calls
            });
            eprintln!("summary reuse size={size}, dependency work={work}");
            assert_eq!(calls.len(), size);
            assert!(calls.contains(&format!("callee_{}", size - 1)));
            if let Some(before) = previous {
                assert!(
                    work <= 5 * before,
                    "superlinear summary reuse: {before} -> {work}"
                );
            }
            previous = Some(work);
        }
    }
}
