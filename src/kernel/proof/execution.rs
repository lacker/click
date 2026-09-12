//! Semantic execution-frontier state owned by the checked proof object.
//!
//! A frontier identifies the exact C region and next statement a checked
//! execution proof must advance. It contains no Surface Click syntax,
//! certificate builder, diagnostic cursor, or smart-planning state.

use super::{PersistentOrderedSet, PersistentSequence, ProofFacts, SharedValue, SharedVec};
use crate::kernel::{
    Bitvector32Term, CCompositeResourceDefinition, CConditionOutcome, CExpression, CFunction,
    CFunctionExecutionCandidates, CMemory, CMemoryRange, CResource, CResourceFact, CResourceSpec,
    CState, CStatement, CStatementOutcome, CValue, CVerifiedLoopRule, ExecutionBudget,
    ExecutionLimit, ExecutionPureFact, Pointer, Proposition, PureFactContext, ResourceContext,
    SpecProposition, Theorem, Variable,
};
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
}

impl LoopControlExit {
    /// Whether this path leaves the loop rather than returning to its head.
    pub(crate) fn is_exit(self) -> bool {
        matches!(self, Self::Break)
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
    Branch(CheckedExecutionBranch),
    ProofCase(CheckedProofCaseArm),
    ResourceObservation(CheckedResourceObservation),
    ResourceRewrite(CheckedResourceRewrite),
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
    instance: Option<crate::kernel::ResourceInstance>,
    selected_children: Option<Arc<[(String, Variable)]>>,
    load_equalities: Vec<crate::kernel::CheckedLoadEquality>,
    delta_proofs: Arc<Vec<CheckedResourceDeltaProof>>,
}

/// Whether `after` differs from `before` only by cells that name their own
/// load: each added cell holds the canonical form of the load of that very
/// pointer at `before`. Adding one is definitional — it records what the
/// snapshot already said about the cell — so a rewrite that names the cells it
/// exposes stays checkable without a second state comparison rule. Bounded by
/// the cell count, with no assumption consulted and nothing searched.
fn memory_only_adds_named_cells(
    before: &crate::kernel::CMemory,
    after: &crate::kernel::CMemory,
) -> bool {
    let mut rebased = after.clone();
    rebased.cells = before.cells.clone();
    if rebased != *before {
        return false;
    }
    let base = crate::kernel::intern_c_memory(before.clone());
    after
        .cells
        .iter()
        .all(|(pointer, value)| match before.cells.get(pointer) {
            Some(existing) => existing == value,
            None => {
                let load = crate::kernel::canonical_form_of_load(base.clone(), pointer.clone());
                cell_value_is_exactly_load(value, &load, pointer)
            }
        })
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
            target.block == pointer.block
                && matches!(
                    &target.offset,
                    crate::kernel::PointerOffsetTerm::Int32Scaled { value, .. }
                        if value.as_ref() == load
                )
        }
        _ => false,
    }
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
    ) -> Result<Self, &'static str> {
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
    fn check_with_children(
        function: &CFunction,
        before_state: &CState,
        before_facts: &ProofFacts,
        selected: &CResourceFact,
        after_state: &CState,
        after_facts: &ProofFacts,
        call_events: &CheckedCallEvents,
        selected_children: Option<Arc<[(String, Variable)]>>,
    ) -> Result<Self, &'static str> {
        let load_equality_capture =
            crate::kernel::CheckedLoadEqualityCapture::start_with_call_events(call_events);
        let assumptions = before_facts.assumptions();
        if let CResource::Instance(instance) = selected.resource() {
            let definition = function
                .composite_resource_definition(instance.name())
                .ok_or("instance definition is not registered on the function")?;
            let unfold = before_state
                .resources()
                .owned_instance(instance.identity())
                .is_some();
            let (expected, allowed) = crate::kernel::rewrite_resource_instance_selecting_children(
                before_state,
                instance,
                definition,
                function.composite_resource_definitions(),
                assumptions,
                unfold,
                selected_children.as_deref(),
            )?;
            let mut unchanged = after_state.clone();
            unchanged.resources = before_state.resources.clone();
            if unchanged != *before_state {
                // An unfold names the cells it exposes, which materializes
                // them in the snapshot so the body's facts and a later C read
                // of one of those cells are one load variable
                // (`docs/internals/canonicalization.md`). Adding such a cell
                // is the only memory change a resource rewrite may make, and
                // each added cell must hold the canonical load form of its own
                // pointer at the pre-rewrite snapshot. That is a definitional
                // identity, checked here per added cell with no search.
                if !unfold
                    || !memory_only_adds_named_cells(&before_state.memory, &after_state.memory)
                {
                    return Err("instance rewrite changed an unchecked part of the state");
                }
                unchanged.memory = before_state.memory.clone();
                if unchanged != *before_state {
                    return Err("instance rewrite changed an unchecked part of the state");
                }
            }
            if !expected
                .resources
                .same_exchange_from(&after_state.resources, &before_state.resources)
            {
                return Err("instance rewrite changed an unchecked part of the state");
            }
            let introduced = after_facts
                .introduced_since(before_facts)
                .ok_or("instance rewrite facts do not descend from their input")?;
            let allowed = allowed
                .into_iter()
                .collect::<std::collections::BTreeSet<_>>();
            if introduced.iter().any(|fact| !allowed.contains(fact)) {
                return Err("instance rewrite introduced an unchecked fact");
            }
            return Ok(Self {
                before_state: before_state.clone(),
                after_state: after_state.clone(),
                before_facts: before_facts.clone(),
                after_facts: after_facts.clone(),
                definition: definition.clone(),
                instance: Some(instance.clone()),
                selected_children,
                load_equalities: load_equality_capture.finish(),
                delta_proofs: Arc::new(Vec::new()),
            });
        }
        if before_state
            .resources()
            .directly_supporting_fact(selected, assumptions)
            .is_none()
            && after_state
                .resources()
                .directly_supporting_fact(selected, after_facts.assumptions())
                .is_none()
        {
            return Err("the rewritten composite is absent from both resource representations");
        }
        let crate::kernel::CResource::Composite { name, .. } = selected.resource() else {
            return Err("resource rewrite evidence requires a composite resource");
        };
        let definition = function
            .composite_resource_definitions()
            .iter()
            .find(|definition| definition.name() == name)
            .cloned()
            .ok_or("the rewritten composite definition is not registered on the function")?;

        let mut concrete_after = after_state.clone();
        concrete_after.set_memory(before_state.memory.clone());
        concrete_after.resources = before_state.resources.clone();
        concrete_after.counted_populations = before_state.counted_populations.clone();
        if concrete_after != *before_state
            || !crate::kernel::api::contract_certification::c_memories_definitionally_equal(
                before_state.memory(),
                after_state.memory(),
                assumptions,
            )
            || !crate::kernel::api::counted_populations_definitionally_equal(
                before_state,
                after_state,
                function.composite_resource_definitions(),
                assumptions,
            )
        {
            return Err("resource rewrite changed more than a definitional representation");
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
            let singleton = ResourceContext::new().unchecked_with_fact(authority.clone());
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
            return Err("resource rewrite does not match the selected composite definition");
        }

        let introduced = after_facts
            .introduced_since(before_facts)
            .ok_or("resource rewrite facts do not descend from the input facts")?;
        let temporary = ResourceContext::new().unchecked_with_fact(selected.clone());
        let expanded = crate::kernel::functions::expand_composite_resource_fact(
            &temporary,
            selected,
            function.composite_resource_definitions(),
            after_state.memory(),
            assumptions,
        )
        .ok_or("the rewritten composite body could not be instantiated")?;
        let children = expanded
            .facts()
            .iter()
            .filter(|fact| *fact != selected)
            .cloned()
            .collect::<Vec<_>>();
        let child_context = ResourceContext::new().unchecked_with_facts(children);
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
                .ok_or("resource rewrite produced an unchecked pure-fact delta")?;
            delta_proofs.push(proof);
        }

        let load_equalities = load_equality_capture.finish();
        Ok(Self {
            before_state: before_state.clone(),
            after_state: after_state.clone(),
            before_facts: before_facts.clone(),
            after_facts: after_facts.clone(),
            definition,
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
    if let (
        Proposition::CResourceContains {
            child: CResource::Memory(source_range),
            ..
        },
        Proposition::CResourceContains {
            child: CResource::Memory(goal_range),
            ..
        },
    ) = (source, goal)
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

type ResourceContainmentKey = (CResource, Bitvector32Term, Bitvector32Term, u32);

fn resource_containment_key(proposition: &Proposition) -> Option<ResourceContainmentKey> {
    let Proposition::CResourceContains {
        parent,
        child: CResource::Memory(range),
    } = proposition
    else {
        return None;
    };
    Some((
        parent.clone(),
        range.start().clone(),
        range.end().clone(),
        range.element_width(),
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
    definition: CCompositeResourceDefinition,
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

        let mut concrete_after = after_state.clone();
        concrete_after.set_memory(before_state.memory.clone());
        concrete_after.resources = before_state.resources.clone();
        if concrete_after != *before_state
            || !crate::kernel::api::contract_certification::c_memories_definitionally_equal(
                before_state.memory(),
                after_state.memory(),
                assumptions,
            )
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
            let temporary =
                ResourceContext::new().unchecked_with_fact(definition_authority.clone());
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
        let child_context = ResourceContext::new().unchecked_with_facts(children);
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
            definition,
            load_equalities,
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

fn resource_composition_is_supported_by(
    proposition: &Proposition,
    available: &ResourceContext,
    assumptions: &PureFactContext,
) -> bool {
    let Proposition::CResourceComposition(required) = proposition else {
        return false;
    };
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
    function: CFunction,
    arguments: Vec<CExpression>,
    entry_state: CState,
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
    ) -> Option<Arc<Self>> {
        let entry_state = crate::kernel::c_function_entry_state(caller_state, function, arguments)?;
        if &entry_state != expected_entry_state {
            return None;
        }
        let mut entry = Self {
            caller_state: caller_state.clone(),
            function: function.clone(),
            arguments: arguments.to_vec(),
            entry_state,
            assumptions,
            relation_facts: None,
        };
        entry.relation_facts = entry.resource_relation_assumptions(&entry.assumptions);
        Some(Arc::new(entry))
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
        if &self.function != function || self.arguments != arguments {
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
        (&self.function == function && self.arguments == arguments).then_some(&self.entry_state)
    }

    pub(crate) fn resource_relation_assumptions(
        &self,
        assumptions: &PureFactContext,
    ) -> Option<PureFactContext> {
        let (_, propositions) =
            crate::kernel::functions::expand_all_composite_resource_facts_and_propositions(
                self.entry_state.resources(),
                self.function.composite_resource_definitions(),
                self.entry_state.memory(),
                assumptions,
            )?;
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
    /// Exact contradictions checked under root premises plus that case only.
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
        let case = self.case_facts.get(index)?;
        if !self.root_facts.with_fact(case.clone()).contradicts(&fact) {
            return None;
        }
        let mut successor = self.clone();
        // Coverage from the old partition must not discharge this new one.
        successor.identity = Arc::new(());
        successor.excluded[index] = Some(fact);
        Some(Arc::new(successor))
    }

    pub(crate) fn case_fact(&self, index: usize) -> Option<&Proposition> {
        self.case_facts.get(index)
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
        Some(Arc::new(Self {
            identity: Arc::new(()),
            root_facts: root_facts.clone(),
            case_facts: vec![then_fact, else_fact],
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
                    introduced == vec![self.partition.case_facts[self.arm_index].clone()]
                        || introduced.is_empty()
                            && self
                                .partition
                                .root_facts
                                .contains(&self.partition.case_facts[self.arm_index])
                })
    }
}

/// One exhaustive nonterminal C `if`, checked against its exact source arms
/// and retained as a nested execution-evidence node.
#[derive(Clone)]
pub(crate) struct CheckedExecutionBranch {
    split: CheckedBranchSplit,
    arms: [CheckedExecutionBranchArm; 2],
    joined_state: CState,
    interface_successor_facts: Option<ProofFacts>,
    interface_execution_facts: Vec<ExecutionPureFact>,
    interface_effect_facts: Vec<ExecutionPureFact>,
    interface_resource_definitions: Option<Vec<crate::kernel::CCompositeResourceDefinition>>,
    // Keep the actual selected lowering results, not just their boolean verdicts.
    // Every retained judgment has a completed local proof.
    interface_lowerings: Arc<Vec<[CheckedInterfaceLowering; 3]>>,
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
        arm_effect_facts: [&[ExecutionPureFact]; 2],
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
            interface_execution_facts: Vec::new(),
            interface_effect_facts,
            interface_resource_definitions: None,
            interface_lowerings: Arc::new(Vec::new()),
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
        arm_effect_facts: [&[ExecutionPureFact]; 2],
        joined_state: &CState,
        successor_facts: &ProofFacts,
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
        let abstract_then = crate::kernel::abstract_c_state_for_interface_join_across(
            arms[0].reached_state(),
            &sibling_states,
            stable_join_locals,
        )
        .map_err(|_| "the then interface state could not be abstracted")?;
        let abstract_else = crate::kernel::abstract_c_state_for_interface_join_across(
            arms[1].reached_state(),
            &sibling_states,
            stable_join_locals,
        )
        .map_err(|_| "the else interface state could not be abstracted")?;
        if abstract_then != abstract_else {
            return Err("the interface arms do not have one deterministic abstraction");
        }
        if joined_state
            .clone()
            .with_resource_context(ResourceContext::new())
            != abstract_then
        {
            return Err("the interface successor is not the checked arm abstraction");
        }
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
            if let Some(proposition) = interface_resource_intrinsic_fact(spec, &fact, joined_state)
            {
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
                let Some(next) = remaining
                    .clone()
                    .without_facts(std::slice::from_ref(required), facts.assumptions())
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
        let expected_resources = common_resources
            .try_compose_into_valid_context_delaying_normalization(
                successor_interface_resources.iter().cloned(),
                successor_facts.assumptions(),
            )
            .map_err(|_| "the interface resources do not form a valid successor context")?
            .normalized_around_facts(
                &successor_interface_resources,
                successor_facts.assumptions(),
            );
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

        let reference_state = parent
            .frontier
            .execution_start_state
            .as_ref()
            .unwrap_or(&split.state);
        let concrete_access = [0, 1].map(|index| {
            InterfaceReadPremises::new(
                interface_resource_specs
                    .iter()
                    .zip(&arm_interface_resources[index])
                    .filter_map(|(spec, resource)| {
                        interface_resource_intrinsic_fact(
                            spec,
                            resource,
                            arms[index].reached_state(),
                        )
                    }),
            )
        });
        let successor_access =
            InterfaceReadPremises::new(successor_interface_resource_facts.iter().cloned());
        let mut interface_lowerings = Vec::with_capacity(interface_specs.len());
        for spec in interface_specs {
            let concrete = |index: usize| {
                CheckedInterfaceLowering::check(
                    spec,
                    arms[index].reached_state(),
                    reference_state,
                    arm_facts[index],
                    &concrete_access[index],
                )
                .ok_or("an interface fact is not established by both concrete arms")
            };
            let then_lowering = concrete(0)?;
            let else_lowering = concrete(1)?;
            let successor = CheckedInterfaceLowering::check(
                spec,
                joined_state,
                reference_state,
                successor_facts,
                &successor_access,
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
            let interface_resource_fact = ResourceContext::new()
                .unchecked_with_facts(successor_interface_resources.clone())
                .observable_facts_assuming_valid(successor_facts.assumptions())
                .contains(fact)
                || successor_interface_resource_facts.contains(fact);
            if !common_arm_fact && !interface_fact && !interface_resource_fact {
                return Err("the interface successor contains an unchecked new fact");
            }
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
        let interface_effect_facts = checked_interface_effect_facts(
            &split.state,
            joined_state,
            arms,
            arm_facts,
            arm_effect_facts,
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
        })
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

    pub(crate) fn interface_execution_facts(&self) -> &[ExecutionPureFact] {
        &self.interface_execution_facts
    }

    pub(crate) fn interface_effect_facts(&self) -> &[ExecutionPureFact] {
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

/// Collapses two alternative, kernel-issued arm effect chains into the one
/// transition published by an interface join. Arm effects are alternatives,
/// never sequential facts: concatenating them would describe an impossible
/// execution whenever both start at the split memory.
fn arm_effect_deltas_are_exact(
    parent: &ExecutionProofCore,
    arms: [&ExecutionProofCore; 2],
    supplied: [&[ExecutionPureFact]; 2],
) -> bool {
    arms.iter().zip(supplied).all(|(arm, supplied)| {
        arm.effect_facts
            .suffix_since(&parent.effect_facts)
            .is_some_and(|expected| expected == supplied)
    })
}

fn memory_diff_is_covered_by_pointers(
    before: &CMemory,
    after: &CMemory,
    changed: &[Pointer],
    assumptions: &PureFactContext,
    fact: &ExecutionPureFact,
) -> bool {
    let erased_cells_are_certified_store_bookkeeping =
        fact.certified_store_data().is_some_and(|store| {
            store.before == *before
                && store.after == *after
                && changed
                    .iter()
                    .any(|changed_pointer| changed_pointer == &store.pointer)
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
            changed.iter().any(|changed_pointer| {
                !crate::kernel::reasoning::pointers_proven_distinct_for_memory_resolution(
                    &diff_pointer,
                    changed_pointer,
                    assumptions,
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
    let erased_cells_are_call_havoc_bookkeeping =
        after.matches_call_memory_havoc_result(before, mutable_ranges, assumptions);
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
                assumptions.pointer_access_in_range(
                    &diff_pointer,
                    range.element_width(),
                    range.base(),
                    range.start(),
                    range.end(),
                    range.element_width(),
                )
            })
        })
}

fn checked_interface_effect_facts(
    split_state: &CState,
    joined_state: &CState,
    arms: [&ExecutionProofCore; 2],
    arm_facts: [&ProofFacts; 2],
    arm_effect_facts: [&[ExecutionPureFact]; 2],
) -> Result<Vec<ExecutionPureFact>, &'static str> {
    let mut pointers = Vec::new();
    let mut ranges = Vec::new();
    let mut heap_frees = [Vec::new(), Vec::new()];
    for arm_index in 0..2 {
        let assumptions = arm_facts[arm_index].assumptions();
        let mut memory = split_state.memory().clone();
        for fact in arm_effect_facts[arm_index] {
            match fact.proposition() {
                Proposition::CMemoryMutatesOnly {
                    before,
                    after,
                    pointers: changed,
                } => {
                    if !fact.is_certified() {
                        return Err("an interface arm contains an uncertified memory effect");
                    }
                    if !crate::kernel::api::contract_certification::c_memories_definitionally_equal(
                        &memory,
                        before,
                        assumptions,
                    ) {
                        return Err(
                            "an interface arm effect chain does not start at its current memory",
                        );
                    }
                    if !memory_diff_is_covered_by_pointers(
                        before,
                        after,
                        changed,
                        assumptions,
                        fact,
                    ) {
                        return Err(
                            "an interface arm memory effect does not cover its memory diff",
                        );
                    }
                    memory = after.clone();
                    for pointer in changed {
                        if !pointers.contains(pointer) {
                            pointers.push(pointer.clone());
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
                    if !crate::kernel::api::contract_certification::c_memories_definitionally_equal(
                        &memory,
                        before,
                        assumptions,
                    ) {
                        return Err(
                            "an interface arm effect summary does not start at its current memory",
                        );
                    }
                    if !memory_diff_is_covered_by_ranges(before, after, mutable_ranges, assumptions)
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
                    if !crate::kernel::api::contract_certification::c_memories_definitionally_equal(
                        &memory,
                        before,
                        assumptions,
                    ) {
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
        if !crate::kernel::api::contract_certification::c_memories_definitionally_equal(
            &memory,
            arms[arm_index].state.memory(),
            assumptions,
        ) {
            return Err("an interface arm effect chain does not reach its recorded memory");
        }
    }

    if pointers.is_empty() && ranges.is_empty() {
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
            return Ok(facts);
        }
        return Ok(common_non_memory_effect_facts(arm_effect_facts));
    }
    let proposition = if ranges.is_empty() {
        Proposition::CMemoryMutatesOnly {
            before: split_state.memory().clone(),
            after: joined_state.memory().clone(),
            pointers,
        }
    } else {
        for pointer in pointers {
            let range = CMemoryRange::new(
                pointer,
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
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
    let mut facts = vec![ExecutionPureFact::certified(proposition)];
    facts.extend(common_non_memory_effect_facts(arm_effect_facts));
    Ok(facts)
}

fn conditional_heap_frees(
    arm_effect_facts: [&[ExecutionPureFact]; 2],
) -> [Vec<(Pointer, Bitvector32Term)>; 2] {
    std::array::from_fn(|arm_index| {
        arm_effect_facts[arm_index]
            .iter()
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
                &ResourceContext::new().unchecked_with_fact(resource.clone()),
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
    arm_effect_facts: [&[ExecutionPureFact]; 2],
) -> Vec<ExecutionPureFact> {
    arm_effect_facts[0]
        .iter()
        .filter(|fact| {
            fact.is_certified()
                && !matches!(
                    fact.proposition(),
                    Proposition::CMemoryMutatesOnly { .. }
                        | Proposition::CMemoryEffectSummary { .. }
                        | Proposition::CHeapAllocationFreed { .. }
                )
                && arm_effect_facts[1].contains(fact)
        })
        .cloned()
        .collect()
}

fn interface_spec_paths(
    spec: &SpecProposition,
    state: &CState,
    reference_state: &CState,
) -> Option<Vec<crate::kernel::spec::SpecPropositionPath>> {
    crate::kernel::spec::lower_spec_proposition_at_state_with_loop_entry(
        state,
        spec,
        Some(reference_state),
        &PureFactContext::new(),
        &mut ExecutionBudget::new(),
    )
    .ok()
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
        &mut ExecutionBudget::new(),
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
    let element_width = segment.element_width();
    Some(Proposition::CMemoryLoadable {
        memory: state.memory().clone(),
        base: range
            .base()
            .offset_by_elements(range.start().clone(), element_width),
        bytes: crate::kernel::Bitvector32Term::multiply(
            crate::kernel::Bitvector32Term::subtract(range.end().clone(), range.start().clone()),
            crate::kernel::Bitvector32Term::Constant(element_width),
        ),
    })
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
        let paths = interface_spec_paths(spec, state, reference_state)?;
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
            let mut proofs = vec![prove(&path.proposition, None)?];
            for fact in &path.facts {
                let definition = CheckedInterfaceLoadDefinition::check(fact.proposition());
                proofs.push(prove(fact.proposition(), definition.as_ref())?);
            }
            for obligation in &path.obligations {
                proofs.push(prove(obligation.proposition(), None)?);
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
        },
        Proposition::CMemoryLoadable {
            memory: source_memory,
            base: source_base,
            bytes: source_bytes,
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
        let (Bitvector32Term::Variable(variable), Bitvector32Term::MemoryLoad(memory, pointer)) =
            (left.as_ref(), right.as_ref())
        else {
            return None;
        };
        let (defined_memory, defined_pointer) =
            crate::kernel::registered_load_for_variable(variable)?;
        (&defined_memory == memory && &defined_pointer == pointer.as_ref()).then(|| Self {
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
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<crate::kernel::ProofObligation>,
    theorem: Theorem,
}

impl CheckedBranchPath {
    pub(crate) fn outcome(&self) -> &CConditionOutcome {
        &self.outcome
    }

    pub(crate) fn facts(&self) -> &[ExecutionPureFact] {
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
                if proved_state != &state || proved_condition != &condition {
                    return None;
                }
                Some(CheckedBranchPath {
                    outcome: outcome.clone(),
                    facts: path.facts().to_vec(),
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
    pub(crate) next_statement_index: usize,
    pub(crate) continuations: PersistentSequence<ProofExecutionContinuation>,
    /// Whether this frontier executes inside one loop-body region, directly
    /// or through a bounded branch arm of it. A `break` or `continue` here
    /// belongs to that loop, which no continuation of this frontier holds:
    /// the enclosing loop rule consumes it at the region boundary.
    pub(crate) in_loop_body: bool,
    /// How this path reached the loop body's boundary, once it has.
    pub(crate) loop_control: LoopControlExit,
}

#[derive(Clone)]
pub(crate) struct ProofExecutionContinuation {
    pub(crate) remaining: Option<Arc<CStatement>>,
    pub(crate) next_statement_index: usize,
    /// The source statement index immediately after the loop. A `break`
    /// consumes the loop continuation and resumes here; `continue` resumes
    /// at `next_statement_index`, the loop head itself.
    pub(crate) loop_exit_statement_index: usize,
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
    /// Every variable `initial_match_scope` mentions, built once and shared by
    /// every branch forked from this region. A constructor witness introduced
    /// anywhere in the region must avoid these; everything the kernel has
    /// issued since is below `next_kernel_variable`, which the same freshness
    /// probe checks without a second scan.
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
    pub(crate) frontier: ExecutionFrontier,
    pub(crate) effect_facts: SharedVec<ExecutionPureFact>,
    /// One append-only evidence trace per operational outcome represented by
    /// this frontier. Ordinary in-flight execution has one trace; a single C
    /// operation with several return outcomes can complete several traces at
    /// once. Forked proofs share every unchanged trace prefix.
    pub(crate) execution_evidence: SharedVec<PersistentSequence<CheckedExecutionEvent>>,
    /// Post-return exchanges indexed by the selected outcome. Forking a
    /// focused outcome must not copy or modify its sibling traces.
    return_resource_rewrites:
        crate::persistent::PersistentMap<usize, PersistentSequence<CheckedExecutionEvent>>,
    /// Events on the current unjoined path. A branch join restores its
    /// parent's set; finalization collects all retained arm events by walking
    /// the output trace once.
    checked_call_events: CheckedCallEvents,
    pub(crate) function_entry: Option<Arc<CheckedFunctionEntry>>,
    pub(crate) frontier_loop_rules: PersistentSequence<CVerifiedLoopRule>,
    pub(crate) execution_abstraction: bool,
    pub(crate) next_path_choice: usize,
    pub(crate) concrete_loop_execution: bool,
    /// Kernel theorems whose conclusions justify the facts a resource
    /// observation introduces (its count and quantity witnesses).
    pub(crate) function_entry_derivations: PersistentOrderedSet<Theorem>,
    pub(crate) region_invariants_close_requested: bool,
    /// Complete lowerings prepared for this exact execution and premise store.
    pub(crate) checked_invariant_lowerings: Option<Arc<CheckedLoopInvariantLowerings>>,
    pub(crate) next_opaque_call: u64,
    pub(crate) next_kernel_variable: u64,
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
    pub(super) ranking_measures: Vec<crate::kernel::CExpression>,
    pub(super) facts: super::ProofFacts,
    pub(super) effects: SharedVec<ExecutionPureFact>,
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
        | CStatementOutcome::Return { state, .. } => state.memory(),
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
            CheckedExecutionEvent::Statement(_)
            | CheckedExecutionEvent::Condition(_)
            | CheckedExecutionEvent::Context(_)
            | CheckedExecutionEvent::ProofCase(_)
            | CheckedExecutionEvent::ResourceObservation(_)
            | CheckedExecutionEvent::ResourceRewrite(_) => {}
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

fn checked_evidence_premises_hold(theorem: &Theorem, facts: &ProofFacts) -> bool {
    let mut proposition = theorem.proposition();
    while let Proposition::Implies(premise, body) = proposition {
        if !facts.assumptions().proves_exact(premise) && !ground_comparison_premise_holds(premise) {
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

fn checked_statement_event(
    theorem: &Theorem,
    facts: &ProofFacts,
    state: &CState,
    statement: &CStatement,
) -> Option<CStatementOutcome> {
    if !checked_evidence_premises_hold(theorem, facts) {
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
    (proved_state == state && proved_statement == statement).then(|| outcome.clone())
}

fn checked_condition_event(
    theorem: &Theorem,
    facts: &ProofFacts,
    state: &CState,
    statement: CStatement,
    tail: Option<CStatement>,
) -> Option<Option<CStatement>> {
    if !checked_evidence_premises_hold(theorem, facts) {
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
    if proved_state != state {
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
    for event in events {
        if let Some(CStatementOutcome::Return {
            state: returned, ..
        }) = &mut completed
            && let CheckedExecutionEvent::ResourceRewrite(rewrite) = event
        {
            current_facts = rewrite.advance_checked(returned, &current_facts, &call_events)?;
            *returned = rewrite.after_state.clone();
            continue;
        }
        if completed.is_some() {
            return None;
        }
        match event {
            CheckedExecutionEvent::ProofCase(arm) => {
                if !arm.is_valid() {
                    return None;
                }
                current_facts = arm.facts.clone();
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
            // The retained context of the preceding theorem; the arm check
            // above already holds the arm's own facts.
            CheckedExecutionEvent::Context(_) => continue,
            CheckedExecutionEvent::Call(call) => {
                call_events.insert(call);
                continue;
            }
            CheckedExecutionEvent::Statement(_)
            | CheckedExecutionEvent::Condition(_)
            | CheckedExecutionEvent::Branch(_) => {}
        }
        let source = remaining.take()?;
        let (next_statement, tail) = split_checked_evidence_statement(source);
        match event {
            CheckedExecutionEvent::Statement(theorem) => {
                match checked_statement_event(theorem, &current_facts, &state, &next_statement)? {
                    CStatementOutcome::Normal(next_state) => {
                        state = next_state;
                        remaining = tail;
                    }
                    outcome @ (CStatementOutcome::Break(_)
                    | CStatementOutcome::Continue(_)
                    | CStatementOutcome::Return { .. }
                    | CStatementOutcome::VerificationDiverges) => {
                        if tail.is_some() {
                            return None;
                        }
                        completed = Some(outcome);
                    }
                    CStatementOutcome::UndefinedBehavior(_)
                    | CStatementOutcome::RuntimeError(_) => return None,
                }
            }
            CheckedExecutionEvent::Condition(theorem) => {
                remaining =
                    checked_condition_event(theorem, &current_facts, &state, next_statement, tail)?;
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
            CheckedExecutionEvent::ProofCase(_) | CheckedExecutionEvent::Context(_) => {
                unreachable!("handled before source advance")
            }
            CheckedExecutionEvent::Call(_) => unreachable!("handled before source advance"),
            CheckedExecutionEvent::ResourceObservation(_) => {
                unreachable!("handled before source advance")
            }
            CheckedExecutionEvent::ResourceRewrite(_) => {
                unreachable!("handled before source advance")
            }
        }
    }
    Some(CheckedEvidenceProgress {
        state,
        remaining,
        completed,
    })
}

/// A completed trace's completing outcome, the context its completing
/// theorem was proved under (every fact the proof had established on the
/// path), and the interface facts of the branches it joined. A trace that
/// does not complete, continues past its completion, or completes in an
/// error outcome yields nothing.
fn trace_completion(
    function: &CFunction,
    events: &[CheckedExecutionEvent],
    assumptions: &PureFactContext,
    checked_void_fallthrough: bool,
) -> Result<(CStatementOutcome, PureFactContext, Vec<ExecutionPureFact>), &'static str> {
    if !events_use_the_function_definitions(function, events) {
        return Err("a retained resource event was checked under other composite definitions");
    }
    let mut completed: Option<(CStatementOutcome, PureFactContext)> = None;
    let mut fallthrough = None;
    let mut interface_execution_facts: Vec<ExecutionPureFact> = Vec::new();
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
                    CStatementOutcome::Break(_) | CStatementOutcome::Continue(_) => {}
                    CStatementOutcome::Return { .. } | CStatementOutcome::VerificationDiverges => {
                        // The path completes under the context its final
                        // theorem was proved under, recorded right after it.
                        let executed_under = match events.get(index + 1) {
                            Some(CheckedExecutionEvent::Context(context)) => context.clone(),
                            _ => {
                                crate::kernel::api::proof_evidence_assumptions(theorem, assumptions)
                            }
                        };
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
            CheckedExecutionEvent::ResourceRewrite(rewrite) => {
                fallthrough = None;
                if let Some((outcome, executed_under)) = &mut completed {
                    let CStatementOutcome::Return { state, .. } = outcome else {
                        return Err("resource rewriting requires a returned state");
                    };
                    if *state != rewrite.before_state {
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
                        let (checked_state, _) =
                            crate::kernel::rewrite_resource_instance_selecting_children(
                                state,
                                instance,
                                &rewrite.definition,
                                function.composite_resource_definitions(),
                                executed_under,
                                false,
                                rewrite.selected_children.as_deref(),
                            )
                            .map_err(
                                |_| "return fold body is not justified on this execution path",
                            )?;
                        if !checked_state
                            .resources
                            .same_exchange_from(&rewrite.after_state.resources, &state.resources)
                            || !checked_state.instance_field_scope.same_exchange_from(
                                &rewrite.after_state.instance_field_scope,
                                &state.instance_field_scope,
                            )
                        {
                            return Err(
                                "return fold does not match this path's checked resource exchange",
                            );
                        }
                    }
                    *state = rewrite.after_state.clone();
                    // Folding introduces no pure facts. In particular, do not
                    // publish a proof snapshot's entire assumption context as
                    // facts of this path.
                }
            }
            CheckedExecutionEvent::Condition(_) | CheckedExecutionEvent::ResourceObservation(_) => {
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
            CheckedExecutionEvent::Context(_) | CheckedExecutionEvent::Call(_) => {}
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
    let definitions = function.composite_resource_definitions();
    events.iter().all(|event| match event {
        CheckedExecutionEvent::ResourceObservation(observation) => {
            definitions.contains(observation.definition())
        }
        CheckedExecutionEvent::ResourceRewrite(rewrite) => {
            definitions.contains(rewrite.definition())
        }
        CheckedExecutionEvent::Branch(branch) => {
            branch.matches_interface_resource_definitions(function)
                && (0..2).all(|arm_index| {
                    events_use_the_function_definitions(function, branch.arm_events(arm_index))
                })
        }
        CheckedExecutionEvent::Statement(_)
        | CheckedExecutionEvent::Call(_)
        | CheckedExecutionEvent::Condition(_)
        | CheckedExecutionEvent::Context(_)
        | CheckedExecutionEvent::ProofCase(_) => true,
    })
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
            CheckedExecutionEvent::Context(_) => continue,
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
            CheckedExecutionEvent::ResourceObservation(_)
            | CheckedExecutionEvent::ResourceRewrite(_) => {
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
            initial_match_reserved: Arc::new(std::sync::OnceLock::new()),
            state,
            evidence_state: None,
            evidence_completed: false,
            evidence_source: None,
            frontier,
            effect_facts: Default::default(),
            execution_evidence: vec![PersistentSequence::default()].into(),
            return_resource_rewrites: Default::default(),
            checked_call_events: CheckedCallEvents::new(),
            function_entry: None,
            frontier_loop_rules: Default::default(),
            execution_abstraction: false,
            next_path_choice: 0,
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

    pub(crate) fn record_checked_function_entry(
        &mut self,
        function: &CFunction,
        arguments: &[CExpression],
        expected_entry_state: &CState,
        assumptions: PureFactContext,
    ) -> bool {
        if !self.frontier.is_at_function_entry()
            || self.execution_evidence.len() != 1
            || !self.execution_evidence[0].is_empty()
        {
            return false;
        }
        let Some(entry) = CheckedFunctionEntry::check(
            &self.state,
            function,
            arguments,
            expected_entry_state,
            assumptions,
        ) else {
            return false;
        };
        self.function_entry = Some(entry);
        true
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
        execution_facts: &[ExecutionPureFact],
        obligations: &[crate::kernel::ProofObligation],
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
        let call_events = statement_call_havoc_views(&theorem)
            .into_iter()
            .map(|view| self.checked_call_events.new_event(view))
            .collect::<Vec<_>>();
        for trace in &mut *self.execution_evidence {
            trace.push(CheckedExecutionEvent::Statement(theorem.clone()));
            trace.push(CheckedExecutionEvent::Context(context.clone()));
            for call in &call_events {
                trace.push(CheckedExecutionEvent::Call(call.clone()));
            }
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
        match outcome {
            CStatementOutcome::Normal(next_state) => self.evidence_state = Some(next_state),
            CStatementOutcome::Return { state, .. } => {
                self.evidence_state = Some(state);
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
                self.evidence_state = Some(state);
                self.evidence_completed = true;
            }
            CStatementOutcome::Break(state) => {
                let source_after = self.advance_loop_control(false, None)?;
                self.evidence_source = source_after;
                self.evidence_state = Some(state);
                self.evidence_completed = false;
            }
            CStatementOutcome::Continue(state) => {
                let source_after = self.advance_loop_control(true, source_after)?;
                self.evidence_source = source_after;
                self.evidence_state = Some(state);
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
        let (next_statement_index, source_after) = if continue_statement {
            let frontier_source = loop_source.clone();
            // The validated tail still contains the rest of the source body
            // before the loop head. Preserve the exact loop head (and any
            // enclosing-loop suffix after it) rather than treating that body
            // tail as the next frontier statement.
            let loop_head = split_shared_source(&loop_source).0;
            let mut source = validated_source_after;
            let source_after =
                loop_head_source(source.take(), &loop_head).or(Some(loop_source.clone()));
            self.frontier.position = FrontierPosition::StatementEntry {
                remaining: frontier_source,
            };
            (continuation.next_statement_index, source_after)
        } else {
            let (_, tail) = split_shared_source(&loop_source);
            (continuation.loop_exit_statement_index, tail)
        };
        self.frontier.next_statement_index = next_statement_index;
        if !continue_statement {
            self.frontier.position = match &source_after {
                Some(remaining) => FrontierPosition::StatementEntry {
                    remaining: remaining.clone(),
                },
                None => FrontierPosition::RegionBoundary,
            };
        }
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
            &[ExecutionPureFact],
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

    /// The state the retained evidence has reached, or the core's state
    /// before any evidence is recorded.
    pub(crate) fn reached_state(&self) -> &CState {
        self.evidence_state.as_ref().unwrap_or(&self.state)
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
        &self,
        function: &CFunction,
        arguments: &[CExpression],
        theorem: &Theorem,
        context: &PureFactContext,
        execution_facts: &[ExecutionPureFact],
        obligations: &[crate::kernel::ProofObligation],
    ) -> Result<(CStatementOutcome, Option<Arc<CStatement>>), EvidenceRefusal> {
        let running_state = self.running_state(function, arguments)?;
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
        // The source left after the theorem: a `Skip` theorem consumes a
        // `Skip` at the head of the source when there is one and otherwise
        // nothing; another theorem consumes its statement after the
        // `Skip`s before it.
        let source_after = if matches!(proved_statement, CStatement::Skip) {
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
        } else if matches!(proved_statement, CStatement::Seq(..))
            && self
                .current_source(function)
                .is_some_and(|source| source == proved_statement)
        {
            // A checked sequence may cover the entire remaining source. This
            // is exact structural identity, not a search through the suffix.
            // In particular an executes proof checks call + return together.
            None
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
                    body,
                } if !matches!(proved_statement, CStatement::While { .. }) => {
                    let (body_head, body_tail) = split_shared_source(body);
                    if !statements_have_same_source(&body_head, proved_statement) {
                        return Err(EvidenceRefusal {
                            reason: "statement evidence does not prove the frontier's next source statement",
                            expected: Some(next.into_owned()),
                            proved: Some(proved_statement.clone()),
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
                    proved: Some(proved_statement.clone()),
                    premise: None,
                });
            }
            do_while_initial_body.or(tail)
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
        let Some((next, tail)) = self.next_source_statement_and_tail(function) else {
            return Err(
                "condition evidence was recorded with no source statement remaining".into(),
            );
        };
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
            reached =
                crate::kernel::resolve_pending_heap_allocations(&reached, &theorem_assumptions);
        }
        Ok((reached, source_after))
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
        execution_facts: &[ExecutionPureFact],
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
        if !states_match {
            return Err("evidence does not start from the running state".into());
        }
        let mut retained_execution_facts = execution_facts.to_vec();
        for fact in self.effect_facts.iter() {
            if !retained_execution_facts.contains(fact) {
                retained_execution_facts.push(fact.clone());
            }
        }
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
        for trace in &mut *self.execution_evidence {
            trace.push(CheckedExecutionEvent::Condition(theorem.clone()));
            trace.push(CheckedExecutionEvent::Context(context.clone()));
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
        for trace in &mut *self.execution_evidence {
            trace.push(CheckedExecutionEvent::ProofCase(arm.clone()));
        }
        true
    }

    /// Every variable the region this proof started in already mentions,
    /// built once and shared by every branch forked from it. This is the
    /// frontier-independent half of a constructor witness's freshness: the
    /// other half is `next_kernel_variable`, which bounds everything the
    /// kernel has issued since, so no later frontier rescans the state.
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
                        state: entry.caller_state.clone(),
                        function: entry.function.clone(),
                        arguments: entry.arguments.clone(),
                        outcome: CFunctionOutcome::Return {
                            value: CValue::Void,
                            state: entry.entry_state.clone(),
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
    /// kernel has issued since lies below `next_kernel_variable`, so the probe
    /// is one comparison rather than a rescan of the current state. The
    /// environment, the scrutinee, and the persistent fact index are queried
    /// per candidate as before.
    pub(crate) fn algebraic_case_partition(
        &self,
        facts: &ProofFacts,
        value: &crate::kernel::AlgebraicTerm,
        environment: &crate::kernel::CExecutionEnvironment,
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
        let reserved = self.initial_match_reserved_variables();
        let issued = self.next_kernel_variable;
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
                    if candidate.0 >= issued
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
        Some((
            Arc::new(CheckedProofCasePartition {
                identity: Arc::new(()),
                root_facts: facts.clone(),
                excluded: vec![None; case_facts.len()],
                case_facts,
                witness_scope: Some(self.state.clone()),
            }),
            bindings,
            next,
        ))
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
        self.execution_evidence = traces.into();
        Ok(())
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
        if self.frontier.is_at_function_entry() {
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
        for trace in &mut *self.execution_evidence {
            trace.push(CheckedExecutionEvent::ResourceObservation(
                observation.clone(),
            ));
        }
        Ok(())
    }

    pub(crate) fn record_resource_rewrite(
        &mut self,
        function: &CFunction,
        arguments: &[CExpression],
        before_facts: &ProofFacts,
        selected: &CResourceFact,
        after_state: &CState,
        after_facts: &ProofFacts,
    ) -> Result<(), &'static str> {
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
    ) -> Result<(), &'static str> {
        if self.evidence_completed {
            return Err("a resource rewrite was recorded after the trace completed");
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
        if self.frontier.is_at_function_entry() {
            rewrite.before_state =
                crate::kernel::c_function_entry_state(&rewrite.before_state, function, arguments)
                    .ok_or("resource rewrite could not bind the function entry state")?;
            rewrite.after_state =
                crate::kernel::c_function_entry_state(&rewrite.after_state, function, arguments)
                    .ok_or("resource rewrite could not bind its successor entry state")?;
        }
        if self.evidence_state.is_some() {
            self.evidence_state = Some(rewrite.after_state.clone());
        }
        for trace in &mut *self.execution_evidence {
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
    ) -> Result<(), &'static str> {
        self.record_return_resource_rewrite_with_children(
            function,
            path_index,
            before_facts,
            selected,
            after_facts,
            None,
        )
    }

    pub(crate) fn record_return_resource_rewrite_with_children(
        &mut self,
        function: &CFunction,
        path_index: usize,
        before_facts: &ProofFacts,
        selected: &CResourceFact,
        after_facts: &ProofFacts,
        selected_children: Option<Arc<[(String, Variable)]>>,
    ) -> Result<(), &'static str> {
        if !self.evidence_completed {
            return Err("return resource rewrite requires completed execution");
        }
        let CResource::Instance(instance) = selected.resource() else {
            return Err("return rewrite requires a named instance");
        };
        let definition = function
            .composite_resource_definition(instance.name())
            .ok_or("instance definition is not registered on the function")?;
        let mut trace = self
            .return_resource_rewrites
            .get(&path_index)
            .or_else(|| self.execution_evidence.get(path_index))
            .cloned()
            .ok_or("return resource rewrite selected an unknown path")?;
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
                        return Err("return resource rewrite requires a returning path");
                    };
                    break state.clone();
                }
                Some(
                    CheckedExecutionEvent::Context(_)
                    | CheckedExecutionEvent::Call(_)
                    | CheckedExecutionEvent::ProofCase(_),
                ) => {}
                _ => return Err("return resource rewrite has no completing theorem"),
            }
        };
        // Compute the exchange in the retained C-body state, not the
        // caller-side projection used by postcondition expressions.
        let (after_state, _) = crate::kernel::rewrite_resource_instance_selecting_children(
            &before_state,
            instance,
            definition,
            function.composite_resource_definitions(),
            before_facts.assumptions(),
            false,
            selected_children.as_deref(),
        )?;
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
        arm_effect_facts: [&[ExecutionPureFact]; 2],
    ) -> Result<Vec<ExecutionPureFact>, &'static str> {
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
        let interface_effect_facts = branch.interface_effect_facts().to_vec();
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
        arm_effect_facts: [&[ExecutionPureFact]; 2],
        joined_state: &CState,
        successor_facts: &ProofFacts,
    ) -> Result<Vec<ExecutionPureFact>, &'static str> {
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
        )?;
        let interface_effect_facts = branch.interface_effect_facts().to_vec();
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

    /// The checked whole-function execution a completed proof yields: one
    /// path per retained trace, each its trace's completing theorem under
    /// the contract's exit rule, stating everything the proof established
    /// on the path. Every step of every trace was checked when it was
    /// recorded, so this composes the traces and walks nothing.
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
        let (paths, has_checked_entry) =
            self.checked_execution_paths(candidates, checked_function, &assumptions, None)?;
        Ok(crate::kernel::CCheckedFunctionExecution {
            state: candidates.state().clone(),
            function: checked_function.clone(),
            arguments: candidates.arguments().to_vec(),
            assumptions,
            environment,
            execution_semantics,
            mode,
            execution: crate::kernel::SymbolicCExecution { paths, limit: None },
            entry_representation_origin: has_checked_entry
                .then_some(self.function_entry.as_ref())
                .flatten()
                .map(|entry| entry.caller_state().clone()),
            checked_call_events: self.retained_call_events(),
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
    ) -> Result<(Vec<crate::kernel::SymbolicCExecutionPath>, bool), &'static str> {
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
        // rebases onto the published caller state. A proof that bound loop
        // clauses into its function publishes a different function and
        // completes as a proof without a checked entry.
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
            // Population materialization is part of the contract-entry
            // transition. Without the kernel-issued entry artifact, the
            // transition theorems alone cannot authorize that ghost state.
            let entry_state = crate::kernel::c_function_entry_state(
                candidates.state(),
                function,
                candidates.arguments(),
            )
            .ok_or("the published arguments do not bind at entry")?;
            if entry_state.counted_populations().next().is_some() {
                return Err("population materialization at entry needs a checked function entry");
            }
        }
        let mut paths = Vec::with_capacity(range.len());
        for path_index in range {
            let candidate = &candidates.paths()[path_index];
            let trace = self
                .return_resource_rewrites
                .get(&path_index)
                .unwrap_or(&self.execution_evidence[path_index]);
            let events = trace.to_vec();
            let (completed, statement_assumptions, interface_execution_facts) = trace_completion(
                function,
                &events,
                assumptions,
                function.return_type() == crate::kernel::CType::Void
                    && self.evidence_source.is_none()
                    && self.frontier.region == ExecutionRegionKind::Function,
            )?;
            // Publication precedes post-return logical folds. Check its
            // original C outcome against the trace before those exchanges;
            // the final exit rule below still checks the folded ownership.
            let publication_end = events
                .iter()
                .rposition(|event| !matches!(event, CheckedExecutionEvent::ResourceRewrite(_)))
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
            if &outcome != candidate.outcome() {
                return Err("a published path outcome is not its trace's outcome");
            }
            // The published outcome is the body's. The path's theorem states
            // the function's: the body's after the contract's exit rule, the
            // same resource transfer or population transition an independent
            // execution applies at return. A contract the body violates at
            // exit ends the path in that runtime error.
            let (outcome, obligations) = match crate::kernel::functions::contract_exit_outcome(
                if has_checked_entry {
                    self.function_entry
                        .as_ref()
                        .expect("checked entry exists")
                        .caller_state()
                } else {
                    candidates.state()
                },
                function,
                candidates.arguments(),
                completed,
                obligations,
                &statement_assumptions,
                &mut ExecutionBudget::default(),
            ) {
                Ok(Ok(exit)) => exit,
                Ok(Err(error)) => (
                    crate::kernel::CFunctionOutcome::RuntimeError(error),
                    candidate.obligations().to_vec(),
                ),
                Err(_) => return Err("the contract's exit rule hit an execution limit"),
            };
            let proposition = Proposition::CFunctionVerifies {
                state: candidates.state().clone(),
                function: function.clone(),
                arguments: candidates.arguments().to_vec(),
                outcome,
            };
            // The path states everything the proof established on it: the
            // candidate's execution facts, the interface facts of joined
            // branches, and the facts of the context its final theorem was
            // proved under (a `have` in one arm that both arms share, say).
            let mut facts = candidate.facts().to_vec();
            for fact in interface_execution_facts.into_iter().chain(
                statement_assumptions
                    .pure_facts()
                    .into_iter()
                    .map(ExecutionPureFact::new),
            ) {
                if !facts
                    .iter()
                    .any(|retained| retained.proposition() == fact.proposition())
                {
                    facts.push(fact);
                }
            }
            let theorem = Theorem::new(crate::kernel::reasoning::wrap_proof_facts(
                proposition,
                assumptions,
                &facts,
                candidate.obligations(),
            ));
            paths.push(crate::kernel::SymbolicCExecutionPath {
                assumptions: assumptions.clone(),
                facts,
                effect_facts: candidate.effect_facts().to_vec(),
                obligations,
                theorem,
            });
        }
        Ok((paths, has_checked_entry))
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

    fn constructor_partition_fixture(
        width: usize,
    ) -> (ExecutionProofCore, crate::kernel::AlgebraicTerm) {
        use crate::kernel::{
            AlgebraicSchemas, AlgebraicTerm, AlgebraicTermNode, AlgebraicType, AlgebraicValueType,
            AlgebraicVariantType,
        };
        let variants: Arc<[AlgebraicVariantType]> = (0..width)
            .map(|index| AlgebraicVariantType {
                name: format!("C{index}"),
                fields: vec![AlgebraicValueType::C(CType::Int32)],
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
        assert!(core.record_checked_function_entry(&function, &[], &state, PureFactContext::new()));
        (core, value)
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
        assert!(old_arm.record_proof_case_arm(partition, 0, root.with_fact(live.clone())));
        assert!(!crate::kernel::api::proof_case_partitions_are_exhaustive(
            &old_arm.execution_evidence
        ));
        let mut live_arm = core;
        assert!(live_arm.record_proof_case_arm(excluded, 0, root.with_fact(live)));
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
            .algebraic_case_partition(&root, &value, &env, 4_000_000, 65_536)
            .unwrap();
        assert!(fields.iter().flatten().all(|(var, _)| var.0 > occupied.0));
        let facts = root.with_fact(partition.case_fact(0).unwrap().clone());
        let (_, later, _) = core
            .algebraic_case_partition(&facts, &value, &env, next, 65_536)
            .unwrap();
        assert!(later.iter().flatten().all(|(var, _)| var.0 >= next));
        assert!(
            core.algebraic_case_partition(&root, &value, &env, u64::MAX, 1)
                .is_none()
        );
        assert!(
            core.algebraic_case_partition(&root, &value, &env, 0, 0)
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
            .algebraic_case_partition(&root, &value, &env, 4_000_000, 65_536)
            .expect("a loop-body frontier issues its partition");
        assert!(fields.iter().flatten().all(|(var, _)| *var != occupied));

        let mut issued = core.clone();
        issued.next_kernel_variable = 4_200_000;
        let (_, fields, _) = issued
            .algebraic_case_partition(&root, &value, &env, 4_000_000, 65_536)
            .expect("a partition skips the issued range");
        assert!(fields.iter().flatten().all(|(var, _)| var.0 >= 4_200_000));
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
                4_000_000,
                65_536,
            )
            .unwrap();
        assert!(fields.iter().flatten().all(|(var, _)| var.0 > 4_065_536));
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
                    .algebraic_case_partition(&facts, &value, &environment, next, 65_536)
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
                    state: open.clone(),
                    statement,
                    outcome: CStatementOutcome::Return {
                        value: int32(0),
                        state: open,
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
                    state: state.clone(),
                    statement: statement.clone(),
                    outcome: CStatementOutcome::Return {
                        value: int32(7),
                        state,
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
            assert_eq!(
                outcome,
                CStatementOutcome::Return {
                    value: int32(7),
                    state: folded.clone()
                }
            );
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
            state: state.clone(),
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
            ));
        let theorem = Theorem::new(Proposition::CStatementVerifies {
            state: before.clone(),
            statement: CStatement::Skip,
            outcome: CStatementOutcome::Normal(after),
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
    fn checked_function_entry_rebase_rejects_semantic_memory_and_population_changes() {
        let function = c_function(
            CType::Void,
            "checked_entry",
            Vec::new(),
            CStatement::Return(CExpression::Value(CValue::Void)),
        )
        .with_composite_resource_definitions(vec![
            CCompositeResourceDefinition::counted_population(
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
            .with_counted_population("item", Vec::new().into(), Bitvector32Term::Constant(1));
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

        let changed_population =
            caller.with_counted_population("item", Vec::new().into(), Bitvector32Term::Constant(2));
        assert!(
            checked
                .entry_state_for(&changed_population, &function, &[], &assumptions)
                .is_none(),
            "a resource rebase must not authorize a changed counted population"
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
        let freed = live.clone().free_heap_block(&external).unwrap();
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
            parent: CResourceFact::own_composite("cell".into(), Vec::new())
                .resource()
                .clone(),
            child: CResource::Memory(crate::kernel::CMemoryRange::new(
                pointer(i),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(end),
            )),
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
            parent: CResourceFact::own_composite("other".into(), Vec::new())
                .resource()
                .clone(),
            child: CResource::Memory(crate::kernel::CMemoryRange::new(
                pointer(21),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )),
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
            };
            let goal = Proposition::CMemoryLoadable {
                memory: memory.store(pointer.clone(), int32(7)),
                base: pointer.clone(),
                bytes: Bitvector32Term::Variable(Variable(42)),
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
                .contains(observation.definition()),
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
                        )
                        .expect("the then arm should abstract"),
                        crate::kernel::abstract_c_state_for_interface_join_across(
                            &else_state,
                            &siblings,
                            &stable_locals,
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
                .store(left_pointer.clone(), int32(1)),
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
            pointers: vec![left_pointer.clone()],
        });
        let right_effect = ExecutionPureFact::certified(Proposition::CMemoryMutatesOnly {
            before: before.memory().clone(),
            after: right.memory().clone(),
            pointers: vec![right_pointer.clone()],
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
        )
        .expect("alternative memories should have one deterministic abstraction");
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
            summaries.as_slice(),
            [fact] if matches!(
                fact.proposition(),
                Proposition::CMemoryMutatesOnly { before: effect_before, after, pointers }
                    if effect_before == before.memory()
                        && after == joined.memory()
                        && pointers == &vec![left_pointer, right_pointer]
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
            pointers: vec![pointer],
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
            pointers: vec![declared_pointer.clone()],
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
                .free_heap_block(&allocation_base)
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
        )
        .expect("the conditional heap states should abstract");
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
                    facts: Vec::new(),
                    obligations: Vec::new(),
                    theorem: then_theorem.clone(),
                },
                CheckedBranchPath {
                    outcome: CConditionOutcome::Value(false),
                    facts: Vec::new(),
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
                    facts: Vec::new(),
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

    #[test]
    fn interface_lowering_retains_generated_facts_and_read_obligations() {
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
            right: load,
        };
        let path = interface_spec_paths(&spec, &state, &state)
            .unwrap()
            .remove(0);
        assert!(
            !path.facts.is_empty(),
            "retain the load-variable definition, not just the asserted equality"
        );
        assert!(
            !path.obligations.is_empty(),
            "reflexivity does not establish read safety"
        );
        let mut facts = ProofFacts::default().with_fact(path.proposition.clone());
        for fact in &path.facts {
            facts = facts.with_fact(fact.proposition().clone());
        }
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
        let variable = crate::kernel::eval::load_variable_for_cell(&memory, &pointer);
        let equation = |variable, memory, pointer| {
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(
                    Box::new(Bitvector32Term::Variable(variable)),
                    Box::new(Bitvector32Term::MemoryLoad(memory, Box::new(pointer))),
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
                    facts: Vec::new(),
                    obligations: Vec::new(),
                    theorem: then_theorem.clone(),
                },
                CheckedBranchPath {
                    outcome: CConditionOutcome::Value(false),
                    facts: Vec::new(),
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
        let checked_fact = interface_spec_paths(&spec, &state, &state)
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
            )
            .is_err(),
            "a resource absent from both arms must not gain interface authority"
        );
    }
}
