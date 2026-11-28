//! Semantic execution-frontier state owned by the checked proof object.
//!
//! A frontier identifies the exact C region and next statement a checked
//! execution proof must advance. It contains no Surface Click syntax,
//! certificate builder, diagnostic cursor, or smart-planning state.

mod return_producer;
pub(crate) use return_producer::CheckedReturnSeed;

use super::{PersistentOrderedSet, PersistentSequence, PureFactStore, SharedValue};
use crate::kernel::population_authority::storage_creation::{
    CheckedPopulationAuthorityExchange, CheckedPopulationMemberExchange,
};
use crate::kernel::{
    Address, CompositeResourceDefinition, ConditionOutcome, ExecutionBudget, ExecutionLimit,
    ExecutionPureFact, ExecutionState, FunctionExecutionCandidates, FunctionOutcome, MemoryRange,
    OldConditionTerm, OldMachineTerm, ProgramExpression, ProgramFunction, ProgramStatement,
    ProgramValue, ProofObligation, Proposition, PureFactContext, Resource, ResourceContext,
    ResourceFact, ResourceSpec, RuntimeError, SpecProposition, StatementOutcome, SymbolicMemory,
    Theorem, Variable, VerifiedLoopRule,
};
use crate::kernel::{BindingName, InstanceId};
use crate::kernel::{ExecutionFactSource, ExecutionFacts};
use crate::kernel::{LoadKind, StoredExecutionValue};
use crate::persistent::PersistentSet;
use std::collections::{BTreeMap, HashMap};
use std::ops::{Deref, DerefMut};
use std::sync::Arc;

#[cfg(test)]
thread_local! {
    static CHECKED_PATH_EFFECT_ADMISSIONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
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
    /// A checked forward `goto` leaves the loop for a function label.
    Jump(crate::kernel::ControlTargetId),
    /// The loop's own test is false: the path leaves the loop there.
    TestFalse,
}

impl LoopControlExit {
    /// Whether this path leaves the loop rather than returning to its head.
    pub(crate) fn is_exit(self) -> bool {
        matches!(self, Self::Break | Self::Jump(_) | Self::TestFalse)
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
    /// Source navigation issued by entering a checked loop phase. It changes
    /// neither the symbolic state nor the path's facts.
    LoopEntry {
        source_after: Arc<ProgramStatement>,
    },
    /// One opaque call occurrence introduced by the preceding checked
    /// statement. Its registered states are exact recomputed views of that
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
    Context(Box<PureFactContext>),
    /// How many memory effects the statement just recorded added to the
    /// proof's effect list. The recorder that pushes the statement appends
    /// those effects itself, so a later join reads a statement's effects off
    /// the list by count instead of matching memories to find them.
    StatementEffects(usize),
    Branch(Box<CheckedExecutionBranch>),
    ProofCase(Box<CheckedProofCaseArm>),
    /// Every live arm of one logical partition, rejoined at one program
    /// point and one state. What follows it is checked once.
    ProofCaseJoin(Box<CheckedProofCaseJoin>),
    ResourceObservation(Box<CheckedResourceObservation>),
    AutomaticLifetimeEnd(Box<CheckedAutomaticLifetimeEnd>),
    ViewRelease(Box<CheckedViewRelease>),
    ResourceRewrite(Box<CheckedResourceRewrite>),
    ReturnProposition(Box<CheckedReturnProposition>),
    PopulationAuthorityRewrite(Box<CheckedPopulationAuthorityRewrite>),
    PopulationMemberRewrite(Box<CheckedPopulationMemberRewrite>),
    /// One checked operation on iterated guarded ownership. Like a lifetime end, it changes only the resource context
    /// and is re-derived from its input state when the trace is checked.
    IteratedStep(CheckedIteratedStep),
    /// One application of a user-defined tactic: the verified rule of a
    /// procedure whose body runs no code, applied with no C statement. It
    /// changes the resource context and adds the rule's `ensures` facts.
    TacticApplication(Box<CheckedTacticApplication>),
    /// What the kernel established along the path a completing statement
    /// just ended, recorded right after its effects.
    CompletedContext(Arc<CheckedPathContext>),
}

/// Append-only evidence with the states its producers most recently constructed.
/// Cloning or extending a path never searches its history for an endpoint.
#[derive(Clone, Default)]
pub(crate) struct ExecutionEvidence {
    events: PersistentSequence<CheckedExecutionEvent>,
    origin: Option<Arc<StatementOutcome>>,
    retained: Option<Arc<ExecutionState>>,
    presented: Option<Arc<ExecutionState>>,
}

impl Deref for ExecutionEvidence {
    type Target = PersistentSequence<CheckedExecutionEvent>;
    fn deref(&self) -> &Self::Target {
        &self.events
    }
}

impl ExecutionEvidence {
    pub(crate) fn push(&mut self, event: CheckedExecutionEvent) {
        match &event {
            CheckedExecutionEvent::Statement(theorem) => {
                if let Proposition::ProgramStatementVerifies { outcome, .. } =
                    checked_evidence_conclusion(theorem)
                {
                    self.origin = Some(Arc::new(outcome.clone()));
                    self.retained = match outcome {
                        StatementOutcome::Normal(state)
                        | StatementOutcome::Return { state, .. }
                        | StatementOutcome::Throw { state, .. }
                        | StatementOutcome::LoopTestFalse(state)
                        | StatementOutcome::Break(state)
                        | StatementOutcome::Continue(state)
                        | StatementOutcome::Jump { state, .. } => Some(Arc::new(*state.clone())),
                        _ => None,
                    };
                    self.presented = None;
                }
            }
            CheckedExecutionEvent::ViewRelease(release) => {
                self.retained = Some(Arc::new(release.after_state.clone()));
            }
            CheckedExecutionEvent::AutomaticLifetimeEnd(end) => {
                self.retained = Some(Arc::new(end.after_state.clone()));
            }
            CheckedExecutionEvent::ResourceRewrite(rewrite) => {
                self.retained = Some(Arc::new(rewrite.after_state.clone()));
                self.presented = rewrite
                    .return_observation
                    .as_ref()
                    .map(|observation| Arc::new(observation.after.clone()))
                    .or_else(|| {
                        rewrite
                            .return_presentation
                            .as_ref()
                            .map(|presentation| Arc::new(presentation.rewrite.after_state.clone()))
                    });
            }
            CheckedExecutionEvent::TacticApplication(application) => {
                if let Some(effect) = &application.return_effect {
                    self.retained = Some(Arc::new(application.after_state.clone()));
                    self.presented = Some(effect.presented.clone());
                }
            }
            _ => {}
        }
        self.events.push(event);
    }

    fn retained_state(&self) -> Result<&ExecutionState, String> {
        let _timing = crate::instrumentation::OperationTiming::new(
            "fold",
            "resource fold",
            "return fold: recover state",
        );
        crate::instrumentation::record_deterministic_work(1);
        self.retained
            .as_deref()
            .ok_or_else(|| "return resource rewrite has no retained state".into())
    }
}

/// Publication of a completing statement, retaining its selected fact delta.
/// The combined stream is still the complete candidate presentation. The delta
/// is what its producer added beyond the context already retained on the trace.
#[derive(Clone)]
pub(crate) struct CompletedExecutionFacts {
    pub(in crate::kernel) facts: ExecutionFacts,
    pub(in crate::kernel) additional: Option<ExecutionFacts>,
}

impl CompletedExecutionFacts {
    pub(crate) fn from_facts(facts: ExecutionFacts) -> Self {
        Self {
            facts,
            additional: None,
        }
    }

    pub(crate) fn push(&mut self, fact: ExecutionPureFact) {
        self.facts.push(fact.clone());
        if let Some(additional) = &mut self.additional {
            additional.push(fact);
        }
    }

    pub(crate) fn into_facts(self) -> ExecutionFacts {
        self.facts
    }
}

/// What the kernel established along one open trace: every fact of each
/// context recorded on it, every case fact it admitted, and every effect it
/// retained. It is extended at each recorded transition by what that
/// transition adds, so completing a path reads it instead of rebuilding a
/// context from the path's whole history, which forks share.
///
/// Kernel facts name the values and states they relate, so a fact
/// recorded earlier on a path still holds at its end. A recorded context
/// that drops or changes a fact, or changes its reasoning policy or resource
/// compositions, which a fact projection does not show, restarts the
/// context from that recorded context. A restart folds the trace's case
/// facts and effects lazily: once as many transitions have recorded since,
/// or when the path completes, so a path whose heap operations or
/// calls restart it at every step does not refold its history each time.
#[derive(Clone)]
pub(crate) struct CheckedPathContext {
    /// The last context recorded on the trace.
    recorded: PureFactContext,
    facts: PureFactContext,
    /// How many of the trace's case facts and effects `facts` holds.
    cases: usize,
    effects: usize,
    /// While a restart's fold is deferred, the transitions recorded since
    /// it, the restarting one included; `None` once `facts` holds every case
    /// fact and effect the trace has.
    lagging: Option<usize>,
    /// The trace's case facts, whose objects a completed candidate's fact
    /// stream begins with when it was published from this trace.
    case_facts: ExecutionFacts,
}

/// `facts`, which holds every fact of `previous`, extended by what `next`
/// adds to it. `None` when `next` drops or changes a fact of `previous`,
/// differs in what its fact projection does not show, or adds more than
/// `budget` facts: a context recorded after a join or an abstraction need
/// not extend the arm's last one, and a restart leaves only the budget to
/// fold.
fn path_context_extended_by(
    facts: &PureFactContext,
    previous: &PureFactContext,
    next: &PureFactContext,
    budget: usize,
) -> Option<PureFactContext> {
    // A prepared statement retains open requirements for the driver;
    // a branch decision may discharge them immediately. That choice only
    // controls obligation reporting, so both use the same admitted facts.
    let policy_delta =
        previous.reasoning_policy.fingerprint() ^ next.reasoning_policy.fingerprint();
    let obligation_policy =
        crate::kernel::ReasoningPolicy::RETAIN_REQUIRED_OBLIGATIONS.fingerprint();
    if policy_delta & !obligation_policy != 0
        || !previous
            .resource_compositions
            .shares_root_with(&next.resource_compositions)
    {
        return None;
    }
    // A walk that gives up has visited at most `budget` changes, which the
    // restart it chooses spares; a walk that succeeds is charged per change.
    let mut added = Vec::new();
    for change in previous
        .execution_fact_projection
        .diff(&next.execution_fact_projection)
    {
        let imbl::ordmap::DiffItem::Add(_, fact) = change else {
            return None;
        };
        if added.len() == budget {
            return None;
        }
        added.push(fact);
    }
    crate::instrumentation::record_deterministic_work(added.len());
    let mut facts = facts.clone().with_reasoning_policy_of(next);
    for fact in added {
        facts = facts.assume_execution_pure_fact(fact);
    }
    Some(facts)
}

/// A kernel-published return, shared by all logical proofs on that path.
#[derive(Clone)]
struct CheckedReturnContext {
    origin: StatementOutcome,
    published: FunctionOutcome,
    facts: ExecutionFacts,
}

impl CheckedReturnContext {
    fn from_candidate(
        origin: StatementOutcome,
        candidate: &crate::kernel::FunctionExecutionCandidate,
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
    base: PureFactStore,
    context: Arc<CheckedReturnContext>,
}

/// The selected return producer's constructed path and publication, ready
/// for ordinary contract closing without replaying its C history.
pub(crate) struct CheckedReturnPath {
    path: crate::kernel::SymbolicExecutionPath,
    publication: Arc<crate::kernel::PublishedFunctionOutcome>,
}

impl CheckedReturnPath {
    pub(crate) fn publication(&self) -> &Arc<crate::kernel::PublishedFunctionOutcome> {
        &self.publication
    }
    pub(crate) fn path(&self) -> &crate::kernel::SymbolicExecutionPath {
        &self.path
    }
}

impl crate::kernel::CheckedFunctionExecution {
    pub(crate) fn published_outcome(
        &self,
        index: usize,
    ) -> &Arc<crate::kernel::PublishedFunctionOutcome> {
        &self.published_outcomes[index]
    }
    pub(crate) fn open_outcome(&self, index: usize) -> Option<super::OutcomeProofCore> {
        self.published_outcome(index).open_core()
    }
}

/// Why [`ExecutionProofCore::checked_return_path`] refused a path: the
/// kernel's reason and, when a return proof assumed a fact the path does not
/// justify, that fact, for the diagnostic to name.
pub(crate) struct ReturnPathRefusal {
    pub(crate) reason: &'static str,
    pub(crate) unjustified_fact: Option<Proposition>,
}

impl CheckedReturnProposition {
    fn check(
        proof: super::CheckedProposition,
        base: &PureFactStore,
        context: Arc<CheckedReturnContext>,
    ) -> Result<Self, String> {
        let FunctionOutcome::Return { value, state } = &context.published else {
            return Err("return proof requires a published return".into());
        };
        let outcome = proof.outcome().ok_or("return proof has no outcome")?;
        // As for checked function propositions, resource representation may
        // change during the proof. The program state and result may not.
        if outcome.is_exceptional
            || value != &outcome.result
            || outcome.state.locals() != state.locals()
            || outcome.state.aggregate_destination != state.aggregate_destination
            || !crate::kernel::api::contract_certification::memories_definitionally_equal(
                outcome.state.memory(),
                state.memory(),
                proof.root_assumptions().assumptions(),
            )
        {
            return Err("return proof has a different program state".into());
        }
        Ok(Self {
            proof,
            base: base.clone(),
            context,
        })
    }
}

/// A verified tactic's proposed state change, retained until its call-site
/// obligations have been discharged.
#[derive(Clone)]
struct PreparedTacticApplication {
    name: String,
    before_state: ExecutionState,
    after_state: ExecutionState,
    return_path: Option<(usize, Vec<Proposition>)>,
}

/// A tactic application admitted to the execution trace after its obligations
/// were proved at the original frontier.
#[derive(Clone)]
pub(crate) struct CheckedTacticApplication {
    name: String,
    before_state: ExecutionState,
    after_state: ExecutionState,
    return_effect: Option<ReturnTacticEffect>,
}

#[derive(Clone)]
struct ReturnTacticEffect {
    presented: Arc<ExecutionState>,
    facts: Vec<Proposition>,
}

impl CheckedTacticApplication {
    pub(crate) fn before_state(&self) -> &ExecutionState {
        &self.before_state
    }
}

/// Proof-object-owned authority for one checked call occurrence.
///
/// Construction may register additional exact result states when a later
/// statement theorem is accepted from a recomputed view of the running state.
/// Consumers can only cite this opaque object and states in its registry;
/// evaluator-local havoc variables never act as authority.
#[derive(Default)]
struct CheckedCallEventRegistryData {
    canonical_views: HashMap<u64, crate::kernel::SharedMemory>,
    events_by_view: HashMap<crate::kernel::SharedMemory, Vec<u64>>,
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

    fn new_event(&self, canonical_view: crate::kernel::SharedMemory) -> CheckedCallEvent {
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

    fn register_view(&self, id: u64, view: crate::kernel::SharedMemory) {
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

    fn contains_view(&self, id: u64, view: &crate::kernel::SharedMemory) -> bool {
        self.data
            .lock()
            .expect("checked call registry poisoned")
            .events_by_view
            .get(view)
            .is_some_and(|events| events.contains(&id))
    }

    fn event_ids_for_view(&self, view: &crate::kernel::SharedMemory) -> Vec<u64> {
        self.data
            .lock()
            .expect("checked call registry poisoned")
            .events_by_view
            .get(view)
            .cloned()
            .unwrap_or_default()
    }

    fn canonical_view(&self, id: u64) -> crate::kernel::SharedMemory {
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
    pub(crate) fn new(canonical_view: crate::kernel::SharedMemory) -> Self {
        CheckedCallEventRegistry::new().new_event(canonical_view)
    }

    fn canonical_view(&self) -> crate::kernel::SharedMemory {
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

    fn new_event(&mut self, canonical_view: crate::kernel::SharedMemory) -> CheckedCallEvent {
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

    pub(crate) fn contains(&self, event: &CheckedCallEvent) -> bool {
        self.groups.iter().any(|group| {
            group.registry.same_registry(&event.registry) && group.active.contains(&event.id)
        })
    }

    pub(crate) fn contains_view(
        &self,
        event: &CheckedCallEvent,
        view: &crate::kernel::SharedMemory,
    ) -> bool {
        self.contains(event) && event.registry.contains_view(event.id, view)
    }

    pub(crate) fn register_view(
        &self,
        event: &CheckedCallEvent,
        view: crate::kernel::SharedMemory,
    ) {
        if self.contains(event) {
            event.registry.register_view(event.id, view);
        }
    }

    pub(crate) fn events_for_view(
        &self,
        view: &crate::kernel::SharedMemory,
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
    before_state: ExecutionState,
    pub(crate) after_state: ExecutionState,
    pub(crate) before_facts: PureFactStore,
    pub(crate) after_facts: PureFactStore,
    definition: CompositeResourceDefinition,
    consumption_contract: Option<Arc<CheckedFunctionEntry>>,
    return_context: Option<Arc<CheckedReturnContext>>,
    instance: Option<crate::kernel::ResourceInstance>,
    selected_children: Option<Arc<[(String, InstanceId)]>>,
    return_observation: Option<Arc<ReturnResourceObservation>>,
    return_presentation: Option<Arc<CheckedReturnPresentation>>,
}

/// A selected fold whose body obligations are being proved at its input
/// frontier. Completion publishes this construction without selecting again.
#[derive(Clone)]
struct PreparedResourceFold {
    rewrite: CheckedResourceRewrite,
    semantic_facts: Vec<Proposition>,
}

#[derive(Clone)]
struct PreparedReturnFold {
    path_index: usize,
    rewrite: Option<CheckedResourceRewrite>,
    semantic_facts: Vec<Proposition>,
}

/// A composite exchange independently checked at the published state.
/// Its facts retain that state rather than pretending to be C-body reads.
#[derive(Clone)]
struct CheckedReturnPresentation {
    /// The selected unfold's outputs are evidence even if already in its input context.
    published_facts: Vec<Proposition>,
    context: Arc<CheckedReturnContext>,
    selected: ResourceFact,
    rewrite: CheckedResourceRewrite,
}

/// The same selected resource exchange at the kernel-published return state.
#[derive(Clone)]
struct ReturnResourceObservation {
    context: Arc<CheckedReturnContext>,
    after: ExecutionState,
    semantic_facts: Vec<Proposition>,
}

/// The successor constructed by an authority establishment or retirement on
/// the execution frontier. The event changes neither memory nor pure facts.
#[derive(Clone)]
pub(crate) struct CheckedPopulationAuthorityRewrite {
    before_state: ExecutionState,
    after_state: ExecutionState,
    description: crate::kernel::ResourceDescription,
    establish: bool,
    witness: CheckedPopulationAuthorityExchange,
}

/// A birth or consumption of one field-free member, checked together with
/// the exact population ledger and the ordinary owned resource exchange.
#[derive(Clone)]
pub(crate) struct CheckedPopulationMemberRewrite {
    before_state: ExecutionState,
    after_state: ExecutionState,
    before_facts: PureFactStore,
    after_facts: PureFactStore,
    selected: ResourceFact,
    produce: bool,
    definition: CompositeResourceDefinition,
}

impl CheckedPopulationAuthorityRewrite {
    pub(crate) fn before_state(&self) -> &ExecutionState {
        &self.before_state
    }

    fn construct(
        before_state: &ExecutionState,
        selected: &ResourceFact,
        establish: bool,
        assumptions: &PureFactContext,
    ) -> Result<Self, String> {
        let Resource::PopulationAuthority(description) = selected.resource() else {
            return Err("Requires owns authority(R(p))".into());
        };
        let (after_state, witness) =
            before_state.checked_population_authority_exchange(selected, establish, assumptions)?;
        Ok(Self {
            before_state: before_state.clone(),
            after_state,
            description: description.clone(),
            establish,
            witness,
        })
    }

    fn advance_checked(&self, state: &ExecutionState) -> Option<&ExecutionState> {
        if !state.memory.same_storage_roots(&self.before_state.memory)
            || !state.shares_non_memory_storage_with(&self.before_state)
        {
            return None;
        }
        let before_events = state.population_effects.creation.as_ref()?;
        let after_events = self.after_state.population_effects.creation.as_ref()?;
        self.witness
            .matches(
                before_events,
                after_events,
                &self.description,
                self.establish,
            )
            .then_some(&self.after_state)
    }
}

fn checks_population_member_exchange(
    definition: &CompositeResourceDefinition,
    before: &ExecutionState,
    after: &ExecutionState,
    selected: &ResourceFact,
    produce: bool,
    witness: &CheckedPopulationMemberExchange,
    assumptions: &PureFactContext,
) -> Result<(), String> {
    let ResourceFact::Own(Resource::Composite { name, arguments }, quantity) = selected else {
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
                crate::kernel::ResourceTerm::Memory(_)
                    | crate::kernel::ResourceTerm::Token { .. }
                    | crate::kernel::ResourceTerm::Composite { .. }
            ) || spec.access() != crate::kernel::ResourceAccessMode::Own
                || spec.quantity() != &crate::kernel::ResourceQuantity::One
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
    let Some(crate::kernel::ResourceFieldValue::Program(ProgramValue::Pointer(pointer))) =
        description.arguments().first()
    else {
        return Err("population member rewrite requires one pointer anchor".into());
    };
    let anchor = pointer.address();
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
        && (!matches!(
            crate::kernel::OffsetTree::view(&anchor.offset),
            crate::kernel::OffsetView::Constant(0)
        ) || !(matches!(&anchor.base, crate::kernel::AddressBase::Heap(_))
            && before.memory.live_heap_block_size(anchor).is_some()
            || anchor.base.is_local_block() && before.memory.has_block(&anchor.base)))
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
    let authority = ResourceFact::own(Resource::PopulationAuthority(governing));
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
            &after.resources.borrow_dependencies,
            &expected_resources.borrow_dependencies,
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
        &before.instance_field_scope.borrow_dependencies,
        &after.instance_field_scope.borrow_dependencies,
    ) || !same_bindings
        || !before
            .locals
            .bindings
            .shares_root_with(&after.locals.bindings)
        || !before.locals.slots.shares_root_with(&after.locals.slots)
        || before.memory.diagnostic_identity() != after.memory.diagnostic_identity()
        || before.borrow_ledger != after.borrow_ledger
        || before.borrow_participant != after.borrow_participant
        || before.borrow_bindings != after.borrow_bindings
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
    pub(crate) fn before_state(&self) -> &ExecutionState {
        &self.before_state
    }

    fn check(
        function: &ProgramFunction,
        before_state: &ExecutionState,
        before_facts: &PureFactStore,
        selected: &ResourceFact,
        produce: bool,
        witness: &CheckedPopulationMemberExchange,
        after_state: &ExecutionState,
        after_facts: &PureFactStore,
    ) -> Result<Self, String> {
        let Resource::Composite { name, .. } = selected.resource() else {
            return Err("population member rewrite requires a declared resource".into());
        };
        let definition = function
            .proof_composite_resource_definition(name)
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
}

/// Whether `after` differs from `before` only by cells that name their own
/// load: each added cell holds the canonical form of the load of that very
/// pointer at `before`. Adding one is definitional — it records what the
/// state already said about the cell — so a rewrite that names the cells it
/// exposes stays checkable without a second state comparison rule. Bounded by
/// the cell count, with no assumption consulted and nothing searched.
///
/// Returns a description of the first deviation when the rule does not hold,
/// naming the offending cell, so the caller can report which cell or field a
/// rejected rewrite changed.
fn memory_only_adds_named_cells(
    before_state: &ExecutionState,
    after: &crate::kernel::SymbolicMemory,
) -> Result<(), String> {
    let before = before_state.memory();
    let mut rebased = after.clone();
    rebased.cells = before.cells.clone();
    if rebased != *before {
        let changed = if rebased.blocks != before.blocks {
            "blocks"
        } else if rebased.union_cells != before.union_cells {
            "union cells"
        } else if rebased.forgotten != before.forgotten {
            "forgotten-cell history"
        } else if rebased.heap.initialized != before.heap.initialized {
            "initialized bytes"
        } else {
            "heap allocation state"
        };
        return Err(format!("changed non-cell memory state ({changed})"));
    }
    let source = before_state.program_point();
    let base = source.shared_memory();
    for change in before.cells.diff_after_naming(&after.cells, &source)? {
        let crate::kernel::HashedOrdMapChange::Added(pointer) = change else {
            return Err("removed or rewrote an existing cell".into());
        };
        let value = after.cells.get(pointer).expect("added cell exists");
        // A cell of an abstract type holds the load of its type, which no
        // machine load kind reads.
        if let ProgramValue::Parameter(term) = &value {
            let load = crate::kernel::AlgebraicTermNode::parameter_cell_load(
                &source,
                pointer.clone(),
                crate::kernel::TypeParameterName::of(&term.algebraic_type),
            );
            if value != load {
                return Err("added an abstract-type cell that is not its own load".into());
            }
            continue;
        }
        if let ProgramValue::Pointer(named) = &value
            && named
                .address()
                .as_loaded_value()
                .is_some_and(|read| read.point.read_version_id().is_some())
        {
            let expected = crate::kernel::eval::point_named_pointer_cell_read(
                &source,
                pointer,
                named.program_type(),
            );
            if expected.as_ref() != Some(named) {
                return Err(format!(
                    "added a pointer cell at {pointer:?} without its complete indexed source read"
                ));
            }
            continue;
        }
        let Some(kind) = LoadKind::of_value(&value) else {
            return Err("added a cell no load reads".into());
        };
        if let Some(OldMachineTerm::MemoryLoad(point, _, _)) =
            crate::kernel::spec::program_value_bitvector_term(&value)
            && point.read_version_id().is_some()
        {
            let expected = crate::kernel::eval::expected_point_named_cell_read(
                &source,
                pointer,
                value.program_type(),
            );
            if expected
                .as_ref()
                .is_none_or(|load| !cell_value_is_exactly_load(&value, load))
            {
                return Err(format!(
                    "added a cell at {pointer:?} without its indexed source read"
                ));
            }
            continue;
        }
        let load = crate::kernel::canonical_form_of_load_at(&source, pointer.clone(), kind);
        if !cell_value_is_exactly_load(&value, &load) {
            return Err(describe_unnamed_cell_addition(base, pointer, &value, &load));
        }
    }
    Ok(())
}

/// Explains a rejected unnamed-cell addition with bounded, actionable detail.
///
/// Names the held value and the recomputed canonical load, the pre-rewrite
/// state and version identities (compact arena ids, not
/// memory dumps), and whether the pointer itself embeds an inner load whose own
/// version drift would cascade into this outer name. The version lookup is the same
/// assumption-free memoized walk the naming itself uses, so this adds no proof
/// search or ambient-fact scan.
fn describe_unnamed_cell_addition(
    base: &crate::kernel::SharedMemory,
    pointer: &crate::kernel::Address,
    value: &ProgramValue,
    load: &OldMachineTerm,
) -> String {
    let held = truncate_debug(value, 240);
    let expected = truncate_debug(load, 240);
    let (base_arena, base_id) = base.arena_id();
    let version_note = match crate::kernel::resource_tracker::last_same_version_memory(
        crate::kernel::resource_tracker::TrackedResource::Cell {
            pointer,
            bytes: crate::kernel::AccessExtent::from(
                crate::kernel::resource_tracker::widest_scalar_access_bytes(),
            ),
        },
        base,
    ) {
        Some(version) => {
            let (version_arena, version_id) = version.arena_id();
            format!("version state ({version_arena},{version_id})")
        }
        None => "version state none (unwritten at a derivation root)".to_string(),
    };
    let mut detail = format!(
        "added a cell at {pointer:?} that is not the canonical load of its own pointer at the pre-rewrite memory state; \
held {held} but canonical is {expected}; \
pre-rewrite retained_state ({base_arena},{base_id}), {version_note}"
    );
    let embedded: Vec<String> = pointer
        .offset
        .native_scaled_values_for_output()
        .iter()
        .take(2)
        .map(|term| truncate_debug(term, 120))
        .collect();
    if !embedded.is_empty() {
        detail.push_str(&format!(
            "; pointer embeds {} scaled value(s) such as {} — if that inner load's version drifted, this outer name drifts too",
            pointer.offset.native_scaled_values_for_output().len(),
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
/// internal-state dump: load terms can embed whole memory states, so cap
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
fn describe_changed_state_field(
    changed: &ExecutionState,
    original: &ExecutionState,
) -> &'static str {
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
/// term itself, the `_Bool` normalization of it, or the complete typed pointer
/// read (including its provenance and bounds).
fn cell_value_is_exactly_load(value: &ProgramValue, load: &OldMachineTerm) -> bool {
    match value {
        ProgramValue::Int8(term) => term == load,
        ProgramValue::Int16(term)
        | ProgramValue::Int32(term)
        | ProgramValue::UInt8(term)
        | ProgramValue::UInt16(term)
        | ProgramValue::UInt32(term)
        | ProgramValue::Int64(term)
        | ProgramValue::UInt64(term)
        | ProgramValue::Int128(term)
        | ProgramValue::UInt128(term)
        | ProgramValue::Float32(term)
        | ProgramValue::Float64(term) => term == load,
        ProgramValue::Bool(term) => {
            term == &OldMachineTerm::if_then_else(
                crate::kernel::OldConditionTerm::equal(load.clone(), OldMachineTerm::constant(0)),
                OldMachineTerm::constant(0),
                OldMachineTerm::constant(1),
            )
        }
        ProgramValue::Pointer(pointer) => {
            value == &crate::kernel::cell_run_value(pointer.program_type(), load.clone())
        }
        _ => false,
    }
}

/// Exact comparison retained at a failed named-resource rewrite. Diagnostic
/// data only: carrying it grants no fact or resource authority.
#[derive(Clone, Debug)]
pub(crate) struct RejectedResourceRewriteFact {
    pub(crate) rejected: Proposition,
    pub(crate) allowed: Arc<[Proposition]>,
}

#[derive(Debug)]
pub(crate) struct ResourceRewriteCheckError {
    pub(crate) message: String,
    pub(crate) rejected_fact: Option<Arc<RejectedResourceRewriteFact>>,
}

pub(crate) enum InstanceUnfoldError {
    Construction(crate::kernel::ResourceRewriteRefusal),
    Recording(ResourceRewriteCheckError),
}

impl From<String> for ResourceRewriteCheckError {
    fn from(message: String) -> Self {
        Self {
            message,
            rejected_fact: None,
        }
    }
}

impl From<&str> for ResourceRewriteCheckError {
    fn from(message: &str) -> Self {
        message.to_owned().into()
    }
}

/// A checked body's identical readability range at a state differing only
/// by caches of unchanged reads. This transports neither values nor ownership,
/// and admits no different address, bounds, or wide/narrow representation.
fn cached_body_loadability(
    fact: &Proposition,
    body_memory: &SymbolicMemory,
    allowed: &std::collections::BTreeSet<Proposition>,
    comparisons: &mut HashMap<((u32, u32), (u32, u32)), bool>,
) -> bool {
    let Proposition::MemoryLoadable {
        memory,
        base,
        bytes,
        wide,
        ..
    } = fact
    else {
        return false;
    };
    let key = (
        crate::kernel::intern_memory_ref(memory).arena_id(),
        crate::kernel::intern_memory_ref(body_memory).arena_id(),
    );
    if !*comparisons.entry(key).or_insert_with(|| {
        crate::kernel::api::contract_certification::memories_match_up_to_cached_reads(
            memory,
            body_memory,
        )
    }) {
        return false;
    }
    allowed.contains(&Proposition::MemoryLoadable {
        memory: body_memory.clone(),
        point: crate::kernel::program_point::PathLink::lookup_key(),
        base: base.clone(),
        bytes: bytes.clone(),
        wide: *wide,
    })
}

impl CheckedResourceRewrite {
    pub(crate) fn before_state(&self) -> &ExecutionState {
        &self.before_state
    }

    #[cfg(test)]
    fn check(
        function: &ProgramFunction,
        before_state: &ExecutionState,
        before_facts: &PureFactStore,
        selected: &ResourceFact,
        after_state: &ExecutionState,
        after_facts: &PureFactStore,
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
        before_state: &ExecutionState,
        before_facts: &PureFactStore,
        selected: &ResourceFact,
        after_state: &ExecutionState,
        after_facts: &PureFactStore,
        definition: &CompositeResourceDefinition,
        selected_children: Option<Arc<[(String, InstanceId)]>>,
    ) -> Result<Self, String> {
        let ResourceFact::Own(Resource::Composite { name, arguments }, quantity) = selected else {
            return Err("authority control requires one owned composite".into());
        };
        if quantity.as_const() != Some(1) || selected_children.is_some() {
            return Err("authority control requires one whole owned composite".into());
        }
        let assumptions = before_facts.assumptions();
        if !before_state.borrow_bindings_are_consistent()
            || !after_state.borrow_bindings_are_consistent()
        {
            return Err("authority control changed borrow bindings".into());
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
                .filter(|child| matches!(child.resource(), Resource::PopulationAuthority(_)))
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
            if folded
                .borrow_ledger()
                .is_some_and(|ledger| !ledger.rewrite_separates_from_borrows(range, assumptions))
            {
                return Err(
                    "authority control body requires separation from active borrows".into(),
                );
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
            base.install_established_partition(children.iter().cloned(), assumptions)
                .map(|(context, _)| context)
                .map_err(|error| {
                    format!("authority control body overlaps existing ownership: {error}")
                })?
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
                base.install_established_partition(std::iter::once(selected.clone()), assumptions)
                    .map(|(context, _)| context)
                    .map_err(|error| {
                        format!("authority control duplicates its folded resource: {error}")
                    })?
            }
        };
        if !after_state
            .resources()
            .same_exchange_from(&expected_resources, before_state.resources())
            || !Arc::ptr_eq(
                &after_state.resources.borrow_dependencies,
                &expected_resources.borrow_dependencies,
            )
        {
            return Err("authority control has the wrong resource exchange".into());
        }
        if exposing {
            memory_only_adds_named_cells(before_state, after_state.memory())?;
        } else if !crate::kernel::api::contract_certification::memories_definitionally_equal(
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
                .as_program_value()
                .ok_or("authority control requires C arguments")?;
            if value.program_type() != parameter.program_type() {
                return Err("authority control argument type mismatch".into());
            }
            evaluation.locals.set_typed(
                parameter.binding_name().clone(),
                value.clone(),
                parameter.program_type(),
            );
        }
        let mut evaluation_assumptions = assumptions.clone();
        for imported in imported_counts.into_iter().flatten() {
            evaluation_assumptions =
                evaluation_assumptions.assume_proposition(imported.entry_lower_bound());
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
            if !path
                .facts
                .iter()
                .all(|fact| evaluation_assumptions.settles_exactly(fact.proposition()))
                || !path.obligations.iter().all(|obligation| {
                    evaluation_assumptions.settles_exactly(obligation.proposition())
                })
            {
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
        }
        // The resource operation constructs its fact delta while naming the
        // selected body's loaded children. Retain those facts directly, as for
        // ordinary composite rewrites below. Reconstructing a second allowed
        // list loses auxiliary pointer-value equalities from that operation.
        Ok(Self {
            before_state: before_state.clone(),
            after_state: after_state.clone(),
            before_facts: before_facts.clone(),
            after_facts: after_facts.clone(),
            definition: definition.clone(),
            consumption_contract: None,
            return_context: None,
            instance: None,
            selected_children: None,
            return_presentation: None,
            return_observation: None,
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn check_transfer_wrapper(
        before_state: &ExecutionState,
        before_facts: &PureFactStore,
        selected: &ResourceFact,
        after_state: &ExecutionState,
        after_facts: &PureFactStore,
        definition: &CompositeResourceDefinition,
        selected_children: Option<Arc<[(String, InstanceId)]>>,
    ) -> Result<Self, String> {
        let ResourceFact::Own(Resource::Composite { name, arguments }, quantity) = selected else {
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
                spec.access() != crate::kernel::ResourceAccessMode::Own
                    || spec.quantity() != &crate::kernel::ResourceQuantity::One
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
            &before_state.program_point(),
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
                .install_established_partition(expanded.facts().iter().cloned(), assumptions)
                .map(|(context, _)| context)
                .map_err(|error| format!("transfer wrapper overlaps existing children: {error}"))?
        } else {
            let mut resources = before_state.resources().clone();
            for child in expanded.facts() {
                resources = resources
                    .without_fact_incrementally(child, assumptions)
                    .ok_or("transfer wrapper is missing an existing child")?;
            }
            resources
                .install_established_partition(std::iter::once(selected.clone()), assumptions)
                .map(|(context, _)| context)
                .map_err(|error| {
                    format!("transfer wrapper duplicates its folded resource: {error}")
                })?
        };
        if !before_state.borrow_bindings_are_consistent()
            || !after_state.borrow_bindings_are_consistent()
            || !after_state
                .resources()
                .same_exchange_from(&expected, before_state.resources())
            || !Arc::ptr_eq(
                &after_state.resources.borrow_dependencies,
                &expected.borrow_dependencies,
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
            || !before_state
                .locals
                .bindings
                .shares_root_with(&after_state.locals.bindings)
            || !before_state
                .locals
                .slots
                .shares_root_with(&after_state.locals.slots)
            || !Arc::ptr_eq(
                &before_state.instance_field_scope.storage,
                &after_state.instance_field_scope.storage,
            )
            || !Arc::ptr_eq(
                &before_state.instance_field_scope.borrow_dependencies,
                &after_state.instance_field_scope.borrow_dependencies,
            )
            || before_state.borrow_ledger != after_state.borrow_ledger
            || before_state.borrow_participant != after_state.borrow_participant
            || before_state.borrow_bindings != after_state.borrow_bindings
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
                allowed.push(Proposition::ResourceContains {
                    parent: Box::new(selected.resource().clone()),
                    child: Box::new(owned.clone()),
                })
            }
        }
        allowed.push(Proposition::ResourceComposition(child_context));
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
            return_context: None,
            instance: None,
            selected_children: None,
            return_presentation: None,
            return_observation: None,
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn check_with_children(
        function: &ProgramFunction,
        before_state: &ExecutionState,
        before_facts: &PureFactStore,
        selected: &ResourceFact,
        after_state: &ExecutionState,
        after_facts: &PureFactStore,
        call_events: &CheckedCallEvents,
        selected_children: Option<Arc<[(String, InstanceId)]>>,
    ) -> Result<Self, String> {
        Self::check_with_children_diagnostic(
            function,
            before_state,
            before_facts,
            selected,
            after_state,
            after_facts,
            call_events,
            selected_children,
            &[],
        )
        .map_err(|error| error.message)
    }

    #[allow(clippy::too_many_arguments)]
    fn check_with_children_diagnostic(
        function: &ProgramFunction,
        before_state: &ExecutionState,
        before_facts: &PureFactStore,
        selected: &ResourceFact,
        after_state: &ExecutionState,
        after_facts: &PureFactStore,
        call_events: &CheckedCallEvents,
        selected_children: Option<Arc<[(String, InstanceId)]>>,
        borrow_holds: &[crate::kernel::CheckedBorrowTransition],
    ) -> Result<Self, ResourceRewriteCheckError> {
        Self::check_with_return_observation(
            function,
            before_state,
            before_facts,
            selected,
            after_state,
            after_facts,
            call_events,
            selected_children,
            None,
            borrow_holds,
            None,
        )
    }

    fn check_instance_definition(
        function: &ProgramFunction,
        definition: &CompositeResourceDefinition,
    ) -> Result<(), String> {
        if definition.reaches_population() {
            let memory_only = |spec: &crate::kernel::ResourceSpec| {
                matches!(
                    spec.term(),
                    crate::kernel::ResourceTerm::Memory(_)
                        | crate::kernel::ResourceTerm::Token { .. }
                        | crate::kernel::ResourceTerm::PopulationAuthority { .. }
                )
            };
            // A named child is admitted when its own definition reaches no
            // population, so it cannot hide a member or an authority; the
            // exchange then moves only memory, tokens, and this body's own
            // authority, which the ledger equality below checks.
            let ordinary_child = |child: &crate::kernel::ResourceChildSpec| {
                function
                    .proof_composite_resource_definition(&child.resource)
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
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn check_with_return_observation(
        function: &ProgramFunction,
        before_state: &ExecutionState,
        before_facts: &PureFactStore,
        selected: &ResourceFact,
        after_state: &ExecutionState,
        after_facts: &PureFactStore,
        call_events: &CheckedCallEvents,
        selected_children: Option<Arc<[(String, InstanceId)]>>,
        return_observation: Option<Arc<ReturnResourceObservation>>,
        borrow_holds: &[crate::kernel::CheckedBorrowTransition],
        prepared_instance: Option<&crate::kernel::functions::ResourceInstanceRewriteResult>,
    ) -> Result<Self, ResourceRewriteCheckError> {
        let mut rejected_fact = None;
        Self::check_with_children_recording(
            function,
            before_state,
            before_facts,
            selected,
            after_state,
            after_facts,
            call_events,
            selected_children,
            &mut rejected_fact,
            return_observation,
            borrow_holds,
            prepared_instance,
        )
        .map_err(|message| ResourceRewriteCheckError {
            message,
            rejected_fact,
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn check_with_children_recording(
        function: &ProgramFunction,
        before_state: &ExecutionState,
        before_facts: &PureFactStore,
        selected: &ResourceFact,
        after_state: &ExecutionState,
        after_facts: &PureFactStore,
        call_events: &CheckedCallEvents,
        selected_children: Option<Arc<[(String, InstanceId)]>>,
        rejected_fact: &mut Option<Arc<RejectedResourceRewriteFact>>,
        return_observation: Option<Arc<ReturnResourceObservation>>,
        borrow_holds: &[crate::kernel::CheckedBorrowTransition],
        prepared_instance: Option<&crate::kernel::functions::ResourceInstanceRewriteResult>,
    ) -> Result<Self, String> {
        if !borrow_holds.is_empty() {
            // Check the hold on its own, then check the fold as a
            // definitional rewrite from the input state with that one hold
            // already placed. The event keeps the true input state.
            let held_before = checked_borrowing_fold_hold(
                function,
                before_state,
                before_facts,
                selected,
                after_state,
                borrow_holds,
            )?;
            let mut checked = Self::check_with_children_recording(
                function,
                &held_before,
                before_facts,
                selected,
                after_state,
                after_facts,
                call_events,
                selected_children,
                rejected_fact,
                return_observation,
                &[],
                None,
            )?;
            checked.before_state = before_state.clone();
            return Ok(checked);
        }
        // A family that reaches no population keeps its ordinary definition
        // law; only population-reaching bodies take the checks below.
        let reaches_population = match selected.resource() {
            Resource::Composite { name, .. } => function
                .proof_composite_resource_definition(name)
                .is_none_or(|definition| definition.reaches_population()),
            _ => true,
        };
        if !matches!(selected.resource(), Resource::Instance(_)) {
            if let Resource::Composite { name, .. } = selected.resource()
                && let Some(definition) = function.proof_composite_resource_definition(name)
                && definition.contains().iter().any(|spec| {
                    matches!(
                        spec.term(),
                        crate::kernel::ResourceTerm::PopulationAuthority { .. }
                    )
                })
            {
                return Self::check_authority_wrapper(
                    before_state,
                    before_facts,
                    selected,
                    after_state,
                    after_facts,
                    definition,
                    selected_children,
                );
            }
            if let ResourceFact::Own(Resource::Composite { name, arguments }, _) = selected
                && let Some(definition) = function.proof_composite_resource_definition(name)
                && !before_state.tracks_authority_member(selected)
                && before_state.population_body_is_open(name, arguments)
                    == after_state.population_body_is_open(name, arguments)
                && !definition.contains().is_empty()
                && definition.contains().iter().all(|spec| {
                    matches!(
                        spec.term(),
                        crate::kernel::ResourceTerm::Composite { .. }
                            | crate::kernel::ResourceTerm::Token { .. }
                    )
                })
            {
                let checked = Self::check_transfer_wrapper(
                    before_state,
                    before_facts,
                    selected,
                    after_state,
                    after_facts,
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
                    ResourceFact::Own(Resource::Composite { name, .. }, _)
                        if function
                            .proof_composite_resource_definition(name)
                            .is_some_and(|definition| !definition.is_authorized())
                );
            if !ordinary_family {
                let ResourceFact::Own(Resource::Composite { name, arguments }, quantity) = selected
                else {
                    return Err("member body access requires one owned member".into());
                };
                let definition = function
                    .proof_composite_resource_definition(name)
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
                            crate::kernel::ResourceTerm::Memory(_)
                                | crate::kernel::ResourceTerm::Composite { .. }
                        ) || spec.access() != crate::kernel::ResourceAccessMode::Own
                            || spec.quantity() != &crate::kernel::ResourceQuantity::One
                            || spec.guard().is_some()
                            || !spec.resource_arguments().is_empty()
                    })
                    || selected_children.is_some()
                {
                    return Err(
                    "member body access requires a private body of owned memory or declared resources".into(),
                );
                }
                if !before_state.borrow_bindings_are_consistent()
                    || !after_state.borrow_bindings_are_consistent()
                {
                    return Err("member body access changed borrow bindings".into());
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
                    &before_state.program_point(),
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
                        if let ResourceFact::Own(Resource::Composite { .. }, quantity) = child
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
                        && base.base != crate::kernel::AddressBase::ExternalArgument
                    {
                        return Err("member private body exceeds live storage".into());
                    }
                    if before_state.borrow_ledger().is_some_and(|ledger| {
                        !ledger.rewrite_separates_from_borrows(range, assumptions)
                    }) {
                        return Err(
                            "member private body requires separation from active borrows".into(),
                        );
                    }
                }
                let child_context = ResourceContext::new_with_equalities(assumptions)
                    .unchecked_with_facts(children.iter().cloned());
                let mut allowed = child_context.observable_facts_assuming_valid(assumptions);
                allowed.push(Proposition::ResourceComposition(child_context.clone()));
                if let Some(propositions) =
                    crate::kernel::functions::evaluate_composite_resource_relation_propositions(
                        selected,
                        function.composite_resource_definitions(),
                        &after_state.program_point(),
                        assumptions,
                    )
                {
                    allowed.extend(propositions);
                }
                if let Some(propositions) =
                    crate::kernel::functions::evaluate_composite_resource_loadable_propositions(
                        selected,
                        function.composite_resource_definitions(),
                        &after_state.program_point(),
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
                        .install_established_partition(children.iter().cloned(), assumptions)
                        .map(|(context, _)| context)
                        .map_err(|error| {
                            format!("member body access duplicates private ownership: {error}")
                        })?
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
                        &after_state.resources.borrow_dependencies,
                        &expected_resources.borrow_dependencies,
                    )
                {
                    return Err("member body access has the wrong resource exchange".into());
                }
                if now_open {
                    memory_only_adds_named_cells(before_state, after_state.memory())?;
                } else if !crate::kernel::api::contract_certification::memories_definitionally_equal(
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
                    || !before_state
                        .locals
                        .bindings
                        .shares_root_with(&after_state.locals.bindings)
                    || !before_state
                        .locals
                        .slots
                        .shares_root_with(&after_state.locals.slots)
                    || !Arc::ptr_eq(
                        &before_state.instance_field_scope.storage,
                        &after_state.instance_field_scope.storage,
                    )
                    || !Arc::ptr_eq(
                        &before_state.instance_field_scope.borrow_dependencies,
                        &after_state.instance_field_scope.borrow_dependencies,
                    )
                    || before_state.borrow_ledger != after_state.borrow_ledger
                    || before_state.borrow_participant != after_state.borrow_participant
                    || before_state.borrow_bindings != after_state.borrow_bindings
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
                    return_context: None,
                    instance: None,
                    selected_children: None,
                    return_presentation: None,
                    return_observation: None,
                });
            }
        }
        if !before_state.borrow_bindings_are_consistent()
            || !after_state.borrow_bindings_are_consistent()
        {
            return Err(
                "resource rewrite carries mismatched borrow dependency sidecar".to_string(),
            );
        }
        let load_equality_capture =
            crate::kernel::CheckedLoadEqualityCapture::start_with_call_events(call_events);
        let assumptions = before_facts.assumptions();
        if let Resource::Instance(instance) = selected.resource() {
            let definition = function
                .proof_composite_resource_definition(instance.name())
                .ok_or_else(|| {
                    "instance definition is not registered on the function".to_string()
                })?;
            // Ordinary named memory resources retain their existing checked
            // definitional exchange. Population members cannot be introduced
            // through this path: those require ledger evidence. An exact owned
            // authority may move into or out of a control instance; the
            // creation-ledger equality below proves that no population changed.
            Self::check_instance_definition(function, definition)?;
            let unfold = before_state
                .resources()
                .owned_instance(instance.identity())
                .is_some();
            let checked;
            let rewrite = if let Some(prepared) = prepared_instance {
                prepared
            } else {
                checked = crate::kernel::rewrite_resource_instance_selecting_children(
                    before_state,
                    instance,
                    definition,
                    function.composite_resource_definitions(),
                    assumptions,
                    unfold,
                    selected_children.as_deref(),
                )
                .map_err(|refusal| refusal.describe())?;
                &checked
            };
            let expected = &rewrite.state;
            let allowed = rewrite.semantic_facts.iter().cloned().chain(
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
            if unchanged != *before_state {
                // An unfold names the cells it exposes, which materializes
                // them in the state so the body's facts and a later C read
                // of one of those cells are one load variable
                // (`docs/internals/canonicalization.md`). Adding such a cell
                // is the only memory change a resource rewrite may make, and
                // each added cell must hold the canonical load form of its own
                // pointer at the pre-rewrite state. That is a definitional
                // identity, checked here per added cell with no search.
                if let Err(detail) = memory_only_adds_named_cells(before_state, &after_state.memory)
                {
                    return Err(if unfold {
                        format!(
                            "internal error while applying an unfold: Click named an exposed cell \
inconsistently; it {detail}; this is a Click implementation error, not an invalid unfold"
                        )
                    } else {
                        format!("a fold may not change the memory state, but it {detail}")
                    });
                }
                if !unfold {
                    return Err("a fold may not change the memory state".to_string());
                }
                unchanged.memory = before_state.memory.clone();
                if unchanged != *before_state {
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
            let observed_facts = if let Some(observation) = &return_observation {
                observation.semantic_facts.clone()
            } else {
                Vec::new()
            };
            let allowed = allowed
                .chain(observed_facts)
                .collect::<std::collections::BTreeSet<_>>();
            // A visible return projection may repeat a fact already checked
            // at its frozen state. Accept it only when the input context
            // independently proves that exact memory/resource proposition.
            let mut cached_comparisons = HashMap::new();
            // Check direct introductions in order. On the first one that
            // needs propagation, replay the already justified prefix once.
            // Only consequences of that prefix can justify a later fact.
            let mut admitted = None::<PureFactStore>;
            for (index, fact) in introduced.iter().enumerate() {
                let directly_allowed = allowed.contains(fact)
                    || cached_body_loadability(
                        fact,
                        before_state.memory(),
                        &allowed,
                        &mut cached_comparisons,
                    )
                    || (matches!(fact, Proposition::MemoryReadDefined { .. })
                        && assumptions.proves_atomic_memory_or_resource(fact));
                if !directly_allowed {
                    let context = admitted.get_or_insert_with(|| {
                        introduced[..index]
                            .iter()
                            .fold(before_facts.clone(), |facts, fact| {
                                facts.with_kernel_checked_fact(fact.clone())
                            })
                    });
                    if !context.contains(fact) {
                        *rejected_fact = Some(Arc::new(RejectedResourceRewriteFact {
                            rejected: fact.clone(),
                            allowed: allowed.into_iter().collect(),
                        }));
                        return Err("instance rewrite introduced an unchecked fact".to_string());
                    }
                } else if let Some(context) = &mut admitted {
                    *context = context.with_kernel_checked_fact(fact.clone());
                }
            }
            return Ok(Self {
                before_state: before_state.clone(),
                after_state: after_state.clone(),
                before_facts: before_facts.clone(),
                after_facts: after_facts.clone(),
                definition: definition.clone(),
                consumption_contract: None,
                return_context: None,
                instance: Some(instance.clone()),
                selected_children,
                return_presentation: None,
                return_observation,
            });
        }
        let crate::kernel::Resource::Composite { name, .. } = selected.resource() else {
            return Err("resource rewrite evidence requires a composite resource".to_string());
        };
        let definition = function
            .proof_composite_resource_definition(name)
            .cloned()
            .ok_or_else(|| {
                "the rewritten composite definition is not registered on the function".to_string()
            })?;
        // The surface built `after_state` and `after_facts` with the kernel's
        // own fold or unfold of `selected`, in this session; recording it
        // re-expands nothing and compares nothing (`AGENTS.md`, construct
        // valid proofs). Re-deriving the expansion and normalizing both whole
        // resource contexts to compare them cost work in every resource the
        // state holds at every fold and unfold (`roadmap/scaling.md`).
        // The capture lent its call events to the checks above.
        load_equality_capture.finish();
        Ok(Self {
            before_state: before_state.clone(),
            after_state: after_state.clone(),
            before_facts: before_facts.clone(),
            after_facts: after_facts.clone(),
            definition,
            consumption_contract: None,
            return_context: None,
            instance: None,
            selected_children: None,
            return_presentation: None,
            return_observation: None,
        })
    }

    /// The registered composite definition the event applied.
    pub(crate) fn definition(&self) -> &CompositeResourceDefinition {
        &self.definition
    }
}

/// The input state of a proof `fold` with its one borrow hold placed.
///
/// A fold whose owned head packages a borrow-backed view is a borrowing
/// composite (escaping borrows in `docs/internals/stable-views.md`): the head
/// carries body facts read through the borrow, so the fold places a hold on the
/// borrow's scope and the head's binding names it. While the hold exists the
/// scope cannot end, so the owner behind the borrow cannot be recovered and
/// written while the head still describes its memory. The hold grants nothing:
/// it creates no borrow, share or view, changes no memory and no resource, and
/// only removes the scope's ability to end. A ledger with it permits a subset
/// of what the input ledger permits.
///
/// Checked here, without trusting the proof driver's choice of borrow:
/// - `selected` is one owned composite folded by this step: no input
///   occurrence supports it, and the successor holds an owned occurrence of
///   it whose borrow binding carries a hold;
/// - that binding's borrow is the dependency of a view the composite's body
///   names in the input state, so the hold is on the borrow the body reads
///   through;
/// - the one transition is exactly that hold, placed by this state's borrow
///   participant on that authority, applied to the exact input ledger, and
///   its result is the successor's ledger.
///
/// The caller then checks the fold as a definitional rewrite from the
/// returned state, so every other part of the state is compared as before.
fn checked_borrowing_fold_hold(
    function: &ProgramFunction,
    before_state: &ExecutionState,
    before_facts: &PureFactStore,
    selected: &ResourceFact,
    after_state: &ExecutionState,
    borrow_holds: &[crate::kernel::CheckedBorrowTransition],
) -> Result<ExecutionState, String> {
    let [hold] = borrow_holds else {
        return Err("a fold places at most one borrow hold".into());
    };
    if !matches!(selected, ResourceFact::Own(Resource::Composite { .. }, _)) {
        return Err("a borrow hold requires the fold of one owned composite".into());
    }
    let assumptions = before_facts.assumptions();
    if before_state
        .resources()
        .directly_supporting_fact(selected, assumptions)
        .is_some()
    {
        return Err("a borrow hold requires a fold of a composite the input does not hold".into());
    }
    if before_state.borrow_participant() != after_state.borrow_participant() {
        return Err("a borrow hold changed the borrow participant".into());
    }
    let holder = before_state
        .borrow_participant()
        .ok_or("a borrow hold requires a borrow participant")?;
    let ledger = before_state
        .borrow_ledger()
        .ok_or("a borrow hold requires a borrow ledger")?;
    let binding = after_state
        .resources()
        .unique_owned_occurrence_for_fact(selected)
        .and_then(|(occurrence, _)| after_state.resources().borrow_dependency(occurrence))
        .filter(|binding| binding.hold.is_some())
        .ok_or("a borrow hold is not carried by the folded composite")?;
    let temporary =
        ResourceContext::new_with_equalities(assumptions).unchecked_with_fact(selected.clone());
    let body = crate::kernel::functions::expand_composite_resource_fact(
        &temporary,
        selected,
        function.composite_resource_definitions(),
        &before_state.program_point(),
        assumptions,
    )
    .ok_or("a borrow hold's composite body could not be instantiated")?;
    let same_authority = |dependency: &crate::kernel::BorrowBinding| {
        dependency.borrow == binding.borrow
            && dependency.scope == binding.scope
            && dependency.share == binding.share
            && dependency.support == binding.support
    };
    let body_reads_through_borrow = body
        .facts()
        .iter()
        .filter(|child| *child != selected && child.is_view())
        .any(|child| {
            before_state
                .fold_view_dependency(child, assumptions)
                .is_ok_and(|dependency| {
                    dependency.is_some_and(|(_, dependency)| same_authority(&dependency))
                })
        });
    if !body_reads_through_borrow {
        return Err("a borrow hold is not on a borrow the folded body views".into());
    }
    let held = ledger
        .apply_borrowing_fold_hold(hold, binding, holder)
        .map_err(|refusal| format!("a fold's borrow hold is not checked: {refusal:?}"))?;
    if after_state.borrow_ledger() != Some(&held) {
        return Err("a fold changed the borrow ledger beyond its one hold".into());
    }
    Ok(before_state.clone().with_borrow_ledger(Some(held)))
}

/// An exact automatic-storage retirement, retained beside the C transition
/// that leaves the source scope. Construction is private to the kernel.
#[derive(Clone)]
pub(crate) struct CheckedAutomaticLifetimeEnd {
    before_state: ExecutionState,
    after_state: ExecutionState,
    names: Vec<BindingName>,
}

impl CheckedAutomaticLifetimeEnd {
    pub(crate) fn before_state(&self) -> &ExecutionState {
        &self.before_state
    }
    fn advance_checked(&self, state: &ExecutionState) -> Option<ExecutionState> {
        if state != &self.before_state
            || self.after_state
                != crate::kernel::eval::end_scope_automatic_lifetimes(state, &self.names).ok()?
        {
            return None;
        }
        Some(self.after_state.clone())
    }
}

/// State transition constructed by giving up a selected, held memory view.
#[derive(Clone)]
pub(crate) struct CheckedViewRelease {
    before_state: ExecutionState,
    after_state: ExecutionState,
}

impl CheckedViewRelease {
    pub(crate) fn before_state(&self) -> &ExecutionState {
        &self.before_state
    }

    fn advance_checked(&self, state: &ExecutionState) -> Option<&ExecutionState> {
        (state.memory.same_storage_roots(&self.before_state.memory)
            && state.shares_non_memory_storage_with(&self.before_state))
        .then_some(&self.after_state)
    }
}

/// One iterated guarded-ownership step, retained with the exact state it
/// started from and the fact context it was decided under. Construction is
/// private to the kernel: `record_iterated_step` applies the step itself, and
/// trace checking applies it again from the same input.
#[derive(Clone)]
pub(crate) struct CheckedIteratedStep {
    before_state: ExecutionState,
}

impl CheckedIteratedStep {
    pub(crate) fn before_state(&self) -> &ExecutionState {
        &self.before_state
    }
}

/// Surface can request naming of cells for an ordinary observation. The
/// kernel builds the successor's resource partition from the selected body.
/// Counted observations use their ledger rule.
pub(crate) enum ResourceObservationInput<'a> {
    NamedCells(&'a SymbolicMemory),
    Legacy(&'a ExecutionState),
}

/// Kernel-checked evidence for one source-ordered, non-consuming, one-layer
/// observation of a folded composite resource. The event advances no C
/// source; it changes only the ghost-resource representation and the exact
/// facts available to later retained C theorems.
#[derive(Clone)]
pub(crate) struct CheckedResourceObservation {
    before_state: ExecutionState,
    pub(crate) after_state: ExecutionState,
    definition: Option<CompositeResourceDefinition>,
}

impl CheckedResourceObservation {
    pub(crate) fn before_state(&self) -> &ExecutionState {
        &self.before_state
    }

    #[cfg(test)]
    fn check(
        function: &ProgramFunction,
        before_state: &ExecutionState,
        before_facts: &PureFactStore,
        observed: &ResourceFact,
        after_state: &ExecutionState,
        after_facts: &PureFactStore,
        derivations: &PersistentOrderedSet<Theorem>,
        call_events: &CheckedCallEvents,
    ) -> Result<Self, &'static str> {
        Self::certify(
            function,
            before_state,
            before_facts,
            observed,
            ResourceObservationInput::Legacy(after_state),
            after_facts,
            derivations,
            call_events,
        )
    }

    fn certify(
        function: &ProgramFunction,
        before_state: &ExecutionState,
        before_facts: &PureFactStore,
        observed: &ResourceFact,
        input: ResourceObservationInput<'_>,
        after_facts: &PureFactStore,
        derivations: &PersistentOrderedSet<Theorem>,
        call_events: &CheckedCallEvents,
    ) -> Result<Self, &'static str> {
        // Only an authorized family has a population count to observe; any
        // other observation is an ordinary resource observation.
        let counted = match observed.resource() {
            crate::kernel::Resource::Composite { name, .. } => function
                .proof_composite_resource_definition(name)
                .is_none_or(|definition| definition.is_authorized()),
            crate::kernel::Resource::Token { name, .. } => !function
                .contract_interface()
                .is_ordinary_abstract_family(name),
            _ => true,
        };
        if counted {
            let ResourceObservationInput::Legacy(after_state) = input else {
                return Err("count observation requires the ledger observation rule");
            };
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
            let crate::kernel::Resource::Composite { name, .. } = observed.resource() else {
                return Err("count observation requires an owned declared member");
            };
            function
                .proof_composite_resource_definition(name)
                .ok_or("the observed definition is not registered on the function")?;
            let bound = crate::kernel::api::checked_owned_resource_count_lower_bound(
                before_state,
                observed,
                before_facts.assumptions(),
            )
            .ok_or("count observation lacks member ownership or count authority")?;
            let nonnegative = crate::kernel::api::owned_quantity_nonnegative_claim(observed)
                .ok_or("count observation requires owned member quantity")?;
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
                definition: None,
            });
        }
        if !before_state.borrow_bindings_are_consistent() {
            return Err("resource observation carries mismatched borrow dependency sidecar");
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
        let crate::kernel::Resource::Composite { name, .. } = observed.resource() else {
            return Err("resource observation evidence requires a composite resource");
        };
        let definition = function
            .composite_resource_definition(name)
            .cloned()
            .ok_or("the observed composite definition is not registered on the function")?;

        let named_state;
        let (after_state, construct) = match input {
            ResourceObservationInput::NamedCells(memory) => {
                // The input describes memory naming only. No caller-supplied
                // locals, resource context, or borrow ledger enters construction.
                named_state = before_state
                    .clone()
                    .with_materialized_memory_at_current_point(memory.clone());
                (&named_state, true)
            }
            #[cfg(not(test))]
            ResourceObservationInput::Legacy(_) => {
                return Err("ordinary resource observation requires named cells");
            }
            #[cfg(test)]
            ResourceObservationInput::Legacy(after_state) => {
                if !after_state.borrow_bindings_are_consistent() {
                    return Err(
                        "resource observation carries mismatched borrow dependency sidecar",
                    );
                }
                // Compare everything but memory: take the before state's memory
                // and place, without making a point for the scratch copy.
                let mut concrete_after = after_state.clone();
                concrete_after.keep_memory_of(before_state);
                concrete_after =
                    concrete_after.with_resource_context(before_state.resources.clone());
                if concrete_after != *before_state {
                    return Err("resource observation changed concrete execution state");
                }
                (after_state, false)
            }
        };
        if memory_only_adds_named_cells(before_state, after_state.memory()).is_err()
            && !crate::kernel::api::contract_certification::memories_definitionally_equal(
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
        if observed.is_own() && !zero_quantity && observation_support.is_none() {
            return Err("resource observation requires a directly selected live owner");
        }
        let observation_authority = before_state
            .resources()
            .directly_supporting_fact(observed, assumptions)
            .unwrap_or(observed);
        let projects_body =
            observed.is_view() || observed.has_proven_positive_quantity(assumptions);
        let observed_at = after_state.program_point();
        let (children, raw_children) = if !projects_body {
            (Vec::new(), Vec::new())
        } else {
            let definition_authority = ResourceFact::own(observed.resource().clone());
            let temporary = ResourceContext::new_with_equalities(assumptions)
                .unchecked_with_fact(definition_authority.clone());
            let (_, children, raw_children) =
                crate::kernel::functions::expand_composite_resource_fact_with_children(
                    &temporary,
                    &definition_authority,
                    function.composite_resource_definitions(),
                    &observed_at,
                    assumptions,
                )
                .ok_or("the observed composite body could not be instantiated")?;
            (children, raw_children)
        };
        let body_is_already_exposed = raw_children.iter().any(ResourceFact::is_own)
            && raw_children
                .iter()
                .filter(|fact| fact.is_own())
                .all(|fact| {
                    before_state
                        .resources()
                        .directly_supporting_fact(fact, assumptions)
                        .is_some()
                });
        let borrowed = if before_state.borrow_bindings().is_empty() {
            None
        } else {
            before_state
                .unique_borrowed_resource_dependency(observed)
                .map_err(|_| "resource observation refused ambiguous or inactive parent borrow")?
        };
        let all_views = raw_children
            .iter()
            .filter_map(|fact| fact.core_with_assumptions(assumptions));
        let mut expected_views = Vec::new();
        for child in all_views {
            if before_state
                .resources()
                .contains_exact_representation(&child)
            {
                if let Some(parent) = &borrowed {
                    let existing = before_state
                        .unique_borrowed_resource_dependency(&child)
                        .map_err(
                            |_| "resource observation refused ambiguous or inactive child borrow",
                        )?;
                    if existing.as_ref().is_none_or(|binding| {
                        binding.borrow != parent.borrow
                            || binding.scope != parent.scope
                            || binding.share != parent.share
                            || binding.support != parent.support
                    }) {
                        return Err(
                            "resource observation cannot reuse an unbound or differently bound child",
                        );
                    }
                }
            } else if !body_is_already_exposed {
                expected_views.push(child);
            }
        }
        let after_state = if construct {
            let resources = before_state.resources().clone();
            let witness = (!body_is_already_exposed)
                .then(|| resources.open_structural_witness(observed, assumptions))
                .flatten();
            let (resources, inserted) = match observation_support {
                Some((occurrence, support)) => resources
                    .unchecked_with_supported_facts_from_occurrence_with_memory_and_occurrences(
                        occurrence,
                        support,
                        expected_views,
                        after_state.memory(),
                    ),
                None => resources.unchecked_with_facts_and_occurrences(expected_views),
            };
            let resources = resources.with_opened_structural_witnesses(
                witness,
                &raw_children,
                true,
                assumptions,
            );
            let mut next = after_state.clone();
            if let Some(binding) = borrowed.filter(|_| !inserted.is_empty()) {
                let evidence =
                    crate::kernel::borrows::CompositeProjectionEvidence::from_checked_expansion(
                        observed.clone(),
                        inserted.iter().map(|(child, _)| child.clone()).collect(),
                    )
                    .ok_or("resource observation cannot project a non-view child of a borrow")?;
                let ledger = before_state
                    .borrow_ledger()
                    .zip(before_state.borrow_participant())
                    .ok_or("resource observation has no active borrow holder")?;
                let ledger = ledger
                    .0
                    .project_observed_body(ledger.1, &binding, evidence)
                    .map_err(
                        |_| "resource observation cannot project a child of the viewed composite",
                    )?;
                next = next.with_borrow_ledger(Some(ledger));
                next.with_resource_context_and_borrow_dependencies(
                    resources,
                    inserted.into_iter().map(|(viewed, occurrence)| {
                        (
                            occurrence,
                            crate::kernel::BorrowBinding {
                                viewed,
                                ..binding.clone()
                            },
                        )
                    }),
                )
            } else {
                next.with_resource_context(resources)
            }
        } else {
            #[cfg(not(test))]
            unreachable!("ordinary observation only accepts a naming input");
            #[cfg(test)]
            {
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
                        !after_state.resources().has_supported_projection(
                            fact,
                            support_occurrence,
                            support,
                        )
                    }) {
                        return Err("resource observation views are missing their owned support");
                    }
                }
                after_state.clone()
            }
        };

        let introduced = after_facts
            .introduced_since(before_facts)
            .ok_or("resource observation facts do not descend from the input facts")?;
        let child_context =
            ResourceContext::new_with_equalities(assumptions).unchecked_with_facts(children);
        let mut allowed = child_context.observable_facts_assuming_valid(assumptions);
        allowed.push(Proposition::ResourceComposition(child_context.clone()));
        let relation_authority = ResourceFact::own(observed.resource().clone());
        if projects_body
            && let Some(propositions) =
                crate::kernel::functions::evaluate_composite_resource_relation_propositions(
                    &relation_authority,
                    function.composite_resource_definitions(),
                    &observed_at,
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
                    &after_state.program_point(),
                    assumptions,
                )
        {
            allowed.extend(propositions);
        }
        if projects_body
            && let Some(instantiated) =
                crate::kernel::functions::instantiate_composite_resource_facts_at(
                    observation_authority,
                    function.composite_resource_definitions(),
                    &observed_at,
                    &child_context,
                    assumptions,
                )
        {
            allowed.extend(instantiated.propositions);
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
                && !crate::kernel::proposition_holds_without_facts(fact)
                && !resource_composition_is_supported_by(fact, &child_context, assumptions)
                && !allowed_assumptions.proves_exact(fact)
        }) {
            return Err("resource observation produced an unchecked pure-fact delta");
        }

        // The capture lent its call events to the checks above.
        load_equality_capture.finish();
        Ok(Self {
            before_state: before_state.clone(),
            after_state: after_state.clone(),
            definition: Some(definition),
        })
    }

    /// The registered composite definition the event applied.
    pub(crate) fn definition(&self) -> Option<&CompositeResourceDefinition> {
        self.definition.as_ref()
    }
}

fn resource_composition_is_supported_by(
    proposition: &Proposition,
    available: &ResourceContext,
    assumptions: &PureFactContext,
) -> bool {
    let Proposition::ResourceComposition(required) = proposition else {
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

/// Kernel-issued evidence for the exact contract-entry state from which a
/// function proof begins. In particular, this retains population materialization
/// instead of asking finalization to reconstruct it from Surface bookkeeping.
#[derive(Clone)]
pub(crate) struct CheckedFunctionEntry {
    cases: Option<Arc<crate::kernel::PreparedContractEntryCases>>,
    caller_state: ExecutionState,
    function: Arc<ProgramFunction>,
    arguments: Vec<ProgramExpression>,
    entry_state: ExecutionState,
    boundary_transfer: Option<Arc<crate::kernel::functions::CheckedBoundaryResourceTransfer>>,
    /// The facts the proof assumes at entry: the contract's requirements
    /// and the caller's facts, before any step. Recorded evidence is
    /// checked under these, not under each step's full context, so the
    /// definitional comparisons stay proportional to the entry.
    assumptions: PureFactContext,
}

impl CheckedFunctionEntry {
    #[cfg(test)]
    fn check(
        caller_state: &ExecutionState,
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        expected_entry_state: &ExecutionState,
        assumptions: PureFactContext,
    ) -> Result<Arc<Self>, RuntimeError> {
        let entry_state =
            crate::kernel::program_function_entry_state(caller_state, function, arguments)
                .ok_or_else(|| {
                    RuntimeError::FunctionContract(
                        "could not bind the function entry arguments".into(),
                    )
                })?;
        if &entry_state != expected_entry_state {
            return Err(RuntimeError::FunctionContract(
                "the checked function entry does not match the proof entry".into(),
            ));
        }
        Self::construct(
            caller_state,
            function,
            arguments,
            entry_state,
            assumptions,
            None,
        )
    }

    fn construct(
        caller_state: &ExecutionState,
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        entry_state: ExecutionState,
        assumptions: PureFactContext,
        cases: Option<Arc<crate::kernel::PreparedContractEntryCases>>,
    ) -> Result<Arc<Self>, RuntimeError> {
        let function = Arc::new(function.clone());
        let boundary_transfer = {
            Some(
                // The function's own entry clauses; the proof keeps the
                // unflagged assumptions (`assume_entry_clause_spans`).
                crate::kernel::functions::capture_checked_boundary_resource_transfer(
                    caller_state,
                    function.clone(),
                    arguments,
                    &assumptions.clone().assume_entry_clause_spans(),
                    &mut ExecutionBudget::beside_live_state(),
                )
                .map_err(|limit| {
                    RuntimeError::FunctionContract(format!(
                        "checking the function entry resource transfer stopped at {}",
                        limit.describe(),
                    ))
                })??,
            )
        };
        if let (Some(cases), Some(transfer)) = (&cases, &boundary_transfer) {
            cases.retain_closing_footprint(transfer, &assumptions);
        }
        let entry = Self {
            cases,
            caller_state: caller_state.clone(),
            function,
            arguments: arguments.to_vec(),
            entry_state,
            boundary_transfer,
            assumptions,
        };
        Ok(Arc::new(entry))
    }

    /// The facts the proof assumed at entry.
    pub(crate) fn assumptions(&self) -> &PureFactContext {
        &self.assumptions
    }

    pub(crate) fn entry_state_for(
        &self,
        caller_state: &ExecutionState,
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        assumptions: &PureFactContext,
    ) -> Option<ExecutionState> {
        if self.function.as_ref() != function || self.arguments != arguments {
            return None;
        }
        if &self.caller_state == caller_state {
            return Some(self.entry_state.clone());
        }
        let rebased_entry =
            crate::kernel::program_function_entry_state(caller_state, function, arguments)?;
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
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
    ) -> Option<&ExecutionState> {
        (self.function.has_same_entry_and_source(function) && self.arguments == arguments)
            .then_some(&self.entry_state)
    }

    pub(crate) fn caller_state(&self) -> &ExecutionState {
        &self.caller_state
    }
}

/// Authority retained only by an execution composed under its opened entry's
/// own premises. Separate clause proofs share this generative entry identity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ContractEntryAuthority {
    cases: Arc<crate::kernel::PreparedContractEntryCases>,
}

impl ContractEntryAuthority {
    pub(crate) fn cases(&self) -> &Arc<crate::kernel::PreparedContractEntryCases> {
        &self.cases
    }
}

/// The contract entry opened before a body proof. The producer selects its
/// premises and constructs the state and resource transfer together; retaining
/// it never asks the body proof to reconstruct or authorize its own inputs.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum OpenedEntryFactSource {
    SourceFact(usize),
    Requirement(usize),
}

#[derive(Clone)]
pub(crate) struct OpenedContractEntry {
    entry: Arc<CheckedFunctionEntry>,
    facts: PureFactStore,
    source_origins: Vec<Option<OpenedEntryFactSource>>,
    cases: Arc<crate::kernel::PreparedContractEntryCases>,
    contract_root: Option<crate::kernel::WholeContractRoot>,
}

impl OpenedContractEntry {
    pub(crate) fn open(
        caller_state: &ExecutionState,
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        source_facts: &(impl super::PropositionSource + ?Sized),
        environment: &crate::kernel::ExecutionEnvironment,
    ) -> Result<Self, RuntimeError> {
        let contract = crate::kernel::program_function_contract_entry_with_refusal(
            caller_state,
            function,
            arguments,
        )
        .map_err(crate::kernel::ContractEntryRefusal::into_runtime_error)?;
        let mut propositions = Vec::new();
        let mut source_origins = Vec::new();
        let mut kept = std::collections::BTreeSet::new();
        for (index, fact) in source_facts.propositions().enumerate() {
            // Preserve source aliases, except complete pointer equations: those
            // keep the entry producer's form, avoiding extra read-over-write
            // equations being admitted as independent premises.
            let selected = match fact {
                condition_source_0 @ Proposition::ConditionIs(_, _)
                    if let Some((crate::kernel::OldConditionTerm::PointerEqual(..), _)) =
                        condition_source_0.old_condition() =>
                {
                    contract.explicitly_states(fact)
                }
                _ => contract.states(fact),
            };
            if selected && kept.insert(fact.clone()) {
                propositions.push(fact.clone());
                source_origins.push(Some(OpenedEntryFactSource::SourceFact(index)));
            }
        }
        for fact in contract.facts() {
            use crate::kernel::ContractEntryFactOrigin as Origin;
            let visible = !matches!(
                fact.origin(),
                Origin::CompositeDefinition
                    | Origin::PopulationFact
                    | Origin::Observable
                    | Origin::ResourceQuantity
                    | Origin::PredicateBody(_)
            );
            if visible && kept.insert(fact.proposition().clone()) {
                propositions.push(fact.proposition().clone());
                source_origins.push(match fact.origin() {
                    Origin::PredicateIdentity(Some(source)) => {
                        Some(OpenedEntryFactSource::Requirement(source))
                    }
                    _ => None,
                });
            }
        }
        let byte_order = environment.byte_order_fact();
        if kept.insert(byte_order.clone()) {
            propositions.push(byte_order);
            source_origins.push(None);
        }
        // Contract facts and `function.entry` must name the same observation
        // point, including when binding by-value parameters allocated storage.
        let entry_state = contract.argument_state().clone();
        let cases = Arc::new(crate::kernel::prepare_function_contract_entry_cases(
            contract,
            environment.byte_order_fact(),
        ));
        let mut facts = PureFactStore::from_ordered(&propositions);
        facts.prepare_entry_resources(caller_state.resources());
        let entry = CheckedFunctionEntry::construct(
            caller_state,
            function,
            arguments,
            entry_state,
            facts.assumptions().clone(),
            Some(cases.clone()),
        )?;
        Ok(Self {
            entry,
            facts,
            source_origins,
            cases,
            contract_root: None,
        })
    }

    pub(crate) fn caller_state(&self) -> &ExecutionState {
        self.entry.caller_state()
    }

    /// The one annotated function whose binder identities this entry owns.
    pub(crate) fn function(&self) -> &ProgramFunction {
        &self.entry.function
    }

    /// Start the parent judgment for a function-proof session. Independent
    /// entry/execution APIs do not acquire whole-contract obligations.
    pub(crate) fn open_contract_root(
        mut self,
        program: Option<&crate::kernel::ProgramContractBodies>,
    ) -> Result<Self, String> {
        self.contract_root = Some(match program {
            Some(program) => {
                crate::kernel::WholeContractRoot::open_in_program(self.cases.clone(), program)?
            }
            None => crate::kernel::WholeContractRoot::open(self.cases.clone())?,
        });
        Ok(self)
    }

    pub(crate) fn contract_root(&self) -> Option<&crate::kernel::WholeContractRoot> {
        self.contract_root.as_ref()
    }

    pub(crate) fn prepared_cases(&self) -> &Arc<crate::kernel::PreparedContractEntryCases> {
        &self.cases
    }

    pub(crate) fn facts(&self) -> &PureFactStore {
        &self.facts
    }

    /// The selected source occurrence for each admitted fact. Derived facts
    /// carry no source occurrence; Surface retains only their presentation.
    pub(crate) fn source_origins(&self) -> &[Option<OpenedEntryFactSource>] {
        &self.source_origins
    }

    pub(crate) fn entry_state(&self) -> &ExecutionState {
        &self.entry.entry_state
    }

    pub(crate) fn into_execution_core_with_environment(
        self,
        environment: &crate::kernel::ExecutionEnvironment,
    ) -> Result<ExecutionProofCore, String> {
        let descent = crate::kernel::termination::descent_completion::OpenedDescent::open(
            &self.entry.function,
            environment,
        )?;
        // This explicit entry producer publishes the contract's admitted
        // resource input once. Subsequent child/alias lookups use its deltas.
        if self
            .entry
            .function
            .contract_interface()
            .recursion_resource()
            .is_some()
        {
            self.entry
                .caller_state
                .resources()
                .synchronize_memory_equalities(self.facts.assumptions());
        }
        let mut core = self.into_execution_core();
        if let Some(resource) = environment
            .recursion_anchor()
            .and_then(|anchor| anchor.structural_resource.as_ref())
        {
            core.state = resource.at_entry(&core.state).into();
        }
        core.descent = descent;
        Ok(core)
    }

    pub(crate) fn into_execution_core(self) -> ExecutionProofCore {
        let mut core = ExecutionProofCore::at_entry(
            self.entry.caller_state.clone(),
            ExecutionFrontier::default(),
        );
        core.function_entry = Some(self.entry);
        core.entry_facts = Some(self.facts);
        core
    }
}

/// Each premise among `facts` that mentions algebraic variable `variable`,
/// instantiated at `constructor`, when that changes it. The facts come from
/// the index of facts by the variables they mention, so the work is the
/// premises about this value and nothing else. A constructor equation for the
/// variable is the case itself, so it is skipped.
fn matched_value_premise_instances(
    facts: &PureFactStore,
    variable: Variable,
    constructor: &crate::kernel::AlgebraicTerm,
) -> Vec<Proposition> {
    let key = crate::kernel::AtomicConnectionKey::Variable(variable);
    let (connected, _) = facts.assumptions().atomic_facts_connected_to(&key, true);
    let mut instances = Vec::new();
    for fact in connected {
        crate::instrumentation::record_deterministic_work(1);
        let premise = match fact {
            crate::kernel::AtomicConnectedFact::Condition(condition, value) => {
                Proposition::condition_is(condition.clone(), value)
            }
            crate::kernel::AtomicConnectedFact::Proposition(proposition) => proposition.clone(),
        };
        if matches!(
            &premise,
            Proposition::Equal(
                crate::kernel::Term::Algebraic(_),
                crate::kernel::Term::Algebraic(_)
            )
        ) {
            continue;
        }
        let instance = crate::kernel::reasoning::substitute_algebraic_variable_in_proposition(
            &premise,
            variable,
            constructor,
        );
        if instance != premise && !instances.contains(&instance) {
            // A premise whose consequent the arm's constructor makes an
            // equation of two constructors says what that equation decides.
            for decided in super::facts::constructor_consequent_instances(&instance) {
                if !instances.contains(&decided) {
                    instances.push(decided);
                }
            }
            instances.push(instance);
        }
    }
    instances
}

/// One kernel-issued complementary logical partition over an unchanged C
/// execution frontier.
#[derive(Clone)]
pub(crate) struct CheckedProofCasePartition {
    identity: Arc<()>,
    root_facts: PureFactStore,
    case_facts: Vec<Proposition>,
    /// The exact delta each arm adds to `root_facts`: its constructor case,
    /// followed by any facts checked for the one resource field that was
    /// matched. Keeping this in the kernel-issued partition makes independent
    /// certificate checking use the same premises without trusting surface
    /// bookkeeping.
    arm_additions: Vec<Vec<Proposition>>,
    /// The indexed contexts constructed while deriving those exact deltas.
    /// Entering an arm shares its context rather than admitting it again.
    arm_contexts: Vec<PureFactStore>,
    /// Ordered declaration correspondence, including clauses whose exact
    /// proposition was already in the arm's fact store.
    arm_body_clauses: Vec<Vec<crate::kernel::functions::ResourceBodyClauseRecord>>,
    /// Exact contradictions checked under that arm's canonical premises.
    excluded: Vec<Option<Proposition>>,
    /// Generative constructor witnesses are introduced only at their unchanged
    /// entry scope. Complementary propositional splits need no such scope.
    witness_scope: Option<SharedValue<ExecutionState>>,
}

/// One entry of an outcome-evidence fork plan
/// ([`ExecutionProofCore::fork_outcome_evidence`]): keep a path's trace, or
/// split it into one trace per live case of a checked partition, each of
/// which may split again.
pub(crate) enum OutcomeEvidenceFork {
    Keep,
    Split {
        partition: Arc<CheckedProofCasePartition>,
        /// One arm per case the partition does not exclude, in case order.
        arms: Vec<OutcomeForkArm>,
    },
}

/// One arm of an outcome-evidence split: the partition case it enters, its
/// facts, and how its trace continues.
pub(crate) struct OutcomeForkArm {
    pub(crate) case: usize,
    pub(crate) facts: PureFactStore,
    pub(crate) then: OutcomeEvidenceFork,
}

impl OutcomeEvidenceFork {
    /// The split of a two-case partition, such as a proof `if` or `cases`.
    pub(crate) fn binary(
        partition: Arc<CheckedProofCasePartition>,
        arm_facts: [PureFactStore; 2],
        then: [OutcomeEvidenceFork; 2],
    ) -> Self {
        let [first, second] = then;
        let [first_facts, second_facts] = arm_facts;
        Self::Split {
            partition,
            arms: vec![
                OutcomeForkArm {
                    case: 0,
                    facts: first_facts,
                    then: first,
                },
                OutcomeForkArm {
                    case: 1,
                    facts: second_facts,
                    then: second,
                },
            ],
        }
    }
}

/// How many traces one entry of an outcome evidence fork plan produces.
fn outcome_fork_count(fork: &OutcomeEvidenceFork) -> usize {
    match fork {
        OutcomeEvidenceFork::Keep => 1,
        OutcomeEvidenceFork::Split { arms, .. } => {
            arms.iter().map(|arm| outcome_fork_count(&arm.then)).sum()
        }
    }
}

/// One arm of a checked logical partition. This event advances no C source;
/// it changes only the authoritative fact context for later evidence.
#[derive(Clone)]
pub(crate) struct CheckedProofCaseArm {
    partition: Arc<CheckedProofCasePartition>,
    arm_index: usize,
    facts: PureFactStore,
}

/// Whether two logical cases cover every state `root_facts` admits: they
/// are complementary, as a proof `if` splits, or their disjunction is an
/// exact available fact, as `cases` splits.
pub(crate) fn proof_cases_are_exhaustive(
    root_facts: &PureFactStore,
    then_fact: &Proposition,
    else_fact: &Proposition,
) -> bool {
    let negated_then = Proposition::Not(Box::new(then_fact.clone()));
    *else_fact == negated_then
        || super::fact_reasoning::condition_polarity_forms(&negated_then).contains(else_fact)
        || root_facts.contains(&Proposition::Or(
            Box::new(then_fact.clone()),
            Box::new(else_fact.clone()),
        ))
}

impl CheckedProofCasePartition {
    /// The cases this partition does not exclude, in order.
    pub(crate) fn live_cases(&self) -> impl Iterator<Item = usize> + '_ {
        self.excluded
            .iter()
            .enumerate()
            .filter(|(_, excluded)| excluded.is_none())
            .map(|(case, _)| case)
    }

    /// Excludes a constructor whose arm refutes itself after bridging steps.
    ///
    /// `arm_facts` are the facts the arm's own proof reached: this case's
    /// facts plus what the arm's `have`s established from them, each checked
    /// by its own proof. The arm must hold `false` and its constructor fact, so a
    /// context from another arm, or from before the split, cannot exclude
    /// this one.
    pub(crate) fn excluding_constructor_case_in(
        &self,
        index: usize,
        arm_facts: &PureFactStore,
    ) -> Option<Arc<Self>> {
        self.witness_scope.as_ref()?;
        if !arm_facts.contains(self.case_fact(index)?) || !arm_facts.holds_false() {
            return None;
        }
        let mut successor = self.clone();
        successor.identity = Arc::new(());
        successor.excluded[index] = Some(Proposition::condition_is(
            OldConditionTerm::Constant(false),
            true,
        ));
        Some(Arc::new(successor))
    }

    pub(crate) fn case_fact(&self, index: usize) -> Option<&Proposition> {
        self.case_facts.get(index)
    }

    /// The facts arm `index` adds beyond its case fact: constructor field
    /// equalities and the instances of premises about the matched value.
    pub(crate) fn additions_for_case(&self, index: usize) -> &[Proposition] {
        self.arm_additions.get(index).map_or(&[], Vec::as_slice)
    }

    pub(crate) fn body_clauses_for_case(
        &self,
        index: usize,
    ) -> Option<&[crate::kernel::functions::ResourceBodyClauseRecord]> {
        self.arm_body_clauses.get(index).map(Vec::as_slice)
    }

    pub(crate) fn facts_for_case(&self, index: usize) -> Option<PureFactStore> {
        self.arm_contexts.get(index).cloned()
    }

    /// The facts this partition was issued against. An arm's premises are
    /// these plus that arm's case fact, so a caller entering an arm builds
    /// the arm's context from here rather than from its own branch: the
    /// partition may carry model facts the frontier's premises force on the
    /// scrutinee's instance (A26, gap 57b), and those belong to every arm.
    pub(crate) fn root_facts(&self) -> &PureFactStore {
        &self.root_facts
    }
    pub(crate) fn check(
        root_facts: &PureFactStore,
        then_fact: Proposition,
        else_fact: Proposition,
    ) -> Option<Arc<Self>> {
        if !proof_cases_are_exhaustive(root_facts, &then_fact, &else_fact) {
            return None;
        }
        let arm_contexts: Vec<_> = [&then_fact, &else_fact]
            .into_iter()
            .map(|fact| root_facts.with_fact(fact.clone()))
            .collect();
        let arm_additions = arm_contexts
            .iter()
            .map(|facts| facts.introduced_since(root_facts).unwrap_or_default())
            .collect();
        Some(Arc::new(Self {
            identity: Arc::new(()),
            root_facts: root_facts.clone(),
            case_facts: vec![then_fact.clone(), else_fact.clone()],
            arm_additions,
            arm_contexts,
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
    start_state: ExecutionState,
    /// The source the arms were walked over from the split, and the source
    /// they all leave: a later walk reaching the join over the same source
    /// takes this result instead of walking the arms again.
    start_source: Option<ProgramStatement>,
    end_source: Option<ProgramStatement>,
    joined_state: ExecutionState,
    /// The facts the proof holds after the join: the partition's root facts,
    /// and what every arm established or the interface admits.
    joined_facts: PureFactStore,
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
    resource_definitions: Vec<crate::kernel::CompositeResourceDefinition>,
    lowerings: Arc<Vec<[CheckedInterfaceLowering; 3]>>,
    next_kernel_variable: u64,
}

#[derive(Clone)]
struct CheckedProofCaseJoinArm {
    /// The cases of the partition this arm stands for.
    cases: Vec<usize>,
    facts: PureFactStore,
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
) -> Option<(&Arc<CheckedProofCasePartition>, Vec<usize>, &PureFactStore)> {
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
    start_state: ExecutionState,
    start_source: Option<ProgramStatement>,
    end_source: Option<ProgramStatement>,
    /// Each arm's memory changes, as its walk met them.
    memory_steps: Vec<Vec<CheckedMemoryStep>>,
}

impl CheckedProofCaseJoin {
    /// Checks that `arms` are arms of one partition over disjoint cases,
    /// each continuing `parent`'s one trace to the same program point, and
    /// with `same_state` to the same state.
    fn walk_arms(
        parent: &ExecutionProofCore,
        arms: &[(&ExecutionProofCore, &PureFactStore)],
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
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
        let mut joined: Option<(&ExecutionProofCore, Option<ProgramStatement>)> = None;
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
            let progress =
                check_evidence_events(walked.walked_events(), start_state.clone(), source.clone())
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
        let (_, end_source) = joined.expect("a join of two arms walked them");
        Ok(WalkedCaseArms {
            partition: partition.expect("a join of two arms found their partition"),
            arms: checked,
            start_state,
            start_source: source,
            end_source,
            memory_steps,
        })
    }

    /// Checks that `arms` rejoin in one state, and that `successor_facts`
    /// adds to the partition's root facts only what every arm established.
    fn check(
        parent: &ExecutionProofCore,
        arms: &[(&ExecutionProofCore, &PureFactStore)],
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        successor_facts: &PureFactStore,
    ) -> Result<Self, &'static str> {
        let WalkedCaseArms {
            partition,
            arms: checked,
            start_state,
            start_source,
            end_source,
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
        let mut joined_state = arms[0].0.reached_state().clone();
        let mut resources = joined_state.resources().clone();
        for (arm, _) in &arms[1..] {
            resources.meet_structural_witnesses(arm.reached_state().resources());
        }
        joined_state = joined_state.with_resource_context(resources);
        Ok(Self {
            partition,
            arms: checked,
            start_state,
            start_source,
            end_source,
            joined_state,
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
    fn construct_interface(
        parent: &ExecutionProofCore,
        root_facts: &PureFactStore,
        arms: [(&ExecutionProofCore, &PureFactStore); 2],
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        interface_specs: &[SpecProposition],
        interface_resource_specs: &[ResourceSpec],
        arm_effect_facts: [&(impl ExecutionFactSource + ?Sized); 2],
        joined_state: &ExecutionState,
        successor_facts: &PureFactStore,
        old_reference: Option<&ExecutionState>,
    ) -> Result<Self, &'static str> {
        let WalkedCaseArms {
            partition,
            arms: checked,
            start_state,
            start_source,
            end_source,
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
            state: constructed_state,
            next_kernel_variable,
            arm_interface_resources,
            introduced,
            interface_lowerings,
        } = construct_interface_abstraction(
            root_facts,
            &start_state,
            parent,
            arm_cores,
            arm_facts,
            interface_specs,
            interface_resource_specs,
            joined_state,
            successor_facts,
            old_reference,
        )?;
        let mut resources = constructed_state.resources().clone();
        resources.structural_witnesses = arm_cores[0]
            .reached_state()
            .resources()
            .structural_witnesses
            .clone();
        resources.meet_structural_witnesses(arm_cores[1].reached_state().resources());
        let constructed_state = constructed_state.with_resource_context(resources);
        let joined_state = &constructed_state;
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
            start_source,
            end_source,
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

    /// Whether an interface join was checked under this function's resource
    /// definitions and kept a complete, consistent lowering of every
    /// interface fact. A structural join has nothing of the kind to check.
    pub(crate) fn matches_interface_resource_definitions(
        &self,
        function: &ProgramFunction,
    ) -> bool {
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
                    && lowerings[2].retained_state == self.joined_state
                    && lowerings[0].facts.shares_premises_with(&then_arm.facts)
                    && lowerings[1].facts.shares_premises_with(&else_arm.facts)
                    && lowerings[2].facts.shares_premises_with(&self.joined_facts)
            })
    }

    pub(crate) fn start_state(&self) -> &ExecutionState {
        &self.start_state
    }

    pub(crate) fn joined_state(&self) -> &ExecutionState {
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
                    | CheckedExecutionEvent::CompletedContext(_)
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

    /// The source the arms leave when a walk reaches the join at `state`
    /// over `source`: the recorded result when that is the source they were
    /// checked over, and otherwise their walk over it, which fails if any
    /// arm misses that one program point or, without an interface, the
    /// joined state.
    fn advance_checked(
        &self,
        state: &ExecutionState,
        source: &Option<ProgramStatement>,
    ) -> Option<Option<ProgramStatement>> {
        if state != &self.start_state {
            return None;
        }
        // The check that built this join walked every arm from this state
        // over this source; walking them again would only repeat it.
        if source == &self.start_source {
            return Some(self.end_source.clone());
        }
        // A walk over a different source, such as one that continues past
        // the program point the arms reached, walks the arms over it.
        let mut remaining: Option<Option<ProgramStatement>> = None;
        for arm in &self.arms {
            let (entered, cases, _) = case_join_arm_entry(&arm.events)?;
            if !Arc::ptr_eq(entered, &self.partition) || cases != arm.cases {
                return None;
            }
            let progress =
                check_evidence_events(arm.walked_events(), state.clone(), source.clone())?;
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
    arm_interface_resources: [Vec<ResourceFact>; 2],
    successor_interface_resources: Vec<ResourceFact>,
    successor_interface_resource_facts: Vec<Proposition>,
    /// What neither arm changed, with the checked interface resources
    /// composed into that frame.
    expected_resources: ResourceContext,
}

fn interface_join_resources(
    parent: &ExecutionProofCore,
    arms: [&ExecutionProofCore; 2],
    arm_facts: [&PureFactStore; 2],
    interface_resource_specs: &[ResourceSpec],
    joined_state: &ExecutionState,
    successor_facts: &PureFactStore,
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
    }
    let mut arm_residuals = Vec::with_capacity(2);
    for (index, (arm, facts)) in arms.iter().zip(arm_facts).enumerate() {
        let mut remaining = arm.state.resources().clone();
        // Check observations against the held context while the owned
        // support is present. The same indexed view judgment is used by
        // Surface and for views already established by the common frame.
        for required in arm_interface_resources[index]
            .iter()
            .filter(|fact| fact.is_view())
        {
            if !remaining.satisfies_fact(required, facts.assumptions()) {
                return Err("an interface resource is not owned by one concrete arm");
            }
        }
        // Consume owned exports in source order: giving up one may also
        // remove the retained observations it supported.
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
    // Successor expressions can read through the retained common frame,
    // while named interface models are supplied by the arm abstraction.
    // This is a lowering scope only; final ownership is constructed below
    // from the clauses that both concrete arms supplied.
    let lowering_state = joined_state.clone().with_resource_context(
        common_resources
            .unpublished_contract_view()
            .unchecked_with_facts(joined_state.resources().iter().cloned()),
    );
    for spec in interface_resource_specs {
        let fact = evaluate_interface_resource_spec(spec, &lowering_state, successor_facts)
            .ok_or("an interface resource does not lower at the abstract successor")?;
        if let Some(proposition) = interface_resource_intrinsic_fact(spec, &fact, &lowering_state) {
            successor_interface_resource_facts.push(proposition);
        }
        if let Some(range) = fact.memory_range() {
            successor_interface_resource_facts
                .extend(crate::kernel::admitted_memory_range_span_facts(range));
        }
        successor_interface_resources.push(fact);
    }
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
    let assumptions = successor_facts.assumptions();
    let (expected_resources, mut inserted) = common_resources
        .install_established_partition(additions, assumptions)
        .map_err(|_| "the interface resources do not form a valid successor context")?;
    // Keep the native representation of structural resource witnesses.
    // Each other published occurrence can coalesce with its indexed neighbors.
    inserted.retain(|(fact, _)| !expected_resources.protects_structural_resource(fact.resource()));
    let expected_resources = expected_resources.normalized_delta(inserted, assumptions);
    Ok(InterfaceJoinResources {
        arm_interface_resources,
        successor_interface_resources,
        successor_interface_resource_facts,
        expected_resources,
    })
}

/// Accept only the facts supplied by the arms and the written interface.
fn check_interface_successor_facts(
    introduced: &[Proposition],
    arm_facts: [&PureFactStore; 2],
    interface_propositions: &std::collections::BTreeSet<&Proposition>,
    exported_resources: &[ResourceFact],
    intrinsic_facts: &[Proposition],
    assumptions: &PureFactContext,
) -> Result<(), &'static str> {
    let _timing =
        crate::instrumentation::OperationTiming::new("", "", "branch interface successor facts");
    let intrinsic_facts = intrinsic_facts
        .iter()
        .inspect(|_| crate::instrumentation::record_deterministic_work(1))
        .collect::<std::collections::BTreeSet<_>>();
    let mut composition_facts = None;
    for fact in introduced {
        crate::instrumentation::record_deterministic_work(1);
        if arm_facts
            .iter()
            .all(|facts| checked_branch_fact_is_available(facts, fact))
            || interface_propositions.contains(fact)
            || intrinsic_facts.contains(fact)
        {
            continue;
        }
        // The observable projection can supply a composition of the exports.
        // Build it lazily, since ordinary facts only need the indexes above.
        if matches!(fact, Proposition::ResourceComposition(_))
            && composition_facts
                .get_or_insert_with(|| {
                    let _timing = crate::instrumentation::OperationTiming::new(
                        "",
                        "",
                        "branch interface exported composition",
                    );
                    ResourceContext::new_with_equalities(assumptions)
                        .unchecked_with_facts(exported_resources.iter().cloned().inspect(|_| {
                            crate::instrumentation::record_deterministic_work(1);
                        }))
                        .observable_facts_assuming_valid(assumptions)
                })
                .contains(fact)
        {
            continue;
        }
        return Err("the interface successor contains an unchecked new fact");
    }
    Ok(())
}

/// What an explicit join interface makes of two concrete arms: the
/// abstraction both agree on, the interface resources each arm gives up, the
/// facts the successor gains, and the checked lowering of every interface
/// fact. The split the arms came from, a C `if` or a logical partition,
/// plays no part here.
struct CheckedInterfaceAbstraction {
    state: ExecutionState,
    next_kernel_variable: u64,
    arm_interface_resources: [Vec<ResourceFact>; 2],
    introduced: Vec<Proposition>,
    interface_lowerings: Vec<[CheckedInterfaceLowering; 3]>,
}

#[allow(clippy::too_many_arguments)]
fn construct_interface_abstraction(
    root_facts: &PureFactStore,
    split_state: &ExecutionState,
    parent: &ExecutionProofCore,
    arms: [&ExecutionProofCore; 2],
    arm_facts: [&PureFactStore; 2],
    interface_specs: &[SpecProposition],
    interface_resource_specs: &[ResourceSpec],
    joined_state: &ExecutionState,
    successor_facts: &PureFactStore,
    old_reference: Option<&ExecutionState>,
) -> Result<CheckedInterfaceAbstraction, &'static str> {
    let sibling_states = [arms[0].reached_state(), arms[1].reached_state()];
    // Both arms abstract from the same counter, the higher of the two, so
    // the abstraction is the same whichever arm allocated more and neither
    // arm's own identities can be re-issued by the join.
    let join_next_kernel_variable = arms[0]
        .next_kernel_variable
        .max(arms[1].next_kernel_variable);
    let abstract_then = crate::kernel::abstract_execution_state_for_interface_join_across(
        arms[0].reached_state(),
        &sibling_states,
        join_next_kernel_variable,
    )
    .map_err(|_| "the then interface state could not be abstracted")?;
    let abstract_else = crate::kernel::abstract_execution_state_for_interface_join_across(
        arms[1].reached_state(),
        &sibling_states,
        join_next_kernel_variable,
    )
    .map_err(|_| "the else interface state could not be abstracted")?;
    if abstract_then
        .unproved_memory_separation(root_facts)
        .is_some()
        || abstract_else
            .unproved_memory_separation(root_facts)
            .is_some()
    {
        return Err("branch memory join requires separation from active borrows at the split");
    }
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
    // dropped the same way on both sides, then check the successor's borrow
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
    // borrow dependency the successor's interface carries must be one an arm
    // already held; a changed or invented root is not admitted here.
    if !interface_successor_borrows_are_inherited(joined_state, sibling_states) {
        return Err("the interface successor claims a borrow dependency no arm held");
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
    // Construct ownership once from the concrete arms and selected
    // interface. The supplied state describes abstract memory and locals;
    // its resource context cannot grant authority to the successor.
    let constructed_state = joined_state
        .clone()
        .with_resource_context(expected_resources);
    let joined_state = &constructed_state;
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
            true,
        )
        .ok_or_else(|| {
            // Say which fact the join does not carry, for the refusal's
            // report; arm 2 is the successor.
            UNESTABLISHED_INTERFACE_GOAL.with(|unestablished| {
                if let Some(unestablished) = unestablished.borrow_mut().as_mut() {
                    unestablished.fact = spec_index;
                    unestablished.arm = 2;
                }
            });
            "an interface fact is not retained at the abstract successor"
        })?;
        interface_lowerings.push([then_lowering, else_lowering, successor]);
    }
    let interface_propositions = interface_lowerings
        .iter()
        .flat_map(|lowerings| {
            std::iter::once(&lowerings[2].path.proposition)
                .chain(lowerings[2].assumed_domains.iter())
        })
        .collect::<std::collections::BTreeSet<_>>();
    let introduced = successor_facts
        .introduced_since(root_facts)
        .ok_or("the interface successor facts do not descend from the branch root")?;
    check_interface_successor_facts(
        &introduced,
        arm_facts,
        &interface_propositions,
        &successor_interface_resources,
        &successor_interface_resource_facts,
        successor_facts.assumptions(),
    )?;

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
        state: constructed_state,
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
    joined_state: ExecutionState,
    interface_successor_facts: Option<PureFactStore>,
    interface_execution_facts: crate::kernel::ExecutionFacts,
    interface_effect_facts: crate::kernel::ExecutionFacts,
    interface_resource_definitions: Option<Vec<crate::kernel::CompositeResourceDefinition>>,
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
    facts: PureFactStore,
    events: Vec<CheckedExecutionEvent>,
}

fn branch_split_starts_at_parent(
    parent: &ExecutionProofCore,
    split_state: &ExecutionState,
    function: &ProgramFunction,
    arguments: &[ProgramExpression],
    root_facts: &PureFactStore,
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
        crate::kernel::program_function_entry_state(parent.reached_state(), function, arguments)
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
        root_facts: &PureFactStore,
        arm_theorems: [&Theorem; 2],
        arm_facts: [&PureFactStore; 2],
        parent: &ExecutionProofCore,
        arms: [&ExecutionProofCore; 2],
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
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
        let mut memory_steps = Vec::with_capacity(2);
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
            let progress =
                check_evidence_events(&events, split.state.clone(), Some(full_source.clone()))
                    .ok_or("a branch arm theorem trace does not follow its exact C source")?;
            if progress.completed.is_some() || progress.remaining != split.continuation {
                return Err("a branch arm theorem trace does not reach the shared continuation");
            }
            if &progress.state != arm.reached_state() {
                return Err("a branch arm theorem trace does not reach its recorded state");
            }
            memory_steps.push(progress.memory_steps);
            checked_arms.push(CheckedExecutionBranchArm {
                facts: arm_facts[index].clone(),
                events,
            });
        }
        let [then_arm, else_arm] = checked_arms
            .try_into()
            .map_err(|_| "the checked branch does not have exactly two arms")?;
        // A structural join retains the same checked statement-effect records
        // as an interface join, including a call's complete-pointer refinements.
        let interface_effect_facts = checked_interface_effect_facts_along(
            &split.state,
            arms[0].reached_state(),
            arms,
            arm_facts,
            arm_effect_facts,
            Some([&memory_steps[0], &memory_steps[1]]),
        )?;
        // The arms reach equal states by different routes; the join is a new
        // point reached from both.
        let mut joined_state = arms[0].reached_state().clone();
        joined_state.join_program_points(
            arms[0].reached_state(),
            arms[1].reached_state(),
            split.state.path_link(),
        );
        Ok(Self {
            split,
            arms: [then_arm, else_arm],
            joined_state,
            interface_successor_facts: None,
            interface_execution_facts: Vec::new().into(),
            interface_effect_facts,
            interface_resource_definitions: None,
            interface_lowerings: Arc::new(Vec::new()),
            interface_next_kernel_variable: None,
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn construct_interface(
        split: CheckedBranchSplit,
        root_facts: &PureFactStore,
        arm_theorems: [&Theorem; 2],
        arm_facts: [&PureFactStore; 2],
        parent: &ExecutionProofCore,
        arms: [&ExecutionProofCore; 2],
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        interface_specs: &[SpecProposition],
        interface_resource_specs: &[ResourceSpec],
        arm_effect_facts: [&(impl ExecutionFactSource + ?Sized); 2],
        joined_state: &ExecutionState,
        successor_facts: &PureFactStore,
        old_reference: Option<&ExecutionState>,
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
            state: constructed_state,
            next_kernel_variable,
            arm_interface_resources,
            introduced,
            interface_lowerings,
        } = construct_interface_abstraction(
            root_facts,
            &split.state,
            parent,
            arms,
            arm_facts,
            interface_specs,
            interface_resource_specs,
            joined_state,
            successor_facts,
            old_reference,
        )?;
        let joined_state = &constructed_state;
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
            let progress =
                check_evidence_events(&events, split.state.clone(), Some(full_source.clone()))
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
        state: &ExecutionState,
        branch_statement: &ProgramStatement,
        continuation: &Option<ProgramStatement>,
    ) -> bool {
        &self.split.state == state
            && &self.split.branch_statement == branch_statement
            && statement_sequence_is_prefix(&self.split.continuation, continuation)
    }

    pub(crate) fn joined_state(&self) -> &ExecutionState {
        &self.joined_state
    }

    pub(crate) fn start_statement(&self) -> &ProgramStatement {
        &self.split.branch_statement
    }

    pub(crate) fn continuation(&self) -> &Option<ProgramStatement> {
        &self.split.continuation
    }

    pub(crate) fn start_state(&self) -> &ExecutionState {
        &self.split.state
    }

    pub(crate) fn arm_events(&self, index: usize) -> &[CheckedExecutionEvent] {
        &self.arms[index].events
    }

    pub(crate) fn interface_successor_facts(&self) -> Option<&PureFactStore> {
        self.interface_successor_facts.as_ref()
    }

    pub(crate) fn interface_execution_facts(&self) -> &crate::kernel::ExecutionFacts {
        &self.interface_execution_facts
    }

    pub(crate) fn interface_effect_facts(&self) -> &crate::kernel::ExecutionFacts {
        &self.interface_effect_facts
    }

    pub(crate) fn matches_interface_resource_definitions(
        &self,
        function: &ProgramFunction,
    ) -> bool {
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
                    && lowerings[2].retained_state == self.joined_state
                    && lowerings[0].facts.shares_premises_with(&self.arms[0].facts)
                    && lowerings[1].facts.shares_premises_with(&self.arms[1].facts)
                    && self
                        .interface_successor_facts
                        .as_ref()
                        .is_some_and(|facts| lowerings[2].facts.shares_premises_with(facts))
            })
    }
}

/// Whether every stable-view borrow dependency the interface successor carries
/// was already held by a concrete arm.
///
/// Check the exact authority (including the borrow, share, scope, support,
/// viewed fact and hold) of each claimed binding. Interface publication can
/// give a held view a fresh occurrence, so membership is by binding value
/// and the arms maintain that index as their bindings change (D2 law 9).
fn interface_successor_borrows_are_inherited(
    successor: &ExecutionState,
    arms: [&ExecutionState; 2],
) -> bool {
    successor.borrow_bindings().iter().all(|(_, binding)| {
        arms.iter()
            .any(|arm| arm.borrow_bindings().contains_binding(binding))
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
    before: &SymbolicMemory,
    after: &SymbolicMemory,
    changed: &[(Address, crate::kernel::AccessExtent)],
    assumptions: &PureFactContext,
    fact: &ExecutionPureFact,
) -> bool {
    let erased_cells_are_certified_store_bookkeeping =
        fact.certified_store_data().is_some_and(|store| {
            store.before == *before
                && store.after == *after
                && changed.iter().any(|(changed_pointer, bytes)| {
                    changed_pointer == &store.pointer
                        && *bytes
                            == crate::kernel::assumptions::access_extent_of_value(&store.value)
                })
        });
    if erased_cells_are_certified_store_bookkeeping {
        return true;
    }
    before
        .differing_cell_pointers(after)
        .into_iter()
        .filter(|pointer| !pointer.base.is_local_block())
        .all(|diff_pointer| {
            if !after.has_known_cell_at(&diff_pointer) {
                return false;
            }
            let Some(value) = after.known_value(&diff_pointer) else {
                return false;
            };
            changed.iter().any(|(changed_pointer, bytes)| match bytes {
                crate::kernel::AccessExtent::Bytes(bytes) => assumptions.pointer_access_in_range(
                    &diff_pointer,
                    value.byte_width(),
                    changed_pointer,
                    &OldMachineTerm::constant(0),
                    &OldMachineTerm::constant(1),
                    *bytes,
                ),
                // A whole object of abstract size changes the cell at its
                // own address.
                crate::kernel::AccessExtent::Object(_) => *changed_pointer == diff_pointer,
            })
        })
}

fn memory_diff_is_covered_by_ranges(
    before: &SymbolicMemory,
    after: &SymbolicMemory,
    mutable_ranges: &[MemoryRange],
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
        .filter(|pointer| !pointer.base.is_local_block())
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
/// ([`SymbolicMemory::with_interface_memory_havoc_preserving_borrows`]), so this
/// admits no write the effects do not cover.
fn interface_chain_memory_matches(
    produced: &SymbolicMemory,
    recorded: &SymbolicMemory,
    assumptions: &PureFactContext,
) -> bool {
    use crate::kernel::api::contract_certification::memories_definitionally_equal;
    // End the lifetimes first: with them the memories are usually the same
    // state, which the comparison answers without looking at a cell.
    let mut ended: Option<SymbolicMemory> = None;
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
    memories_definitionally_equal(ended.as_ref().unwrap_or(produced), recorded, assumptions)
}

#[cfg(test)]
fn checked_interface_effect_facts(
    split_state: &ExecutionState,
    joined_state: &ExecutionState,
    arms: [&ExecutionProofCore; 2],
    arm_facts: [&PureFactStore; 2],
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
        Proposition::MemoryMutatesOnly { .. }
            | Proposition::MemoryEffectSummary { .. }
            | Proposition::HeapAllocationFreed { .. }
    )
}

/// Whether an arm's memory effects account for every memory change its walk
/// passed through that could have written.
///
/// The walk has already checked that the arm's events follow one another
/// from the split to the arm's end, so its steps are the arm's whole memory
/// history. A step that cannot write needs no effect. A step that can is
/// covered when the effects starting at its first state lead to its last,
/// and states are matched by identity first: only a statement that reads
/// or assigns a local before it stores leaves two that differ, and those
/// differ in what that one statement cached.
///
/// This is why the join does not compare the arm's memories as wholes. A
/// comparison of two states that differ in the reads an `unfold` cached
/// has to justify each read against the memory history, and its cost grows
/// with the proof before the split rather than with the arm.
fn arm_effects_follow_memory_steps(
    steps: &[CheckedMemoryStep],
    effects: &(impl ExecutionFactSource + ?Sized),
    assumptions: &PureFactContext,
) -> bool {
    use crate::kernel::api::contract_certification::memories_definitionally_equal;
    let mut effects = effects
        .fact_iter()
        .filter_map(|fact| match fact.proposition() {
            Proposition::MemoryMutatesOnly { before, after, .. }
            | Proposition::MemoryEffectSummary { before, after, .. }
            | Proposition::HeapAllocationFreed { before, after, .. } => Some((before, after)),
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
            } else if memories_definitionally_equal(memory, &step.after, assumptions) {
                break;
            } else if let Some((_, after)) = effects
                .next_if(|(before, _)| memories_definitionally_equal(memory, before, assumptions))
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
    split_state: &ExecutionState,
    joined_state: &ExecutionState,
    arms: [&ExecutionProofCore; 2],
    arm_facts: [&PureFactStore; 2],
    arm_effect_facts: [&(impl ExecutionFactSource + ?Sized); 2],
    arm_memory_steps: Option<[&[CheckedMemoryStep]; 2]>,
) -> Result<crate::kernel::ExecutionFacts, &'static str> {
    let mut writes = Vec::new();
    let mut ranges = Vec::new();
    let mut heap_frees = [Vec::new(), Vec::new()];
    for arm_index in 0..2 {
        let assumptions = arm_facts[arm_index].assumptions();
        // The arm's checked walk and exact effect stream already account
        // for each statement's writes. Combine their recorded footprints;
        // do not reconstruct those same stores or call havocs at the join.
        // Without that record, retain the standalone coverage checks.
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
                Proposition::MemoryMutatesOnly {
                    before,
                    after,
                    writes: changed,
                    ..
                } => {
                    if !fact.is_certified() {
                        return Err("an interface arm contains an uncertified memory effect");
                    }
                    if !chained && !interface_chain_memory_matches(&memory, before, assumptions) {
                        return Err(
                            "an interface arm effect chain does not start at its current memory",
                        );
                    }
                    if !chained
                        && !fact.is_join_summary()
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
                Proposition::MemoryEffectSummary {
                    before,
                    after,
                    mutable_ranges,
                    ..
                } => {
                    if !fact.is_certified() {
                        return Err("an interface arm contains an uncertified memory effect");
                    }
                    if !chained && !interface_chain_memory_matches(&memory, before, assumptions) {
                        return Err(
                            "an interface arm effect summary does not start at its current memory",
                        );
                    }
                    if !chained
                        && !fact.is_join_summary()
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
                Proposition::HeapAllocationFreed {
                    before,
                    after,
                    after_point,
                    blocks,
                    mutable_ranges,
                    ..
                } => {
                    if !chained && !interface_chain_memory_matches(&memory, before, assumptions) {
                        return Err(
                            "an interface heap-free effect does not start at its current memory",
                        );
                    }
                    memory = after.clone();
                    heap_frees[arm_index].push((
                        blocks.clone(),
                        mutable_ranges.clone(),
                        after.clone(),
                        after_point.clone(),
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
                .map(|(blocks, mutable_ranges, after, after_point)| {
                    ExecutionPureFact::certified(Proposition::HeapAllocationFreed {
                        before: split_state.memory().clone(),
                        before_point: split_state.memory_point(),
                        after: after.clone(),
                        after_point: after_point.clone(),
                        blocks: blocks.clone(),
                        mutable_ranges: mutable_ranges.clone(),
                    })
                })
                .collect::<Vec<_>>();
            return Ok(facts.into());
        }
        return Ok(common_non_memory_effect_facts(arm_effect_facts));
    }
    let proposition = if ranges.is_empty() {
        Proposition::MemoryMutatesOnly {
            before: split_state.memory().clone(),
            before_point: split_state.memory_point(),
            after: joined_state.memory().clone(),
            after_point: joined_state.memory_point(),
            writes,
        }
    } else {
        for (pointer, bytes) in writes {
            let range = MemoryRange::of_access(&pointer, bytes);
            if !ranges.contains(&range) {
                ranges.push(range);
            }
        }
        Proposition::MemoryEffectSummary {
            before: split_state.memory().clone(),
            before_point: split_state.path_link().clone(),
            after: joined_state.memory().clone(),
            after_point: joined_state.path_link().clone(),
            mutable_ranges: ranges,
        }
    };
    let mut facts = vec![ExecutionPureFact::certified_join_summary(proposition)];
    facts.extend(common_non_memory_effect_facts(arm_effect_facts));
    Ok(facts.into())
}

fn conditional_heap_frees(
    arm_effect_facts: [&(impl ExecutionFactSource + ?Sized); 2],
) -> [Vec<(Address, crate::kernel::AllocationSize)>; 2] {
    std::array::from_fn(|arm_index| {
        arm_effect_facts[arm_index]
            .fact_iter()
            .flat_map(|fact| match fact.proposition() {
                Proposition::HeapAllocationFreed { blocks, .. } => blocks.clone(),
                _ => Vec::new(),
            })
            .collect()
    })
}

fn interface_resources_guard_heap_frees(
    function: &ProgramFunction,
    arm_resources: &[Vec<ResourceFact>; 2],
    arm_states: [&ExecutionState; 2],
    arm_facts: [&PureFactStore; 2],
    heap_frees: &[Vec<(Address, crate::kernel::AllocationSize)>; 2],
) -> bool {
    let has_allocation = |arm_index: usize,
                          base: &Address,
                          bytes: &crate::kernel::AllocationSize| {
        arm_resources[arm_index].iter().any(|resource| {
            if resource
                .allocation_size()
                .is_some_and(|(candidate_base, candidate_bytes)| {
                    candidate_base.address() == base && &candidate_bytes == bytes
                })
            {
                return true;
            }
            if !resource.is_own() || !matches!(resource.resource(), Resource::Composite { .. }) {
                return false;
            }
            crate::kernel::functions::expand_composite_resource_fact(
                &ResourceContext::new_with_equalities(arm_facts[arm_index].assumptions())
                    .unchecked_with_fact(resource.clone()),
                resource,
                function.composite_resource_definitions(),
                &arm_states[arm_index].program_point(),
                arm_facts[arm_index].assumptions(),
            )
            .is_some_and(|expanded| {
                expanded.facts().iter().any(|fact| {
                    fact.allocation_size()
                        .is_some_and(|(candidate_base, candidate_bytes)| {
                            candidate_base.address() == base && &candidate_bytes == bytes
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
    // The inputs are the two arm deltas. Index the right delta once and
    // retain the left's ordering and exact producer evidence.
    let right = arm_effect_facts[1].persistent_facts();
    arm_effect_facts[0]
        .fact_iter()
        .inspect(|_| crate::instrumentation::record_deterministic_work(1))
        .filter(|fact| {
            fact.is_certified()
                && !matches!(
                    fact.proposition(),
                    Proposition::MemoryMutatesOnly { .. }
                        | Proposition::MemoryEffectSummary { .. }
                        | Proposition::HeapAllocationFreed { .. }
                )
                && right.contains(fact)
        })
        .cloned()
        .collect()
}

#[cfg(test)]
fn interface_spec_paths(
    spec: &SpecProposition,
    state: &ExecutionState,
    reference_state: &ExecutionState,
    assumptions: &PureFactContext,
) -> Option<Vec<crate::kernel::spec::SpecPropositionPath>> {
    interface_spec_paths_with(spec, state, reference_state, assumptions, false)
}

/// The abstract successor (`successor`) assumes the typed-call domains both
/// arms established; see `spec::lower_assumed_interface_proposition`.
fn interface_spec_paths_with(
    spec: &SpecProposition,
    state: &ExecutionState,
    reference_state: &ExecutionState,
    assumptions: &PureFactContext,
    successor: bool,
) -> Option<Vec<crate::kernel::spec::SpecPropositionPath>> {
    let lower = if successor {
        crate::kernel::spec::lower_assumed_interface_proposition
    } else {
        crate::kernel::spec::lower_spec_proposition_at_state_with_loop_entry
    };
    let mut paths = lower(
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
    spec: &ResourceSpec,
    state: &ExecutionState,
    facts: &PureFactStore,
) -> Option<ResourceFact> {
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
    spec: &ResourceSpec,
    resource: &ResourceFact,
    state: &ExecutionState,
) -> Option<Proposition> {
    let segment = spec.memory_segment()?;
    let range = resource.memory_range()?;
    (segment.element_width() == range.element_width())
        .then(|| range.loadable_fact(state.memory(), state.memory_point()))
}

/// The selected kernel lowering and the precise context in which it passed
/// the local proof rules. Every value, generated fact, and safety obligation
/// has a completed proof rooted in these exact premises. Load definitions
/// use their kernel origin, not a contextual proof search.
#[derive(Clone)]
struct CheckedInterfaceLowering {
    spec: Arc<SpecProposition>,
    retained_state: ExecutionState,
    reference: ExecutionState,
    facts: PureFactStore,
    path: Arc<crate::kernel::spec::SpecPropositionPath>,
    proofs: Arc<Vec<super::CheckedProposition>>,
    /// At the abstract successor only: the typed-call domains the lowering
    /// introduced for joined values. Both arms lowered the same fact with
    /// ordinary lowering, which established them there, so the successor
    /// assumes them rather than proving them.
    assumed_domains: Arc<Vec<Proposition>>,
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
        state: &ExecutionState,
        reference_state: &ExecutionState,
        facts: &PureFactStore,
        access: &InterfaceReadPremises,
    ) -> Option<Self> {
        // Lower each arm's interface fact as a `have` of the same text in
        // that arm lowers: the arm's proof states the fact in that form.
        let assumptions = crate::kernel::api::proof_lowering_assumptions(facts.assumptions(), spec);
        Self::check_in(
            spec,
            state,
            reference_state,
            facts,
            access,
            &assumptions,
            false,
        )
    }

    fn check_in(
        spec: &SpecProposition,
        state: &ExecutionState,
        reference_state: &ExecutionState,
        facts: &PureFactStore,
        access: &InterfaceReadPremises,
        assumptions: &PureFactContext,
        successor: bool,
    ) -> Option<Self> {
        // Concrete reads use this arm's checked aliases. The abstract
        // successor instead retains the state-only exported spelling.
        // Lowering grants no authority: check each resulting fact and
        // safety obligation against the exact retained context below.
        let paths =
            interface_spec_paths_with(spec, state, reference_state, assumptions, successor)?;
        paths.into_iter().find_map(|mut path| {
            let mut assumed_domains = Vec::new();
            if successor {
                let receipt = |fact: &ExecutionPureFact| {
                    crate::kernel::object_types::is_checked_call_type_fact(fact.proposition())
                };
                assumed_domains.extend(
                    path.facts
                        .iter()
                        .filter(|fact| receipt(fact))
                        .map(|fact| fact.proposition().clone()),
                );
                path.facts.retain(|fact| !receipt(fact));
            }
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
                retained_state: state.clone(),
                reference: reference_state.clone(),
                facts: facts.clone(),
                path: Arc::new(path),
                proofs: Arc::new(proofs),
                assumed_domains: Arc::new(assumed_domains),
            })
        })
    }
}

/// An index over the explicitly exported, already ownership-checked resource
/// clauses. Building it is output-sized; no ambient resource/fact scan occurs
/// per interface judgment. Equal bases retain the largest constant span.
#[derive(Default)]
struct InterfaceReadPremises {
    by_base: std::collections::BTreeMap<
        (crate::kernel::SymbolicMemory, crate::kernel::Address),
        (u32, Proposition),
    >,
}

impl InterfaceReadPremises {
    fn new(premises: impl IntoIterator<Item = Proposition>) -> Self {
        let mut index = Self::default();
        for premise in premises {
            crate::instrumentation::record_deterministic_work(1);
            let Proposition::MemoryLoadable {
                memory,
                base,
                bytes,
                wide: false,
                ..
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
        let Proposition::MemoryLoadable { memory, base, .. } = goal else {
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
        Proposition::MemoryLoadable {
            memory,
            base,
            bytes,
            wide: false,
            ..
        },
        Proposition::MemoryLoadable {
            memory: source_memory,
            base: source_base,
            bytes: source_bytes,
            wide: false,
            ..
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
        let Some((
            crate::kernel::OldConditionTerm::Compare {
                format:
                    crate::kernel::MachineIntegerType::Int32 | crate::kernel::MachineIntegerType::UInt32,
                relation: crate::kernel::CompareRelation::Equal,
                left,
                right,
            },
            true,
        )) = proposition.old_condition()
        else {
            return None;
        };
        let (OldMachineTerm::Variable(variable), load @ OldMachineTerm::MemoryLoad(_, _, _)) =
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
    outcome: ConditionOutcome,
    facts: crate::kernel::ExecutionFacts,
    obligations: Vec<crate::kernel::ProofObligation>,
    theorem: Theorem,
}

impl CheckedBranchPath {
    pub(crate) fn outcome(&self) -> &ConditionOutcome {
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
    state: ExecutionState,
    branch_statement: ProgramStatement,
    continuation: Option<ProgramStatement>,
    condition: ProgramExpression,
    root_facts: PureFactStore,
    paths: Vec<CheckedBranchPath>,
}

pub(crate) enum CheckedBranchSplitError {
    Limit(ExecutionLimit),
    InvalidEvidence,
}

/// A complete, kernel-checked direct call with one normal successor and one
/// exceptional successor. An arm may be inconsistent with the root facts;
/// its proof then closes by contradiction. Individual statement
/// theorems prove each arm; this witness proves that neither arm was omitted.
/// Its source and fact root are exact, so it cannot authorize a fork at a
/// different call or after the proof context has changed.
#[derive(Clone)]
pub(crate) struct CheckedCallOutcomeSplit {
    state: ExecutionState,
    statement: ProgramStatement,
    root_facts: PureFactStore,
    normal: StatementOutcome,
    exceptional: StatementOutcome,
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
        state: ExecutionState,
        statement: ProgramStatement,
        root_facts: &PureFactStore,
        normal_theorem: &Theorem,
        normal: &StatementOutcome,
        normal_path_facts: &[Proposition],
        normal_obligations: &[crate::kernel::ProofObligation],
        exceptional_theorem: &Theorem,
        exceptional: &StatementOutcome,
        exceptional_path_facts: &[Proposition],
        exceptional_obligations: &[crate::kernel::ProofObligation],
    ) -> Result<Self, CheckedCallOutcomeSplitError> {
        if !matches!(
            statement,
            ProgramStatement::Call { .. }
                | ProgramStatement::CallConstruct { .. }
                | ProgramStatement::CallResult { .. }
        ) || !matches!(normal, StatementOutcome::Normal(_))
            || !matches!(exceptional, StatementOutcome::Throw { .. })
        {
            return Err(CheckedCallOutcomeSplitError::InvalidEvidence);
        }
        let validates_arm =
            |theorem: &Theorem,
             expected: &StatementOutcome,
             path_facts: &[Proposition],
             obligations: &[crate::kernel::ProofObligation]| {
                let Proposition::ProgramStatementVerifies {
                    state: proved_state,
                    statement: proved_statement,
                    outcome,
                } = crate::kernel::api::proof_evidence_conclusion(theorem)
                else {
                    return false;
                };
                if **proved_state != state || **proved_statement != statement || outcome != expected
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
        state: &ExecutionState,
        statement: &ProgramStatement,
        root_facts: &PureFactStore,
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
                Proposition::ProgramStatementVerifies {
                    state: proved_state,
                    statement: proved_statement,
                    outcome,
                } if **proved_state == *state && **proved_statement == *statement && outcome == *expected
            )
        })
    }
}

impl CheckedBranchSplit {
    pub(crate) fn state(&self) -> &ExecutionState {
        &self.state
    }

    pub(crate) fn check(
        state: ExecutionState,
        branch_statement: ProgramStatement,
        continuation: Option<ProgramStatement>,
        root_facts: &PureFactStore,
    ) -> Result<Self, CheckedBranchSplitError> {
        let ProgramStatement::If { condition, .. } = &branch_statement else {
            return Err(CheckedBranchSplitError::InvalidEvidence);
        };
        let condition = condition.clone();
        let evaluation = crate::kernel::prove_symbolic_program_condition_evaluation(
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
                let conclusion = path.theorem().execution_conclusion();
                let Proposition::ProgramConditionEvaluates {
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

    fn has_exact_root(&self, root_facts: &PureFactStore) -> bool {
        self.root_facts
            .introduced_since(root_facts)
            .is_some_and(|delta| delta.is_empty())
            && root_facts
                .introduced_since(&self.root_facts)
                .is_some_and(|delta| delta.is_empty())
    }

    pub(crate) fn validates_exhaustive_join(
        &self,
        state: &ExecutionState,
        condition: &ProgramExpression,
        root_facts: &PureFactStore,
        arm_theorems: [Option<&Theorem>; 2],
        arm_facts: [Option<&PureFactStore>; 2],
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
            let ConditionOutcome::Value(value) = path.outcome else {
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
    pub(crate) execution_start_state: Option<ExecutionState>,
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
    /// The loop-owned update, shared by all continuing edges of this region.
    pub(crate) loop_update: Option<(Arc<ProgramStatement>, usize)>,
    /// How this path reached the loop body's boundary, once it has.
    pub(crate) loop_control: LoopControlExit,
    pub(crate) loop_phase_source: Option<LoopPhaseSource>,
    /// A proof-only natural cycle's source back edge, when this frontier is
    /// executing that loop body. Matching `goto` evidence reaches the typed
    /// body boundary instead of reopening the source target.
    pub(crate) natural_backedge_target: Option<crate::kernel::ControlTargetId>,
    /// A proof-only natural cycle's checked forward exit, when this frontier
    /// is executing that loop body.
    pub(crate) natural_exit_target: Option<crate::kernel::ControlTargetId>,
}

impl ExecutionFrontier {
    pub(crate) fn active_loop_phase_source(&self) -> Option<LoopPhaseSource> {
        self.continuations
            .last()
            .and_then(|frame| {
                frame
                    .loop_control
                    .as_ref()
                    .map(|control| control.phase_source)
            })
            .or(self.loop_phase_source)
    }

    /// Whether two frontiers that split from one stand at the same program
    /// point: the same statement to run next, in the same region, with the
    /// same enclosing continuations still owed.
    pub(crate) fn at_same_program_point(&self, other: &Self) -> bool {
        self.region == other.region
            && self.entry_member_prefix == other.entry_member_prefix
            && self.next_statement_index == other.next_statement_index
            && self.in_loop_body == other.in_loop_body
            && self.loop_update == other.loop_update
            && self.loop_control == other.loop_control
            && self.loop_phase_source == other.loop_phase_source
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

/// How an exceptional exit enters the statements that handle it.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum ExceptionalEntry {
    /// A source `try`: the handler starts by binding the int32 payload.
    Catch(BindingName),
    /// An [`ProgramStatement::UnwindCleanup`]: its cleanup runs, then the
    /// same exception continues ([`crate::kernel::program_unwind_continuation`]).
    /// The cleanup it was entered with identifies it.
    Unwind(Arc<ProgramStatement>),
}

impl ExceptionalEntry {
    fn binding(&self) -> Option<&BindingName> {
        match self {
            Self::Catch(binding) => Some(binding),
            Self::Unwind(_) => None,
        }
    }
    fn is_unwind(&self) -> bool {
        matches!(self, Self::Unwind(_))
    }
}

/// One entered `try` body or unwind cleanup body tracked for evidence order
/// validation: the statements to resume at if an exception reaches it, and
/// the source tail after it for normal completion. An unwind frame's
/// `handler` is its cleanup until an exception enters it, and then its
/// cleanup followed by that exception continuing.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct EvidenceTryFrame {
    pub(crate) entry: ExceptionalEntry,
    pub(crate) handler: Arc<ProgramStatement>,
    pub(crate) tail_after_try: Option<Arc<ProgramStatement>>,
}

/// Source coordinates for a semantic phase with no separate source statement.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct LoopPhaseSource {
    pub(crate) header_index: usize,
    pub(crate) test_position: crate::kernel::LoopTestPosition,
}

/// The complete evidence successors issued while entering a source loop.
/// Unlike the driver's local remainder, these retain every enclosing source
/// continuation. Only checked source navigation constructs them.
#[derive(Clone)]
pub(crate) struct LoopControlSources {
    repeat: Arc<ProgramStatement>,
    exit: Option<Arc<ProgramStatement>>,
    continuation: Option<Arc<ProgramStatement>>,
    test_position: crate::kernel::LoopTestPosition,
    try_depth: usize,
}

#[derive(Clone)]
struct LoopControlDestination {
    remaining: Option<Arc<ProgramStatement>>,
    statement_index: usize,
    evidence_source: Option<Arc<ProgramStatement>>,
}

#[derive(Clone)]
pub(crate) struct LoopControlDestinations {
    continuing: LoopControlDestination,
    exiting: LoopControlDestination,
    continue_keeps_loop: bool,
    phase_source: LoopPhaseSource,
    try_depth: usize,
}

#[derive(Clone)]
pub(crate) struct ProofExecutionContinuation {
    pub(crate) loop_control: Option<LoopControlDestinations>,
    pub(crate) remaining: Option<Arc<ProgramStatement>>,
    pub(crate) next_statement_index: usize,
    /// The exceptional successor of an entered `try` body. A throw abandons
    /// its remaining statements and resumes at this handler entry.
    pub(crate) exceptional: Option<ExceptionalContinuation>,
}

impl ProofExecutionContinuation {
    pub(crate) fn loop_body(
        repeat: Arc<ProgramStatement>,
        repeat_index: usize,
        after_loop: Option<Arc<ProgramStatement>>,
        after_loop_index: usize,
        update_index: Option<usize>,
        sources: LoopControlSources,
    ) -> Result<Self, EvidenceRefusal> {
        let continue_keeps_loop = sources.continuation.is_some();
        let continuing = match sources.continuation {
            Some(update) => LoopControlDestination {
                remaining: Some(update.clone()),
                statement_index: update_index.ok_or_else(|| {
                    EvidenceRefusal::from("loop continuation has no source entry")
                })?,
                evidence_source: Some(prepend_shared_source(update, Some(sources.repeat))),
            },
            None => LoopControlDestination {
                remaining: Some(repeat.clone()),
                statement_index: repeat_index,
                evidence_source: Some(sources.repeat),
            },
        };
        Ok(Self {
            loop_control: Some(LoopControlDestinations {
                continuing,
                exiting: LoopControlDestination {
                    remaining: after_loop,
                    statement_index: after_loop_index,
                    evidence_source: sources.exit,
                },
                continue_keeps_loop,
                phase_source: LoopPhaseSource {
                    header_index: repeat_index,
                    test_position: sources.test_position,
                },
                try_depth: sources.try_depth,
            }),
            remaining: Some(repeat),
            next_statement_index: repeat_index,
            exceptional: None,
        })
    }
}

/// The handler a `Throw` inside an entered `try` body resumes at. Only the
/// typed C++ frontend produces `TryCatchInt32`, so C execution never
/// carries one of these.
#[derive(Clone)]
pub(crate) struct ExceptionalContinuation {
    pub(crate) entry: ExceptionalEntry,
    pub(crate) handler: Arc<ProgramStatement>,
    pub(crate) handler_first_index: usize,
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
    trace: ExecutionEvidence,
    /// The source loop whose rule returned this path, for the point its
    /// premises are read at.
    pub(crate) loop_index: Option<usize>,
    pub(crate) outcome: FunctionOutcome,
    pub(crate) execution_facts: ExecutionFacts,
    pub(crate) obligations: Vec<crate::kernel::ProofObligation>,
    pub(crate) pure_facts: PureFactStore,
    pub(crate) borrow_evidence: crate::kernel::borrows::CheckedBorrowCallEvidenceSequence,
}

/// Surface-independent execution state owned by a checked proof branch.
///
/// Language lowering and certificate capture wrap this value with their own
/// path-local records. The kernel core contains only C state, checked facts
/// and rules, typed frontier state, and semantic freshness/region flags.
#[derive(Clone)]
pub(crate) struct ExecutionProofCore {
    descent: Option<crate::kernel::termination::descent_completion::OpenedDescent>,
    pub(crate) last_footprint: Option<Arc<crate::kernel::RegionFootprint>>,
    pub(crate) state: SharedValue<ExecutionState>,
    initial_match_scope: SharedValue<ExecutionState>,
    /// The admitted case delta, shared by every returned descendant. Retain
    /// it at the split, before terminal joins could copy it into every path.
    publication_case_facts: ExecutionFacts,
    /// Whether a case fact is a memory-effect proposition, which an effect
    /// could repeat. Case facts are never certified, and every effect is
    /// certified or a memory effect, so otherwise the two cannot overlap.
    cases_hold_memory_effects: bool,
    /// What the open trace has established, as of its last recorded context.
    path_context: Option<Arc<CheckedPathContext>>,
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
    pub(crate) evidence_state: Option<ExecutionState>,
    /// The open trace has completed with a returning or diverging theorem
    /// or an outcome fork; only post-execution case arms may follow.
    pub(crate) evidence_completed: bool,
    /// The source the retained evidence has yet to consume, advanced with
    /// each recorded theorem or join: a statement's tail, a condition's
    /// selected arm (or loop body followed by the loop head) before the
    /// tail. Meaningful once `evidence_state` is set; `None` then means
    /// the source is exhausted. Checks read this and never the driver's
    /// frontier once it is set.
    pub(crate) evidence_source: Option<Arc<ProgramStatement>>,
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
    pub(crate) execution_evidence: super::PersistentVector<ExecutionEvidence>,
    prepared_tactic_application: Option<Arc<PreparedTacticApplication>>,
    prepared_instance_fold: Option<Arc<PreparedResourceFold>>,
    prepared_return_fold: Option<Arc<PreparedReturnFold>>,
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
    pub(crate) borrow_evidence: crate::kernel::borrows::CheckedBorrowCallEvidenceSequence,
    /// One kernel publication shared by post-return proofs on each path.
    return_proof_contexts: crate::persistent::PersistentMap<usize, Arc<CheckedReturnContext>>,
    /// Completed pure proofs awaiting a resource exchange that needs them.
    return_pending_propositions: crate::persistent::PersistentMap<
        usize,
        PersistentSequence<(super::CheckedProposition, PureFactStore)>,
    >,
    /// Post-return exchanges indexed by the selected outcome. Forking a
    /// focused outcome must not copy or modify its sibling traces.
    return_resource_rewrites: crate::persistent::PersistentMap<usize, ExecutionEvidence>,
    return_producers:
        crate::persistent::PersistentMap<usize, return_producer::ReturnRewriteProducer>,
    /// Events on the current unjoined path. A branch join restores its
    /// parent's set; finalization collects all retained arm events by walking
    /// the output trace once.
    checked_call_events: CheckedCallEvents,
    pub(crate) function_entry: Option<Arc<CheckedFunctionEntry>>,
    /// The proof's facts at the checked entry, whose context the entry was
    /// checked under. A retained return proof's facts descend from it, so
    /// completion checks only what the proof introduced since.
    entry_facts: Option<PureFactStore>,
    pub(crate) frontier_loop_rules: PersistentSequence<VerifiedLoopRule>,
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
}

#[derive(Clone)]
pub(crate) struct CheckedLoopInvariantLowerings {
    pub(super) body: Option<super::object::CheckedInvariantBody>,
    pub(super) retained_state: SharedValue<ExecutionState>,
    pub(super) checks: Vec<crate::kernel::LoopInvariantCheck>,
    /// The loop's declared `decreases` components, whose back-edge members
    /// the retained body also closed. Validation compares them exactly, so a
    /// body checked before a `decreases` clause existed cannot be reused.
    pub(super) ranking_measures: Vec<crate::kernel::RankingComponent>,
    pub(super) facts: super::PureFactStore,
    pub(super) effects: crate::kernel::ExecutionFacts,
}

impl CheckedLoopInvariantLowerings {
    pub(super) fn matches_context(
        &self,
        core: &ExecutionProofCore,
        facts: &super::PureFactStore,
    ) -> bool {
        self.retained_state.shares_storage_with(&core.state)
            && self.facts.shares_premises_with(facts)
            && self.effects.shares_storage_with(&core.effect_facts)
    }
}

#[cfg(test)]
impl CheckedLoopInvariantLowerings {
    pub(crate) fn checks(&self) -> &[crate::kernel::LoopInvariantCheck] {
        &self.checks
    }
    pub(crate) fn recorded_state(&self) -> &SharedValue<ExecutionState> {
        &self.retained_state
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
    theorem.execution_conclusion()
}

fn statement_call_havoc_views(theorem: &Theorem) -> Vec<crate::kernel::SharedMemory> {
    let (before, outcome) = match checked_evidence_conclusion(theorem) {
        Proposition::ProgramStatementVerifies { state, outcome, .. } => (state.memory(), outcome),
        _ => return Vec::new(),
    };
    let after = match outcome {
        StatementOutcome::Normal(state)
        | StatementOutcome::LoopTestFalse(state)
        | StatementOutcome::Break(state)
        | StatementOutcome::Continue(state)
        | StatementOutcome::Jump { state, .. }
        | StatementOutcome::Return { state, .. }
        | StatementOutcome::Throw { state, .. } => state.memory(),
        StatementOutcome::VerificationDiverges
        | StatementOutcome::UndefinedBehavior(_)
        | StatementOutcome::RuntimeError(_) => return Vec::new(),
    };
    let before = crate::kernel::intern_memory_ref(before);
    let mut current = crate::kernel::intern_memory_ref(after);
    let mut calls = Vec::new();
    while current != before {
        let Some(derivation) = current.derivation() else {
            return Vec::new();
        };
        if matches!(
            derivation.as_ref(),
            crate::kernel::MemoryDerivation::CallHavoc { .. }
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
    running: &SymbolicMemory,
    recomputed: &SymbolicMemory,
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
fn collect_applied_tactics<'e>(
    events: impl IntoIterator<Item = &'e CheckedExecutionEvent>,
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
fn collect_checked_callees<'e>(
    events: impl IntoIterator<Item = &'e CheckedExecutionEvent>,
    seen: &mut std::collections::HashSet<usize>,
    callees: &mut std::collections::BTreeSet<crate::kernel::termination::CallDependency>,
) {
    for event in events {
        crate::kernel::termination::charge_termination_work(1);
        match event {
            CheckedExecutionEvent::Statement(theorem) => {
                match checked_evidence_conclusion(theorem) {
                    Proposition::ProgramStatementVerifies { statement, .. } => {
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

fn collect_retained_call_events<'e>(
    events: impl IntoIterator<Item = &'e CheckedExecutionEvent>,
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
            CheckedExecutionEvent::LoopEntry { .. }
            | CheckedExecutionEvent::Statement(_)
            | CheckedExecutionEvent::Condition(_)
            | CheckedExecutionEvent::Context(_)
            | CheckedExecutionEvent::CompletedContext(_)
            | CheckedExecutionEvent::StatementEffects(_)
            | CheckedExecutionEvent::ProofCase(_)
            | CheckedExecutionEvent::ResourceObservation(_)
            | CheckedExecutionEvent::ViewRelease(_)
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

/// Branch evidence names its exact arm context. Do not derive a missing
/// prerequisite from other facts at the join. Literal comparisons and
/// integer reflexivity are context-free rules, not premise search.
pub(crate) fn checked_branch_fact_is_available(facts: &PureFactStore, fact: &Proposition) -> bool {
    crate::instrumentation::record_deterministic_work(1);
    facts.contains(fact)
        || facts.assumptions().proves_exact(fact)
        // Interface facts are explicitly selected claims. Their native and
        // shared comparison spellings use the same retained source; this
        // does not derive a weaker bound or search for a missing premise.
        || matches!(fact, Proposition::ConditionIs(condition, truth)
            if facts.assumptions().selected_comparison_source(condition.old_form(), *truth).is_some())
        || matches!(&fact, condition_source_0 @ Proposition::ConditionIs(_, _) if matches!(condition_source_0.old_condition(), Some((crate::kernel::OldConditionTerm::Compare { .. }, _)) if crate::kernel::proposition_holds_without_facts(fact)))
        || matches!(fact, Proposition::And(left, right)
            if checked_branch_fact_is_available(facts, left)
                && checked_branch_fact_is_available(facts, right))
        || matches!(&fact, condition_source_0 @ Proposition::ConditionIs(_, true) if matches!(condition_source_0.old_condition(), Some((crate::kernel::OldConditionTerm::Compare { format: crate::kernel::MachineIntegerType::Int32 | crate::kernel::MachineIntegerType::UInt32, relation: crate::kernel::CompareRelation::Equal, left, right }, _)) if (left == right)))
}

/// The pointer congruence fragment may give a field read another spelling
/// in the same checked arm. This normalizes just the named positive equality;
/// it neither searches premises nor proves a missing read/safety obligation.
pub(super) fn checked_interface_pointer_equality(
    facts: &PureFactStore,
    goal: &Proposition,
) -> bool {
    matches!(goal, Proposition::ConditionIs(condition, true) if condition.pointer_equality().is_some())
        && super::fact_reasoning::normalize_using_conditions(goal, &[], facts).is_ok()
}

fn split_checked_evidence_statement(
    statement: ProgramStatement,
) -> (ProgramStatement, Option<ProgramStatement>) {
    match statement {
        ProgramStatement::Seq(statements) => {
            let (head, first_tail) =
                split_checked_evidence_statement((**statements.first()).clone());
            let tail = match first_tail {
                Some(first_tail) => {
                    ProgramStatement::Seq(statements.with_statement(0, Arc::new(first_tail)))
                }
                None => Arc::unwrap_or_clone(statements.rest()),
            };
            (head, Some(tail))
        }
        statement => (statement, None),
    }
}

/// `split_checked_evidence_statement` without taking the source: the head
/// is borrowed and the tail shares every statement after it.
fn split_shared_source(
    source: &ProgramStatement,
) -> (
    std::borrow::Cow<'_, ProgramStatement>,
    Option<Arc<ProgramStatement>>,
) {
    crate::instrumentation::record_deterministic_work(1);
    match source {
        ProgramStatement::Seq(statements) => {
            let (head, first_tail) = split_shared_source(statements.first());
            let tail = match first_tail {
                Some(first_tail) => Arc::new(ProgramStatement::Seq(
                    statements.with_statement(0, first_tail),
                )),
                None => statements.rest(),
            };
            (head, Some(tail))
        }
        statement => (std::borrow::Cow::Borrowed(statement), None),
    }
}

fn prepend_shared_source(
    statement: Arc<ProgramStatement>,
    tail: Option<Arc<ProgramStatement>>,
) -> Arc<ProgramStatement> {
    match tail {
        Some(tail) => Arc::new(ProgramStatement::seq(statement, tail)),
        None => statement,
    }
}

fn prepend_checked_evidence_statement(
    statement: ProgramStatement,
    tail: Option<ProgramStatement>,
) -> ProgramStatement {
    match tail {
        Some(tail) => ProgramStatement::seq(Arc::new(statement), Arc::new(tail)),
        None => statement,
    }
}

/// Whether two statements are the same C source. A proof binds loop
/// clauses into the `while` statements at its frontier, so the theorem it
/// records names the annotated statement while the proof object holds the
/// plain source; the invariant and effect annotations do not change what
/// the C executes, only what the theorem additionally checks.
fn statements_have_same_source(left: &ProgramStatement, right: &ProgramStatement) -> bool {
    fn flatten<'a>(statement: &'a ProgramStatement, output: &mut Vec<&'a ProgramStatement>) {
        match statement {
            ProgramStatement::Seq(statements) => {
                for statement in statements.iter() {
                    flatten(statement, output);
                }
            }
            statement => output.push(statement),
        }
    }
    match (left, right) {
        (ProgramStatement::Seq(..), _) | (_, ProgramStatement::Seq(..)) => {
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
            ProgramStatement::If {
                condition: left_condition,
                then_branch: left_then,
                else_branch: left_else,
            },
            ProgramStatement::If {
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
            ProgramStatement::Loop {
                test: left_loop_test,
                update: left_update,
                body: left_body,
                ..
            },
            ProgramStatement::Loop {
                test: right_loop_test,
                update: right_update,
                body: right_body,
                ..
            },
        ) => {
            left_loop_test == right_loop_test
                && left_update == right_update
                && statements_have_same_source(left_body, right_body)
        }
        (left, right) => left == right,
    }
}

/// `statement_sequence_is_prefix` up to loop annotations.
fn statement_sequence_has_same_source_prefix(
    expected_prefix: &Option<ProgramStatement>,
    actual: Option<&ProgramStatement>,
) -> bool {
    fn flatten<'a>(statement: &'a ProgramStatement, output: &mut Vec<&'a ProgramStatement>) {
        match statement {
            ProgramStatement::Seq(statements) => {
                for statement in statements.iter() {
                    flatten(statement, output);
                }
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
    expected_prefix: &Option<ProgramStatement>,
    actual: &Option<ProgramStatement>,
) -> bool {
    fn flatten<'a>(statement: &'a ProgramStatement, output: &mut Vec<&'a ProgramStatement>) {
        match statement {
            ProgramStatement::Seq(statements) => {
                for statement in statements.iter() {
                    flatten(statement, output);
                }
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
fn checked_source_statement_matches(proved: &ProgramStatement, source: &ProgramStatement) -> bool {
    if proved == source {
        return true;
    }
    let (
        ProgramStatement::Loop {
            test: proved_loop_test,
            update: proved_update,
            body: proved_body,
            ..
        },
        ProgramStatement::Loop {
            test: source_loop_test,
            update: source_update,
            invariant,
            invariant_checks,
            effect_checks,
            resource_specs,
            ranking_measures,
            structural_measure,
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
        && proved_loop_test == source_loop_test
        && proved_update == source_update
        && proved_body == source_body
}

fn checked_statement_event(
    theorem: &Theorem,
    state: &ExecutionState,
    statement: &ProgramStatement,
) -> Option<StatementOutcome> {
    let (proved_state, proved_statement, outcome) = match checked_evidence_conclusion(theorem) {
        Proposition::ProgramStatementVerifies {
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
    state: &ExecutionState,
    statement: ProgramStatement,
    tail: Option<ProgramStatement>,
) -> Option<Option<ProgramStatement>> {
    let (proved_state, proved_condition, value) = match checked_evidence_conclusion(theorem) {
        Proposition::ProgramConditionEvaluates {
            state,
            condition,
            outcome: ConditionOutcome::Value(value),
        } => (state, condition, *value),
        _ => return None,
    };
    if **proved_state != *state {
        return None;
    }
    let selected = match statement {
        ProgramStatement::If {
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
        _ => return None,
    };
    Some(if matches!(selected, ProgramStatement::Skip) {
        tail
    } else {
        Some(prepend_checked_evidence_statement(selected, tail))
    })
}

struct CheckedEvidenceProgress {
    state: ExecutionState,
    remaining: Option<ProgramStatement>,
    completed: Option<StatementOutcome>,
    /// Where the walk saw memory change, in order.
    memory_steps: Vec<CheckedMemoryStep>,
}

/// One change of memory a walk of checked events passed through: the
/// state before an event and the one after it.
///
/// `may_write` is false for an event that only rewrites what the proof holds
/// (a fold, an unfold, an observation, the end of an automatic lifetime).
/// Such an event changes which values a state caches, never a byte a
/// pointer can reach, and it leaves no effect fact.
#[derive(Clone)]
struct CheckedMemoryStep {
    before: SymbolicMemory,
    after: SymbolicMemory,
    may_write: bool,
    /// For a statement, how many memory effects its recorder appended.
    statement_effects: Option<usize>,
}

/// Follows a retained event tree, which the recorder checked event by event,
/// through an exact source tree: each event's recorded result gives the next
/// state, and nothing it was checked against is checked again. This does not
/// evaluate a C operation.
fn check_evidence_events(
    events: &[CheckedExecutionEvent],
    mut state: ExecutionState,
    mut remaining: Option<ProgramStatement>,
) -> Option<CheckedEvidenceProgress> {
    let mut completed = None;
    let mut memory_steps = Vec::new();
    let mut step_memory = state.memory().clone();
    let mut step_may_write = false;
    // The step of the statement last walked, for its effect count to land on.
    let mut statement_step: Option<usize> = None;
    let mut after_statement = false;
    for event in events {
        // A completed path's context follows its completion and changes
        // nothing the walk follows.
        if matches!(event, CheckedExecutionEvent::CompletedContext(_)) {
            continue;
        }
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
            CheckedExecutionEvent::Context(_)
            | CheckedExecutionEvent::CompletedContext(_)
            | CheckedExecutionEvent::Call(_) => {}
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
        if let Some(StatementOutcome::Return {
            state: returned, ..
        }) = &mut completed
            && let CheckedExecutionEvent::ResourceRewrite(rewrite) = event
        {
            **returned = rewrite.after_state.clone();
            continue;
        }
        if let Some(StatementOutcome::Return {
            state: returned, ..
        }) = &mut completed
            && let CheckedExecutionEvent::PopulationAuthorityRewrite(rewrite) = event
        {
            **returned = rewrite.after_state.clone();
            continue;
        }
        if let CheckedExecutionEvent::AutomaticLifetimeEnd(end) = event {
            if let Some(outcome) = &mut completed {
                let returned = match outcome {
                    StatementOutcome::Normal(state)
                    | StatementOutcome::LoopTestFalse(state)
                    | StatementOutcome::Break(state)
                    | StatementOutcome::Continue(state)
                    | StatementOutcome::Return { state, .. }
                    | StatementOutcome::Throw { state, .. } => state,
                    _ => return None,
                };
                **returned = end.after_state.clone();
            } else {
                state = end.after_state.clone();
            }
            continue;
        }
        if completed.is_some() {
            return None;
        }
        match event {
            CheckedExecutionEvent::LoopEntry { source_after } => {
                remaining = Some(source_after.as_ref().clone());
                continue;
            }
            CheckedExecutionEvent::ReturnProposition(_) => return None,
            CheckedExecutionEvent::ProofCase(_) => continue,
            CheckedExecutionEvent::ProofCaseJoin(join) => {
                remaining = join.advance_checked(&state, &remaining)?;
                state = join.joined_state().clone();
                continue;
            }
            CheckedExecutionEvent::ResourceObservation(observation) => {
                state = observation.after_state.clone();
                continue;
            }
            CheckedExecutionEvent::ResourceRewrite(rewrite) => {
                state = rewrite.after_state.clone();
                continue;
            }
            CheckedExecutionEvent::ViewRelease(release) => {
                state = release.advance_checked(&state)?.clone();
                continue;
            }
            CheckedExecutionEvent::PopulationAuthorityRewrite(rewrite) => {
                state = rewrite.after_state.clone();
                continue;
            }
            CheckedExecutionEvent::PopulationMemberRewrite(rewrite) => {
                state = rewrite.after_state.clone();
                continue;
            }
            // A checked iterated step does not advance an existing trace: the
            // authority ledger records its events, so the trace is checked
            // again from the start.
            CheckedExecutionEvent::IteratedStep(_) => return None,
            CheckedExecutionEvent::TacticApplication(application) => {
                state = application.after_state.clone();
                continue;
            }
            CheckedExecutionEvent::Context(_)
            | CheckedExecutionEvent::CompletedContext(_)
            | CheckedExecutionEvent::StatementEffects(_)
            | CheckedExecutionEvent::Call(_) => continue,
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
                Proposition::ProgramStatementVerifies { statement, .. }
                    if matches!(**statement, ProgramStatement::Skip)
            )
            && !remaining.as_ref().is_some_and(|source| {
                matches!(*split_shared_source(source).0, ProgramStatement::Skip)
            })
        {
            let StatementOutcome::Normal(next_state) =
                checked_statement_event(theorem, &state, &ProgramStatement::Skip)?
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
                match checked_statement_event(theorem, &state, &next_statement)? {
                    StatementOutcome::Normal(next_state) => {
                        state = *next_state;
                        remaining = tail;
                    }
                    outcome @ (StatementOutcome::LoopTestFalse(_)
                    | StatementOutcome::Break(_)
                    | StatementOutcome::Continue(_)
                    | StatementOutcome::Return { .. }
                    | StatementOutcome::Throw { .. }
                    | StatementOutcome::VerificationDiverges) => {
                        if tail.is_some() {
                            return None;
                        }
                        completed = Some(outcome);
                    }
                    StatementOutcome::UndefinedBehavior(_)
                    | StatementOutcome::RuntimeError(_)
                    | StatementOutcome::Jump { .. } => return None,
                }
            }
            CheckedExecutionEvent::Condition(theorem) => {
                remaining = checked_condition_event(theorem, &state, next_statement, tail)?;
            }
            CheckedExecutionEvent::Branch(branch) => {
                let ProgramStatement::If { .. } = &next_statement else {
                    return None;
                };
                // The check that built `branch` walked both arms from this
                // state over this `if`; they consume it alone, so they leave
                // `tail` here as they left the branch's own continuation.
                if !branch.matches_source(&state, &next_statement, &tail) {
                    return None;
                }
                state = branch.joined_state().clone();
                remaining = tail;
            }
            CheckedExecutionEvent::ProofCase(_)
            | CheckedExecutionEvent::ProofCaseJoin(_)
            | CheckedExecutionEvent::Context(_)
            | CheckedExecutionEvent::CompletedContext(_)
            | CheckedExecutionEvent::StatementEffects(_) => {
                unreachable!("handled before source advance")
            }
            CheckedExecutionEvent::LoopEntry { .. } | CheckedExecutionEvent::Call(_) => {
                unreachable!("handled before source advance")
            }
            CheckedExecutionEvent::AutomaticLifetimeEnd(_)
            | CheckedExecutionEvent::ResourceObservation(_) => {
                unreachable!("handled before source advance")
            }
            CheckedExecutionEvent::ReturnProposition(_)
            | CheckedExecutionEvent::ResourceRewrite(_)
            | CheckedExecutionEvent::PopulationAuthorityRewrite(_)
            | CheckedExecutionEvent::PopulationMemberRewrite(_)
            | CheckedExecutionEvent::IteratedStep(_)
            | CheckedExecutionEvent::ViewRelease(_)
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
        && (!fact.is_certified()
            || (fact.generated_load_binding().is_none() && !fact.has_checked_pointer_read()))
    {
        return assumptions;
    }
    crate::kernel::reasoning::path_facts::count_context_rebuild_entries(1);
    assumptions.assume_execution_pure_fact(fact)
}

fn trace_completion<E: std::borrow::Borrow<CheckedExecutionEvent>>(
    function: &ProgramFunction,
    events: &[E],
    assumptions: &PureFactContext,
    checked_void_fallthrough: bool,
) -> Result<
    (
        StatementOutcome,
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
        &mut None,
    )
}

/// Imports one kernel-published return context for both propositions and folds.
fn retain_return_context(
    function: &ProgramFunction,
    executed_under: &mut PureFactContext,
    return_origin: Option<&StatementOutcome>,
    context: &Arc<CheckedReturnContext>,
    return_context: &mut Option<Arc<CheckedReturnContext>>,
) -> Result<(), &'static str> {
    if return_origin != Some(&context.origin) {
        return Err("return proof belongs to a different execution path");
    }
    if let Some(previous) = return_context.as_ref() {
        if !Arc::ptr_eq(previous, context) {
            return Err("return proofs have different publication contexts");
        }
    } else {
        // Import this path's kernel-produced effects and resource
        // observations once, before consuming any logical proof.
        for fact in context
            .facts
            .facts_not_assumed_by(executed_under)
            .into_iter()
            .chain(
                context
                    .facts
                    .producer_facts()
                    .filter(|fact| fact.is_certified() && fact.generated_load_binding().is_some()),
            )
        {
            *executed_under = retain_completed_path_fact(std::mem::take(executed_under), fact);
        }
        let FunctionOutcome::Return {
            state: published, ..
        } = &context.published
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
            let Resource::Composite { name, .. } = held.resource() else {
                continue;
            };
            let Some(definition) = definitions.get(name.as_str()) else {
                continue;
            };
            if !(held.is_view() || held.has_proven_positive_quantity(executed_under)) {
                continue;
            }
            let authority = ResourceFact::own(held.resource().clone());
            // Immutable argument facts of an ordinary held resource
            // survive a return. Instantiate with no memory, resources,
            // or ambient read premises so this cannot import a mutable
            // invariant from an unchecked current state.
            if !definition[0].is_authorized()
                && let Some(facts) =
                    crate::kernel::functions::evaluate_composite_resource_fact_propositions(
                        &authority,
                        definition,
                        &SymbolicMemory::new(),
                        &ResourceContext::new(),
                        &PureFactContext::new().require_owned_expression_loads(),
                    )
            {
                for fact in facts {
                    *executed_under = std::mem::take(executed_under).assume_proposition(fact);
                }
            }
            if let Some(facts) =
                crate::kernel::functions::evaluate_composite_resource_relation_propositions(
                    &authority,
                    definition,
                    &published.program_point(),
                    executed_under,
                )
            {
                for fact in facts {
                    *executed_under = std::mem::take(executed_under).assume_proposition(fact);
                }
            }
            if let Some(facts) =
                crate::kernel::functions::evaluate_composite_resource_loadable_propositions(
                    held,
                    definition,
                    &published.program_point(),
                    executed_under,
                )
            {
                for fact in facts {
                    *executed_under = std::mem::take(executed_under).assume_proposition(fact);
                }
            }
        }
        *return_context = Some(context.clone());
    }
    Ok(())
}

/// As [`trace_completion`], where `entry_facts` are the facts the checked
/// entry was checked under. A return proof's facts that the entry already
/// held are the proof's assumptions, not path facts, so only the facts it
/// introduced since are checked against the path.
///
/// When a return proof assumes a fact the path does not justify, that fact
/// is left in `unjustified` for the refusal's diagnostic. It is only read
/// after the refusal; it never affects the verdict.
fn trace_completion_from_entry<E: std::borrow::Borrow<CheckedExecutionEvent>>(
    function: &ProgramFunction,
    events: &[E],
    assumptions: &PureFactContext,
    checked_void_fallthrough: bool,
    entry_facts: Option<&PureFactStore>,
    unjustified: &mut Option<Proposition>,
) -> Result<
    (
        StatementOutcome,
        PureFactContext,
        crate::kernel::ExecutionFacts,
    ),
    &'static str,
> {
    if !events_use_the_function_definitions(function, events) {
        return Err("a retained resource event was checked under other composite definitions");
    }
    let mut completed: Option<(StatementOutcome, PureFactContext)> = None;
    let mut return_origin = None;
    let mut return_context: Option<Arc<CheckedReturnContext>> = None;
    let mut proposition_base: Option<&PureFactStore> = None;
    let mut fallthrough = None;
    // Only the last checked statement can be the function's implicit return.
    // Earlier normal statements may still have resource exchanges before a
    // source tail. One reverse pass keeps this decision linear in the trace.
    let last_statement = checked_void_fallthrough
        .then(|| {
            events
                .iter()
                .rposition(|event| matches!(event.borrow(), CheckedExecutionEvent::Statement(_)))
        })
        .flatten();
    let mut interface_execution_facts: crate::kernel::ExecutionFacts = Vec::new().into();
    for (index, event) in events.iter().enumerate() {
        match event.borrow() {
            CheckedExecutionEvent::Statement(theorem) => {
                if completed.is_some() {
                    return Err("a trace continues past its completing theorem");
                }
                let Proposition::ProgramStatementVerifies { outcome, .. } =
                    checked_evidence_conclusion(theorem)
                else {
                    return Err("retained statement evidence has a non-statement conclusion");
                };
                match outcome {
                    StatementOutcome::Normal(state) => {
                        let context = match events.get(index + 1).map(E::borrow) {
                            Some(CheckedExecutionEvent::Context(context)) => {
                                context.as_ref().clone()
                            }
                            _ => {
                                crate::kernel::api::proof_evidence_assumptions(theorem, assumptions)
                            }
                        };
                        let returning = StatementOutcome::Return {
                            value: ProgramValue::Void.into(),
                            state: state.clone(),
                        };
                        if last_statement == Some(index) {
                            return_origin = Some(outcome.clone());
                            completed = Some((returning, context));
                        } else {
                            fallthrough = Some((returning, context));
                        }
                    }
                    StatementOutcome::LoopTestFalse(_)
                    | StatementOutcome::Break(_)
                    | StatementOutcome::Continue(_)
                    | StatementOutcome::Jump { .. } => {
                        fallthrough = None;
                    }
                    StatementOutcome::Throw { .. }
                        if events[index + 2..].iter().any(|event| {
                            matches!(event.borrow(), CheckedExecutionEvent::Statement(_))
                        }) =>
                    {
                        // A caught throw is followed by the synthetic
                        // handler-binding/cleanup trace. It is an internal
                        // control transfer, not this execution path's final
                        // function outcome.
                    }
                    StatementOutcome::Return { .. }
                    | StatementOutcome::Throw { .. }
                    | StatementOutcome::VerificationDiverges => {
                        // The path completes under the context its final
                        // theorem was proved under, recorded right after it.
                        let executed_under = match events.get(index + 1).map(E::borrow) {
                            Some(CheckedExecutionEvent::Context(context)) => {
                                context.as_ref().clone()
                            }
                            _ => {
                                crate::kernel::api::proof_evidence_assumptions(theorem, assumptions)
                            }
                        };
                        return_origin = Some(outcome.clone());
                        completed = Some((outcome.clone(), executed_under));
                    }
                    StatementOutcome::UndefinedBehavior(_) | StatementOutcome::RuntimeError(_) => {
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
                    let StatementOutcome::Return { state, .. } = outcome else {
                        return Err("population authority rewrite requires a returned state");
                    };
                    **state = rewrite
                        .advance_checked(state)
                        .ok_or("population authority rewrite failed certificate check")?
                        .clone();
                }
            }
            CheckedExecutionEvent::ViewRelease(_) => {
                fallthrough = None;
                if completed.is_some() {
                    return Err("release_view must precede function exit");
                }
            }
            CheckedExecutionEvent::PopulationMemberRewrite(_) => {
                fallthrough = None;
                if completed.is_some() {
                    return Err("population member rewrite must precede function exit");
                }
            }
            CheckedExecutionEvent::TacticApplication(application) => {
                fallthrough = None;
                if let Some(effect) = &application.return_effect {
                    let Some((StatementOutcome::Return { state, .. }, executed_under)) =
                        &mut completed
                    else {
                        return Err("an outcome tactic application requires a returned state");
                    };
                    **state = application.after_state.clone();
                    for fact in &effect.facts {
                        *executed_under =
                            std::mem::take(executed_under).assume_proposition(fact.clone());
                    }
                } else if completed.is_some() {
                    return Err("a frontier tactic application must precede function exit");
                }
            }
            CheckedExecutionEvent::ReturnProposition(retained) => {
                let Some((StatementOutcome::Return { state, .. }, executed_under)) = &mut completed
                else {
                    return Err("return proof requires a returning path");
                };
                retain_return_context(
                    function,
                    executed_under,
                    return_origin.as_ref(),
                    &retained.context,
                    &mut return_context,
                )?;
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
                    // A store materializes its exact cell in this state.
                    // This is read validity, not ownership or a value equality;
                    // no ambient range search or cross-state transport occurs.
                    let materialized_read = matches!(fact,
                        Proposition::MemoryLoadable { memory, base, bytes, wide: false, .. }
                            if bytes.as_const().is_some_and(|width|
                                width > 0 && memory.is_loadable_concretely(base, width)));
                    if !materialized_read
                        && !executed_under.settles_exactly(fact)
                        && !resource_composition_is_supported_by(
                            fact,
                            state.resources(),
                            executed_under,
                        )
                        && !matches!(fact, Proposition::ResourceComposition(resources)
                            if ResourceContext::new()
                                .try_compose_with_facts(resources.facts().iter().cloned(), executed_under)
                                .is_ok())
                    {
                        *unjustified = Some(fact.clone());
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
                    let StatementOutcome::Return { state, .. } = outcome else {
                        return Err("resource rewriting requires a returned state");
                    };
                    if let Some(context) = &rewrite.return_context {
                        retain_return_context(
                            function,
                            executed_under,
                            return_origin.as_ref(),
                            context,
                            &mut return_context,
                        )?;
                    }
                    if **state != rewrite.before_state {
                        return Err("post-return resource rewrite has a different input state");
                    }
                    if let Some(observation) = &rewrite.return_observation {
                        // This private event retains the kernel producer's
                        // completed exchange. Its premises were checked there;
                        // do not choose and check the body again at C's state.
                        if return_origin.as_ref() != Some(&observation.context.origin) {
                            return Err(
                                "return resource observation belongs to a different execution path",
                            );
                        }
                        for fact in &observation.semantic_facts {
                            *executed_under =
                                std::mem::take(executed_under).assume_proposition(fact.clone());
                        }
                        **state = rewrite.after_state.clone();
                        continue;
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
                        // The event's successor was constructed by the kernel.
                        // This pass binds its premises to the selected execution
                        // path; it must not replace or compare that successor
                        // with a newly chosen resource representation.
                        // Import only the selected body's rechecked facts, including
                        // its identical readability at the caller's cached state.
                        // Do not import an arbitrary post-rewrite fact context.
                        let allowed = checked
                            .semantic_facts
                            .iter()
                            .cloned()
                            .chain(
                                checked
                                    .body_clauses
                                    .iter()
                                    .map(|clause| clause.proposition.clone()),
                            )
                            .collect::<std::collections::BTreeSet<_>>();
                        let mut cached_comparisons = HashMap::new();
                        for fact in rewrite
                            .after_facts
                            .introduced_since(&rewrite.before_facts)
                            .ok_or("return fold facts have a different lineage")?
                        {
                            if !allowed.contains(&fact)
                                && cached_body_loadability(
                                    &fact,
                                    state.memory(),
                                    &allowed,
                                    &mut cached_comparisons,
                                )
                            {
                                *executed_under =
                                    std::mem::take(executed_under).assume_proposition(fact);
                            }
                        }
                        for fact in checked.semantic_facts {
                            *executed_under =
                                std::mem::take(executed_under).assume_proposition(fact);
                        }
                    }
                    if let Some(presentation) = &rewrite.return_presentation {
                        if return_origin.as_ref() != Some(&presentation.context.origin) {
                            return Err(
                                "return composite presentation belongs to a different execution path",
                            );
                        }
                        let observed = &presentation.rewrite;
                        CheckedResourceRewrite::check_with_children(
                            function,
                            &observed.before_state,
                            &observed.before_facts,
                            &presentation.selected,
                            &observed.after_state,
                            &observed.after_facts,
                            &CheckedCallEvents::default(),
                            None,
                        )
                        .map_err(|_| "return composite presentation has an unchecked exchange")?;
                        for fact in &presentation.published_facts {
                            *executed_under =
                                std::mem::take(executed_under).assume_proposition(fact.clone());
                        }
                        for fact in observed
                            .after_facts
                            .introduced_since(&observed.before_facts)
                            .ok_or("return composite presentation facts have a different lineage")?
                        {
                            *executed_under =
                                std::mem::take(executed_under).assume_proposition(fact);
                        }
                    }
                    **state = rewrite.after_state.clone();
                    // Only the rechecked exchange's semantic facts enter this
                    // path, never a proof state's entire assumption context.
                }
            }
            CheckedExecutionEvent::AutomaticLifetimeEnd(end) => {
                if let Some((outcome, _)) = completed.as_mut().or(fallthrough.as_mut()) {
                    let state = match outcome {
                        StatementOutcome::Return { state, .. }
                        | StatementOutcome::Throw { state, .. } => state,
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
            CheckedExecutionEvent::LoopEntry { .. }
            | CheckedExecutionEvent::Condition(_)
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
            | CheckedExecutionEvent::CompletedContext(_)
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
fn events_use_the_function_definitions<E: std::borrow::Borrow<CheckedExecutionEvent>>(
    function: &ProgramFunction,
    events: &[E],
) -> bool {
    fn check<E: std::borrow::Borrow<CheckedExecutionEvent>>(
        function: &ProgramFunction,
        events: &[E],
        checked_entries: &mut std::collections::HashSet<usize>,
    ) -> bool {
        let definitions = function.composite_resource_definitions();
        events.iter().all(|event| match event.borrow() {
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
            CheckedExecutionEvent::LoopEntry { .. }
            | CheckedExecutionEvent::ViewRelease(_)
            | CheckedExecutionEvent::AutomaticLifetimeEnd(_)
            | CheckedExecutionEvent::IteratedStep(_)
            | CheckedExecutionEvent::Statement(_)
            | CheckedExecutionEvent::Call(_)
            | CheckedExecutionEvent::Condition(_)
            | CheckedExecutionEvent::Context(_)
            | CheckedExecutionEvent::CompletedContext(_)
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
    pub(crate) expected: Option<ProgramStatement>,
    /// The statement the offered theorem proves.
    pub(crate) proved: Option<ProgramStatement>,
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

fn validate_checked_event_shapes<'e>(
    events: impl IntoIterator<Item = &'e CheckedExecutionEvent>,
) -> Result<(), &'static str> {
    validate_checked_event_shapes_after(events, Vec::new())
}

/// The call views a statement introduced that later events have not yet
/// consumed, given the events before a point, newest first. Only the events
/// since the last statement are read: any other event closes the views.
fn pending_call_views_after<'e>(
    before: impl IntoIterator<Item = &'e CheckedExecutionEvent>,
) -> Vec<crate::kernel::SharedMemory> {
    let mut consumed = Vec::new();
    for event in before {
        match event {
            CheckedExecutionEvent::Context(_)
            | CheckedExecutionEvent::CompletedContext(_)
            | CheckedExecutionEvent::StatementEffects(_) => {}
            CheckedExecutionEvent::Call(call) => consumed.push(call.canonical_view()),
            CheckedExecutionEvent::Statement(theorem) => {
                let mut pending = statement_call_havoc_views(theorem);
                for view in consumed.iter().rev() {
                    if let Some(index) = pending.iter().position(|pending| pending == view) {
                        pending.remove(index);
                    }
                }
                return pending;
            }
            _ => return Vec::new(),
        }
    }
    Vec::new()
}

fn validate_checked_event_shapes_after<'e>(
    events: impl IntoIterator<Item = &'e CheckedExecutionEvent>,
    mut pending_call_views: Vec<crate::kernel::SharedMemory>,
) -> Result<(), &'static str> {
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
            CheckedExecutionEvent::Context(_)
            | CheckedExecutionEvent::CompletedContext(_)
            | CheckedExecutionEvent::StatementEffects(_) => {
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
            CheckedExecutionEvent::LoopEntry { .. }
            | CheckedExecutionEvent::ViewRelease(_)
            | CheckedExecutionEvent::AutomaticLifetimeEnd(_)
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
                Proposition::ProgramStatementVerifies { .. }
            )
        } else {
            matches!(
                checked_evidence_conclusion(theorem),
                Proposition::ProgramConditionEvaluates { .. }
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
    pub(crate) fn checked_call_events(&self) -> CheckedCallEvents {
        self.checked_call_events.clone()
    }

    fn retained_checked_callees(
        &self,
    ) -> Option<Arc<std::collections::BTreeSet<crate::kernel::termination::CallDependency>>> {
        if self.execution_evidence.is_empty() {
            return None;
        }
        let mut callees = std::collections::BTreeSet::new();
        let mut seen = std::collections::HashSet::new();
        // Traces share their prefixes; each shared event is read once.
        let mut visited = std::collections::HashSet::new();
        for trace in &self.execution_evidence {
            collect_checked_callees(
                trace.unvisited_suffix(&mut visited).0,
                &mut seen,
                &mut callees,
            );
        }
        Some(Arc::new(callees))
    }

    fn retained_applied_tactics(&self) -> std::collections::BTreeSet<String> {
        let mut tactics = std::collections::BTreeSet::new();
        let mut visited = std::collections::HashSet::new();
        for trace in &self.execution_evidence {
            collect_applied_tactics(trace.unvisited_suffix(&mut visited).0, &mut tactics);
        }
        tactics
    }

    fn retained_call_events(&self) -> CheckedCallEvents {
        // A shared event is inserted where the first trace reaching it
        // inserted it before, so the groups keep their order.
        let mut call_events = CheckedCallEvents::default();
        let mut visited = std::collections::HashSet::new();
        for trace in &self.execution_evidence {
            collect_retained_call_events(trace.unvisited_suffix(&mut visited).0, &mut call_events);
        }
        call_events
    }

    pub(crate) fn at_entry_with_descent(
        state: ExecutionState,
        frontier: ExecutionFrontier,
        function: &ProgramFunction,
        environment: &crate::kernel::ExecutionEnvironment,
    ) -> Result<Self, String> {
        let descent = crate::kernel::termination::descent_completion::OpenedDescent::inherit(
            function,
            environment,
        )?;
        let mut core = Self::at_entry(state, frontier);
        core.descent = descent;
        Ok(core)
    }

    pub(crate) fn at_entry(state: ExecutionState, frontier: ExecutionFrontier) -> Self {
        let state: SharedValue<ExecutionState> = state.into();
        Self {
            descent: None,
            last_footprint: None,
            initial_match_scope: state.clone(),
            publication_case_facts: ExecutionFacts::new(),
            cases_hold_memory_effects: false,
            path_context: None,
            initial_match_reserved: Arc::new(std::sync::OnceLock::new()),
            state,
            evidence_state: None,
            evidence_completed: false,
            evidence_source: None,
            evidence_try_stack: Vec::new(),
            frontier,
            effect_facts: Default::default(),
            execution_evidence: vec![ExecutionEvidence::default()].into(),
            prepared_tactic_application: None,
            prepared_instance_fold: None,
            prepared_return_fold: None,
            pending_loop_returns: Default::default(),
            completed_pending_loop_returns: None,
            pending_loop_return_start: None,
            borrow_evidence: crate::kernel::borrows::empty_checked_borrow_evidence_sequence(),
            return_resource_rewrites: Default::default(),
            return_producers: Default::default(),
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
        }
    }

    /// The entry facts while the proof has not left its checked entry.
    pub(crate) fn entry_facts_at_entry(&self) -> Option<&PureFactStore> {
        (self.frontier.is_at_function_entry()
            && self.execution_evidence.len() == 1
            && self.execution_evidence[0].is_empty())
        .then_some(self.entry_facts.as_ref())
        .flatten()
    }

    #[cfg(test)]
    pub(crate) fn record_checked_function_entry(
        &mut self,
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        expected_entry_state: &ExecutionState,
        assumptions: PureFactContext,
    ) -> Result<(), RuntimeError> {
        if !self.frontier.is_at_function_entry()
            || self.execution_evidence.len() != 1
            || !self.execution_evidence[0].is_empty()
        {
            return Err(RuntimeError::FunctionContract(
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

    /// Extends the open trace's path context by a newly recorded context and
    /// by the case facts and effects admitted since the last one. Each new
    /// fact is assumed once; a context that does not extend the last one, or
    /// adds more facts than restarting would leave to fold, restarts it
    /// ([`CheckedPathContext`]).
    fn advance_path_context(&mut self, context: &PureFactContext) {
        let streams = (self.publication_case_facts.len(), self.effect_facts.len());
        let extended = self.path_context.as_deref().and_then(|built| {
            (built.cases <= streams.0 && built.effects <= streams.1)
                .then(|| {
                    path_context_extended_by(
                        &built.facts,
                        &built.recorded,
                        context,
                        streams.0 + streams.1,
                    )
                    .map(|facts| {
                        let lagging = built.lagging.map(|steps| steps + 1);
                        (facts, built.cases, built.effects, lagging)
                    })
                })
                .flatten()
        });
        let (facts, cases, effects, lagging) =
            extended.unwrap_or_else(|| (context.clone(), 0, 0, Some(1)));
        let mut built = CheckedPathContext {
            recorded: context.clone(),
            facts,
            cases,
            effects,
            lagging,
            case_facts: self.publication_case_facts.clone(),
        };
        // A restart leaves the trace's history to fold. Folding it once as
        // many transitions have recorded since, the restarting one included,
        // keeps each transition's share constant when a path restarts often;
        // completion folds what remains.
        let lag = (streams.0 - cases) + (streams.1 - effects);
        if lagging.is_none_or(|steps| steps >= lag) {
            built = self.caught_up(built);
        }
        self.path_context = Some(Arc::new(built));
    }

    /// `built` with every case fact and effect of the open trace folded in.
    fn caught_up(&self, mut built: CheckedPathContext) -> CheckedPathContext {
        for fact in self.publication_case_facts.facts_from(built.cases) {
            built.facts = retain_completed_path_fact(built.facts, fact);
        }
        for fact in self.effect_facts.facts_from(built.effects) {
            #[cfg(test)]
            CHECKED_PATH_EFFECT_ADMISSIONS.with(|count| count.set(count.get() + 1));
            built.facts = retain_completed_path_fact(built.facts, fact);
        }
        built.cases = self.publication_case_facts.len();
        built.effects = self.effect_facts.len();
        built.lagging = None;
        built
    }

    /// Records the path context on the traces a completing statement ended,
    /// first folding whatever a recent restart left to fold.
    fn record_completed_path_context(&mut self) {
        let Some(built) = self.path_context.as_deref() else {
            return;
        };
        if built.cases < self.publication_case_facts.len()
            || built.effects < self.effect_facts.len()
        {
            let built = self.caught_up(built.clone());
            self.path_context = Some(Arc::new(built));
        }
        let context = self.path_context.clone().expect("path context");
        for trace in self.execution_evidence.iter_mut() {
            trace.push(CheckedExecutionEvent::CompletedContext(context.clone()));
        }
    }

    #[cfg(test)]
    pub(crate) fn take_checked_path_effect_admissions() -> usize {
        CHECKED_PATH_EFFECT_ADMISSIONS.with(|count| count.replace(0))
    }

    /// Open the facts of this exact completed trace before outcome
    /// publication. The path context already carries its checked effects.
    pub(crate) fn checked_outcome_facts(
        &self,
        candidate: &crate::kernel::FunctionExecutionCandidate,
        entry: &PureFactStore,
        facts: &PureFactStore,
    ) -> Option<PureFactStore> {
        let frontier = self.frontier.execution()?;
        if !self.evidence_completed
            || self.execution_evidence.len() != 1
            || frontier.path_count() != 1
            || !frontier.candidate_at(0)?.shares_record_with(candidate)
        {
            return None;
        }
        let built = self.path_context.as_ref()?;
        if built.cases != self.publication_case_facts.len()
            || built.effects != self.effect_facts.len()
        {
            return None;
        }
        facts.with_outcome_context(built.facts.clone(), entry)
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
    #[cfg(test)]
    pub(crate) fn record_statement_transition(
        &mut self,
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        theorem: Theorem,
        context: PureFactContext,
        execution_facts: &(impl ExecutionFactSource + ?Sized),
        obligations: &[crate::kernel::ProofObligation],
    ) -> Result<(), EvidenceRefusal> {
        self.record_statement_transition_with_borrow_evidence(
            function,
            arguments,
            theorem,
            context,
            execution_facts,
            obligations,
            &crate::kernel::borrows::empty_checked_borrow_evidence_sequence(),
        )
    }

    #[cfg(test)]
    pub(crate) fn record_statement_transition_with_borrow_evidence(
        &mut self,
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        theorem: Theorem,
        context: PureFactContext,
        execution_facts: &(impl ExecutionFactSource + ?Sized),
        obligations: &[crate::kernel::ProofObligation],
        borrow_evidence: &crate::kernel::borrows::CheckedBorrowCallEvidenceSequence,
    ) -> Result<(), EvidenceRefusal> {
        if let Some(opened) = &self.descent {
            opened.accept(None).map_err(EvidenceRefusal::from)?;
        }
        self.record_statement_transition_native(
            function,
            arguments,
            theorem,
            context,
            execution_facts,
            obligations,
            borrow_evidence,
        )
        .map(|_| ())
    }

    /// Returns the statement footprint's checked containment fact, if it has
    /// a resource bound, for publication in the successor's pure fact store.
    pub(crate) fn record_statement_transition_with_descent(
        &mut self,
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        native_step: &crate::kernel::SymbolicExecutionPath,
        context: PureFactContext,
        execution_facts: &(impl ExecutionFactSource + ?Sized),
    ) -> Result<Option<Proposition>, EvidenceRefusal> {
        if let Some(opened) = &self.descent {
            opened
                .accept_at_state(native_step.descent_step.as_ref(), self.reached_state())
                .map_err(EvidenceRefusal::from)?;
        }
        self.record_statement_transition_native(
            function,
            arguments,
            native_step.theorem.clone(),
            context,
            execution_facts,
            &native_step.obligations,
            &native_step.borrow_evidence,
        )
    }

    /// Records a statement theorem and appends the exact stable-view evidence
    /// emitted by the checked evaluator for that transition.
    fn record_statement_transition_native(
        &mut self,
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        theorem: Theorem,
        context: PureFactContext,
        execution_facts: &(impl ExecutionFactSource + ?Sized),
        _obligations: &[crate::kernel::ProofObligation],
        borrow_evidence: &crate::kernel::borrows::CheckedBorrowCallEvidenceSequence,
    ) -> Result<Option<Proposition>, EvidenceRefusal> {
        debug_assert_eq!(self.execution_evidence.len(), 1);
        let (outcome, source_after) =
            self.check_statement_evidence(function, arguments, &theorem, &context)?;
        self.borrow_evidence = crate::kernel::borrows::concat_checked_borrow_evidence(
            &self.borrow_evidence,
            borrow_evidence,
        );
        let call_events = statement_call_havoc_views(&theorem)
            .into_iter()
            .map(|view| self.checked_call_events.new_event(view))
            .collect::<Vec<_>>();
        let before = match checked_evidence_conclusion(&theorem) {
            Proposition::ProgramStatementVerifies {
                state, statement, ..
            } => Some((state.as_ref(), statement.as_ref())),
            _ => None,
        };
        let after = match &outcome {
            StatementOutcome::Normal(state)
            | StatementOutcome::Return { state, .. }
            | StatementOutcome::LoopTestFalse(state)
            | StatementOutcome::Break(state)
            | StatementOutcome::Continue(state)
            | StatementOutcome::Jump { state, .. }
            | StatementOutcome::Throw { state, .. } => Some(state.as_ref()),
            _ => None,
        };
        self.last_footprint = before.zip(after).map(|((before, statement), after)| {
            crate::kernel::RegionFootprint::statement_transition(
                format!("region({}).footprint", self.frontier.next_statement_index),
                statement,
                before,
                after,
                execution_facts,
            )
        });
        let footprint_bound = self.last_footprint.as_ref().and_then(|footprint| {
            let bound = footprint.resource_bound.as_ref()?;
            Some(Proposition::ResourceContains {
                parent: Box::new(bound.clone()),
                child: Box::new(Resource::Footprint(footprint.clone())),
            })
        });
        if let Some(fact) = &footprint_bound {
            self.effect_facts
                .push(ExecutionPureFact::new(fact.clone()).into_certified());
            self.retain_step_case(fact.clone());
        }
        let memory_effects = self.append_statement_effects(execution_facts);
        self.advance_path_context(&context);
        for trace in self.execution_evidence.iter_mut() {
            trace.push(CheckedExecutionEvent::Statement(theorem.clone()));
            trace.push(CheckedExecutionEvent::Context(Box::new(context.clone())));
            for call in &call_events {
                trace.push(CheckedExecutionEvent::Call(call.clone()));
            }
            trace.push(CheckedExecutionEvent::StatementEffects(memory_effects));
        }
        self.evidence_source = matches!(&outcome, StatementOutcome::Normal(_))
            .then_some(source_after.clone())
            .flatten();
        if matches!(
            &outcome,
            StatementOutcome::LoopTestFalse(_)
                | StatementOutcome::Break(_)
                | StatementOutcome::Continue(_)
        ) {
            self.leave_loop_control_scopes();
        }
        // A `break` or `continue` this frontier's own region owns, rather
        // than one belonging to a concretely executed loop it contains.
        let region_loop_control = if self.frontier.continuations.is_empty()
            && (self.frontier.in_loop_body
                || matches!(self.frontier.region, ExecutionRegionKind::LoopBody))
        {
            match &outcome {
                StatementOutcome::LoopTestFalse(_) => Some(LoopControlExit::TestFalse),
                StatementOutcome::Break(_) => Some(LoopControlExit::Break),
                StatementOutcome::Continue(_) => Some(LoopControlExit::Continue),
                _ => None,
            }
        } else {
            None
        };
        if let StatementOutcome::Throw { value, .. } = &outcome
            && let Some(exceptional) = self
                .frontier
                .continuations
                .iter()
                .filter_map(|continuation| continuation.exceptional.as_ref())
                .next_back()
        {
            // An unwind cleanup entered by this exception runs its cleanup
            // and then continues with exactly this payload.
            let handler = match &exceptional.entry {
                ExceptionalEntry::Catch(_) => exceptional.handler.clone(),
                ExceptionalEntry::Unwind(cleanup) => {
                    Arc::new(crate::kernel::program_unwind_continuation(
                        cleanup,
                        ProgramExpression::Value(value.clone().into_native()),
                    ))
                }
            };
            match self.evidence_try_stack.last_mut() {
                Some(frame) if frame.entry == exceptional.entry => {
                    if frame.entry.is_unwind() {
                        frame.handler = handler;
                    }
                }
                _ => self.evidence_try_stack.push(EvidenceTryFrame {
                    entry: exceptional.entry.clone(),
                    handler,
                    tail_after_try: self
                        .frontier
                        .continuations
                        .iter()
                        .filter(|continuation| continuation.exceptional.is_some())
                        .rfind(|continuation| continuation.exceptional.is_some())
                        .and_then(|continuation| continuation.remaining.clone()),
                }),
            }
        }
        match outcome {
            StatementOutcome::Normal(next_state) => {
                self.evidence_state = Some(*next_state);
                // A checked final normal statement also completes a void
                // function. Keep the recorder consistent with the completion
                // checker, so post-return folds can retain their certificates.
                self.evidence_completed = function.return_type()
                    == crate::kernel::ProgramType::Void
                    && source_after.is_none()
                    && self.frontier.region == ExecutionRegionKind::Function
                    && !self.frontier.in_loop_body
                    && self.frontier.continuations.is_empty();
                if self.evidence_completed {
                    self.record_completed_path_context();
                }
            }
            StatementOutcome::Throw { state, .. }
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
            StatementOutcome::Return { state, .. } | StatementOutcome::Throw { state, .. } => {
                self.evidence_state = Some(*state);
                self.evidence_completed = true;
                self.record_completed_path_context();
            }
            StatementOutcome::Continue(state)
                if region_loop_control.is_some() && self.frontier.loop_update.is_some() =>
            {
                self.evidence_try_stack.clear();
                let (update, index) = self.frontier.loop_update.take().expect("checked update");
                self.frontier.position = FrontierPosition::StatementEntry {
                    remaining: update.clone(),
                };
                self.frontier.next_statement_index = index;
                self.frontier.loop_control = LoopControlExit::Continue;
                self.evidence_source = Some(update);
                self.evidence_state = Some(*state);
                self.evidence_completed = false;
            }
            StatementOutcome::LoopTestFalse(state)
            | StatementOutcome::Break(state)
            | StatementOutcome::Continue(state)
                if region_loop_control.is_some() =>
            {
                // A loop-preservation proof executes one body iteration in a
                // bounded region. Each control reaches that region's typed
                // boundary, and the path stops there. The enclosing loop rule
                // retains the distinct exit reason: break or false test exits,
                // while continue reaches the back edge. A continuation on this
                // frontier means the innermost loop is a concretely executed
                // one this region contains, which is resumed below instead.
                self.evidence_try_stack.clear();
                self.frontier.loop_control =
                    region_loop_control.expect("the guard matched a loop control");
                self.frontier.position = FrontierPosition::RegionBoundary;
                self.evidence_state = Some(*state);
                self.evidence_completed = true;
            }
            StatementOutcome::LoopTestFalse(state) | StatementOutcome::Break(state) => {
                let source_after = self.advance_loop_control(false)?;
                self.evidence_source = source_after;
                self.evidence_state = Some(*state);
                self.evidence_completed = false;
            }
            StatementOutcome::Continue(state) => {
                let source_after = self.advance_loop_control(true)?;
                self.evidence_source = source_after;
                self.evidence_state = Some(*state);
                self.evidence_completed = false;
            }
            StatementOutcome::Jump { target, state } => {
                if self.frontier.natural_backedge_target == Some(target)
                    && self.frontier.in_loop_body
                {
                    self.frontier.position = FrontierPosition::RegionBoundary;
                    self.frontier.loop_control = LoopControlExit::BodyEnd;
                    self.evidence_state = Some(*state);
                    self.evidence_completed = true;
                    return Ok(footprint_bound);
                }
                if self.frontier.in_loop_body && function.control_target(target).is_some() {
                    self.frontier.position = FrontierPosition::RegionBoundary;
                    self.frontier.loop_control = LoopControlExit::Jump(target);
                    self.evidence_state = Some(*state);
                    self.evidence_completed = true;
                    return Ok(footprint_bound);
                }
                let target = function
                    .control_target(target)
                    .ok_or_else(|| EvidenceRefusal::from("goto target is not in its function"))?;
                self.frontier.continuations.clear();
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
            StatementOutcome::VerificationDiverges
            | StatementOutcome::UndefinedBehavior(_)
            | StatementOutcome::RuntimeError(_) => self.evidence_completed = true,
        }
        Ok(footprint_bound)
    }

    /// Abandon only the lexical continuations this transfer leaves. The
    /// nearest loop stays on top; unrelated enclosing frames are untouched.
    fn leave_loop_control_scopes(&mut self) {
        while self
            .frontier
            .continuations
            .last()
            .is_some_and(|frame| frame.loop_control.is_none())
        {
            crate::instrumentation::record_deterministic_work(1);
            self.frontier.continuations.pop();
        }
    }

    /// Follow a destination captured by checked loop entry. Its evidence
    /// cursor already includes enclosing loops, even when the driver's local
    /// remainder ends at the current body's boundary.
    fn advance_loop_control(
        &mut self,
        continue_statement: bool,
    ) -> Result<Option<Arc<ProgramStatement>>, EvidenceRefusal> {
        crate::instrumentation::record_deterministic_work(1);
        let continuation = self
            .frontier
            .continuations
            .pop()
            .ok_or_else(|| EvidenceRefusal::from("loop control has no enclosing loop"))?;
        let control = continuation
            .loop_control
            .as_ref()
            .ok_or_else(|| EvidenceRefusal::from("loop control has no enclosing loop"))?;
        let destination = if continue_statement {
            &control.continuing
        } else {
            &control.exiting
        };
        self.evidence_try_stack.truncate(control.try_depth);
        self.frontier.position = match &destination.remaining {
            Some(remaining) => FrontierPosition::StatementEntry {
                remaining: remaining.clone(),
            },
            None => FrontierPosition::RegionBoundary,
        };
        self.frontier.next_statement_index = destination.statement_index;
        let source = destination.evidence_source.clone();
        if continue_statement && control.continue_keeps_loop {
            self.frontier.continuations.push(continuation);
        }
        Ok(source)
    }

    /// Forks the single open trace into one trace per outcome theorem, each
    /// recording its theorem and the shared context they were proved under,
    /// once every theorem is checked to advance this frontier.
    #[cfg(test)]
    pub(crate) fn record_statement_outcomes(
        &mut self,
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        outcomes: &[(
            Theorem,
            &(impl ExecutionFactSource + ?Sized),
            &[crate::kernel::ProofObligation],
        )],
        context: PureFactContext,
    ) -> Result<(), EvidenceRefusal> {
        if let Some(opened) = &self.descent {
            opened.accept(None).map_err(EvidenceRefusal::from)?;
        }
        self.record_statement_outcomes_native(function, arguments, outcomes, context)
    }

    pub(crate) fn record_statement_outcomes_with_descent(
        &mut self,
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        outcomes: &[(&crate::kernel::SymbolicExecutionPath, &ExecutionFacts)],
        context: PureFactContext,
    ) -> Result<(), EvidenceRefusal> {
        if let Some(opened) = &self.descent {
            for (step, _) in outcomes {
                opened
                    .accept_at_state(step.descent_step.as_ref(), self.reached_state())
                    .map_err(EvidenceRefusal::from)?;
            }
        }
        let native = outcomes
            .iter()
            .map(|(step, facts)| (step.theorem.clone(), *facts, step.obligations.as_slice()))
            .collect::<Vec<_>>();
        self.record_statement_outcomes_native(function, arguments, &native, context)
    }

    fn record_statement_outcomes_native(
        &mut self,
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        outcomes: &[(
            Theorem,
            &(impl ExecutionFactSource + ?Sized),
            &[crate::kernel::ProofObligation],
        )],
        context: PureFactContext,
    ) -> Result<(), EvidenceRefusal> {
        debug_assert_eq!(self.execution_evidence.len(), 1);
        for (theorem, _, _) in outcomes {
            let (outcome, _) =
                self.check_statement_evidence(function, arguments, theorem, &context)?;
            if matches!(outcome, StatementOutcome::Normal(_)) {
                return Err("an outcome fork records only completing outcomes".into());
            }
        }
        let prefix = self.execution_evidence.first().cloned().unwrap_or_default();
        let mut traces = Vec::with_capacity(outcomes.len());
        for (theorem, _, _) in outcomes {
            let mut trace = prefix.clone();
            trace.push(CheckedExecutionEvent::Statement(theorem.clone()));
            trace.push(CheckedExecutionEvent::Context(Box::new(context.clone())));
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
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        native_step: &crate::kernel::SymbolicExecutionPath,
        context: &PureFactContext,
        _execution_facts: &(impl ExecutionFactSource + ?Sized),
        _obligations: &[crate::kernel::ProofObligation],
        outcome: FunctionOutcome,
        completed_execution_facts: ExecutionFacts,
        completed_obligations: Vec<crate::kernel::ProofObligation>,
        pure_facts: PureFactStore,
        borrow_evidence: crate::kernel::borrows::CheckedBorrowCallEvidenceSequence,
        loop_index: Option<usize>,
        return_index: usize,
    ) -> Result<(), EvidenceRefusal> {
        if let Some(opened) = &parent.descent {
            opened
                .accept_at_state(native_step.descent_step.as_ref(), parent.reached_state())
                .map_err(EvidenceRefusal::from)?;
        }
        let theorem = &native_step.theorem;
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
        let (statement_outcome, _) =
            probe.check_statement_evidence(function, arguments, theorem, context)?;
        if !matches!(statement_outcome, StatementOutcome::Return { .. }) {
            return Err("a loop's retained terminal path does not return".into());
        }
        if !matches!(
            outcome,
            FunctionOutcome::Return { .. }
                | FunctionOutcome::RuntimeError(_)
                | FunctionOutcome::UndefinedBehavior(_)
        ) {
            return Err("a loop's returned path was published with a non-returning outcome".into());
        }
        let mut trace = parent.execution_evidence[0].clone();
        trace.push(CheckedExecutionEvent::Statement(theorem.clone()));
        trace.push(CheckedExecutionEvent::Context(Box::new(context.clone())));
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
            borrow_evidence,
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
    pub(crate) fn pending_loop_return_pure_facts(
        &self,
        path_index: usize,
    ) -> Option<&PureFactStore> {
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
    pub(crate) fn completed_return_outcome(
        &self,
    ) -> Option<(StoredExecutionValue, ExecutionState)> {
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
            Proposition::ProgramStatementVerifies {
                outcome: StatementOutcome::Return { value, .. },
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
    fn current_source<'a>(&'a self, function: &'a ProgramFunction) -> Option<&'a ProgramStatement> {
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
    fn current_source_shared(&self, function: &ProgramFunction) -> Option<Arc<ProgramStatement>> {
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
        function: &'a ProgramFunction,
    ) -> Option<(
        std::borrow::Cow<'a, ProgramStatement>,
        Option<Arc<ProgramStatement>>,
    )> {
        use std::borrow::Cow;
        let source = self.current_source(function)?;
        let (mut head, mut tail) = split_shared_source(source);
        while matches!(*head, ProgramStatement::Skip) {
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
        function: &ProgramFunction,
        branch: &CheckedExecutionBranch,
    ) -> Result<Option<Arc<ProgramStatement>>, &'static str> {
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
        self.cases_hold_memory_effects |= is_memory_effect(&fact);
        self.publication_case_facts.ensure_indexed();
        self.publication_case_facts
            .push(ExecutionPureFact::new(fact));
    }

    pub(crate) fn publication_case_prefix(&self) -> ExecutionFacts {
        self.publication_case_facts.clone()
    }

    /// Keep the completing statement's explicit delta beside its full
    /// publication. Completion already has the trace's cases and effects.
    pub(crate) fn completed_execution_facts(
        &self,
        delta: &ExecutionFacts,
    ) -> CompletedExecutionFacts {
        let facts = self
            .completed_path_facts_with_effects(delta)
            .unwrap_or_else(|| {
                // Preserve the existing overlap route's publication order.
                let mut facts = self.completed_path_facts(delta);
                let mut seen = std::collections::BTreeSet::new();
                let accepted = self
                    .effect_facts
                    .iter()
                    .enumerate()
                    .filter_map(|(index, fact)| {
                        ((is_memory_effect(fact.proposition()) || fact.is_certified())
                            && !facts.contains(fact)
                            && seen.insert(fact))
                        .then_some(index)
                    })
                    .collect::<Vec<_>>();
                facts.extend_shared(&self.effect_facts.selected(&accepted));
                facts
            });
        CompletedExecutionFacts {
            facts,
            additional: Some(delta.clone()),
        }
    }

    /// Candidate publication retains the admitted case prefix and appends
    /// only this statement's own evidence. This carries no theorem authority.
    pub(crate) fn completed_path_facts(&self, delta: &ExecutionFacts) -> ExecutionFacts {
        let mut facts = self.publication_case_facts.clone();
        let delta = delta.filtered(|fact| !facts.contains(fact));
        facts.extend_shared(&delta);
        facts
    }

    /// [`Self::completed_path_facts`] followed by every effect of the trace,
    /// or `None` when one may repeat a completed fact. The effects are
    /// distinct, and each is certified or a memory effect while case facts
    /// are neither, so only the statement's own facts can repeat one; when
    /// none does, the effects are appended whole instead of each being looked
    /// up in the path's facts.
    pub(crate) fn completed_path_facts_with_effects(
        &self,
        delta: &ExecutionFacts,
    ) -> Option<ExecutionFacts> {
        if self.cases_hold_memory_effects {
            return None;
        }
        let mut facts = self.completed_path_facts(delta);
        if facts
            .facts_from(self.publication_case_facts.len())
            .into_iter()
            .any(|fact| self.effect_facts.contains(fact))
        {
            return None;
        }
        facts.forget_indexes();
        facts.extend_shared(&self.effect_facts);
        Some(facts)
    }

    /// The state the retained evidence has reached, or the core's state
    /// before any evidence is recorded.
    pub(crate) fn reached_state(&self) -> &ExecutionState {
        self.evidence_state.as_ref().unwrap_or(&self.state)
    }

    pub(crate) fn borrow_evidence(
        &self,
    ) -> &crate::kernel::borrows::CheckedBorrowCallEvidenceSequence {
        &self.borrow_evidence
    }

    /// The state the frontier's next theorem must start from: the state the
    /// evidence has reached. Before any evidence, at function entry, the
    /// core holds the caller-side state (resource observations and
    /// rewrites recorded there keep that form, and the trace holds their
    /// entry-bound states); the theorem starts from binding the arguments
    /// in it, as the recorded observations were bound.
    fn running_state(
        &self,
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
    ) -> Result<std::borrow::Cow<'_, ExecutionState>, EvidenceRefusal> {
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
        crate::kernel::program_function_entry_state(&self.state, function, arguments)
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
        let bound = crate::kernel::program_function_entry_state(
            &self.state,
            &entry.function,
            &entry.arguments,
        )
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

    /// A proof at its original checked entry already owns the argument-bound
    /// state. Begin the retained trace there before checking an observation.
    pub(crate) fn materialize_observation_entry(&mut self) {
        if !self.frontier.is_at_function_entry()
            || self.frontier.entry_member_prefix
            || self.evidence_state.is_some()
            || self.execution_evidence.len() != 1
            || !self.execution_evidence[0].is_empty()
            || !self.state.shares_storage_with(&self.initial_match_scope)
        {
            return;
        }
        let Some(entry) = &self.function_entry else {
            return;
        };
        self.state = entry.entry_state.clone().into();
        self.evidence_state = Some(entry.entry_state.clone());
        self.frontier.execution_start_state = Some(entry.caller_state.clone());
        self.frontier.entry_member_prefix = true;
        self.evidence_source = Some(Arc::new(entry.function.body().clone()));
    }

    /// Enter the same test/body/update pass for every structured loop.
    /// The retained loop node keeps its original phase placement at backedges.
    pub(crate) fn enter_loop_phases(
        &mut self,
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
    ) -> Result<LoopControlSources, EvidenceRefusal> {
        let state = self.running_state(function, arguments)?.into_owned();
        let Some((next, tail)) = self.next_source_statement_and_tail(function) else {
            return Err("loop entry has no source loop".into());
        };
        let ProgramStatement::Loop {
            test,
            update,
            body,
            backedge_target: None,
            natural_exit_target: None,
            ..
        } = next.as_ref()
        else {
            return Err("loop entry does not name a structured source loop".into());
        };
        let repeat = prepend_shared_source(Arc::new(next.clone().into_owned()), tail.clone());
        let (pass, continuation) =
            crate::kernel::program_loop_pass_and_continuation(body, update.as_deref(), Some(test));
        let entered = prepend_shared_source(Arc::new(pass), Some(repeat.clone()));
        let sources = LoopControlSources {
            repeat,
            exit: tail,
            continuation,
            test_position: test.position,
            try_depth: self.evidence_try_stack.len(),
        };
        for trace in self.execution_evidence.iter_mut() {
            trace.push(CheckedExecutionEvent::LoopEntry {
                source_after: entered.clone(),
            });
        }
        self.evidence_state = Some(state);
        self.evidence_source = Some(entered);
        Ok(sources)
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
        function: &ProgramFunction,
        proved_statement: &ProgramStatement,
    ) -> Option<Option<Arc<ProgramStatement>>> {
        let next_tail = self.next_source_statement_and_tail(function);
        // Binding micro-steps and handler heads are meaningful only while
        // a `try` frame is open; without one there is nothing to route to.
        let frame_binding_matches =
            |frame: &EvidenceTryFrame| match (frame.entry.binding(), proved_statement) {
                (Some(binding), ProgramStatement::Declare { name, .. }) => {
                    name.binding() == binding
                }
                (Some(binding), ProgramStatement::Assign { name, .. }) => name == binding,
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
                frame.entry.is_unwind()
                    && matches!(
                        split_shared_source(&frame.handler).0.as_ref(),
                        ProgramStatement::Throw(_)
                    )
                    && !matches!(proved_statement, ProgramStatement::Throw(_))
            }) {
                self.evidence_try_stack.pop();
                return self.try_evidence_source_after(function, proved_statement);
            }
            let mut handler_source = self.evidence_try_stack.last()?.handler.clone();
            loop {
                let (head, tail) = split_shared_source(&handler_source);
                if matches!(head.as_ref(), ProgramStatement::Skip) {
                    let Some(next) = tail else { break };
                    handler_source = next;
                    continue;
                }
                if statements_have_same_source(&head, proved_statement) {
                    if let Some(frame) = self.evidence_try_stack.last_mut() {
                        if let Some(tail) = tail {
                            frame.handler = tail;
                        } else {
                            let completed = self
                                .evidence_try_stack
                                .pop()
                                .expect("handler frame just matched");
                            return Some(completed.tail_after_try);
                        }
                    }
                    return Some(self.evidence_source.clone());
                }
                break;
            }
        }
        if let Some((next, tail)) = &next_tail {
            let next: &ProgramStatement = next;
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
            if let Some((try_body, entry, handler)) = exceptional_region(next) {
                let (body_head, body_tail) = split_shared_source(try_body);
                if statements_have_same_source(&body_head, proved_statement) {
                    self.evidence_try_stack.push(EvidenceTryFrame {
                        entry,
                        handler,
                        tail_after_try: tail.clone(),
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
                    let cleanup_rethrows = frame.entry.is_unwind()
                        && handler_tail.as_ref().is_some_and(|tail| {
                            let (tail_head, tail_tail) = split_shared_source(tail);
                            matches!(tail_head.as_ref(), ProgramStatement::Throw(_))
                                && tail_tail.is_none()
                        });
                    let completed = self
                        .evidence_try_stack
                        .pop()
                        .expect("handler frame just matched");
                    if cleanup_rethrows {
                        return Some(self.evidence_source.clone());
                    }
                    return Some(match (handler_tail, completed.tail_after_try) {
                        (Some(handler), Some(tail)) => {
                            Some(Arc::new(ProgramStatement::seq(handler, tail)))
                        }
                        (Some(handler), None) => Some(handler),
                        (None, tail) => tail,
                    });
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
            // The statement after this `try` is another `try` whose body
            // begins with the theorem, as two calls are while a destructible
            // local's unwind cleanup wraps each: leave this `try` normally
            // and enter that one, as the linear rule above enters a `try`.
            if let Some((try_body, entry, handler)) = exceptional_region(tail_head.as_ref()) {
                let (body_head, body_tail) = split_shared_source(try_body);
                if statements_have_same_source(&body_head, proved_statement) {
                    let entered = EvidenceTryFrame {
                        entry,
                        handler,
                        tail_after_try: tail_tail,
                    };
                    self.evidence_try_stack.pop();
                    self.evidence_try_stack.push(entered);
                    return Some(body_tail);
                }
            }
        }
        None
    }

    /// Checks that a statement theorem advances this frontier: it proves
    /// the frontier's next source statement (a `Skip` theorem consumes
    /// nothing) from the running state, modulo definitionally equal
    /// resource representation (and, before the first C operation of a
    /// checked entry, the representation-only change resource scopes
    /// make). Definitional comparisons run under the context the theorem
    /// executed under. Its premises are not looked up again: they are that
    /// context and the facts of its own path.
    fn check_statement_evidence(
        &mut self,
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        theorem: &Theorem,
        context: &PureFactContext,
    ) -> Result<(StatementOutcome, Option<Arc<ProgramStatement>>), EvidenceRefusal> {
        // Owned (not borrowed) so try-evidence advancement below can take
        // `&mut self`; `ExecutionState` clones are persistent-structure shares.
        let running_state = self.running_state(function, arguments)?.into_owned();
        let (proved_state, proved_statement, outcome) =
            match crate::kernel::api::proof_evidence_conclusion(theorem) {
                Proposition::ProgramStatementVerifies {
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
                ProgramStatement::Goto {
                    target: expected, ..
                },
                StatementOutcome::Jump { target: actual, .. },
            ) if expected == actual && function.control_target(*actual).is_some() => {}
            (ProgramStatement::Goto { .. }, _) => {
                return Err("goto evidence does not carry its checked function target".into());
            }
            (
                ProgramStatement::Loop {
                    backedge_target: Some(_),
                    natural_exit_target: Some(expected),
                    ..
                },
                StatementOutcome::Jump { target: actual, .. },
            ) if expected == actual && function.control_target(*actual).is_some() => {}
            (
                ProgramStatement::Loop {
                    backedge_target: None,
                    ..
                }
                | ProgramStatement::Switch { .. },
                StatementOutcome::Jump { target, .. },
            ) if function.control_target(*target).is_some() => {}
            (_, StatementOutcome::Jump { .. }) => {
                return Err("statement evidence carries an invalid control-flow jump".into());
            }
            _ => {}
        }
        // The source left after the theorem: a `Skip` theorem consumes a
        // `Skip` at the head of the source when there is one and otherwise
        // nothing; another theorem consumes its statement after the
        // `Skip`s before it.
        let source_after = if matches!(&**proved_statement, ProgramStatement::Skip) {
            match self.current_source(function) {
                Some(source) => {
                    let (head, tail) = split_shared_source(source);
                    if matches!(*head, ProgramStatement::Skip) {
                        tail
                    } else {
                        self.current_source_shared(function)
                    }
                }
                None => None,
            }
        } else if matches!(&**proved_statement, ProgramStatement::Seq(..))
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
                if !statements_have_same_source(&next, proved_statement) {
                    return Err(EvidenceRefusal {
                        reason: "statement evidence does not prove the frontier's next source statement",
                        expected: Some(next.into_owned()),
                        proved: Some(*proved_statement.clone()),
                        premise: None,
                    });
                }
                tail
            }
        };
        self.check_evidence_state(function, &running_state, context, proved_state)?;
        Ok((outcome.clone(), source_after))
    }

    /// Checks that a condition theorem decides the frontier's next `if` or
    /// `while` (a loop head re-entered from its body is the frontier's next
    /// statement again) from the running state, under retained premises:
    /// the statement judgment for the theorem that selects an arm or a
    /// loop iteration.
    fn check_condition_evidence(
        &self,
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        theorem: &Theorem,
        context: &PureFactContext,
        path_facts: &[Proposition],
        obligations: &[crate::kernel::ProofObligation],
    ) -> Result<(ExecutionState, Option<Arc<ProgramStatement>>), EvidenceRefusal> {
        let running_state = self.running_state(function, arguments)?;
        let (proved_state, proved_condition, value) =
            match crate::kernel::api::proof_evidence_conclusion(theorem) {
                Proposition::ProgramConditionEvaluates {
                    state,
                    condition,
                    outcome: ConditionOutcome::Value(value),
                } => (state, condition, *value),
                _ => return Err("retained condition evidence has a non-value conclusion".into()),
            };
        let Some((next, tail)) = self.next_source_statement_and_tail(function) else {
            return Err(
                "condition evidence was recorded with no source statement remaining".into(),
            );
        };
        let decided = match &*next {
            ProgramStatement::If { condition, .. } => condition,
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
            ProgramStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                let selected: &ProgramStatement = if value { then_branch } else { else_branch };
                if matches!(selected, ProgramStatement::Skip) {
                    tail
                } else {
                    Some(prepend_shared_source(Arc::new(selected.clone()), tail))
                }
            }
            _ => tail,
        };
        let path_facts = path_facts
            .iter()
            .cloned()
            .map(ExecutionPureFact::new)
            .collect::<Vec<_>>();
        self.check_evidence_state(function, &running_state, context, proved_state)?;
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
            *reached = crate::kernel::resolve_pending_heap_allocations_with(
                &reached,
                &theorem_assumptions,
                |obligation| {
                    // The condition theorem decides the outcome. Retirement
                    // evidence is a separate premise in the checked context.
                    let premise = obligation.proposition();
                    if context.states_required_goal(premise) {
                        return Ok(());
                    }
                    Err(EvidenceRefusal {
                        reason: "successful realloc requires separation from its call-entry borrows",
                        expected: None,
                        proved: None,
                        premise: Some(premise.clone()),
                    })
                },
            )?;
            reached.complete_staged_memory();
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
        // The condition's call results end with it.
        let reached = crate::kernel::eval::without_read_step_results(*reached, decided);
        Ok((reached, source_after))
    }

    /// The part of the evidence judgment shared by statement and condition
    /// theorems: the theorem starts from the running state. Its premises are
    /// not walked: they are the context it executed under, which is recorded
    /// beside it, and the facts of its own path, both produced by this
    /// session (`AGENTS.md`, construct valid proofs).
    fn check_evidence_state(
        &self,
        function: &ProgramFunction,
        running_state: &ExecutionState,
        context: &PureFactContext,
        proved_state: &ExecutionState,
    ) -> Result<(), EvidenceRefusal> {
        let at_checked_entry = matches!(self.frontier.position, FrontierPosition::FunctionEntry)
            && self.function_entry.is_some()
            && self.execution_evidence.iter().all(|trace| trace.is_empty());
        // The representation-only change before the first operation is
        // allowed against the checked entry state itself: once the trace
        // holds an observation or rewrite, the theorem follows its state.
        let states_match = *running_state == *proved_state
            || if at_checked_entry {
                let no_assumptions = PureFactContext::new();
                let entry_assumptions = self
                    .function_entry
                    .as_ref()
                    .map_or(&no_assumptions, |entry| entry.assumptions());
                crate::kernel::api::function_entry_representation_states_match(
                    function,
                    running_state,
                    proved_state,
                    entry_assumptions,
                )
            } else {
                crate::kernel::api::execution_evidence_states_match(
                    function,
                    running_state,
                    proved_state,
                    context,
                )
            };
        let states_match = states_match
            || proved_state
                .pending_thread_create
                .as_ref()
                .is_some_and(|pending| {
                    pending
                        .resolve(proved_state, context)
                        .is_some_and(|resolved| resolved == *running_state)
                });
        if !states_match {
            return Err("evidence does not start from the running state".into());
        }
        if running_state.memory() != proved_state.memory() {
            register_recomputed_call_views(
                &self.checked_call_events,
                running_state.memory(),
                proved_state.memory(),
                context,
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
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
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
            trace.push(CheckedExecutionEvent::Context(Box::new(context.clone())));
        }
        for fact in path_facts {
            let fact = ExecutionPureFact::new(fact.clone());
            if !self.publication_case_facts.contains(&fact) {
                self.cases_hold_memory_effects |= is_memory_effect(fact.proposition());
                self.publication_case_facts.push(fact);
            }
        }
        self.advance_path_context(&context);
        self.evidence_state = Some(reached);
        self.evidence_source = source_after;
        Ok(())
    }

    pub(crate) fn record_proof_case_arm(
        &mut self,
        partition: Arc<CheckedProofCasePartition>,
        arm_index: usize,
        facts: PureFactStore,
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
            trace.push(CheckedExecutionEvent::ProofCase(Box::new(arm.clone())));
        }
        true
    }

    /// Retains the sole surviving case of a logical split. The sibling's
    /// checked facts must refute the exact case it entered, and the live
    /// trace must still be at its case entry.
    pub(crate) fn exclude_refuted_case_sibling(
        &mut self,
        parent: &Self,
        refuted: &Self,
        refuted_facts: &PureFactStore,
    ) -> Result<(), &'static str> {
        let ([parent_trace], [live_trace], [refuted_trace]) = (
            parent.execution_evidence.as_slice(),
            self.execution_evidence.as_slice(),
            refuted.execution_evidence.as_slice(),
        ) else {
            return Err("logical refutation requires one trace per case");
        };
        let live_events = live_trace
            .suffix_since(parent_trace)
            .ok_or("the live case did not start from this split")?;
        let [CheckedExecutionEvent::ProofCase(live)] = live_events.as_slice() else {
            return Err("the live case already advanced from its entry");
        };
        let refuted_events = refuted_trace
            .suffix_since(parent_trace)
            .ok_or("the refuted case did not start from this split")?;
        let Some(CheckedExecutionEvent::ProofCase(dead)) = refuted_events.first() else {
            return Err("the refutation did not enter a logical case");
        };
        if refuted.evidence_completed
            || !refuted.frontier.at_same_program_point(&parent.frontier)
            || !refuted_events[1..].iter().all(|event| {
                matches!(
                    event,
                    CheckedExecutionEvent::ResourceObservation(_)
                        | CheckedExecutionEvent::ResourceRewrite(_)
                        | CheckedExecutionEvent::PopulationAuthorityRewrite(_)
                        | CheckedExecutionEvent::PopulationMemberRewrite(_)
                        | CheckedExecutionEvent::TacticApplication(_)
                )
            })
        {
            return Err("a case refutation must leave the C frontier unchanged");
        }
        if !Arc::ptr_eq(&live.partition, &dead.partition)
            || live.width() != 2
            || live.arm_index == dead.arm_index
            || live.partition.witness_scope.is_some()
            || refuted_facts.introduced_since(&dead.facts).is_none()
            || !refuted_facts.holds_false()
        {
            return Err("the sibling's own facts do not refute its case");
        }
        let mut partition = (*live.partition).clone();
        partition.identity = Arc::new(());
        partition.excluded[dead.arm_index] = Some(Proposition::condition_is(
            OldConditionTerm::Constant(false),
            true,
        ));
        let mut trace = parent_trace.clone();
        trace.push(CheckedExecutionEvent::ProofCase(Box::new(
            CheckedProofCaseArm {
                partition: Arc::new(partition),
                arm_index: live.arm_index,
                facts: live.facts.clone(),
            },
        )));
        self.execution_evidence = vec![trace].into();
        Ok(())
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
        arms: &[(&ExecutionProofCore, &PureFactStore)],
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        successor_facts: &PureFactStore,
    ) -> Result<bool, &'static str> {
        let join = CheckedProofCaseJoin::check(parent, arms, function, arguments, successor_facts)?;
        let changed_execution = join.arms_changed_execution();
        let first = arms[0].0;
        let mut trace = parent.execution_evidence[0].clone();
        let joined_state = join.joined_state().clone();
        trace.push(CheckedExecutionEvent::ProofCaseJoin(Box::new(join)));
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
        root_facts: &PureFactStore,
        arms: [(&ExecutionProofCore, &PureFactStore); 2],
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        interface_specs: &[SpecProposition],
        interface_resource_specs: &[ResourceSpec],
        arm_effect_facts: [&(impl ExecutionFactSource + ?Sized); 2],
        joined_state: &ExecutionState,
        successor_facts: &PureFactStore,
        old_reference: Option<&ExecutionState>,
    ) -> Result<crate::kernel::ExecutionFacts, &'static str> {
        let join = CheckedProofCaseJoin::construct_interface(
            parent,
            root_facts,
            arms,
            function,
            arguments,
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
        if !join
            .joined_state
            .has_interface_join_point(arms.map(|(arm, _)| arm.reached_state()), &join.start_state)
        {
            return Err("the interface point does not join the checked cases");
        }
        let effect_facts = interface.effect_facts.clone();
        let joined_state = join.joined_state.clone();
        self.advance_kernel_variable_mark(interface.next_kernel_variable)?;
        let mut trace = parent.execution_evidence[0].clone();
        trace.push(CheckedExecutionEvent::ProofCaseJoin(Box::new(join)));
        self.execution_evidence = vec![trace].into();
        self.checked_call_events = parent.checked_call_events.clone();
        self.state = joined_state.clone().into();
        self.evidence_state = Some(joined_state);
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
    #[cfg(test)]
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
            use crate::kernel::FunctionOutcome;
            #[cfg(test)]
            MATCH_SCOPE_INDEX_BUILDS.with(|count| count.set(count.get() + 1));
            let mut reserved = std::collections::BTreeSet::new();
            crate::kernel::reasoning::collect_execution_state_bitvector_variables(
                &self.initial_match_scope,
                &mut reserved,
            );
            crate::kernel::reasoning::collect_execution_state_bound_variables(
                &self.initial_match_scope,
                &mut reserved,
            );
            if let Some(entry) = self.function_entry.as_ref() {
                reserved.extend(crate::kernel::proposition_variables(
                    &Proposition::ProgramFunctionVerifies {
                        state: Box::new(entry.caller_state.clone()),
                        function: Box::new(entry.function.as_ref().clone()),
                        arguments: entry.arguments.clone(),
                        outcome: FunctionOutcome::Return {
                            value: ProgramValue::Void.into(),
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
    /// The witnesses are algebraic binders, numbered from `first_binder`,
    /// and fresh against everything the region can name. Its entry state
    /// (and, at a function entry, the entry theorem) is reserved once by
    /// [`Self::initial_match_reserved_variables`]; the kernel never issues an
    /// algebraic binder, so nothing issued since needs a probe. The
    /// environment, the scrutinee, and the persistent fact index are queried
    /// per candidate.
    pub(crate) fn algebraic_case_partition(
        &self,
        facts: &PureFactStore,
        value: &crate::kernel::AlgebraicTerm,
        environment: &crate::kernel::ExecutionEnvironment,
        definitions: &[crate::kernel::CompositeResourceDefinition],
        matched_resource_field: Option<&crate::kernel::ResourceFieldProjection>,
        first_binder: u64,
    ) -> Option<(
        Arc<CheckedProofCasePartition>,
        Vec<Vec<(Variable, crate::kernel::Sort)>>,
        u64,
    )> {
        use crate::kernel::Term;
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
        let environment_variables =
            crate::kernel::reasoning::execution_environment_variable_index(environment);
        let value_variables = crate::kernel::proposition_variables(&Proposition::Equal(
            Term::Algebraic(value.clone().into()),
            Term::Algebraic(value.clone().into()),
        ));
        let mut next = first_binder;
        let mut overflow = false;
        let equations =
            crate::kernel::api::algebraic_constructor_case_equations(value, &mut || {
                loop {
                    // Case binders are algebraic binders, an origin no
                    // execution issues, so only binders the region already
                    // names can collide.
                    let candidate =
                        Variable::produced(crate::kernel::Producer::AlgebraicBinder, next);
                    #[cfg(test)]
                    MATCH_FRESHNESS_PROBES.with(|count| count.set(count.get() + 1));
                    if let Some(successor) = next.checked_add(1) {
                        next = successor;
                    } else {
                        overflow = true;
                        return candidate;
                    }
                    if !reserved.contains(&candidate)
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
        let (arm_contexts, arm_body_clauses): (Vec<_>, Vec<_>) = case_facts
            .iter()
            .map(|case| {
                let mut arm_facts = facts.with_fact(case.clone());
                if super::facts::is_constructor_clash(case) {
                    arm_facts = arm_facts.with_fact(Proposition::condition_is(
                        OldConditionTerm::Constant(false),
                        true,
                    ));
                }
                // A term an exact premise equates with the scrutinee is the
                // same constructor in this arm: a local holding a call's
                // result `c = a` matched at `c == None` gives `a == None`.
                // Only the scrutinee's own index bucket is read.
                if let Proposition::Equal(_, constructor) = case {
                    let scrutinee = Term::Algebraic(value.clone().into());
                    for equality in
                        facts.algebraic_equalities_mentioning(&Proposition::Equal(
                            scrutinee.clone(),
                            scrutinee.clone(),
                        ))
                    {
                        let Proposition::Equal(left, right) = &equality else {
                            continue;
                        };
                        let other = if *left == scrutinee {
                            right
                        } else if *right == scrutinee {
                            left
                        } else {
                            continue;
                        };
                        if *other != scrutinee
                            && !matches!(other, Term::Algebraic(term)
                                if matches!(term.old_form().node, crate::kernel::AlgebraicTermNode::Constructor { .. }))
                        {
                            arm_facts = arm_facts
                                .with_fact(Proposition::Equal(other.clone(), constructor.clone()));
                        }
                    }
                }
                // A concrete scrutinee already names its payload. Relate each
                // fresh pattern binding to that payload by checked constructor
                // injectivity, so resource unfolds and the written arm refer
                // to the same pointers and models.
                if let Some(fields) =
                    crate::kernel::assumptions::algebraic_constructor_field_equalities(case)
                {
                    for field in fields {
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
                        model.old_form(),
                        constructor.old_form(),
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
                        &constructor.old_form().node
                {
                    let spelled_fields = fields
                        .iter()
                        .enumerate()
                        .map(|(index, field)| match field {
                            crate::kernel::AlgebraicValue::Program(value) => {
                                crate::kernel::AlgebraicValue::Program(value.clone())
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
                            algebraic_type: constructor.old_form().algebraic_type.clone(),
                            node: crate::kernel::AlgebraicTermNode::Constructor {
                                variant: variant.clone(),
                                fields: spelled_fields,
                            },
                        };
                        arm_facts = arm_facts
                            .with_fact(Proposition::Equal(left.clone(), Term::Algebraic(spelled.into())));
                    }
                }
                // A premise that reads the matched value holds of this arm's
                // constructor: its instance, with each match on the value
                // reduced, `r <= 100` from `match s { Circle(r) => r, .. } <= 100`.
                if let crate::kernel::AlgebraicTermNode::Variable(variable) = value.node
                    && let Proposition::Equal(_, Term::Algebraic(constructor)) = case
                {
                    for instance in matched_value_premise_instances(facts, variable, constructor.old_form()) {
                        arm_facts = arm_facts.with_fact(instance);
                    }
                }
                (arm_facts, body_clauses)
            })
            .unzip();
        let arm_additions = arm_contexts
            .iter()
            .map(|arm| arm.introduced_since(facts).unwrap_or_default())
            .collect();
        Some((
            Arc::new(CheckedProofCasePartition {
                identity: Arc::new(()),
                root_facts: facts.clone(),
                excluded: vec![None; case_facts.len()],
                case_facts,
                arm_additions,
                arm_contexts,
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
        facts: &PureFactStore,
        value: &crate::kernel::AlgebraicTerm,
        definitions: &[crate::kernel::CompositeResourceDefinition],
        matched_resource_field: Option<&crate::kernel::ResourceFieldProjection>,
    ) -> PureFactStore {
        let crate::kernel::AlgebraicTermNode::Variable(variable) = value.node else {
            return facts.clone();
        };
        if definitions.is_empty() {
            return facts.clone();
        }
        let state: &crate::kernel::ExecutionState = &self.state;
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
                        crate::kernel::ResourceFieldValue::Algebraic(model) if model == value
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
            let crate::kernel::Resource::Instance(instance) = fact.resource() else {
                continue;
            };
            if !instance.fields().iter().any(|field| {
                matches!(
                    field,
                    crate::kernel::ResourceFieldValue::Algebraic(model)
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
            trace: &ExecutionEvidence,
            fork: &OutcomeEvidenceFork,
            traces: &mut Vec<ExecutionEvidence>,
        ) -> Result<(), &'static str> {
            match fork {
                OutcomeEvidenceFork::Keep => traces.push(trace.clone()),
                OutcomeEvidenceFork::Split { partition, arms } => {
                    // A split path takes every case the partition leaves
                    // live, each once and in order: coverage is pooled per
                    // partition, so a missing arm would drop a case.
                    if !arms.iter().map(|arm| arm.case).eq(partition.live_cases()) {
                        return Err(
                            "outcome evidence fork does not take each live case of its partition once, in order",
                        );
                    }
                    for fork_arm in arms {
                        let arm = CheckedProofCaseArm {
                            partition: partition.clone(),
                            arm_index: fork_arm.case,
                            facts: fork_arm.facts.clone(),
                        };
                        if !arm.is_valid() {
                            return Err(
                                "outcome evidence fork arm does not extend the partition root by its case fact",
                            );
                        }
                        let mut forked = trace.clone();
                        forked.push(CheckedExecutionEvent::ProofCase(Box::new(arm)));
                        append(&forked, &fork_arm.then, traces)?;
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

    pub(crate) fn record_view_release(
        &mut self,
        segment: &crate::kernel::MemorySegment,
        assumptions: &PureFactContext,
    ) -> Result<ExecutionState, String> {
        if self.evidence_completed || self.frontier.is_at_function_entry() {
            return Err("release_view requires an active function body".into());
        }
        let before_state = self.reached_state().clone();
        let segment = crate::kernel::loops::evaluate_loop_effect_segment(
            &before_state,
            segment,
            assumptions,
            &mut ExecutionBudget::beside_live_state(),
        )
        .map_err(|error| {
            format!(
                "release_view could not evaluate its operand: {}",
                error.describe()
            )
        })?
        .map_err(|error| format!("release_view could not evaluate its operand: {error}"))?;
        let view = ResourceFact::view_memory(segment.into_range());
        let after_state = before_state.release_produced_view(&view, assumptions)?;
        let release = CheckedViewRelease {
            before_state,
            after_state: after_state.clone(),
        };
        self.evidence_state = Some(after_state.clone());
        for trace in self.execution_evidence.iter_mut() {
            trace.push(CheckedExecutionEvent::ViewRelease(Box::new(
                release.clone(),
            )));
        }
        Ok(after_state)
    }

    pub(crate) fn record_automatic_lifetime_end(
        &mut self,
        state: &ExecutionState,
        names: &[BindingName],
    ) -> Result<ExecutionState, RuntimeError> {
        self.last_footprint = None;
        if names.is_empty() {
            return Ok(state.clone());
        }
        let after_state = crate::kernel::eval::end_scope_automatic_lifetimes(state, names)?;
        if after_state == *state {
            return Ok(after_state);
        }
        if self.reached_state() != state {
            return Err(RuntimeError::FunctionContract(
                "automatic lifetime end does not start from the running state".into(),
            ));
        }
        self.last_footprint = Some(crate::kernel::RegionFootprint::transition(
            format!("region({}).footprint", self.frontier.next_statement_index),
            state,
            &after_state,
            &ExecutionFacts::new(),
        ));
        let end = CheckedAutomaticLifetimeEnd {
            before_state: state.clone(),
            after_state: after_state.clone(),
            names: names.to_vec(),
        };
        self.evidence_state = Some(after_state.clone());
        for trace in self.execution_evidence.iter_mut() {
            trace.push(CheckedExecutionEvent::AutomaticLifetimeEnd(Box::new(
                end.clone(),
            )));
        }
        Ok(after_state)
    }

    /// Applies one iterated guarded-ownership step to the running state and
    /// records it. The kernel performs the step; the caller supplies only the
    /// step's operands.
    pub(crate) fn record_iterated_step(
        &mut self,
        before_facts: &PureFactStore,
        step: crate::kernel::IteratedStep,
    ) -> Result<ExecutionState, String> {
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

    pub(crate) fn record_named_resource_observation(
        &mut self,
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        facts: &PureFactStore,
        instance: &crate::kernel::ResourceInstance,
    ) -> Result<crate::kernel::functions::ResourceInstanceRewriteResult, String> {
        if self.evidence_completed {
            return Err("a resource observation was recorded after the trace completed".into());
        }
        let definition = function
            .proof_composite_resource_definition(instance.name())
            .ok_or("resource instance has no visible body")?;
        let before = self.reached_state();
        let result = crate::kernel::functions::observe_resource_instance(
            before,
            instance,
            definition,
            function.composite_resource_definitions(),
            facts.assumptions(),
        )
        .map_err(|refusal| refusal.describe())?;
        let observation = CheckedResourceObservation {
            before_state: before.clone(),
            after_state: result.state.clone(),
            definition: Some(definition.clone()),
        };
        self.record_checked_resource_observation(function, arguments, observation)?;
        Ok(result)
    }

    pub(crate) fn record_resource_observation(
        &mut self,
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        before_facts: &PureFactStore,
        observed: &ResourceFact,
        input: ResourceObservationInput<'_>,
        after_facts: &PureFactStore,
    ) -> Result<ExecutionState, &'static str> {
        if self.evidence_completed {
            return Err("a resource observation was recorded after the trace completed");
        }
        let observation = CheckedResourceObservation::certify(
            function,
            self.reached_state(),
            before_facts,
            observed,
            input,
            after_facts,
            &self.function_entry_derivations,
            &self.checked_call_events,
        )?;
        self.record_checked_resource_observation(function, arguments, observation)
    }

    fn record_checked_resource_observation(
        &mut self,
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        mut observation: CheckedResourceObservation,
    ) -> Result<ExecutionState, &'static str> {
        let successor = observation.after_state.clone();
        if self.frontier.is_at_function_entry() && !self.frontier.entry_member_prefix {
            observation.before_state = crate::kernel::program_function_entry_state(
                &observation.before_state,
                function,
                arguments,
            )
            .ok_or("resource observation could not bind the function entry state")?;
            observation.after_state = crate::kernel::program_function_entry_state(
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
            trace.push(CheckedExecutionEvent::ResourceObservation(Box::new(
                observation.clone(),
            )));
        }
        Ok(successor)
    }

    /// Prepare a statement-free call, withhold its trace event, and return
    /// the obligations its transition depends on.
    pub(crate) fn prepare_tactic_application(
        &mut self,
        function: &ProgramFunction,
        function_arguments: &[ProgramExpression],
        before_facts: &PureFactStore,
        name: &str,
        arguments: &[crate::kernel::ProgramValue],
        environment: &crate::kernel::ExecutionEnvironment,
        outcome: Option<(usize, &super::OutcomeProofCore)>,
    ) -> Result<(ExecutionState, PureFactStore, Vec<ProofObligation>), String> {
        if let Some(opened) = &self.descent {
            opened.accept_environment(environment)?;
        }
        if let Some((path, outcome)) = outcome {
            if !self.evidence_completed
                || outcome.is_exceptional
                || !self.has_return_producer(path, &outcome.identity)
            {
                return Err("a tactic application requires the selected checked return".into());
            }
        } else if self.evidence_completed {
            return Err(
                "a frontier tactic must be applied before execution reaches function exit".into(),
            );
        }
        let before_state = outcome.map_or_else(
            || self.reached_state().clone(),
            |(_, outcome)| (*outcome.state).clone(),
        );
        let transition = crate::kernel::functions::prepare_verified_tactic_rule(
            &before_state,
            name,
            arguments,
            before_facts.assumptions(),
            environment,
            self.kernel_variable_mark(),
        )?;
        self.advance_kernel_variable_mark(transition.next_kernel_variable)?;
        let mut prepared = PreparedTacticApplication {
            name: name.to_string(),
            before_state,
            after_state: transition.state.clone(),
            return_path: outcome.map(|(path, _)| {
                (
                    path,
                    transition
                        .facts
                        .iter()
                        .map(|fact| fact.proposition().clone())
                        .collect(),
                )
            }),
        };
        // Before any evidence, the core holds the caller-side state and the
        // trace holds entry-bound states, as for a resource rewrite here.
        if self.frontier.is_at_function_entry() && !self.frontier.entry_member_prefix {
            prepared.before_state = crate::kernel::program_function_entry_state(
                &prepared.before_state,
                function,
                function_arguments,
            )
            .ok_or("a tactic application could not bind the function entry state")?;
            prepared.after_state = crate::kernel::program_function_entry_state(
                &prepared.after_state,
                function,
                function_arguments,
            )
            .ok_or("a tactic application could not bind its successor entry state")?;
        }
        self.prepared_tactic_application = Some(Arc::new(prepared));
        let facts = transition
            .facts
            .iter()
            .fold(before_facts.clone(), |facts, fact| {
                facts.with_kernel_checked_fact(fact.proposition().clone())
            });
        Ok((transition.state, facts, transition.obligations))
    }

    pub(crate) fn has_prepared_tactic_application(&self) -> bool {
        self.prepared_tactic_application.is_some()
    }

    pub(crate) fn has_prepared_return_tactic_application(&self) -> bool {
        self.prepared_tactic_application
            .as_ref()
            .is_some_and(|application| application.return_path.is_some())
    }

    /// Publish the retained transition once the driver has proved its
    /// obligations against the unchanged pre-state.
    pub(crate) fn finish_prepared_tactic_application(&mut self) {
        let PreparedTacticApplication {
            name,
            before_state,
            after_state,
            return_path,
        } = Arc::unwrap_or_clone(
            self.prepared_tactic_application
                .take()
                .expect("completion consumes a prepared tactic application"),
        );
        assert!(return_path.is_none());
        let application = CheckedTacticApplication {
            name,
            before_state,
            after_state,
            return_effect: None,
        };
        if self.evidence_state.is_some() {
            self.evidence_state = Some(application.after_state.clone());
        }
        for trace in self.execution_evidence.iter_mut() {
            trace.push(CheckedExecutionEvent::TacticApplication(Box::new(
                application.clone(),
            )));
        }
    }

    pub(crate) fn record_resource_rewrite(
        &mut self,
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        before_facts: &PureFactStore,
        selected: &ResourceFact,
        after_state: &ExecutionState,
        after_facts: &PureFactStore,
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
        .map_err(|error| error.message)
    }

    /// Construct and publish one authority transition at the reached body.
    pub(crate) fn record_population_authority_rewrite(
        &mut self,
        before_facts: &PureFactStore,
        selected: &ResourceFact,
        establish: bool,
    ) -> Result<ExecutionState, String> {
        let rewrite = CheckedPopulationAuthorityRewrite::construct(
            self.reached_state(),
            selected,
            establish,
            before_facts.assumptions(),
        )?;
        // Preserve the exchange's storage and custody refusals at entry,
        // before testing whether its successor can be recorded in the body.
        if self.evidence_completed
            || (self.frontier.is_at_function_entry() && !self.frontier.entry_member_prefix)
        {
            return Err("population authority rewrite requires an active function body".into());
        }
        let successor = rewrite.after_state.clone();
        if self.evidence_state.is_some() {
            self.evidence_state = Some(successor.clone());
        }
        for trace in self.execution_evidence.iter_mut() {
            trace.push(CheckedExecutionEvent::PopulationAuthorityRewrite(Box::new(
                rewrite.clone(),
            )));
        }
        Ok(successor)
    }

    pub(crate) fn record_population_member_rewrite(
        &mut self,
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        before_facts: &PureFactStore,
        selected: &ResourceFact,
        produce: bool,
        witness: &CheckedPopulationMemberExchange,
        after_state: &ExecutionState,
        after_facts: &PureFactStore,
    ) -> Result<Option<ExecutionState>, String> {
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
            let bound_before = crate::kernel::program_function_entry_state(
                self.reached_state(),
                function,
                arguments,
            )
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
            trace.push(CheckedExecutionEvent::PopulationMemberRewrite(Box::new(
                rewrite.clone(),
            )));
        }
        Ok(entry_successor)
    }

    /// Derive a named instance fold and retain its checked event together.
    /// The caller supplies the instance and child choices, never a proposed
    /// successor or fact delta that would require recomputing the fold.
    #[cfg(test)]
    pub(crate) fn fold_resource_instance_with_children(
        &mut self,
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        before_facts: &PureFactStore,
        instance: &crate::kernel::ResourceInstance,
        selected_children: Option<Arc<[(String, InstanceId)]>>,
    ) -> Result<
        (
            crate::kernel::functions::ResourceInstanceRewriteResult,
            PureFactStore,
        ),
        crate::kernel::ResourceRewriteRefusal,
    > {
        self.fold_resource_instance_with_children_under(
            function,
            arguments,
            before_facts,
            instance,
            selected_children,
            before_facts.assumptions(),
        )
    }

    /// Prepare under the caller's evaluation policy while preserving the
    /// original fact context in the execution record. With retained obligations,
    /// the caller must keep this successor private until its body facts are proved.
    pub(crate) fn fold_resource_instance_with_children_under(
        &mut self,
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        before_facts: &PureFactStore,
        instance: &crate::kernel::ResourceInstance,
        selected_children: Option<Arc<[(String, InstanceId)]>>,
        assumptions: &PureFactContext,
    ) -> Result<
        (
            crate::kernel::functions::ResourceInstanceRewriteResult,
            PureFactStore,
        ),
        crate::kernel::ResourceRewriteRefusal,
    > {
        let _timing = crate::instrumentation::OperationTiming::new(
            instance.name(),
            "resource fold",
            "resource fold: construct selected instance",
        );
        if self.evidence_completed {
            return Err("a resource rewrite was recorded after the trace completed".into());
        }
        let definition = function
            .proof_composite_resource_definition(instance.name())
            .ok_or("instance definition is not registered on the function")?;
        CheckedResourceRewrite::check_instance_definition(function, definition)
            .map_err(crate::kernel::ResourceRewriteRefusal::OwnedMessage)?;
        let _load_capture = crate::kernel::CheckedLoadEqualityCapture::start_with_call_events(
            &self.checked_call_events,
        );
        let result = crate::kernel::rewrite_resource_instance_selecting_children(
            &self.state,
            instance,
            definition,
            function.composite_resource_definitions(),
            assumptions,
            false,
            selected_children.as_deref(),
        )?;
        let after_facts = result
            .semantic_facts
            .iter()
            .fold(before_facts.clone(), |facts, fact| {
                facts.with_kernel_checked_fact(fact.clone())
            });
        let mut rewrite = CheckedResourceRewrite {
            before_state: (*self.state).clone(),
            after_state: result.state.clone(),
            before_facts: before_facts.clone(),
            after_facts: after_facts.clone(),
            definition: definition.clone(),
            consumption_contract: None,
            return_context: None,
            instance: Some(instance.clone()),
            selected_children,
            return_presentation: None,
            return_observation: None,
        };
        if self.frontier.is_at_function_entry() && !self.frontier.entry_member_prefix {
            rewrite.before_state = crate::kernel::program_function_entry_state(
                &rewrite.before_state,
                function,
                arguments,
            )
            .ok_or("resource rewrite could not bind the function entry state")?;
            rewrite.after_state = crate::kernel::program_function_entry_state(
                &rewrite.after_state,
                function,
                arguments,
            )
            .ok_or("resource rewrite could not bind its successor entry state")?;
        }
        if self.evidence_state.is_some() {
            self.evidence_state = Some(rewrite.after_state.clone());
        }
        if assumptions.retains_required_obligations() {
            self.prepared_instance_fold = Some(Arc::new(PreparedResourceFold {
                rewrite,
                semantic_facts: result.semantic_facts.clone(),
            }));
        } else {
            for trace in self.execution_evidence.iter_mut() {
                trace.push(CheckedExecutionEvent::ResourceRewrite(Box::new(
                    rewrite.clone(),
                )));
            }
        }
        self.state = result.state.clone().into();
        Ok((result, after_facts))
    }

    pub(crate) fn has_prepared_fold(&self) -> bool {
        self.prepared_instance_fold.is_some() || self.prepared_return_fold.is_some()
    }

    pub(crate) fn has_prepared_return_fold(&self) -> bool {
        self.prepared_return_fold.is_some()
    }

    /// A definition-law fold changes the selected outcome presentation without
    /// an operational C-state exchange. Its premises are still proved at the
    /// original outcome; completing it retains those proofs on that path.
    pub(crate) fn prepare_return_definition_fold(
        &mut self,
        path_index: usize,
        before: &PureFactStore,
        after: &PureFactStore,
    ) {
        if self.prepared_return_fold.is_none() {
            self.prepared_return_fold = Some(Arc::new(PreparedReturnFold {
                path_index,
                rewrite: None,
                semantic_facts: after
                    .introduced_since(before)
                    .expect("a definition fold extends its input facts"),
            }));
        }
    }

    pub(crate) fn finish_prepared_return_fold(
        &mut self,
        proved: &Self,
        proved_facts: &PureFactStore,
    ) -> Result<PureFactStore, String> {
        let _timing = crate::instrumentation::OperationTiming::new(
            "fold",
            "resource fold",
            "return fold: finish prepared instance",
        );
        let prepared = Arc::unwrap_or_clone(
            self.prepared_return_fold
                .take()
                .expect("completion consumes the selected prepared return fold"),
        );
        let path = prepared.path_index;
        if let Some(producer) = proved.return_producers.get(&path) {
            self.return_producers.insert(path, producer.clone());
        }
        // Only the selected outcome's new proof evidence is transferred.
        if let Some(trace) = proved.return_resource_rewrites.get(&path) {
            self.return_resource_rewrites = self
                .return_resource_rewrites
                .with_inserted(path, trace.clone());
        }
        if let Some(pending) = proved.return_pending_propositions.get(&path) {
            self.return_pending_propositions = self
                .return_pending_propositions
                .with_inserted(path, pending.clone());
        }
        let facts = prepared
            .semantic_facts
            .into_iter()
            .fold(proved_facts.clone(), |facts, fact| {
                facts.with_kernel_checked_fact(fact)
            });
        let Some(mut rewrite) = prepared.rewrite else {
            return Ok(facts);
        };
        self.flush_return_propositions(path)?;
        rewrite.before_facts = proved_facts.clone();
        rewrite.after_facts = facts.clone();
        if let Some(presentation) = &mut rewrite.return_presentation {
            let presentation = Arc::make_mut(presentation);
            presentation.rewrite.before_facts = proved_facts.clone();
            presentation.rewrite.after_facts = rewrite.after_facts.clone();
        }
        self.push_return_rewrite(path, rewrite)?;
        Ok(facts)
    }

    /// The driver has discharged the body obligations at the original
    /// frontier. Attach that context and append only the retained exchange.
    pub(crate) fn finish_prepared_instance_fold(
        &mut self,
        proved: &PureFactStore,
    ) -> PureFactStore {
        let _timing = crate::instrumentation::OperationTiming::new(
            "fold",
            "resource fold",
            "resource fold: finish prepared instance",
        );
        let prepared = Arc::unwrap_or_clone(
            self.prepared_instance_fold
                .take()
                .expect("completion consumes a prepared instance fold"),
        );
        let mut rewrite = prepared.rewrite;
        crate::instrumentation::record_deterministic_work(prepared.semantic_facts.len());
        rewrite.before_facts = proved.clone();
        rewrite.after_facts = prepared
            .semantic_facts
            .into_iter()
            .fold(proved.clone(), |facts, fact| {
                facts.with_kernel_checked_fact(fact)
            });
        let facts = rewrite.after_facts.clone();
        for trace in self.execution_evidence.iter_mut() {
            crate::instrumentation::record_deterministic_work(1);
            trace.push(CheckedExecutionEvent::ResourceRewrite(Box::new(
                rewrite.clone(),
            )));
        }
        facts
    }

    pub(crate) fn record_resource_rewrite_with_children(
        &mut self,
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        before_facts: &PureFactStore,
        selected: &ResourceFact,
        after_state: &ExecutionState,
        after_facts: &PureFactStore,
        selected_children: Option<Arc<[(String, InstanceId)]>>,
    ) -> Result<(), ResourceRewriteCheckError> {
        self.record_resource_rewrite_with_borrow_holds(
            function,
            arguments,
            before_facts,
            selected,
            after_state,
            after_facts,
            selected_children,
            &[],
            false,
        )
    }

    /// Construct the selected unfold once. During execution the retained
    /// exchange also checks the surface presentation against the trace state.
    /// A refuting exit-match arm uses the kernel-produced delta directly.
    /// It needs neither names for later C reads nor an execution event.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn unfold_resource_instance_with_children(
        &mut self,
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        before_facts: &PureFactStore,
        instance: &crate::kernel::ResourceInstance,
        selected_children: Option<Arc<[(String, InstanceId)]>>,
        refuting_exit_match_arm: bool,
        materialize: impl FnOnce(
            &crate::kernel::functions::ResourceInstanceRewriteResult,
            &PureFactStore,
        ) -> ExecutionState,
    ) -> Result<
        (
            crate::kernel::functions::ResourceInstanceRewriteResult,
            PureFactStore,
        ),
        InstanceUnfoldError,
    > {
        if self.evidence_completed && !refuting_exit_match_arm {
            return Err(InstanceUnfoldError::Recording(
                "a resource rewrite was recorded after the trace completed".into(),
            ));
        }
        let definition = function
            .proof_composite_resource_definition(instance.name())
            .ok_or_else(|| {
                InstanceUnfoldError::Construction(
                    "instance definition is not registered on the function".into(),
                )
            })?;
        let mut result = crate::kernel::rewrite_resource_instance_selecting_children(
            &self.state,
            instance,
            definition,
            function.composite_resource_definitions(),
            before_facts.assumptions(),
            true,
            selected_children.as_deref(),
        )
        .map_err(InstanceUnfoldError::Construction)?;
        let after_facts = result
            .semantic_facts
            .iter()
            .fold(before_facts.clone(), |facts, fact| {
                facts.with_kernel_checked_fact(fact.clone())
            });
        if self.evidence_completed {
            CheckedResourceRewrite::check_instance_definition(function, definition)
                .map_err(|message| InstanceUnfoldError::Recording(message.into()))?;
            return Ok((result, after_facts));
        }
        let after_state = materialize(&result, &after_facts);
        // A proof view can differ from the state reached by the trace. The
        // retained exchange is reusable only at its exact input.
        let before_state = self.reached_state();
        let state = &*self.state;
        let same_pending_steps = match (
            &before_state.memory.pending_steps,
            &state.memory.pending_steps,
        ) {
            (None, None) => true,
            (Some(left), Some(right)) => Arc::ptr_eq(left, right),
            _ => false,
        };
        let prepared = (same_pending_steps
            && before_state
                .path_link()
                .shares_point_and_view(state.path_link())
            && before_state
                .resources()
                .shares_projection_inputs_with(state.resources())
            && before_state == state)
            .then_some(&result);
        let selected = ResourceFact::own(Resource::Instance(instance.clone()));
        let checked = CheckedResourceRewrite::check_with_return_observation(
            function,
            before_state,
            before_facts,
            &selected,
            &after_state,
            &after_facts,
            &self.checked_call_events,
            selected_children,
            None,
            &[],
            prepared,
        )
        .map_err(InstanceUnfoldError::Recording)?;
        self.retain_resource_rewrite(
            function,
            arguments,
            before_facts,
            &after_facts,
            checked,
            false,
        )
        .map_err(InstanceUnfoldError::Recording)?;
        result.state = after_state;
        Ok((result, after_facts))
    }

    /// A proof `fold` whose owned head packages a borrow-backed view places one
    /// hold on that borrow's scope. The rewrite check applies that exact hold
    /// transition to the input ledger rather than accepting any ledger change.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_resource_rewrite_with_borrow_holds(
        &mut self,
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        before_facts: &PureFactStore,
        selected: &ResourceFact,
        after_state: &ExecutionState,
        after_facts: &PureFactStore,
        selected_children: Option<Arc<[(String, InstanceId)]>>,
        borrow_holds: &[crate::kernel::CheckedBorrowTransition],
        defer: bool,
    ) -> Result<(), ResourceRewriteCheckError> {
        if self.evidence_completed {
            return Err("a resource rewrite was recorded after the trace completed"
                .to_string()
                .into());
        }
        let rewrite = CheckedResourceRewrite::check_with_children_diagnostic(
            function,
            self.reached_state(),
            before_facts,
            selected,
            after_state,
            after_facts,
            &self.checked_call_events,
            selected_children,
            borrow_holds,
        )?;
        self.retain_resource_rewrite(
            function,
            arguments,
            before_facts,
            after_facts,
            rewrite,
            defer,
        )
    }

    fn retain_resource_rewrite(
        &mut self,
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        before_facts: &PureFactStore,
        after_facts: &PureFactStore,
        mut rewrite: CheckedResourceRewrite,
        defer: bool,
    ) -> Result<(), ResourceRewriteCheckError> {
        if self.frontier.is_at_function_entry() && !self.frontier.entry_member_prefix {
            rewrite.before_state = crate::kernel::program_function_entry_state(
                &rewrite.before_state,
                function,
                arguments,
            )
            .ok_or_else(|| {
                "resource rewrite could not bind the function entry state".to_string()
            })?;
            rewrite.after_state = crate::kernel::program_function_entry_state(
                &rewrite.after_state,
                function,
                arguments,
            )
            .ok_or("resource rewrite could not bind its successor entry state")?;
        }
        if self.evidence_state.is_some() {
            self.evidence_state = Some(rewrite.after_state.clone());
        }
        if defer {
            self.prepared_instance_fold = Some(Arc::new(PreparedResourceFold {
                semantic_facts: after_facts
                    .introduced_since(before_facts)
                    .expect("a checked fold extends its input facts"),
                rewrite,
            }));
            return Ok(());
        }
        for trace in self.execution_evidence.iter_mut() {
            trace.push(CheckedExecutionEvent::ResourceRewrite(Box::new(
                rewrite.clone(),
            )));
        }
        Ok(())
    }

    /// A logical resource exchange after the returning C statement. This
    /// cannot execute C, change the result, or bypass the checked body rule.
    #[cfg(test)]
    pub(crate) fn record_return_resource_rewrite(
        &mut self,
        function: &ProgramFunction,
        path_index: usize,
        before_facts: &PureFactStore,
        selected: &ResourceFact,
        after_facts: &PureFactStore,
    ) -> Result<(), String> {
        self.record_return_resource_rewrite_with_children(
            function,
            path_index,
            before_facts,
            selected,
            after_facts,
            false,
            None,
            None,
            false,
        )
        .map_err(|error| error.message)
    }

    pub(crate) fn record_return_proposition(
        &mut self,
        path_index: usize,
        proof: super::CheckedProposition,
        base: &PureFactStore,
    ) -> Result<(), String> {
        // Contract refinements also use outcome goals, but their proofs are
        // certified by the refinement rule rather than a retained C trace.
        if !self.evidence_completed {
            return Ok(());
        }
        if self.execution_evidence.get(path_index).is_none() {
            return Err("return proof selected an unknown path".into());
        }
        if let Some(producer) = self.return_producers.get(&path_index) {
            let mut next = producer.clone();
            next.accept_proposition(&proof, base)?;
            self.return_producers.insert(path_index, next);
            return Ok(());
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

    fn return_context_for_path(
        &mut self,
        path_index: usize,
    ) -> Result<Arc<CheckedReturnContext>, String> {
        let context = if let Some(context) = self.return_proof_contexts.get(&path_index) {
            context.clone()
        } else {
            if let Some(producer) = self.return_producers.get(&path_index) {
                let context = producer.seed_context();
                self.return_proof_contexts
                    .insert(path_index, context.clone());
                return Ok(context);
            }
            let candidates = self
                .frontier
                .execution()
                .ok_or("return proof has no published execution")?;
            let candidate = candidates
                .paths()
                .get(path_index)
                .ok_or("return proof selected an unknown path")?;
            let origin = self.execution_evidence[path_index]
                .origin
                .as_deref()
                .ok_or("return proof has no completing statement")?
                .clone();
            let context = Arc::new(CheckedReturnContext::from_candidate(origin, candidate));
            self.return_proof_contexts = self
                .return_proof_contexts
                .with_inserted(path_index, context.clone());
            context
        };
        Ok(context)
    }

    fn flush_return_propositions(&mut self, path_index: usize) -> Result<(), String> {
        let Some(pending) = self.return_pending_propositions.get(&path_index).cloned() else {
            return Ok(());
        };
        let context = self.return_context_for_path(path_index)?;
        let mut trace = self
            .return_resource_rewrites
            .get(&path_index)
            .unwrap_or(&self.execution_evidence[path_index])
            .clone();
        for (proof, base) in pending.iter() {
            let retained = if let Some(producer) = self.return_producers.get(&path_index) {
                let mut next = producer.clone();
                next.accept_proposition(proof, base)?;
                self.return_producers.insert(path_index, next);
                CheckedReturnProposition {
                    proof: proof.clone(),
                    base: base.clone(),
                    context: context.clone(),
                }
            } else {
                CheckedReturnProposition::check(proof.clone(), base, context.clone())?
            };
            trace.push(CheckedExecutionEvent::ReturnProposition(Box::new(retained)));
        }
        self.return_resource_rewrites = self
            .return_resource_rewrites
            .with_inserted(path_index, trace);
        self.return_pending_propositions =
            self.return_pending_propositions.without_key(&path_index);
        Ok(())
    }

    /// Construct the published exchange from the selected path's retained
    /// presentation. Callers cannot substitute an unrelated input state.
    #[cfg(test)]
    pub(crate) fn rewrite_return_resource_instance_with_children(
        &mut self,
        function: &ProgramFunction,
        path_index: usize,
        before_facts: &PureFactStore,
        instance: &crate::kernel::ResourceInstance,
        unfold: bool,
        selected_children: Option<Arc<[(String, InstanceId)]>>,
    ) -> Result<
        (
            crate::kernel::functions::ResourceInstanceRewriteResult,
            PureFactStore,
        ),
        crate::kernel::ResourceRewriteRefusal,
    > {
        self.rewrite_return_resource_instance_with_children_under(
            function,
            path_index,
            before_facts,
            instance,
            unfold,
            selected_children,
            before_facts.assumptions(),
        )
    }

    /// Return-outcome counterpart of conditional instance preparation.
    pub(crate) fn rewrite_return_resource_instance_with_children_under(
        &mut self,
        function: &ProgramFunction,
        path_index: usize,
        before_facts: &PureFactStore,
        instance: &crate::kernel::ResourceInstance,
        unfold: bool,
        selected_children: Option<Arc<[(String, InstanceId)]>>,
        assumptions: &PureFactContext,
    ) -> Result<
        (
            crate::kernel::functions::ResourceInstanceRewriteResult,
            PureFactStore,
        ),
        crate::kernel::ResourceRewriteRefusal,
    > {
        let _timing = crate::instrumentation::OperationTiming::new(
            instance.name(),
            "resource fold",
            "return fold: construct selected instance",
        );
        self.flush_return_propositions(path_index)
            .map_err(crate::kernel::ResourceRewriteRefusal::OwnedMessage)?;
        self.retain_return_facts(path_index, before_facts)
            .map_err(crate::kernel::ResourceRewriteRefusal::OwnedMessage)?;
        let definition = function
            .proof_composite_resource_definition(instance.name())
            .ok_or("instance definition is not registered on the function")?;
        let context = self
            .return_context_for_path(path_index)
            .map_err(crate::kernel::ResourceRewriteRefusal::OwnedMessage)?;
        let trace = self
            .return_resource_rewrites
            .get(&path_index)
            .or_else(|| self.execution_evidence.get(path_index))
            .ok_or("return rewrite selected an unknown path")?;
        let before = match trace.presented.as_deref() {
            Some(state) => state.clone(),
            None => match &context.published {
                FunctionOutcome::Return { state, .. } => *state.clone(),
                _ => return Err("return observation requires a returning path".into()),
            },
        };
        let _capture = crate::kernel::CheckedLoadEqualityCapture::start_with_call_events(
            &self.checked_call_events,
        );
        let result = crate::kernel::rewrite_resource_instance_selecting_children(
            &before,
            instance,
            definition,
            function.composite_resource_definitions(),
            assumptions,
            unfold,
            selected_children.as_deref(),
        )?;
        let facts = result
            .semantic_facts
            .iter()
            .fold(before_facts.clone(), |facts, fact| {
                facts.with_kernel_checked_fact(fact.clone())
            });
        self.record_return_resource_rewrite_with_children(
            function,
            path_index,
            before_facts,
            &ResourceFact::own(Resource::Instance(instance.clone())),
            &facts,
            unfold,
            selected_children,
            Some((&before, &result)),
            !unfold && assumptions.retains_required_obligations(),
        )
        .map_err(|error| crate::kernel::ResourceRewriteRefusal::OwnedMessage(error.message))?;
        Ok((result, facts))
    }

    fn record_return_resource_rewrite_with_children(
        &mut self,
        function: &ProgramFunction,
        path_index: usize,
        before_facts: &PureFactStore,
        selected: &ResourceFact,
        after_facts: &PureFactStore,
        unfold: bool,
        selected_children: Option<Arc<[(String, InstanceId)]>>,
        observed: Option<(
            &ExecutionState,
            &crate::kernel::functions::ResourceInstanceRewriteResult,
        )>,
        defer: bool,
    ) -> Result<(), ResourceRewriteCheckError> {
        if !self.evidence_completed {
            return Err("return resource rewrite requires completed execution"
                .to_string()
                .into());
        }
        let Resource::Instance(instance) = selected.resource() else {
            return Err("return rewrite requires a named instance"
                .to_string()
                .into());
        };
        let definition = function
            .proof_composite_resource_definition(instance.name())
            .ok_or_else(|| "instance definition is not registered on the function".to_string())?;
        let trace = self
            .return_resource_rewrites
            .get(&path_index)
            .or_else(|| self.execution_evidence.get(path_index))
            .cloned()
            .ok_or_else(|| "return resource rewrite selected an unknown path".to_string())?;
        let observation = if let Some((_, after)) = observed {
            let context = self.return_context_for_path(path_index)?;
            Some(Arc::new(ReturnResourceObservation {
                context,
                after: after.state.clone(),
                semantic_facts: after.semantic_facts.clone(),
            }))
        } else {
            None
        };
        let before_state = trace.retained_state()?.clone();
        CheckedResourceRewrite::check_instance_definition(function, definition)?;
        let retained_after = if let Some((presented_before, produced)) = observed {
            // The producer already applied the selected body at the logical
            // return state. Transfer its resource delta, not a second fold in
            // a different state with differently named pointer arguments.
            let resources = before_state.resources().clone().with_constructed_exchange(
                presented_before.resources(),
                produced.state.resources(),
            )?;
            let mut retained = produced.state.clone().with_resource_context(resources);
            retained.keep_memory_of(&before_state);
            retained.locals = before_state.locals().clone();
            retained.enclosing_frame_holds_locals = before_state.enclosing_frame_holds_locals;
            Arc::make_mut(&mut retained.population_effects).predicate_count_permissions =
                before_state
                    .population_effects
                    .predicate_count_permissions
                    .clone();
            if produced.state.population_effects.creation
                == presented_before.population_effects.creation
            {
                Arc::make_mut(&mut retained.population_effects).creation =
                    before_state.population_effects.creation.clone();
            } else {
                // A named population fold/unfold constructs a birth/death
                // receipt. Keep that receipt and restore only the retained
                // environment identity, not the old ledger contents.
                retained.restore_population_creation_after_call(
                    before_state.population_effects.creation.as_ref(),
                    produced.state.population_effects.creation.as_ref(),
                );
            }
            retained
        } else {
            crate::kernel::rewrite_resource_instance_selecting_children(
                &before_state,
                instance,
                definition,
                function.composite_resource_definitions(),
                before_facts.assumptions(),
                unfold,
                selected_children.as_deref(),
            )
            .map_err(|refusal| refusal.describe())?
            .state
        };
        let mut rewrite = CheckedResourceRewrite {
            before_state,
            after_state: retained_after,
            before_facts: before_facts.clone(),
            after_facts: after_facts.clone(),
            definition: definition.clone(),
            consumption_contract: None,
            return_context: None,
            instance: Some(instance.clone()),
            selected_children,
            return_observation: observation,
            return_presentation: None,
        };
        if self.frontier.execution().is_some() {
            rewrite.return_context = Some(self.return_context_for_path(path_index)?);
        }
        if defer {
            self.prepared_return_fold = Some(Arc::new(PreparedReturnFold {
                path_index,
                semantic_facts: observed
                    .expect("a prepared fold has a constructed exchange")
                    .1
                    .semantic_facts
                    .clone(),
                rewrite: Some(rewrite),
            }));
            return Ok(());
        }
        self.push_return_rewrite(path_index, rewrite)?;
        Ok(())
    }

    /// Checks and retains an ordinary wrapper exchange on a completed path.
    pub(crate) fn record_return_composite_resource_rewrite(
        &mut self,
        function: &ProgramFunction,
        path_index: usize,
        before_facts: &PureFactStore,
        selected: &ResourceFact,
        outcome: &super::OutcomeProofCore,
        after_state: &ExecutionState,
        after_facts: &PureFactStore,
        published_facts: &[Proposition],
        defer: bool,
    ) -> Result<(), String> {
        // The checked outcome operation owns this goal's current logical
        // presentation, including expansions cached since the C return.
        // Retain it directly rather than reconstructing it from C history.
        self.flush_return_propositions(path_index)?;
        self.retain_return_facts(path_index, before_facts)?;
        let presented_before_state = &*outcome.state;
        if !self.evidence_completed {
            return Err("return resource rewrite requires completed execution".into());
        }
        let trace = self
            .return_resource_rewrites
            .get(&path_index)
            .or_else(|| self.execution_evidence.get(path_index))
            .cloned()
            .ok_or_else(|| "return resource rewrite selected an unknown path".to_string())?;
        let before_state = trace.retained_state()?.clone();
        // An ordinary macro refold may exist only in the visible outcome;
        // unfolding it again does not change the retained C path's body.
        if matches!(selected.resource(), Resource::Composite { name, .. }
            if function.proof_composite_resource_definition(name)
                .is_some_and(|definition| !definition.reaches_population()))
            && presented_before_state
                .resources()
                .directly_supporting_fact(selected, before_facts.assumptions())
                .is_some()
            && before_state
                .resources()
                .directly_supporting_fact(selected, before_facts.assumptions())
                .is_none()
        {
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
            return Ok(());
        }
        let context = self.return_context_for_path(path_index)?;
        if !matches!(&context.published, FunctionOutcome::Return { .. }) {
            return Err("return composite exchange requires a returning path".into());
        }
        let presented = CheckedResourceRewrite::check_with_children(
            function,
            presented_before_state,
            before_facts,
            selected,
            after_state,
            after_facts,
            &self.checked_call_events,
            None,
        )?;
        // Publication ends automatic local lifetimes. Apply only this
        // logical resource exchange on the C-body state, retaining the local
        // cells that publication removed from its expression-facing outcome.
        let frame = before_state
            .resources()
            .changed_memory_inputs_from(presented_before_state.resources())
            .ok_or("return resource exchange has no shared resource frontier")?
            .into_iter()
            .filter(|fact| {
                !presented_before_state
                    .resources()
                    .contains_exact_representation(fact)
            });
        let resources = after_state
            .resources()
            .clone()
            .install_established_partition(frame, before_facts.assumptions())
            .map(|(context, _)| context)
            .map_err(|error| {
                format!("return resource exchange changed its retained frame: {error}")
            })?;
        let mut retained_after_state = after_state.clone().with_resource_context(resources);
        retained_after_state.keep_memory_of(&before_state);
        retained_after_state.locals = before_state.locals().clone();
        retained_after_state.enclosing_frame_holds_locals =
            before_state.enclosing_frame_holds_locals;
        Arc::make_mut(&mut retained_after_state.population_effects).predicate_count_permissions =
            before_state
                .population_effects
                .predicate_count_permissions
                .clone();
        Arc::make_mut(&mut retained_after_state.population_effects).creation =
            before_state.population_effects.creation.clone();
        if let Resource::Composite { name, .. } = selected.resource()
            && let Some(definition) = function.proof_composite_resource_definition(name)
            && definition.contains().iter().any(|spec| {
                matches!(
                    spec.term(),
                    crate::kernel::ResourceTerm::PopulationAuthority { .. }
                )
            })
        {
            retained_after_state = retained_after_state.with_checked_current_control_wrapper(
                selected,
                definition,
                before_facts.assumptions(),
            )?;
        }
        let mut rewrite = CheckedResourceRewrite::check_with_children(
            function,
            &before_state,
            before_facts,
            selected,
            &retained_after_state,
            before_facts,
            &self.checked_call_events,
            None,
        )?;
        if self.frontier.execution().is_some() {
            rewrite.return_context = Some(self.return_context_for_path(path_index)?);
        }
        rewrite.after_facts = after_facts.clone();
        rewrite.return_presentation = Some(Arc::new(CheckedReturnPresentation {
            published_facts: published_facts.to_vec(),
            context,
            selected: selected.clone(),
            rewrite: presented,
        }));
        if defer {
            self.prepared_return_fold = Some(Arc::new(PreparedReturnFold {
                path_index,
                semantic_facts: after_facts
                    .introduced_since(before_facts)
                    .expect("a checked return fold extends its input facts"),
                rewrite: Some(rewrite),
            }));
            return Ok(());
        }
        self.push_return_rewrite(path_index, rewrite)?;
        Ok(())
    }

    /// Records a branch node only after [`CheckedExecutionBranch::check`]
    /// has validated exact source coverage, both persistent arm suffixes,
    /// the common continuation, and the joined state.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn record_exhaustive_branch_join(
        &mut self,
        split: CheckedBranchSplit,
        root_facts: &PureFactStore,
        arm_theorems: [&Theorem; 2],
        arm_facts: [&PureFactStore; 2],
        parent: &ExecutionProofCore,
        arms: [&ExecutionProofCore; 2],
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
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
        trace.push(CheckedExecutionEvent::Branch(Box::new(branch)));
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
        root_facts: &PureFactStore,
        arm_theorems: [&Theorem; 2],
        arm_facts: [&PureFactStore; 2],
        parent: &ExecutionProofCore,
        arms: [&ExecutionProofCore; 2],
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
        interface_specs: &[SpecProposition],
        interface_resource_specs: &[ResourceSpec],
        arm_effect_facts: [&(impl ExecutionFactSource + ?Sized); 2],
        joined_state: &ExecutionState,
        successor_facts: &PureFactStore,
        old_reference: Option<&ExecutionState>,
    ) -> Result<crate::kernel::ExecutionFacts, &'static str> {
        let parent_trace = match parent.execution_evidence.as_slice() {
            [trace] => trace,
            _ => return Err("the interface parent does not have one execution trace"),
        };
        if !joined_state
            .has_interface_join_point(arms.map(ExecutionProofCore::reached_state), &split.state)
        {
            return Err("the interface point does not join the checked branch");
        }
        let branch = CheckedExecutionBranch::construct_interface(
            split,
            root_facts,
            arm_theorems,
            arm_facts,
            parent,
            arms,
            function,
            arguments,
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
        self.last_footprint = crate::kernel::RegionFootprint::shared_branch_write(
            format!("region({}).footprint", parent.frontier.next_statement_index),
            parent.reached_state(),
            &joined_state,
            arms.map(|arm| (arm.reached_state(), arm.last_footprint.as_ref())),
        );
        let mut trace = parent_trace.clone();
        trace.push(CheckedExecutionEvent::Branch(Box::new(branch)));
        self.execution_evidence = vec![trace].into();
        self.checked_call_events = parent.checked_call_events.clone();
        self.state = joined_state.clone().into();
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
        candidates: &FunctionExecutionCandidates,
        checked_function: &ProgramFunction,
        assumptions: PureFactContext,
        environment: crate::kernel::ExecutionEnvironment,
        execution_semantics: crate::kernel::ExecutionSemantics,
        mode: crate::kernel::FunctionContractExecutionMode,
    ) -> Result<crate::kernel::CheckedFunctionExecution, &'static str> {
        // A function that declares an expression `decreases` measure owes a
        // descent obligation at each self-call, and the environment's anchor
        // is what makes the call step emit one. The proof stepped under the
        // environment it publishes here, so refusing an environment without
        // the anchor refuses exactly the executions in which those
        // obligations were never raised.
        if self.descent.is_none()
            && checked_function
                .contract_interface()
                .has_call_ranked_recursion()
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
        if self.descent.is_none() && !environment.verified_loop_rules_answer_for_recursion() {
            return Err(
                "a verified loop rule of a function with a `decreases` measure calls that \
                 function but was certified without its recursion anchor",
            );
        }
        // An opened contract owns its premises. Caller-proposed facts cannot
        // strengthen that root judgment; derived and case facts must travel
        // through the checked trace instead.
        let contract_entry = self
            .function_entry
            .as_ref()
            .filter(|entry| entry.cases.is_some());
        let assumptions = contract_entry.map_or(assumptions, |entry| entry.assumptions.clone());
        let (
            paths,
            has_checked_entry,
            deferred_contract_exits,
            deferred_contract_exit_errors,
            published_outcomes,
        ) = self.checked_execution_paths(
            candidates,
            checked_function,
            &assumptions,
            None,
            &mut None,
        )?;
        let path_count = paths.len();
        Ok(crate::kernel::CheckedFunctionExecution {
            retained_descent: self.descent.is_some(),
            published_outcomes: published_outcomes.into(),
            contract_completion: None,
            entry_authority: has_checked_entry
                .then_some(contract_entry)
                .flatten()
                .and_then(|entry| entry.cases.clone())
                .map(|cases| ContractEntryAuthority { cases }),
            closed_exit_obligations: vec![None; path_count],
            proof_candidates: Some(candidates.clone()),
            state: candidates.state().clone(),
            function: checked_function.clone(),
            arguments: candidates.arguments().to_vec(),
            assumptions,
            environment,
            execution_semantics,
            mode,
            execution: crate::kernel::SymbolicExecution { paths, limit: None },
            checked_resource_claims: vec![Vec::new(); path_count],
            checked_resource_transitions: vec![false; path_count],
            deferred_contract_exits,
            deferred_contract_exit_errors,
            // Empty conclusion placeholders; checked resource clauses replace
            // them before any live resource query.
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

    /// Publish the selected producer's current return for ordinary closing.
    /// No C execution evidence is replayed or compared here.
    pub(crate) fn checked_return_path(
        &self,
        path_index: usize,
    ) -> Result<CheckedReturnPath, ReturnPathRefusal> {
        self.return_producers
            .get(&path_index)
            .ok_or(ReturnPathRefusal {
                reason: "return rewrite has no opened checked outcome",
                unjustified_fact: None,
            })?
            .finish()
    }

    /// Whether this path retains a kernel-checked exchange after its C return.
    pub(crate) fn has_checked_return_resource_rewrite(&self, path_index: usize) -> bool {
        self.return_resource_rewrites.get(&path_index).is_some()
    }

    /// Collect a finished outcome's exchange without copying sibling traces.
    #[cfg(test)]
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
        candidates: &FunctionExecutionCandidates,
        checked_function: &ProgramFunction,
        assumptions: &PureFactContext,
        selected: Option<usize>,
        unjustified: &mut Option<Proposition>,
    ) -> Result<
        (
            Vec<crate::kernel::SymbolicExecutionPath>,
            bool,
            Vec<bool>,
            Vec<Option<crate::kernel::RuntimeError>>,
            Vec<Arc<crate::kernel::PublishedFunctionOutcome>>,
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
        if !candidates
            .function()
            .has_same_entry_and_source(checked_function)
        {
            return Err(
                "the checked function does not preserve the published function's entry and source",
            );
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
                        crate::kernel::api::proof_evidence_initial_state(trace.iter())
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
            crate::kernel::program_function_entry_state(
                candidates.state(),
                function,
                candidates.arguments(),
            )
            .ok_or("the published arguments do not bind at entry")?;
        }
        let mut paths = Vec::with_capacity(range.len());
        let mut publications = Vec::with_capacity(range.len());
        let mut deferred_contract_exits = Vec::with_capacity(range.len());
        let mut deferred_contract_exit_errors = Vec::with_capacity(range.len());
        for path_index in range {
            let candidate = &candidates.paths()[path_index];
            let trace = self
                .return_resource_rewrites
                .get(&path_index)
                .unwrap_or(&self.execution_evidence[path_index]);
            let events = trace.iter().collect::<Vec<_>>();
            let (completed, statement_assumptions, interface_execution_facts) =
                trace_completion_from_entry(
                    function,
                    &events,
                    assumptions,
                    function.return_type() == crate::kernel::ProgramType::Void
                        && self.evidence_source.is_none()
                        && self.frontier.region == ExecutionRegionKind::Function,
                    self.entry_facts.as_ref(),
                    unjustified,
                )?;
            // Publication precedes post-return logical folds. Check its
            // original C outcome against the trace before those exchanges;
            // the final exit rule below still checks the folded ownership.
            let publication_end = events
                .iter()
                .rposition(|event| {
                    !matches!(
                        *event,
                        CheckedExecutionEvent::TacticApplication(application) if application.return_effect.is_some()
                    ) && !matches!(
                        *event,
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
                    function.return_type() == crate::kernel::ProgramType::Void
                        && self.evidence_source.is_none()
                        && self.frontier.region == ExecutionRegionKind::Function,
                )?
                .0
            } else {
                completed.clone()
            };
            let (outcome, obligations) =
                crate::kernel::program_function_outcome_from_statement_outcome(
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
            // The kernel built this path's context as the path advanced.
            // It holds the completing statement's context, every case fact
            // and every effect. Import only the completing producer's delta
            // when it retained one. A path with post-return
            // exchanges completes under their facts too, and is rebuilt.
            let path_context = (publication_end == events.len())
                .then(|| {
                    events.iter().rev().find_map(|event| match event {
                        CheckedExecutionEvent::CompletedContext(context) => Some(context),
                        _ => None,
                    })
                })
                .flatten()
                .filter(|context| {
                    context.cases == 0
                        || candidate
                            .facts()
                            .plain_fact_at(context.cases - 1)
                            .zip(context.case_facts.plain_fact_at(context.cases - 1))
                            .is_some_and(|(published, recorded)| Arc::ptr_eq(published, recorded))
                });
            let retain_post_context =
                path_context.is_some() || function.resource_requires().is_empty();
            let mut boundary_assumptions = statement_assumptions.clone();
            if let Some(path_context) = path_context {
                boundary_assumptions = path_context.facts.clone();
                let _publication_delta = crate::instrumentation::OperationTiming::new(
                    function.name(),
                    "proof completion",
                    "completion fact delta",
                );
                let additional = match &candidate.data.completion_delta {
                    Some(delta) => delta.facts_from(0),
                    // Older candidate producers do not yet retain their delta.
                    None => candidate.facts().facts_from(path_context.cases),
                };
                for fact in additional {
                    boundary_assumptions = retain_completed_path_fact(boundary_assumptions, fact);
                }
            } else {
                for fact in candidate
                    .facts()
                    .facts_not_assumed_by(&boundary_assumptions)
                {
                    crate::instrumentation::record_deterministic_work(1);
                    crate::kernel::reasoning::path_facts::count_context_rebuild_entries(1);
                    boundary_assumptions =
                        boundary_assumptions.assume_proposition(fact.proposition().clone());
                }
            }
            let typed_candidate_facts = candidate.facts().producer_facts().filter(|fact| {
                path_context.is_none()
                    && retain_post_context
                    && fact.is_certified()
                    && fact.generated_load_binding().is_some()
            });
            let return_seed = CheckedReturnSeed::new(
                self,
                path_index,
                candidates,
                candidate,
                function,
                completed.clone(),
                has_checked_entry,
            );
            let (
                outcome,
                obligations,
                borrow_evidence,
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
                    crate::kernel::FunctionOutcome::RuntimeError(error),
                    candidate.obligations().to_vec(),
                    None,
                    false,
                    None,
                ),
                Err(_) => return Err("the contract's exit rule hit an execution limit"),
            };
            let borrow_evidence = match borrow_evidence {
                Some(evidence) => crate::kernel::borrows::concat_checked_borrow_evidence(
                    candidate.borrow_evidence(),
                    &crate::kernel::borrows::append_checked_borrow_evidence(
                        &crate::kernel::borrows::empty_checked_borrow_evidence_sequence(),
                        Some(evidence),
                    ),
                ),
                None => candidate.borrow_evidence().clone(),
            };
            let proposition = Proposition::ProgramFunctionVerifies {
                state: Box::new(candidates.state().clone()),
                function: Box::new(function.clone()),
                arguments: candidates.arguments().to_vec(),
                outcome: outcome.clone(),
            };
            let mut post_assumptions = boundary_assumptions;
            // Preserve the typed-load bridges that the former certification
            // import installed, including private memory-effect evidence.
            if retain_post_context && path_context.is_none() {
                for fact in typed_candidate_facts
                    .into_iter()
                    .chain(candidate.effect_facts())
                {
                    post_assumptions = retain_completed_path_fact(post_assumptions, fact);
                }
            }
            // The path states everything the proof established on it: the
            // candidate's execution facts, the interface facts of joined
            // branches, and the facts of the context its final theorem was
            // proved under (a `have` in one arm that both arms share, say).
            // The theorem lists every one of them: path `k` of a run of early
            // returns states its `k` case facts. That listing is the
            // theorem's own output, charged here apart from completion's
            // other work, which reads the path's suffix only.
            let premises = crate::instrumentation::OperationTiming::new(
                function.name(),
                "proof completion",
                "path theorem premises",
            );
            let mut facts = candidate.facts().clone();
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
            let theorem = Theorem::new(crate::kernel::reasoning::wrap_proof_facts(
                proposition,
                assumptions,
                &facts,
                candidate.obligations(),
            ));
            let path = crate::kernel::SymbolicExecutionPath {
                descent_step: None,
                completion_origin: Some(candidate.outcome().clone()),
                call_result: None,
                assumptions: assumptions.clone(),
                post_assumptions: retain_post_context.then_some(post_assumptions),
                facts,
                effect_facts: candidate.effect_facts().clone(),
                obligations,
                theorem,
                borrow_evidence,
            };
            publications.push(crate::kernel::PublishedFunctionOutcome::from_execution(
                candidates.state(),
                function,
                candidates.arguments(),
                assumptions,
                &path.facts,
                candidate.obligations(),
                &outcome,
                candidate,
                &path,
                return_seed,
            ));
            paths.push(path);
            drop(premises);
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
            publications,
        ))
    }

    /// Checks that every retained event carries the kernel judgment its tag
    /// promises. This is intentionally cheaper than executing any C: it only
    /// inspects the conclusions of already-issued theorem objects.
    pub(crate) fn validate_execution_evidence_shapes(&self) -> Result<(), &'static str> {
        // Traces share their prefixes. A shared event was validated with the
        // first trace that reached it; each later trace validates only its own
        // suffix, starting from the call views its validated prefix left open.
        let mut visited = std::collections::HashSet::new();
        for trace in &self.execution_evidence {
            let (suffix, before) = trace.unvisited_suffix(&mut visited);
            validate_checked_event_shapes_after(suffix, pending_call_views_after(before))?;
        }
        Ok(())
    }
}

#[derive(Clone, Default)]
pub(crate) enum FrontierPosition {
    #[default]
    FunctionEntry,
    StatementEntry {
        remaining: Arc<ProgramStatement>,
    },
    FunctionExit {
        execution: FunctionExecutionCandidates,
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

    pub(crate) fn execution(&self) -> Option<&FunctionExecutionCandidates> {
        match &self.position {
            FrontierPosition::FunctionEntry
            | FrontierPosition::StatementEntry { .. }
            | FrontierPosition::RegionBoundary => None,
            FrontierPosition::FunctionExit { execution } => Some(execution),
        }
    }

    pub(crate) fn execution_start_state<'a>(
        &'a self,
        current_state: &'a ExecutionState,
    ) -> &'a ExecutionState {
        self.execution_start_state.as_ref().unwrap_or(current_state)
    }
}

/// Resolves the named function-entry state used by `old(...)`, falling back
/// to the current region's start state when the proof has no entry state.
pub(crate) fn old_reference_state<'a>(
    function_entry_state: Option<&'a ExecutionState>,
    frontier: &'a ExecutionFrontier,
    current_state: &'a ExecutionState,
) -> &'a ExecutionState {
    match function_entry_state {
        Some(entry_state) => entry_state,
        None => frontier.execution_start_state(current_state),
    }
}

#[cfg(test)]
mod tests;

/// Deterministic four-size curves for the borrow machinery an interface join
/// and a loop-head havoc run (R32; docs/internals/stable-views.md). Both axes
/// grow with proof length rather than with the selected contract: the binding
/// count grows by one per exposed child per unfold or observe, and the cell
/// and symbolic-borrow counts grow with the memory a proof has named. Neither
/// is output the checker must produce, so a quadratic curve here is a scaling
/// defect rather than output-sensitive work. Work is counted with the
/// deterministic counter; host time never decides these tests.
#[cfg(test)]
mod borrow_scaling_tests;

#[cfg(test)]
mod automatic_lifetime_tests;

#[cfg(test)]
mod population_authority_rewrite_tests;

#[cfg(test)]
mod authority_transfer_wrapper_scaling_tests;

#[cfg(test)]
mod wide_range_reader_tests;

#[cfg(test)]
mod checked_callee_dependency_tests;

#[cfg(test)]
mod loop_destination_tests;

/// A source `try` or unwind cleanup: its body, how an exception enters its
/// handling statements, and those statements as known before any exception
/// (an unwind cleanup's cleanup, to which the exception's continuation is
/// added when one enters it).
pub(crate) fn exceptional_region(
    statement: &ProgramStatement,
) -> Option<(&ProgramStatement, ExceptionalEntry, Arc<ProgramStatement>)> {
    match statement {
        ProgramStatement::TryCatchInt32 {
            try_body,
            binding,
            handler,
        } => Some((
            try_body,
            ExceptionalEntry::Catch(binding.clone()),
            Arc::new((**handler).clone()),
        )),
        ProgramStatement::UnwindCleanup { body, cleanup } => {
            let cleanup = Arc::new((**cleanup).clone());
            Some((body, ExceptionalEntry::Unwind(cleanup.clone()), cleanup))
        }
        _ => None,
    }
}
