//! Semantic execution-frontier state owned by the checked proof object.
//!
//! A frontier identifies the exact C region and next statement a checked
//! execution proof must advance. It contains no Surface Click syntax,
//! certificate builder, diagnostic cursor, or smart-planning state.

use super::{PersistentOrderedSet, PersistentSequence, ProofFacts, SharedValue, SharedVec};
use crate::kernel::{
    Bitvector32Term, CCompositeResourceDefinition, CConditionOutcome, CExpression, CFunction,
    CFunctionExecutionCandidates, CLoopEffectCheck, CMemoryRange, CResourceFact, CResourceSpec,
    CState, CStatement, CStatementOutcome, CValue, CVerifiedLoopRule, ExecutionBudget,
    ExecutionLimit, ExecutionPureFact, Proposition, PureFactContext, ResourceContext,
    SpecProposition, Theorem,
};
use std::collections::BTreeMap;
use std::ops::{Deref, DerefMut};
use std::sync::Arc;

/// The typed identity of the execution region a frontier executes.
#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub(crate) enum ExecutionRegionKind {
    #[default]
    Function,
    LoopBody,
    /// One arm of a C `if`: exhausting the arm reaches its typed boundary.
    BranchArm,
}

/// One checked loop-effect obligation carried by an execution proof.
#[derive(Clone)]
pub(crate) struct LoopEffectGoal {
    pub(crate) before_state: CState,
    pub(crate) check: CLoopEffectCheck,
    pub(crate) closed: bool,
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
    Condition(Theorem),
    /// The kernel fact context the preceding `Statement` or `Condition`
    /// theorem was proved under. A transition's theorem lists that context
    /// as its premises; retaining the context is what lets sealing check
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

/// Kernel-checked evidence for a fold, unfold, or scoped open/close that
/// changes only the definitional representation of one composite resource.
#[derive(Clone)]
pub(crate) struct CheckedResourceRewrite {
    before_state: CState,
    pub(crate) after_state: CState,
    pub(crate) before_facts: ProofFacts,
    pub(crate) after_facts: ProofFacts,
    definition: CCompositeResourceDefinition,
}

impl CheckedResourceRewrite {
    pub(crate) fn before_state(&self) -> &CState {
        &self.before_state
    }

    fn check(
        function: &CFunction,
        before_state: &CState,
        before_facts: &ProofFacts,
        selected: &CResourceFact,
        after_state: &CState,
        after_facts: &ProofFacts,
    ) -> Result<Self, &'static str> {
        let assumptions = before_facts.assumptions();
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
        concrete_after.memory = before_state.memory.clone();
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
        let relation_authority = CResourceFact::own(selected.resource().clone());
        if let Some(propositions) =
            crate::kernel::functions::evaluate_composite_resource_relation_propositions(
                &relation_authority,
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
        if introduced.iter().any(|fact| {
            !allowed.contains(fact)
                && !resource_composition_is_supported_by(fact, &child_context, assumptions)
                && !allowed_assumptions.proves(fact)
        }) {
            return Err("resource rewrite produced an unchecked pure-fact delta");
        }

        Ok(Self {
            before_state: before_state.clone(),
            after_state: after_state.clone(),
            before_facts: before_facts.clone(),
            after_facts: after_facts.clone(),
            definition,
        })
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

    pub(crate) fn advances_sealed(&self, function: &CFunction, state: &CState) -> bool {
        function
            .composite_resource_definitions()
            .contains(&self.definition)
            && state == &self.before_state
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
    ) -> Result<Self, &'static str> {
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
        concrete_after.memory = before_state.memory.clone();
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
                && !allowed_assumptions.proves(fact)
        }) {
            return Err("resource observation produced an unchecked pure-fact delta");
        }

        Ok(Self {
            before_state: before_state.clone(),
            after_state: after_state.clone(),
            before_facts: before_facts.clone(),
            after_facts: after_facts.clone(),
            definition,
        })
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

    pub(crate) fn advances_sealed(&self, function: &CFunction, state: &CState) -> bool {
        function
            .composite_resource_definitions()
            .contains(&self.definition)
            && state == &self.before_state
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
        let Some((_, propositions)) =
            crate::kernel::functions::expand_all_composite_resource_facts_and_propositions(
                self.entry_state.resources(),
                self.function.composite_resource_definitions(),
                self.entry_state.memory(),
                assumptions,
            )
        else {
            return None;
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
    case_facts: [Proposition; 2],
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
            case_facts: [then_fact, else_fact],
        }))
    }
}

impl CheckedProofCaseArm {
    pub(crate) fn identity(&self) -> usize {
        Arc::as_ptr(&self.partition.identity) as usize
    }

    pub(crate) fn arm_index(&self) -> usize {
        self.arm_index
    }

    pub(crate) fn facts(&self) -> &ProofFacts {
        &self.facts
    }

    pub(crate) fn is_valid(&self) -> bool {
        self.arm_index < 2
            && self
                .facts
                .introduced_since(&self.partition.root_facts)
                .is_some_and(|introduced| {
                    introduced == vec![self.partition.case_facts[self.arm_index].clone()]
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
            let Some(remaining) = arm
                .state
                .resources()
                .clone()
                .without_facts(&arm_interface_resources[index], facts.assumptions())
            else {
                return Err("an interface resource is not owned by one concrete arm");
            };
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
        for spec in interface_specs {
            for (arm, facts) in arms.iter().zip(arm_facts) {
                if !interface_spec_is_established(spec, arm.reached_state(), reference_state, facts)
                {
                    return Err("an interface fact is not established by both concrete arms");
                }
            }
            if !interface_spec_is_established(spec, joined_state, reference_state, successor_facts)
            {
                return Err("an interface fact is not retained at the abstract successor");
            }
        }
        let introduced = successor_facts
            .introduced_since(root_facts)
            .ok_or("the interface successor facts do not descend from the branch root")?;
        for fact in &introduced {
            let common_arm_fact = arm_facts
                .iter()
                .all(|facts| facts.contains(fact) || facts.assumptions().proves(fact));
            let interface_fact = interface_specs
                .iter()
                .any(|spec| interface_spec_lowers_to(spec, joined_state, reference_state, fact));
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

fn checked_interface_effect_facts(
    split_state: &CState,
    joined_state: &CState,
    arms: [&ExecutionProofCore; 2],
    arm_facts: [&ProofFacts; 2],
    arm_effect_facts: [&[ExecutionPureFact]; 2],
) -> Result<Vec<ExecutionPureFact>, &'static str> {
    let mut pointers = Vec::new();
    let mut ranges = Vec::new();
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
                    if !crate::kernel::api::contract_certification::c_memories_definitionally_equal(
                        &memory,
                        before,
                        assumptions,
                    ) {
                        return Err(
                            "an interface arm effect chain does not start at its current memory",
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
                    if !crate::kernel::api::contract_certification::c_memories_definitionally_equal(
                        &memory,
                        before,
                        assumptions,
                    ) {
                        return Err(
                            "an interface arm effect summary does not start at its current memory",
                        );
                    }
                    memory = after.clone();
                    for range in mutable_ranges {
                        if !ranges.contains(range) {
                            ranges.push(range.clone());
                        }
                    }
                }
                Proposition::CHeapAllocationFreed { .. } => {
                    return Err(
                        "an interface join over conditional heap deallocation is not yet supported",
                    );
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
    match crate::kernel::functions::evaluate_function_resource_spec(
        state,
        spec,
        facts.assumptions(),
        &mut ExecutionBudget::new(),
    )
    .ok()?
    {
        Ok(fact) => Some(fact),
        Err(_) => None,
    }
}

fn interface_resource_intrinsic_fact(
    spec: &CResourceSpec,
    resource: &CResourceFact,
    state: &CState,
) -> Option<Proposition> {
    let segment = match spec {
        CResourceSpec::ViewMemory(segment) | CResourceSpec::OwnMemory(segment) => segment,
        CResourceSpec::Quantified { .. }
        | CResourceSpec::Composite { .. }
        | CResourceSpec::Token { .. } => return None,
    };
    let range = resource.memory_range()?;
    let element_width =
        crate::kernel::eval::c_expression_pointer_step_width(state, &segment.base).unwrap_or(4);
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

fn interface_spec_is_established(
    spec: &SpecProposition,
    state: &CState,
    reference_state: &CState,
    facts: &ProofFacts,
) -> bool {
    interface_spec_paths(spec, state, reference_state).is_some_and(|paths| {
        paths.into_iter().any(|path| {
            facts.assumptions().proves(&path.proposition)
                && path
                    .facts
                    .iter()
                    .all(|fact| facts.assumptions().proves(fact.proposition()))
                && path
                    .obligations
                    .iter()
                    .all(|obligation| facts.assumptions().proves(obligation.proposition()))
        })
    })
}

fn interface_spec_lowers_to(
    spec: &SpecProposition,
    state: &CState,
    reference_state: &CState,
    expected: &Proposition,
) -> bool {
    interface_spec_paths(spec, state, reference_state)
        .is_some_and(|paths| paths.iter().any(|path| &path.proposition == expected))
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
                || path
                    .obligations
                    .iter()
                    .any(|obligation| !arm_facts.assumptions().proves(obligation.proposition()))
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
}

#[derive(Clone)]
pub(crate) struct ProofExecutionContinuation {
    pub(crate) remaining: Option<Arc<CStatement>>,
    pub(crate) next_statement_index: usize,
}

/// Surface-independent execution state owned by a checked proof branch.
///
/// Language lowering and certificate capture wrap this value with their own
/// path-local records. The kernel core contains only C state, checked facts
/// and rules, typed frontier state, and semantic freshness/region flags.
#[derive(Clone)]
pub(crate) struct ExecutionProofCore {
    pub(crate) state: SharedValue<CState>,
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
    pub(crate) function_entry: Option<Arc<CheckedFunctionEntry>>,
    pub(crate) frontier_loop_rules: PersistentSequence<CVerifiedLoopRule>,
    pub(crate) execution_abstraction: bool,
    pub(crate) loop_effect_goal: Option<LoopEffectGoal>,
    pub(crate) next_path_choice: usize,
    pub(crate) concrete_loop_execution: bool,
    /// Kernel theorems whose conclusions justify the facts a resource
    /// observation introduces (its count and quantity witnesses).
    pub(crate) function_entry_derivations: PersistentOrderedSet<Theorem>,
    pub(crate) region_invariants_closed: bool,
    pub(crate) next_opaque_call: u64,
    pub(crate) next_kernel_variable: u64,
    pub(crate) has_empty_execution_branch_leaf: bool,
    pub(crate) has_structured_branch_history: bool,
    pub(crate) unfolded_predicates: SharedVec<String>,
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

fn checked_evidence_premises_hold(theorem: &Theorem, facts: &ProofFacts) -> bool {
    let mut proposition = theorem.proposition();
    while let Proposition::Implies(premise, body) = proposition {
        if !facts.assumptions().proves_exact(premise) && !facts.assumptions().proves(premise) {
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
            body,
        } if &condition == proved_condition => {
            if value {
                let loop_head = CStatement::While {
                    condition,
                    invariant,
                    invariant_checks,
                    effect_checks,
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
    mut state: CState,
    mut remaining: Option<CStatement>,
) -> Option<CheckedEvidenceProgress> {
    let mut completed = None;
    let mut current_facts = facts.clone();
    for event in events {
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
                current_facts = observation.advance_checked(&state, &current_facts)?;
                state = observation.after_state.clone();
                continue;
            }
            CheckedExecutionEvent::ResourceRewrite(rewrite) => {
                current_facts = rewrite.advance_checked(&state, &current_facts)?;
                state = rewrite.after_state.clone();
                continue;
            }
            // The retained context of the preceding theorem; the arm check
            // above already holds the arm's own facts.
            CheckedExecutionEvent::Context(_) => continue,
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
                    outcome @ (CStatementOutcome::Return { .. }
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
                    let arm = check_evidence_events(
                        branch.arm_events(arm_index),
                        branch.arm_facts(arm_index),
                        state.clone(),
                        Some(full_source.clone()),
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
    events: &[CheckedExecutionEvent],
    assumptions: &PureFactContext,
) -> Result<(CStatementOutcome, PureFactContext, Vec<ExecutionPureFact>), &'static str> {
    let mut completed: Option<(CStatementOutcome, PureFactContext)> = None;
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
                    CStatementOutcome::Normal(_) => {}
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
            CheckedExecutionEvent::Condition(_)
            | CheckedExecutionEvent::ResourceObservation(_)
            | CheckedExecutionEvent::ResourceRewrite(_) => {
                if completed.is_some() {
                    return Err("a trace continues past its completing theorem");
                }
            }
            // A post-execution case split records its arm after the path's
            // returning statement; it changes only the assumed facts.
            CheckedExecutionEvent::ProofCase(_) | CheckedExecutionEvent::Context(_) => {}
        }
    }
    let Some((outcome, executed_under)) = completed else {
        return Err("a trace does not reach a return");
    };
    Ok((outcome, executed_under, interface_execution_facts))
}

fn validate_checked_event_shapes(events: &[CheckedExecutionEvent]) -> Result<(), &'static str> {
    for event in events {
        let (theorem, statement) = match event {
            CheckedExecutionEvent::Statement(theorem) => (theorem, true),
            CheckedExecutionEvent::Condition(theorem) => (theorem, false),
            CheckedExecutionEvent::Branch(branch) => {
                for arm in &branch.arms {
                    validate_checked_event_shapes(&arm.events)?;
                }
                continue;
            }
            CheckedExecutionEvent::Context(_) => continue,
            CheckedExecutionEvent::ProofCase(arm) => {
                if !arm.is_valid() {
                    return Err("retained proof-case evidence has an invalid checked arm");
                }
                continue;
            }
            CheckedExecutionEvent::ResourceObservation(_)
            | CheckedExecutionEvent::ResourceRewrite(_) => continue,
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
    pub(crate) fn at_entry(state: CState, frontier: ExecutionFrontier) -> Self {
        Self {
            state: state.into(),
            evidence_state: None,
            evidence_completed: false,
            evidence_source: None,
            frontier,
            effect_facts: Default::default(),
            execution_evidence: vec![PersistentSequence::default()].into(),
            function_entry: None,
            frontier_loop_rules: Default::default(),
            execution_abstraction: false,
            loop_effect_goal: None,
            next_path_choice: 0,
            concrete_loop_execution: false,
            function_entry_derivations: Default::default(),
            region_invariants_closed: false,
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
    ) -> Result<(), &'static str> {
        debug_assert_eq!(self.execution_evidence.len(), 1);
        let (outcome, source_after) = self.check_statement_evidence(
            function,
            arguments,
            &theorem,
            &context,
            execution_facts,
            obligations,
        )?;
        for trace in &mut *self.execution_evidence {
            trace.push(CheckedExecutionEvent::Statement(theorem.clone()));
            trace.push(CheckedExecutionEvent::Context(context.clone()));
        }
        self.evidence_source = match &outcome {
            CStatementOutcome::Normal(_) => source_after,
            _ => None,
        };
        match outcome {
            CStatementOutcome::Normal(next_state) => self.evidence_state = Some(next_state),
            CStatementOutcome::Return { state, .. } => {
                self.evidence_state = Some(state);
                self.evidence_completed = true;
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
    ) -> Result<(), &'static str> {
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
                return Err("an outcome fork records only completing outcomes");
            }
        }
        let prefix = self.execution_evidence.first().cloned().unwrap_or_default();
        self.execution_evidence = outcomes
            .iter()
            .map(|(theorem, _, _)| {
                let mut trace = prefix.clone();
                trace.push(CheckedExecutionEvent::Statement(theorem.clone()));
                trace.push(CheckedExecutionEvent::Context(context.clone()));
                trace
            })
            .collect::<Vec<_>>()
            .into();
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
    ) -> Result<std::borrow::Cow<'_, CState>, &'static str> {
        use std::borrow::Cow;
        if self.evidence_completed {
            return Err("evidence was recorded after the trace completed");
        }
        if let Some(state) = &self.evidence_state {
            return Ok(Cow::Borrowed(state));
        }
        if !matches!(self.frontier.position, FrontierPosition::FunctionEntry) {
            return Ok(Cow::Borrowed(&self.state));
        }
        crate::kernel::c_function_entry_state(&self.state, function, arguments)
            .map(Cow::Owned)
            .ok_or("the function's arguments do not bind at entry")
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
    ) -> Result<(CStatementOutcome, Option<Arc<CStatement>>), &'static str> {
        let running_state = self.running_state(function, arguments)?;
        let (proved_state, proved_statement, outcome) =
            match crate::kernel::api::proof_evidence_conclusion(theorem) {
                Proposition::CStatementVerifies {
                    state,
                    statement,
                    outcome,
                } => (state, statement, outcome),
                _ => return Err("retained statement evidence has a non-statement conclusion"),
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
        } else {
            let Some((next, tail)) = self.next_source_statement_and_tail(function) else {
                return Err("statement evidence was recorded with no source statement remaining");
            };
            if !statements_have_same_source(&next, proved_statement) {
                return Err(
                    "statement evidence does not prove the frontier's next source statement",
                );
            }
            tail
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
    ) -> Result<(CState, Option<Arc<CStatement>>), &'static str> {
        let running_state = self.running_state(function, arguments)?;
        let (proved_state, proved_condition, value) =
            match crate::kernel::api::proof_evidence_conclusion(theorem) {
                Proposition::CConditionEvaluates {
                    state,
                    condition,
                    outcome: CConditionOutcome::Value(value),
                } => (state, condition, *value),
                _ => return Err("retained condition evidence has a non-value conclusion"),
            };
        let Some((next, tail)) = self.next_source_statement_and_tail(function) else {
            return Err("condition evidence was recorded with no source statement remaining");
        };
        let decided = match &*next {
            CStatement::If { condition, .. } | CStatement::While { condition, .. } => condition,
            _ => {
                return Err(
                    "condition evidence does not decide the frontier's next `if` or `while`",
                );
            }
        };
        if decided != proved_condition {
            return Err("condition evidence does not decide the frontier's next source condition");
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
                body,
            } => {
                if value {
                    let loop_head = CStatement::While {
                        condition: condition.clone(),
                        invariant: invariant.clone(),
                        invariant_checks: invariant_checks.clone(),
                        effect_checks: effect_checks.clone(),
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
    ) -> Result<(), &'static str> {
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
            return Err("evidence does not start from the running state");
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
        if !crate::kernel::api::proof_evidence_premises_are_retained(
            theorem,
            entry_assumptions,
            Some(context),
            &retained_execution_facts,
            obligations,
            running_state,
            entry_relation_facts,
        ) {
            return Err("evidence assumes a premise the proof did not retain");
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
    ) -> Result<(), &'static str> {
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
        for (trace, fork) in self.execution_evidence.iter().zip(plan) {
            match fork {
                OutcomeEvidenceFork::Keep => traces.push(trace.clone()),
                OutcomeEvidenceFork::Split {
                    partition,
                    arm_facts,
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
                        traces.push(forked);
                    }
                }
            }
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
        if self.evidence_completed {
            return Err("a resource rewrite was recorded after the trace completed");
        }
        let mut rewrite = CheckedResourceRewrite::check(
            function,
            self.reached_state(),
            before_facts,
            selected,
            after_state,
            after_facts,
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
        if candidates.paths().len() != self.execution_evidence.len() {
            return Err("the published paths do not match the retained traces one to one");
        }
        if !crate::kernel::api::proof_case_partitions_are_exhaustive(&self.execution_evidence) {
            return Err("a proof-case partition is not exhausted by the retained traces");
        }
        if !crate::kernel::api::proof_evidence_function_refines_same_source(
            candidates.function(),
            checked_function,
        ) {
            return Err("the checked function does not refine the published function's source");
        }
        let function = checked_function;
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
                    self.execution_evidence.iter().all(|trace| {
                        crate::kernel::api::proof_evidence_initial_state(&trace.to_vec())
                            == Some(trace_entry)
                    }) || entry
                        .entry_state_for(
                            candidates.state(),
                            candidates.function(),
                            candidates.arguments(),
                            &assumptions,
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
        let mut paths = Vec::with_capacity(candidates.paths().len());
        for (candidate, trace) in candidates.paths().iter().zip(&self.execution_evidence) {
            let (completed, statement_assumptions, interface_execution_facts) =
                trace_completion(&trace.to_vec(), &assumptions)?;
            let (outcome, obligations) = crate::kernel::c_function_outcome_from_statement_outcome(
                candidates.state(),
                function,
                completed.clone(),
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
                candidates.state(),
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
                &assumptions,
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
                .then(|| self.function_entry.as_ref())
                .flatten()
                .map(|entry| entry.caller_state().clone()),
        })
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{
        Bitvector32Term, CComparisonOperator, CCompositeResourceDefinition, CMemory,
        CResourceAccessMode, CResourceFact, CResourceSpec, CType, CValue, Pointer, PointerBlock,
        PointerOffsetTerm, SpecExpression, c_function, int32,
    };

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
            .with_counted_population("item", Vec::new(), Bitvector32Term::Constant(1));
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
            caller.with_counted_population("item", Vec::new(), Bitvector32Term::Constant(2));
        assert!(
            checked
                .entry_state_for(&changed_population, &function, &[], &assumptions)
                .is_none(),
            "a resource rebase must not authorize a changed counted population"
        );
    }

    #[test]
    fn checked_composite_events_reject_forged_resources_facts_memory_and_definitions() {
        let child_spec = CResourceSpec::Token {
            access: CResourceAccessMode::Own,
            name: "child".to_string(),
            arguments: Vec::new(),
            parameter_types: Vec::new(),
        };
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
                .unchecked_with_fact(child_view.clone()),
        );
        let observation = CheckedResourceObservation::check(
            &function,
            &before,
            &facts,
            &selected,
            &observed,
            &facts,
            &PersistentOrderedSet::default(),
        )
        .expect("the exact one-layer child view should check");

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
            )
            .is_err(),
            "observation must not change C memory"
        );

        let unfolded = before
            .clone()
            .with_resource_context(ResourceContext::new().unchecked_with_fact(child.clone()));
        CheckedResourceRewrite::check(&function, &before, &facts, &selected, &unfolded, &facts)
            .expect("the exact folded-to-body representation change should check");
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
            !observation.advances_sealed(&changed_definition, &before),
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
