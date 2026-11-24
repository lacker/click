use super::*;

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/surface/proof/resources/observation_partition_tests.rs");
}
use crate::kernel::ExecutionFactSource;
use crate::kernel::ResourceInstance;
use crate::kernel::proof::fact_reasoning::holds_by_lookup_or_decision;
use crate::kernel::{CompareRelation, MachineIntegerType};
use crate::kernel::{
    bits32_constant, constant_u32, int32_constant, int64_constant, uint64_constant,
};
use crate::surface::proof::execution_planning::refuse_or_record_open_obligation;
use crate::surface::proof_diagnostics::render::{
    render_resource_fact_diagnostic, render_resource_facts_diagnostic,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ResourceBodyAccess {
    Finalize,
    Open,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ResourceBodyClosure {
    Initialize,
    CloseOpen { preserve_exposed_body: bool },
}

/// Literal resource counts are signed int32 values. Classify them without
/// asking whether unrelated assumptions imply a contradictory arithmetic fact.
/// Symbolic counts still require the existing checked proof queries.
fn fold_resource_quantity_activity(
    quantity: &MachineTerm,
    assumptions: &PureFactContext,
) -> (bool, bool) {
    if let Some(value) = quantity.as_const() {
        return (value == 0, (value as i32) > 0);
    }
    let zero = holds_by_lookup_or_decision(
        assumptions,
        &Proposition::condition_is(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(quantity.clone()),
                right: Box::new(MachineTerm::constant(0)),
            },
            true,
        ),
    );
    let positive = holds_by_lookup_or_decision(
        assumptions,
        &Proposition::condition_is(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left: Box::new(quantity.clone()),
                right: Box::new(MachineTerm::constant(0)),
            },
            true,
        ),
    );
    (zero, positive)
}

/// The pure-fact surface needed by resource semantics.
///
/// Checked resource operations consult the persistent Proof fact and
/// assumption indexes. Only diagnostics materialize an ambient fact vector.
trait ResourcePureFacts {
    fn assumptions(&self) -> &PureFactContext;
    fn exact_available_across_effects(
        &self,
        required: &Proposition,
        _framing: &(impl ExecutionFactSource + ?Sized),
    ) -> bool;
    fn insert(&mut self, fact: Proposition) -> bool;
    fn materialize(&self) -> Vec<Proposition>;
}

struct ProofResourcePureFacts {
    facts: PureFactStore,
    added: Vec<Proposition>,
    published: Vec<Proposition>,
}

impl ProofResourcePureFacts {
    fn new(facts: PureFactStore) -> Self {
        Self {
            facts,
            added: Vec::new(),
            published: Vec::new(),
        }
    }
}

impl ResourcePureFacts for ProofResourcePureFacts {
    fn assumptions(&self) -> &PureFactContext {
        self.facts.assumptions()
    }

    fn exact_available_across_effects(
        &self,
        required: &Proposition,
        framing: &(impl ExecutionFactSource + ?Sized),
    ) -> bool {
        self.facts.exact_available_across_effects(required, framing)
    }

    fn insert(&mut self, fact: Proposition) -> bool {
        self.published.push(fact.clone());
        if self.facts.contains_top_level(&fact) {
            return false;
        }
        self.facts = self.facts.with_kernel_checked_fact(fact.clone());
        self.added.push(fact);
        true
    }

    fn materialize(&self) -> Vec<Proposition> {
        self.facts.to_vec()
    }
}

pub(super) struct UnfoldedCompositeResource {
    pub(super) state: ExecutionState,
    pub(super) selected: ResourceFact,
    pub(super) body_was_already_exposed: bool,
}

/// Resolve the dependency of one viewed representation without selecting an
/// authority by equal resource spelling.  Duplicate equal views are valid
/// only when they carry the same checked borrow bundle; otherwise the rewrite
/// is ambiguous and must fail closed.
fn unique_borrowed_resource_dependency(
    state: &ExecutionState,
    resource: &ResourceFact,
) -> Result<Option<crate::kernel::BorrowBinding>, String> {
    state.unique_borrowed_resource_dependency(resource)
}

/// Record the children a checked rewrite exposed from a viewed composite as
/// permitted descriptions of the parent's borrow. The rewrite derived them
/// from the definition in the current state, but the ledger does not take
/// that list on trust: the kernel expands the parent one level itself and
/// `project` re-checks every child against that expansion (D2 law 10).
fn project_children_into_ledger(
    state: ExecutionState,
    binding: &crate::kernel::BorrowBinding,
    children: impl IntoIterator<Item = ResourceFact>,
    assumptions: &PureFactContext,
    definitions: &[CompositeResourceDefinition],
    context_label: &str,
) -> Result<ExecutionState, ClickError> {
    let (Some(ledger), Some(holder)) = (state.borrow_ledger().cloned(), state.borrow_participant())
    else {
        return Ok(state);
    };
    let mut children = children.into_iter().peekable();
    if children.peek().is_none() {
        return Ok(state);
    }
    let evidence = crate::kernel::checked_composite_projection_evidence(
        &binding.viewed,
        definitions,
        &state.program_point(),
        assumptions,
    )
    .ok_or_else(|| {
        ClickError::new(format!(
            "{context_label} cannot expand the viewed composite to check a child projection"
        ))
    })?;
    let mut ledger = ledger;
    for child in children {
        ledger = ledger
            .project(holder, binding.borrow, &binding.viewed, &evidence, child)
            .map_err(|refusal| {
                ClickError::new(format!(
                    "{context_label} cannot project a child of the viewed composite: {refusal}"
                ))
            })?;
    }
    Ok(state.with_borrow_ledger(Some(ledger)))
}

fn same_borrow_authority(
    left: &crate::kernel::BorrowBinding,
    right: &crate::kernel::BorrowBinding,
) -> bool {
    left.borrow == right.borrow
        && left.scope == right.scope
        && left.share == right.share
        && left.support == right.support
}

/// Temporary projections are indexed once per resource rewrite.  This keeps
/// dynamic-load checking proportional to the loads and matching view ranges,
/// rather than multiplying every body fact by every temporary view.
struct DynamicViewDependencyIndex {
    bound: ResourceContext,
    bound_dependencies: BTreeMap<crate::kernel::ResourceOccurrenceId, crate::kernel::BorrowBinding>,
    unbound: ResourceContext,
    /// Owned memory an unfold is about to insert. The folded instance held
    /// it exclusively, so a body fact over it needs no borrow: it is supported
    /// exactly as a read of ambient owned memory is.
    owned: ResourceContext,
    /// The owned instance retained while its body is opened or refolded.
    /// A view it publishes over its own bytes borrows nothing: its authority
    /// is this live owner. Only this one owner's projections count; any
    /// other observation still needs a borrow.
    opened_owner: Option<crate::kernel::ResourceOccurrenceId>,
}

impl DynamicViewDependencyIndex {
    fn new(
        bound_views: &[(ResourceFact, crate::kernel::BorrowBinding)],
        unbound_views: &[ResourceFact],
        assumptions: &PureFactContext,
    ) -> Self {
        Self::with_owned(bound_views, unbound_views, &[], assumptions)
    }

    fn with_owned(
        bound_views: &[(ResourceFact, crate::kernel::BorrowBinding)],
        unbound_views: &[ResourceFact],
        owned: &[ResourceFact],
        assumptions: &PureFactContext,
    ) -> Self {
        let (bound, inserted) = ResourceContext::new_with_equalities(assumptions)
            .unchecked_with_facts_and_occurrences(bound_views.iter().map(|(view, _)| view.clone()));
        let bound_dependencies = inserted
            .into_iter()
            .zip(bound_views.iter())
            .map(|((_, occurrence), (_, binding))| (occurrence, binding.clone()))
            .collect();
        Self {
            bound,
            bound_dependencies,
            unbound: ResourceContext::new_with_equalities(assumptions)
                .unchecked_with_facts(unbound_views.iter().cloned()),
            owned: ResourceContext::new_with_equalities(assumptions)
                .unchecked_with_facts(owned.iter().cloned()),
            opened_owner: None,
        }
    }

    fn with_opened_owner(mut self, owner: Option<crate::kernel::ResourceOccurrenceId>) -> Self {
        self.opened_owner = owner;
        self
    }
}

/// The innermost guarded universal binder around a body-fact read: its
/// variable and the guard its body's implication assumes.
type QuantifiedBinder<'a> = Option<(Variable, &'a Proposition)>;

/// Find the live stable-view authority needed by the current memory loads in
/// one lowered body fact.  Loads from an older memory state are historical
/// scalar facts and deliberately do not participate in this check.  The
/// caller supplies views which are about to be inserted by an observation so
/// that dependency capture does not search equal ambient occurrences.
fn dynamic_body_fact_dependency(
    required: &Proposition,
    state: &ExecutionState,
    assumptions: &PureFactContext,
    temporary_views: &DynamicViewDependencyIndex,
) -> Result<Option<crate::kernel::BorrowBinding>, String> {
    fn check_load(
        pointer: Address,
        width: u32,
        state: &ExecutionState,
        assumptions: &PureFactContext,
        temporary_views: &DynamicViewDependencyIndex,
        binder: QuantifiedBinder<'_>,
        selected: &mut Option<crate::kernel::BorrowBinding>,
    ) -> Result<(), String> {
        // A read under a guarded universal, `forall v { lo <= v < hi implies
        // ... p[v] ... }`, reads only cells of `p[lo..hi]`. Require a live
        // view of that whole range instead of one of the symbolic cell
        // `p[v]`, which no view contains since `v` alone is unconstrained.
        // Every cell the guard admits lies in the range
        // (`MemoryRange::guarded_quantified_cells`), so a view covering the
        // range covers every cell the fact reads, and its borrow is the fact's
        // dependency. A read the range does not describe keeps the one-cell
        // requirement.
        let range = binder
            .and_then(|(variable, guard)| {
                MemoryRange::guarded_quantified_cells(&pointer, variable, guard, width)
            })
            .unwrap_or_else(|| {
                MemoryRange::new_with_element_width(
                    pointer,
                    MachineTerm::constant(0),
                    MachineTerm::constant(1),
                    width,
                )
            });
        let required_view = ResourceFact::view_memory(range);
        if !temporary_views
            .unbound
            .view_occurrences_for_fact(&required_view, assumptions)
            .is_empty()
        {
            return Err("current body fact is covered by an unbound view".into());
        }
        let mut candidates = Vec::new();
        let mut owned_projection = false;
        for occurrence in state
            .resources()
            .view_occurrences_for_fact(&required_view, assumptions)
        {
            let Some(candidate) = state.resources().borrow_dependency(occurrence) else {
                // A view the instance being opened publishes over its own
                // bytes (an owned `cstr_at` held folded across `with`)
                // borrows nothing: its authority is that live owner, so the
                // read is a read of owned memory, as after `unfold`. A view
                // with an exact support edge to plain owned memory likewise
                // needs no borrow. Unrelated owners cannot supply this edge.
                if state
                    .resources()
                    .owned_projection_support(occurrence)
                    .is_some_and(|(support, fact)| {
                        temporary_views.opened_owner == Some(support)
                            || fact.memory_own_range().is_some()
                    })
                {
                    owned_projection = true;
                    continue;
                }
                return Err(
                    "current body fact is covered by an unbound viewed memory occurrence".into(),
                );
            };
            candidates.push(candidate.clone());
        }
        for occurrence in temporary_views
            .bound
            .view_occurrences_for_fact(&required_view, assumptions)
        {
            let candidate = temporary_views
                .bound_dependencies
                .get(&occurrence)
                .ok_or_else(|| "temporary view dependency index lost an occurrence".to_string())?;
            candidates.push(candidate.clone());
        }
        if candidates.is_empty() {
            if owned_projection
                || state
                    .resources()
                    .directly_supporting_owned_entry(&required_view, assumptions)
                    .is_some()
                || temporary_views
                    .owned
                    .directly_supporting_owned_entry(&required_view, assumptions)
                    .is_some()
            {
                return Ok(());
            }
            return Err(
                "current body fact reads memory outside every live viewed-memory dependency".into(),
            );
        }
        let ledger = state.borrow_ledger().ok_or_else(|| {
            "current viewed-memory dependency has no active borrow ledger".to_string()
        })?;
        let holder = state
            .borrow_participant()
            .ok_or_else(|| "current viewed-memory dependency has no borrow holder".to_string())?;
        for checked in candidates {
            // The occurrence lookup above established coverage using the
            // current facts. Preserve its recorded binding: replacing its
            // view with a derived subrange would ask the ledger's fact-free
            // identity check to rediscover that coverage.
            ledger
                .validate_view_binding(checked.clone(), holder)
                .map_err(|error| {
                    format!("current viewed-memory dependency is not live: {error}")
                })?;
            if selected
                .as_ref()
                .is_some_and(|existing| !same_borrow_authority(existing, &checked))
            {
                return Err("one body fact depends on different stable-view authorities".into());
            }
            *selected = Some(checked);
        }
        Ok(())
    }
    fn walk_term(
        term: &Term,
        state: &ExecutionState,
        assumptions: &PureFactContext,
        temporary_views: &DynamicViewDependencyIndex,
        binder: QuantifiedBinder<'_>,
        selected: &mut Option<crate::kernel::BorrowBinding>,
    ) -> Result<(), String> {
        walk_loads(
            crate::kernel::current_memory_loads_in_term(term, state.memory())?,
            state,
            assumptions,
            temporary_views,
            binder,
            selected,
        )
    }
    fn walk_loads(
        loads: Vec<(Address, u32)>,
        state: &ExecutionState,
        assumptions: &PureFactContext,
        temporary_views: &DynamicViewDependencyIndex,
        binder: QuantifiedBinder<'_>,
        selected: &mut Option<crate::kernel::BorrowBinding>,
    ) -> Result<(), String> {
        for (pointer, width) in loads {
            check_load(
                pointer,
                width,
                state,
                assumptions,
                temporary_views,
                binder,
                selected,
            )?;
        }
        Ok(())
    }
    fn walk_proposition(
        proposition: &Proposition,
        state: &ExecutionState,
        assumptions: &PureFactContext,
        temporary_views: &DynamicViewDependencyIndex,
        binder: QuantifiedBinder<'_>,
        selected: &mut Option<crate::kernel::BorrowBinding>,
    ) -> Result<(), String> {
        match proposition {
            Proposition::ConditionIs(condition, _) => walk_term(
                &Term::Condition(condition.clone()),
                state,
                assumptions,
                temporary_views,
                binder,
                selected,
            ),
            Proposition::Equal(left, right) => {
                walk_term(left, state, assumptions, temporary_views, binder, selected)?;
                walk_term(right, state, assumptions, temporary_views, binder, selected)
            }
            Proposition::And(left, right)
            | Proposition::Or(left, right)
            | Proposition::Implies(left, right) => {
                walk_proposition(left, state, assumptions, temporary_views, binder, selected)?;
                walk_proposition(right, state, assumptions, temporary_views, binder, selected)
            }
            Proposition::ForAll { var, body, .. } => match body.as_ref() {
                Proposition::Implies(guard, consequent) => {
                    walk_proposition(guard, state, assumptions, temporary_views, binder, selected)?;
                    // A structurally empty guarded domain evaluates no body
                    // reads. Still check the guard's own read dependencies.
                    if crate::kernel::proof::fact_reasoning::instance_guard_folds_to_false(guard) {
                        return Ok(());
                    }
                    walk_proposition(
                        consequent,
                        state,
                        assumptions,
                        temporary_views,
                        Some((**var, guard)),
                        selected,
                    )
                }
                body => {
                    walk_proposition(body, state, assumptions, temporary_views, binder, selected)
                }
            },
            Proposition::Not(body) | Proposition::Exists { body, .. } => {
                walk_proposition(body, state, assumptions, temporary_views, binder, selected)
            }
            Proposition::Predicate { arguments, .. } => {
                for argument in arguments {
                    walk_term(
                        argument,
                        state,
                        assumptions,
                        temporary_views,
                        binder,
                        selected,
                    )?;
                }
                Ok(())
            }
            Proposition::ResourceSeparate { .. }
            | Proposition::ResourceComposition(_)
            | Proposition::ResourceContains { .. } => Ok(()),
            Proposition::MemoryLoads { outcome, .. } => match outcome {
                ExpressionOutcome::Value(value) => walk_term(
                    &Term::ProgramValue(value.clone()),
                    state,
                    assumptions,
                    temporary_views,
                    binder,
                    selected,
                ),
                ExpressionOutcome::UndefinedBehavior(_) | ExpressionOutcome::RuntimeError(_) => {
                    Ok(())
                }
            },
            Proposition::MemoryReadDefined {
                at,
                memory,
                pointer,
                value_type,
            } => {
                // Definedness is an observation of the same cell as a load.
                // Retain its access dependency, including loads in its address.
                walk_term(
                    &Term::ProgramValue(ProgramValue::pointer(pointer.clone()).into()),
                    state,
                    assumptions,
                    temporary_views,
                    binder,
                    selected,
                )?;
                // The point identifies the observation even when two states
                // share a memory view. Synthetic facts may have no point.
                let is_current = at
                    .and_then(|point| state.observation_point_id().map(|current| point == current))
                    .unwrap_or_else(|| memory == state.memory());
                if is_current {
                    check_load(
                        pointer.clone(),
                        value_type.byte_width(),
                        state,
                        assumptions,
                        temporary_views,
                        binder,
                        selected,
                    )?;
                }
                Ok(())
            }
            Proposition::MemoryLoadable { bytes, .. } => walk_loads(
                crate::kernel::current_memory_loads_in_count(bytes, state.memory())?,
                state,
                assumptions,
                temporary_views,
                binder,
                selected,
            ),
            Proposition::HeapAllocationFreed { bytes, .. } => walk_term(
                &Term::Bitvector32(bytes.bytes().clone().into()),
                state,
                assumptions,
                temporary_views,
                binder,
                selected,
            ),
            Proposition::MemoryCanStore { .. }
            | Proposition::MemoryMutatesOnly { .. }
            | Proposition::MemoryEffectSummary { .. }
            | Proposition::ProgramFunctionPartiallySatisfiesSpecification { .. } => Ok(()),
            _ => Err("unsupported opaque proposition in current-load dependency".into()),
        }
    }
    let mut selected = None;
    walk_proposition(
        required,
        state,
        assumptions,
        temporary_views,
        None,
        &mut selected,
    )?;
    Ok(selected)
}

pub(super) fn materialize_folded_composite_resource_cells(
    resource_environment: &ResourceEnvironment,
    parameter_binding: ParameterBinding<'_>,
    mut state: ExecutionState,
    claim_label: &str,
    spec_definitions: SpecDefinitions<'_>,
    assumptions: &PureFactContext,
) -> Result<ExecutionState, ClickError> {
    let naming_state = name_folded_composite_resource_cells(
        resource_environment,
        parameter_binding,
        &state,
        spec_definitions,
        assumptions,
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}` setup failed: {message}")))?;
    state.keep_memory_of(&naming_state);
    Ok(state)
}

fn name_folded_composite_resource_cells(
    resource_environment: &ResourceEnvironment,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    spec_definitions: SpecDefinitions<'_>,
    assumptions: &PureFactContext,
) -> Result<ExecutionState, String> {
    // Clause evaluation uses just the memory view and the caller's point.
    let mut naming_state = ExecutionState::at_state(state);
    for resource in state.resources().facts() {
        let (name, resource_arguments) = match resource.resource() {
            Resource::Footprint(_) | Resource::Parameter(_) | Resource::Emp | Resource::Star(_) => {
                continue;
            }
            Resource::Composite { name, arguments } => (name, arguments),
            Resource::Memory(_)
            | Resource::Token { .. }
            | Resource::Instance(_)
            | Resource::ConditionalMutexGuard(_)
            | Resource::MutexGuard(_)
            | Resource::MutexLive(_)
            | Resource::MutexUse(_)
            | Resource::Publication(_)
            | Resource::PopulationAuthority(_)
            | Resource::Iterated(_) => {
                continue;
            }
        };
        let Some(definition) = resource_environment.get(name) else {
            continue;
        };
        let Some(composite_body) = definition.composite_body() else {
            continue;
        };
        if composite_body.condition().is_some() {
            continue;
        }
        let substitutions = resource_value_substitutions_with_witnesses(
            definition,
            &(resource_arguments).native_values(),
            state.memory(),
            state.resources(),
            assumptions,
            resource_environment,
            spec_definitions,
            None,
        )
        .map_err(|message| {
            format!("could not instantiate composite resource `{name}` body: {message}")
        })?;
        naming_state = materialize_composite_resource_memory(
            name,
            composite_body,
            &substitutions,
            parameter_binding,
            naming_state,
            assumptions,
        )?;
    }
    Ok(naming_state)
}

/// The match arm one section's premises select for a held resource instance,
/// as a resource definition whose body is that arm's own.
///
/// This is the surface side of decision D7, and it asks the same question the
/// kernel's [`crate::kernel::publish_instance_arms`] asks: the decision itself
/// is [`crate::kernel::decide_resource_model_arm`]. `Selected` projects that
/// arm's cells; `Possible` projects what every surviving arm owns, which is
/// [`common_possible_instance_arm`], the clause-level reading of the very
/// intersection the kernel's read authority takes over evaluated ranges;
/// `Open` leaves the instance folded, and a read through it fails with the
/// note `folded_matched_instance_note` adds.
///
/// The returned definition is the arm scope `resource_match_arm_scopes` builds:
/// its `contains` holds only the arm's own memory clauses, so projecting it
/// exposes cells and never a contained instance, which only an explicit
/// `unfold` may produce.
pub(in crate::surface) fn selected_resource_instance_arm(
    resource_environment: &ResourceEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    instance: &ResourceInstance,
    assumptions: &PureFactContext,
) -> Option<SelectedInstanceArm> {
    let definition = resource_environment.get(instance.name())?;
    let matched = definition
        .composite_body()
        .and_then(|body| body.matched.as_ref())?;
    let field_index = definition
        .fields()
        .iter()
        .position(|field| field.name() == matched.field)?;
    let crate::kernel::ResourceFieldValue::Algebraic(model) = instance.fields().get(field_index)?
    else {
        return None;
    };
    let scopes = crate::surface::validation::resource_match_arm_scopes(
        definition,
        |name| {
            click_function_environment
                .algebraic_type_definitions
                .get(name)
        },
        |name| resource_environment.get(name),
    )
    .ok()?;
    match crate::kernel::decide_resource_model_arm(model, assumptions) {
        crate::kernel::ResourceModelArmDecision::Selected(selection) => {
            let arm = scopes
                .into_iter()
                .find(|(variant, _, _)| variant == selection.variant())
                .map(|(_, _, arm)| arm)?;
            // A `Constructor` selection knows what the arm's bindings hold, so
            // a memory clause written over a pointer payload denotes a cell
            // this projection can name. A `Variant` selection does not.
            let bindings = match selection {
                crate::kernel::ResourceModelArmSelection::Constructor(constructor) => {
                    match constructor.node {
                        crate::kernel::AlgebraicTermNode::Constructor { fields, .. } => fields,
                        _ => Vec::new(),
                    }
                }
                crate::kernel::ResourceModelArmSelection::Variant(_) => Vec::new(),
            };
            Some(SelectedInstanceArm { arm, bindings })
        }
        // No single arm: what every arm the premises leave possible owns is
        // still readable, and that is what this projects.
        crate::kernel::ResourceModelArmDecision::Possible(possible) => {
            common_possible_instance_arm(scopes, &possible).map(|arm| SelectedInstanceArm {
                arm,
                bindings: Vec::new(),
            })
        }
        crate::kernel::ResourceModelArmDecision::Open => None,
    }
}

/// The body an unfold of an instance exposes when its resource does not match
/// on a field. Such a body has one shape: its memory clauses name cells at the
/// instance's arguments and its C-typed field values. Those fields are the
/// scope's extra parameters, in field order, as a matched arm's C-typed
/// constructor bindings are, because a memory clause may use a field as an
/// endpoint. A guarded body is selected only for an explicit rewrite whose
/// kernel check proved the body active. Witness-carrying bodies stay opaque,
/// and a field-free body is not an instance.
fn unmatched_instance_body(
    definition: &ResourceDefinition,
    body: &CompositeResourceBody,
    instance: &ResourceInstance,
    checked_active_body: bool,
) -> Option<SelectedInstanceArm> {
    if (body.condition.is_some() && !checked_active_body)
        || !body.witnesses.is_empty()
        || definition.fields().is_empty()
    {
        return None;
    }
    let mut parameters = definition.parameters.clone();
    for field in definition.fields() {
        if matches!(field.click_type(), ClickType::Program(_)) {
            parameters.push(FunctionParameter {
                slice_length: None,
                name: field.name().to_string(),
                click_type: field.click_type().clone(),
                struct_name: None,
                function_pointer_signature: None,
                constant: false,
                pointee_constant: false,
                reference: false,
            });
        }
    }
    let mut scope = body.clone();
    // Only a successful explicit rewrite supplies the checked guard case.
    // Initial projection still leaves guarded instances opaque.
    scope.condition = None;
    scope.children = Vec::new();
    scope.facts = Vec::new();
    scope.contains.retain(|clause| {
        matches!(
            clause,
            ResourceClause::OwnMemory(_)
                | ResourceClause::ViewMemory(_)
                | ResourceClause::MemoryAggregate { .. }
        )
    });
    Some(SelectedInstanceArm {
        arm: ResourceDefinition {
            name: definition.name.clone(),
            resource_parameters: definition.resource_parameters.clone(),
            parameters,
            composite_body: Some(scope),
            field_schema: definition.field_schema.clone(),
            authorized: definition.authorized,
            sealed: definition.sealed,
        },
        bindings: instance.fields().to_vec(),
    })
}

/// One arm scope together with what the selection proved its constructor
/// bindings hold. The bindings are empty when no constructor is known, which
/// is exactly when a memory clause written over a binding names no cell.
pub(in crate::surface) struct SelectedInstanceArm {
    arm: ResourceDefinition,
    bindings: Vec<AlgebraicValue>,
}

#[derive(Clone)]
pub(in crate::surface) struct ResourceClausePresentation {
    pub(in crate::surface) source: ClickProposition,
    pub(in crate::surface) checked: crate::kernel::ResourceBodyClauseRecord,
}

/// Pair each checked declaration record with its Surface clause by the arm
/// and ordinal retained by the kernel producer. This never searches the fact
/// store or re-lowers a clause after materializing the body's cells. The
/// caller supplies the lexical names bound by its proof `match`; an unfold
/// without those names simply has no usable presentation for binding-relative
/// clauses, while its kernel facts remain available.
pub(in crate::surface) fn pair_instance_body_clause_presentations(
    resource_environment: &ResourceEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    instance: &ResourceInstance,
    records: &[crate::kernel::ResourceBodyClauseRecord],
    function_values: &ProgramValueBindings,
    proof_bindings: Option<&[String]>,
) -> Result<Vec<ResourceClausePresentation>, ClickError> {
    let Some(first) = records.first() else {
        return Ok(Vec::new());
    };
    let Some(variant) = first.arm.as_deref() else {
        return Ok(Vec::new());
    };
    let Some(definition) = resource_environment.get(instance.name()) else {
        return Err(ClickError::new(
            "resource body clause lost its source definition",
        ));
    };
    let scopes = crate::surface::validation::resource_match_arm_scopes(
        definition,
        |name| {
            click_function_environment
                .algebraic_type_definitions
                .get(name)
        },
        |name| resource_environment.get(name),
    )?;
    let Some((_, bindings, arm)) = scopes.into_iter().find(|(name, _, _)| name == variant) else {
        return Err(ClickError::new(
            "resource body clause names an unknown selected arm",
        ));
    };
    let Some(source_facts) = arm.composite_body().map(|body| body.facts()) else {
        return Err(ClickError::new("selected resource arm has no source body"));
    };
    if definition.parameters().len() != instance.arguments().len() {
        return Err(ClickError::new(
            "resource body clause argument count changed",
        ));
    }
    if !bindings.is_empty() && proof_bindings.is_none_or(|names| names.len() != bindings.len()) {
        return Ok(Vec::new());
    }
    let mut names_by_value = BTreeMap::<ProgramValue, Option<String>>::new();
    for (name, value) in function_values {
        use std::collections::btree_map::Entry;
        match names_by_value.entry(value.clone()) {
            Entry::Vacant(slot) => {
                slot.insert(Some(name.clone()));
            }
            Entry::Occupied(mut slot) => {
                *slot.get_mut() = None;
            }
        }
    }
    let mut substitutions = BTreeMap::new();
    for (parameter, argument) in definition.parameters().iter().zip(instance.arguments()) {
        let Some(value) = argument.as_program_value() else {
            return Err(ClickError::new(
                "resource body clause has a non-C parameter",
            ));
        };
        let expression = match names_by_value.get(value).and_then(Option::as_ref) {
            Some(name) => ContractExpression::ProgramExpression(ProgramExpression::Variable(
                (name.clone()).into(),
            )),
            None => ContractExpression::ProgramExpression(ProgramExpression::Value(value.clone())),
        };
        substitutions.insert(parameter.name().to_string(), expression);
    }
    if let Some(names) = proof_bindings {
        for ((name, _), proof_name) in bindings.iter().zip(names) {
            substitutions.insert(
                name.clone(),
                ContractExpression::Binding(proof_name.clone()),
            );
        }
    }
    let instance_name =
        crate::kernel::model_fields::registered_instance_spelling(instance.identity())
            .ok_or_else(|| ClickError::new("resource body clause instance has no source name"))?;
    let substitutions = crate::surface::lowering::ContractSubstitutions::with_body_instance(
        &substitutions,
        instance_name.to_string(),
        instance.identity(),
    );
    let mut paired = Vec::with_capacity(records.len());
    for record in records {
        if record.arm.as_deref() != Some(variant) {
            return Err(ClickError::new("resource body clause changed selected arm"));
        }
        let Some(source) = source_facts.get(record.ordinal) else {
            return Err(ClickError::new(
                "resource body clause ordinal is outside its arm",
            ));
        };
        // The lowering producer retains the exact quantifier introduction
        // chain even when the proposition was previously present. In
        // particular, a quantified declaration must have a written binder
        // in that chain; an unrelated equal fact is not its presentation.
        if matches!(source, ClickProposition::ForAll { .. })
            && !record.introductions.iter().any(|introduction| {
                matches!(
                    introduction,
                    crate::kernel::LoweringIntroduction::WrittenUniversal { .. }
                )
            })
        {
            return Err(ClickError::new(
                "resource body clause lost its quantifier binder",
            ));
        }
        let source =
            crate::surface::lowering::substitute_click_proposition_in(source, &substitutions)
                .map_err(ClickError::new)?;
        paired.push(ResourceClausePresentation {
            source,
            checked: record.clone(),
        });
    }
    Ok(paired)
}

/// The arm scope holding exactly the memory clauses every possible arm owns.
///
/// Not a decision of its own: it is handed the variants
/// [`crate::kernel::decide_resource_model_arm`] left possible and projects the
/// clauses they agree on, exactly as the kernel's read authority intersects
/// the ranges those clauses evaluate to. `requires c.model != Context::Top` on a
/// three-constructor frame decides nothing, but the `Left` and `Right` arms it
/// leaves both own `parent->rb_right`, so that cell is readable however the
/// model turns out.
///
/// Two clauses agree when they are the same clause: the arms of one instance
/// share the resource's own parameters, so a segment written over them denotes
/// the same cells in each arm. A segment naming a constructor binding is never
/// published, because each arm's binding is its own unknown and two arms that
/// happen to spell one the same way are not talking about the same cell.
///
/// The result carries no facts and no children: an arm nothing selected states
/// nothing, and only an explicit `unfold` produces a contained instance. Cost
/// is the clauses of this one instance's arms.
fn common_possible_instance_arm(
    scopes: Vec<(String, Vec<(String, ClickType)>, ResourceDefinition)>,
    possible: &[String],
) -> Option<ResourceDefinition> {
    if possible.len() < 2 {
        return None;
    }
    let mut arms = possible
        .iter()
        .map(|variant| {
            let (_, bindings, arm) = scopes
                .iter()
                .find(|(candidate, _, _)| candidate == variant)?;
            let bound = bindings
                .iter()
                .map(|(name, _)| name.as_str())
                .collect::<BTreeSet<_>>();
            let clauses = arm
                .composite_body()?
                .contains()
                .iter()
                .filter(|clause| match clause {
                    ResourceClause::OwnMemory(segment) => {
                        contract_segment_referenced_names(segment)
                            .iter()
                            .all(|name| !bound.contains(name.as_str()))
                    }
                    _ => false,
                })
                .cloned()
                .collect::<Vec<_>>();
            Some((arm.clone(), clauses))
        })
        .collect::<Option<Vec<_>>>()?;
    let (mut common, first) = arms.remove(0);
    let clauses = first
        .into_iter()
        .filter(|clause| arms.iter().all(|(_, other)| other.contains(clause)))
        .collect::<Vec<_>>();
    if clauses.is_empty() {
        return None;
    }
    let body = common.composite_body.as_mut()?;
    body.contains = clauses;
    body.facts = Vec::new();
    body.children = Vec::new();
    body.witnesses = Vec::new();
    Some(common)
}

/// Names the cells an `unfold` of an instance has just exposed.
///
/// Naming is atomic across producers (`docs/internals/canonicalization.md`).
/// Contract lowering already materializes the cells of the arm a section
/// selects for a held instance, so the fact it states about a cell and the
/// C's own read of that cell are one load variable. An unfold exposes the same
/// cells one layer deeper and must name them the same way. Without this, the
/// unfolded child's facts keep the unfold-time epoch while a later C read of
/// the same cell walks its own epoch, and the two differ as soon as a store
/// the assumption-free version walk cannot cross lies between them — a write to
/// a *separate* object, whose separation is a resource fact and not a DAG
/// edge. That is exactly the gap between `*new = *victim` and the refold after
/// `rb_set_parent(victim->rb_left, new)`.
///
/// This is the same projection contract lowering runs, so the cell layout and
/// element types are the ones already chosen there rather than a second
/// convention. It is bounded by the arm body: one cell per element of each
/// constant-bounded range the arm owns, no search, and cells the state
/// already holds are left alone.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn materialize_unfolded_instance_arm_cells(
    resource_environment: &ResourceEnvironment,
    spec_definitions: SpecDefinitions<'_>,
    parameter_binding: ParameterBinding<'_>,
    state: ExecutionState,
    instance: &ResourceInstance,
    assumptions: &PureFactContext,
    naming_assumptions: &PureFactContext,
    checked_active_body: bool,
) -> ExecutionState {
    if !checked_active_body {
        return state;
    }
    // An unfold consumes the instance and exposes its body, so an unmatched
    // body is the one it exposes. Its cells are named here exactly as a
    // selected arm's are; otherwise a C read of a cell the body owns, after
    // any later write, mints a second load identity for it.
    let selected = selected_resource_instance_arm(
        resource_environment,
        spec_definitions.functions,
        instance,
        assumptions,
    )
    .or_else(|| {
        let definition = resource_environment.get(instance.name())?;
        let body = definition.composite_body()?;
        body.matched
            .is_none()
            .then(|| unmatched_instance_body(definition, body, instance, checked_active_body))?
    });
    let Some(selected) = selected else {
        return state;
    };
    // Select the arm from the facts the rewrite published, but choose its
    // pointer spellings from the exact opening context used by the kernel.
    // Facts introduced later must not rename an already published scalar load.
    project_selected_instance_arm_cells(
        &selected,
        instance,
        parameter_binding,
        state,
        naming_assumptions,
        false,
        None,
    )
}

/// How the entry projection gives read authority for the memory an owned
/// resource owns directly. Holding a resource, viewed or owned, lets C read
/// that memory; a write still needs `unfold`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum OwnedCores {
    /// Views attached to the exact owned occurrence, retired when the owner
    /// is unfolded, consumed or freed, and limited to memory: a child
    /// resource stays folded. The kernel derives them again wherever it
    /// makes the owner anew: at a loop head, and at a fold of a resource
    /// with fields.
    AttachedToOwner,
    /// Free-standing views for every owner, for a temporary state that is
    /// only read from.
    Standing,
}

pub(super) fn project_initial_composite_resource_cores(
    resource_environment: &ResourceEnvironment,
    parameter_binding: ParameterBinding<'_>,
    mut state: ExecutionState,
    available_pure_facts: &(impl PropositionSource + ?Sized),
    claim_label: &str,
    owned: Option<OwnedCores>,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<ExecutionState, ClickError> {
    let include_owned = owned.is_some();
    let attach_to_owner = owned == Some(OwnedCores::AttachedToOwner);
    let attach_instance_arms = attach_to_owner;
    let assumptions = assumptions_from_propositions(available_pure_facts);
    for resource in state.resources().facts().to_vec() {
        // A matched instance exposes the arm its section selects, and nothing
        // when no arm is selected (D7). The arm scope's body holds only that
        // arm's own memory clauses, so this projects cells and never a
        // contained instance.
        if let Resource::Instance(instance) = resource.resource() {
            let Some(selected) = selected_resource_instance_arm(
                resource_environment,
                spec_definitions.functions,
                instance,
                &assumptions,
            ) else {
                // An unconditional, unmatched body is the one arm the
                // instance always has. Its cells are named here as a
                // selected arm's are, so that a C read of one of them after
                // a store to a separately owned object is the same load the
                // body spoke about at entry, and an `unfold` after that
                // store finds the name it was folded at
                // (`materialize_unfolded_instance_arm_cells`). Holding the
                // instance lets C read them, by views attached to it.
                if resource.is_own()
                    && let Some(selected) =
                        resource_environment
                            .get(instance.name())
                            .and_then(|definition| {
                                let body = definition.composite_body()?;
                                body.matched.is_none().then(|| {
                                    unmatched_instance_body(definition, body, instance, false)
                                })?
                            })
                {
                    state = project_selected_instance_arm_cells(
                        &selected,
                        instance,
                        parameter_binding,
                        state,
                        &assumptions,
                        attach_instance_arms,
                        attach_instance_arms.then_some(&resource),
                    );
                }
                continue;
            };
            state = project_selected_instance_arm_cells(
                &selected,
                instance,
                parameter_binding,
                state,
                &assumptions,
                include_owned,
                (attach_instance_arms && resource.is_own()).then_some(&resource),
            );
            continue;
        }
        let head = resource.clone();
        let (name, resource_arguments, is_owned) = match resource {
            ResourceFact::View(Resource::Composite { name, arguments }) => (name, arguments, false),
            ResourceFact::Own(Resource::Composite { name, arguments }, _) => {
                (name, arguments, true)
            }
            _ => continue,
        };
        let Some(definition) = resource_environment.get(&name) else {
            continue;
        };
        let Some(composite_body) = definition.composite_body() else {
            continue;
        };
        if is_owned && !include_owned {
            continue;
        }
        let substitutions = resource_value_substitutions_with_witnesses(
            definition,
            &resource_arguments.native_values(),
            state.memory(),
            state.resources(),
            &assumptions,
            resource_environment,
            spec_definitions,
            None,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` setup failed: could not project composite resource core `{name}`: {message}"
            ))
        })?;
        let Some(body_active) = try_select_composite_resource_body(
            definition,
            &substitutions,
            parameter_binding,
            &state,
            &state,
            &ProgramValue::Int32(MachineTerm::constant(0)),
            &assumptions,
            spec_definitions,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` setup failed: could not select composite resource core `{name}`: {message}"
            ))
        })?
        else {
            continue;
        };
        if !body_active {
            continue;
        }
        let (memory, contained_resources) = instantiate_composite_resource_body_resources(
            &name,
            composite_body,
            &substitutions,
            parameter_binding,
            &state,
            &assumptions.clone().assume_entry_clause_spans().assume_held_resource_domains(),
    )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` setup failed: could not project composite resource core `{name}`: {message}"
            ))
        })?;
        let viewed_contained_resources = contained_resources
            .facts()
            .iter()
            .filter_map(|fact| fact.core_with_assumptions(&assumptions))
            .collect::<Vec<_>>();
        // An owned head's read authority is an observation of that owner: it
        // stays attached to the exact owned occurrence, so unfolding,
        // consuming or freeing the owner retires it. A viewed head has no
        // owner here to attach to and keeps plain views.
        let owned_support = (is_owned && attach_to_owner)
            .then(|| state.resources().owned_occurrences_for_fact(&head))
            .and_then(|occurrences| occurrences.first().copied());
        if is_owned && attach_to_owner && owned_support.is_none() {
            continue;
        }
        let resources = match owned_support {
            Some(occurrence) => {
                // One level: the memory the head owns directly. A child
                // resource stays folded, so its own memory and facts are not
                // read through the parent.
                let fresh = viewed_contained_resources
                    .into_iter()
                    .filter(|fact| fact.memory_view_range().is_some())
                    .filter(|fact| !state.resources().contains_exact_representation(fact))
                    .collect::<Vec<_>>();
                state
                    .resources()
                    .clone()
                    .unchecked_with_supported_facts_from_occurrence_with_memory(
                        occurrence,
                        &head,
                        fresh,
                        &memory,
                    )
            }
            None => state
                .resources()
                .clone()
                .try_compose_with_facts_delaying_normalization(
                    viewed_contained_resources,
                    &assumptions,
                )
                .map_err(|error| {
                    ClickError::new(format!(
                        "`{claim_label}` setup failed: projecting composite resource core `{name}` produced {}",
                        describe_resource_context_validity_error(error, parameter_binding)
                    ))
                })?,
        };
        state = state
            .with_materialized_memory_at_current_point(memory)
            .with_resource_context(resources);
    }
    Ok(state)
}

/// Materializes the selected arm's own cells and, when owned cores are being
/// projected, adds their read authority.
///
/// A failure to instantiate a clause is not an error here: the arm simply
/// exposes nothing, which is the same outcome as an unselected arm. The read
/// that needed the cell reports it.
fn project_selected_instance_arm_cells(
    selected: &SelectedInstanceArm,
    instance: &ResourceInstance,
    parameter_binding: ParameterBinding<'_>,
    state: ExecutionState,
    assumptions: &PureFactContext,
    include_owned: bool,
    owner: Option<&ResourceFact>,
) -> ExecutionState {
    let arm = &selected.arm;
    let Some(body) = arm.composite_body() else {
        return state;
    };
    let Ok(substitutions) = resource_value_substitutions_for_parameters(
        arm.name(),
        &(instance.arguments()).native_values(),
        &selected.bindings,
        arm.parameters(),
    ) else {
        return state;
    };
    let Ok((memory, contained_resources)) = instantiate_composite_resource_body_resources(
        arm.name(),
        body,
        &substitutions,
        parameter_binding,
        &state,
        &assumptions
            .clone()
            .assume_entry_clause_spans()
            .assume_held_resource_domains(),
    ) else {
        return state;
    };
    let state = state.with_materialized_memory_at_current_point(memory);
    if !include_owned {
        return state;
    }
    let viewed = contained_resources
        .facts()
        .iter()
        .filter_map(|fact| fact.core_with_assumptions(assumptions))
        .collect::<Vec<_>>();
    // An owned instance's read authority stays attached to the owner, as an
    // owned composite's does in `project_initial_composite_resource_cores`.
    if let Some(owner) = owner {
        let Some(occurrence) = state
            .resources()
            .owned_occurrences_for_fact(owner)
            .first()
            .copied()
        else {
            return state;
        };
        let fresh = viewed
            .into_iter()
            .filter(|fact| !state.resources().contains_exact_representation(fact))
            .collect::<Vec<_>>();
        let resources = state
            .resources()
            .clone()
            .unchecked_with_supported_facts_from_occurrence_with_memory(
                occurrence,
                owner,
                fresh,
                state.memory(),
            );
        return state.with_resource_context(resources);
    }
    match state
        .resources()
        .clone()
        .try_compose_with_facts_delaying_normalization(viewed, assumptions)
    {
        Ok(resources) => state.with_resource_context(resources),
        Err(_) => state,
    }
}

/// The parameter substitutions for one arm scope. The arm's parameter list
/// begins with the resource's own parameters and continues with the C-typed
/// constructor bindings, in constructor-field order.
///
/// A memory clause may name one of those bindings — that is what lets a
/// context frame own the cells of the node its own payload carries (A5) — so
/// the bindings are substituted too whenever the selection knew the
/// constructor. Without them the projection could not evaluate
/// `identity->rb_left`, the cell would stay unnamed, and a later C read of it
/// across a write to a separately owned object would mint a second load
/// identity for one cell.
fn resource_value_substitutions_for_parameters(
    name: &str,
    instance_arguments: &[AlgebraicValue],
    constructor_bindings: &[AlgebraicValue],
    parameters: &[FunctionParameter],
) -> Result<BTreeMap<String, ContractExpression>, String> {
    if parameters.len() < instance_arguments.len() {
        return Err(format!("resource `{name}` received too many arguments"));
    }
    let mut substitutions = parameters
        .iter()
        .zip(instance_arguments)
        .map(|(parameter, argument)| {
            let argument = argument
                .as_program_value()
                .ok_or_else(|| format!("resource `{name}` has a non-C argument"))?;
            Ok((
                parameter.name().to_string(),
                ContractExpression::ProgramExpression(ProgramExpression::Value(argument.clone())),
            ))
        })
        .collect::<Result<BTreeMap<_, _>, String>>()?;
    // Only C-typed constructor fields become arm parameters, and they are
    // pushed in field order, so one forward pass pairs them up.
    let mut binding_parameters = parameters[instance_arguments.len()..].iter();
    for binding in constructor_bindings {
        let Some(value) = binding.as_program_value() else {
            continue;
        };
        let Some(parameter) = binding_parameters.next() else {
            break;
        };
        substitutions.insert(
            parameter.name().to_string(),
            ContractExpression::ProgramExpression(ProgramExpression::Value(value.clone())),
        );
    }
    Ok(substitutions)
}

pub(super) fn project_initial_resource_facts(
    resource_environment: &ResourceEnvironment,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    available_pure_facts: &(impl PropositionSource + ?Sized),
    spec_definitions: SpecDefinitions<'_>,
    claim_label: &str,
) -> Result<PureFactList, ClickError> {
    let result = ProgramValue::Int32(MachineTerm::constant(0));
    let mut facts = ProofResourcePureFacts::new(available_pure_facts.fact_store());
    append_state_resource_context_observable_facts_with_store(state, &mut facts);
    project_folded_resource_observable_facts_with_store(
        resource_environment,
        parameter_binding,
        state,
        state,
        &result,
        &mut facts,
        spec_definitions,
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}` setup failed: {message}")))?;
    // Entry source origins address the incoming fact occurrences, including
    // repeated requirements and guards. Retain their positions while carrying
    // the producer's appended resource facts and indexes.
    Ok(PureFactList::from_produced_store(facts.facts))
}

pub(super) fn project_outcome_resource_facts(
    resource_environment: &ResourceEnvironment,
    parameter_binding: ParameterBinding<'_>,
    pre_state: &ExecutionState,
    outcome: &FunctionOutcome,
    available_pure_facts: PureFactStore,
    spec_definitions: SpecDefinitions<'_>,
    claim_label: &str,
    path_index: usize,
) -> Result<PureFactStore, ClickError> {
    let FunctionOutcome::Return { value, state } = outcome else {
        return Ok(available_pure_facts);
    };
    let mut facts = ProofResourcePureFacts::new(available_pure_facts);
    append_state_resource_context_observable_facts_with_store(state, &mut facts);
    project_folded_resource_observable_facts_with_store(
        resource_environment,
        parameter_binding,
        pre_state,
        state,
        &value.native(),
        &mut facts,
        spec_definitions,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` path {path_index}: could not project folded resource facts: {message}"
        ))
    })?;
    Ok(facts.facts)
}

fn append_state_resource_context_observable_facts_with_store<F: ResourcePureFacts>(
    state: &ExecutionState,
    available_pure_facts: &mut F,
) {
    // Entry admission and subsequent proof operations construct the partition.
    // Observe its retained composition, without admitting the held owners again.
    for fact in state
        .resources()
        .observable_facts_assuming_valid(available_pure_facts.assumptions())
    {
        available_pure_facts.insert(fact);
    }
}

fn project_folded_resource_observable_facts_with_store(
    resource_environment: &ResourceEnvironment,
    parameter_binding: ParameterBinding<'_>,
    pre_state: &ExecutionState,
    state: &ExecutionState,
    result: &ProgramValue,
    propositions: &mut ProofResourcePureFacts,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<(), String> {
    for resource in state.resources().facts() {
        project_held_resource_observable_facts(
            resource_environment,
            resource,
            parameter_binding,
            pre_state,
            state,
            result,
            propositions,
            spec_definitions,
        )?;
    }
    Ok(())
}

pub(super) enum ResourceObservationSuccessor {
    NamedCells(SymbolicMemory),
    Legacy(Box<ExecutionState>),
}

impl ResourceObservationSuccessor {
    pub(super) fn input(&self) -> crate::kernel::proof::ResourceObservationInput<'_> {
        use crate::kernel::proof::ResourceObservationInput;
        match self {
            Self::NamedCells(memory) => ResourceObservationInput::NamedCells(memory),
            Self::Legacy(state) => ResourceObservationInput::Legacy(state),
        }
    }
}

pub(super) struct CheckedResourceObservation {
    pub(super) successor: ResourceObservationSuccessor,
    pub(super) facts: PureFactStore,
    pub(super) added_facts: Vec<Proposition>,
    pub(super) observed_resource: ResourceFact,
}

#[allow(clippy::too_many_arguments)]
pub(super) fn observe_composite_resource_for_proof(
    function: &ProgramFunction,
    resource_environment: &ResourceEnvironment,
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    state: ExecutionState,
    facts: PureFactStore,
    surface_propositions: &mut SurfacePropositionMap,
    count_derivations: &mut PersistentOrderedSet<Theorem>,
    spec_definitions: SpecDefinitions<'_>,
    claim_label: &str,
    tactic_index: usize,
) -> Result<CheckedResourceObservation, ClickError> {
    let mut facts = ProofResourcePureFacts::new(facts);
    let (successor, observed_resource) = observe_composite_resource_with_facts(
        function,
        resource_environment,
        resource,
        parameter_binding,
        state,
        &mut facts,
        surface_propositions,
        count_derivations,
        spec_definitions,
        claim_label,
        tactic_index,
    )?;
    Ok(CheckedResourceObservation {
        successor,
        facts: facts.facts,
        added_facts: facts.added,
        observed_resource,
    })
}

#[allow(clippy::too_many_arguments)]
fn observe_composite_resource_with_facts<F: ResourcePureFacts>(
    function: &ProgramFunction,
    resource_environment: &ResourceEnvironment,
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    state: ExecutionState,
    available_pure_facts: &mut F,
    surface_propositions: &mut SurfacePropositionMap,
    count_derivations: &mut PersistentOrderedSet<Theorem>,
    spec_definitions: SpecDefinitions<'_>,
    claim_label: &str,
    tactic_index: usize,
) -> Result<(ResourceObservationSuccessor, ResourceFact), ClickError> {
    let requested_resource = lower_resource_clause_at_state(resource, parameter_binding, &state)?;
    let assumptions = available_pure_facts.assumptions().clone();
    let viewed_resource = ResourceFact::View(requested_resource.resource().clone());
    let abstract_resource = state
        .resources()
        .directly_supporting_fact(&requested_resource, &assumptions)
        .or_else(|| {
            (!matches!(resource, ResourceClause::Quantified { .. }))
                .then(|| {
                    state
                        .resources()
                        .directly_supporting_fact(&viewed_resource, &assumptions)
                })
                .flatten()
        })
        .cloned()
        .or_else(|| {
            requested_resource
                .has_proven_zero_quantity(&assumptions)
                .then(|| requested_resource.clone())
        })
        .ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `observe({})` failed: {}",
                describe_resource_clause(resource),
                describe_missing_resource_fact(
                    &requested_resource,
                    &available_pure_facts.materialize(),
                    state.resources().facts(),
                    parameter_binding,
                    &[]
                )
            ))
        })?;
    // The first lookup may have matched a supported view rather than the
    // requested owned spelling. Resolve support from the representation that
    // actually supplied this observation, so nested observations retain the
    // same exact authority.
    let observation_support = state
        .resources()
        .directly_supporting_owned_entry(&abstract_resource, &assumptions);
    if abstract_resource.is_own()
        && !abstract_resource.has_proven_zero_quantity(&assumptions)
        && observation_support.is_none()
    {
        return Err(ClickError::new(
            "`observe` requires a directly selected live owner",
        ));
    }
    let (observed_quantity, counted_resource, explicit_quantity) = match resource {
        ResourceClause::Conditional { .. } => {
            return Err(ClickError::new(
                "conditional resources cannot be observed without establishing their condition",
            ));
        }
        ResourceClause::Named { .. } => {
            return Err(ClickError::new(
                "named resources do not have counted observations",
            ));
        }
        ResourceClause::Quantified { quantity, resource } => {
            (quantity.clone(), resource.as_ref().clone(), true)
        }
        ResourceClause::Declared { .. } => (
            ContractExpression::ProgramExpression(ProgramExpression::Value(int32(1))),
            resource.clone(),
            false,
        ),
        ResourceClause::ViewMemory(_) | ResourceClause::OwnMemory(_) => {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `observe` expects a declared resource"
            )));
        }
        ResourceClause::MemoryAggregate { .. } | ResourceClause::Iterated(_) => {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `observe` expects a declared resource"
            )));
        }
    };
    // Only an authorized family has a
    // population count; any other observation records no count witness.
    let counts_population = matches!(
        &counted_resource,
        ResourceClause::Declared { name, .. }
            if resource_environment
                .get(name)
                .is_some_and(|definition| definition.is_authorized())
    );
    if abstract_resource.owned_quantity_term().is_some() {
        let count_authority = abstract_resource.clone();
        if counts_population {
            let count_witness = ClickProposition::Comparison {
                left: observed_quantity.clone(),
                operator: ComparisonOperator::LessEqual,
                right: ContractExpression::ResourceCount(Box::new(counted_resource.clone())),
            };
            let count_kernel = lower_outcome_proposition_with_assumptions(
                parameter_binding,
                &state,
                &state,
                &ProgramValue::Int32(MachineTerm::constant(0)),
                available_pure_facts.assumptions(),
                &count_witness,
                spec_definitions,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not lower `observe({})` count witness: {message}",
                    describe_resource_clause(resource)
                ))
            })?;
            {
                let checked = crate::kernel::checked_owned_resource_count_lower_bound(
                    &state,
                    &count_authority,
                    &assumptions,
                )
                .ok_or_else(|| {
                    ClickError::new("count observation cannot certify the owned quantity bound")
                })?;
                if checked != count_kernel {
                    return Err(ClickError::new(
                        "count observation does not match its checked ledger bound",
                    ));
                }
                surface_propositions.record_lowering(&count_witness, &count_kernel)?;
                available_pure_facts.insert(count_kernel);
            }
        }
        let nonnegative_witness = ClickProposition::Comparison {
            left: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(0))),
            operator: ComparisonOperator::LessEqual,
            right: observed_quantity.clone(),
        };
        let nonnegative_kernel = lower_outcome_proposition_with_assumptions(
            parameter_binding,
            &state,
            &state,
            &ProgramValue::Int32(MachineTerm::constant(0)),
            available_pure_facts.assumptions(),
            &nonnegative_witness,
            spec_definitions,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: could not lower `observe({})` quantity witness: {message}",
                describe_resource_clause(resource)
            ))
        })?;
        let nonnegative_derivation = prove_owned_resource_quantity_nonnegative(
            &state,
            &count_authority,
            &nonnegative_kernel,
            &assumptions,
        )
        .ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: kernel rejected the quantity witness for `observe({})`",
                describe_resource_clause(resource)
            ))
        })?;
        if !count_derivations.contains(&nonnegative_derivation) {
            count_derivations.insert(nonnegative_derivation);
        }
        surface_propositions.record_lowering(&nonnegative_witness, &nonnegative_kernel)?;
        available_pure_facts.insert(nonnegative_kernel);
        // The observed count is nonnegative: the kernel states that as a
        // population fact of the entry, and a certificate that cites it
        // needs this spelling of it.
        let count_nonnegative_witness = ClickProposition::Comparison {
            left: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(0))),
            operator: ComparisonOperator::LessEqual,
            right: ContractExpression::ResourceCount(Box::new(counted_resource.clone())),
        };
        if let Ok(count_nonnegative_kernel) = lower_outcome_proposition_with_assumptions(
            parameter_binding,
            &state,
            &state,
            &ProgramValue::Int32(MachineTerm::constant(0)),
            available_pure_facts.assumptions(),
            &count_nonnegative_witness,
            spec_definitions,
        ) {
            surface_propositions
                .record_lowering(&count_nonnegative_witness, &count_nonnegative_kernel)?;
        }
    }
    if counts_population {
        // A population observation names checked count/quantity facts only.
        // Member bodies remain folded, with their custody and memory unchanged.
        return Ok((
            ResourceObservationSuccessor::Legacy(Box::new(state)),
            abstract_resource,
        ));
    }
    let underlying_resource = match resource {
        ResourceClause::Quantified { resource, .. } => resource.as_ref(),
        _ => resource,
    };
    if !matches!(
        underlying_resource,
        ResourceClause::Declared {
            kind: ResourceKind::Composite,
            ..
        }
    ) {
        return Ok((
            ResourceObservationSuccessor::Legacy(Box::new(state)),
            abstract_resource,
        ));
    }
    if explicit_quantity {
        let quantity = abstract_resource
            .owned_quantity_term()
            .expect("an explicitly quantified observation lowers to owned authority");
        let positive = quantity.as_const().is_some_and(|value| value > 0)
            || holds_by_lookup_or_decision(
                &assumptions,
                &Proposition::condition_is(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterThan,
                        left: Box::new(quantity.clone()),
                        right: Box::new(MachineTerm::constant(0)),
                    },
                    true,
                ),
            );
        if !positive {
            // The count lower bound remains valid for zero or an undecided
            // nonnegative quantity. The population body, however, grants
            // authority only when the held quantity is proved positive.
            return Ok((
                ResourceObservationSuccessor::NamedCells(state.memory().clone()),
                abstract_resource,
            ));
        }
    }
    let definition = composite_resource_law_definition(
        resource_environment,
        resource,
        "observe",
        claim_label,
        tactic_index,
    )?;
    let Resource::Composite {
        arguments: resource_arguments,
        ..
    } = abstract_resource.resource()
    else {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `observe` expects a composite resource"
        )));
    };
    let mut surface_substitutions =
        resource_argument_substitutions(definition, resource, claim_label, tactic_index)?;
    extend_substitutions_with_witnesses(
        &mut surface_substitutions,
        definition,
        resource,
        parameter_binding,
        &state,
        None,
        available_pure_facts.assumptions(),
        resource_environment,
        spec_definitions,
        Some(function.composite_resource_definitions()),
    )?;
    let observation_pre_state = state.clone();
    // A viewed composite is itself a checked borrow projection.  Its children
    // are fresh occurrences, so remember the exact bundle before projecting
    // the body; equal resource terms are not sufficient to recover it later.
    let borrowed_parent_binding = if state.borrow_bindings().is_empty() {
        None
    } else {
        unique_borrowed_resource_dependency(&state, &abstract_resource)
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `observe` cannot determine which borrow backs this view: {message}"
                ))
            })?
    };
    let (memory, contained_resources, body_projected) = apply_composite_observation_law_with_facts(
        resource_environment,
        definition,
        &(resource_arguments).native_values(),
        parameter_binding,
        &state,
        &state,
        &ProgramValue::Int32(MachineTerm::constant(0)),
        available_pure_facts,
        spec_definitions,
        CompositeObservation::Explicit(&surface_substitutions),
        Some(function.composite_resource_definitions()),
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: could not observe `{}`: {message}",
            describe_resource_clause(resource)
        ))
    })?;
    let fact_state = observation_pre_state
        .clone()
        .with_materialized_memory_at_current_point(memory.clone());
    let instantiated = if body_projected {
        Some(crate::kernel::instantiate_composite_resource_facts_at(
            &abstract_resource,
            function.composite_resource_definitions(),
            &fact_state.program_point(),
            &contained_resources,
            &assumptions,
        )
        .ok_or_else(|| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: could not instantiate the registered facts of observed `{}`",
                describe_resource_clause(resource)
            ))
        })?)
    } else {
        None
    };
    if let Some(instantiated) = &instantiated {
        for fact in &instantiated.propositions {
            available_pure_facts.insert(fact.clone());
        }
        record_observed_composite_surface_facts(
            definition,
            resource,
            &surface_substitutions,
            parameter_binding,
            &observation_pre_state,
            &fact_state,
            instantiated,
            available_pure_facts,
            surface_propositions,
            spec_definitions,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: could not record observed `{}` facts: {message}",
                describe_resource_clause(resource)
            ))
        })?;
    }
    let temporary_views = borrowed_parent_binding
        .as_ref()
        .map(|binding| {
            contained_resources
                .facts()
                .iter()
                .filter(|fact| fact.is_view())
                .map(|fact| (fact.clone(), binding.clone()))
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    let mut dynamic_dependency = None;
    let temporary_view_index =
        DynamicViewDependencyIndex::new(&temporary_views, &[], available_pure_facts.assumptions());
    if let Some(instantiated) = &instantiated {
        for (_, lowered) in &instantiated.declared {
            if let Some(binding) = dynamic_body_fact_dependency(
                lowered,
                &fact_state,
                available_pure_facts.assumptions(),
                &temporary_view_index,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `observe` rejected dynamic body dependency: {message}"
                ))
            })? {
                if borrowed_parent_binding
                    .as_ref()
                    .is_none_or(|parent| !same_borrow_authority(parent, &binding))
                {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `observe` cannot package a current viewed-memory fact without its parent borrow"
                    )));
                }
                if dynamic_dependency
                    .as_ref()
                    .is_some_and(|existing| !same_borrow_authority(existing, &binding))
                {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: observed body facts depend on different stable-view authorities"
                    )));
                }
                dynamic_dependency = Some(binding);
            }
        }
    }
    Ok((
        ResourceObservationSuccessor::NamedCells(memory),
        abstract_resource,
    ))
}

#[allow(clippy::too_many_arguments)]
fn record_observed_composite_surface_facts<F: ResourcePureFacts>(
    definition: &ResourceDefinition,
    resource: &ResourceClause,
    substitutions: &BTreeMap<String, ContractExpression>,
    parameter_binding: ParameterBinding<'_>,
    pre_state: &ExecutionState,
    fact_state: &ExecutionState,
    instantiated: &crate::kernel::InstantiatedCompositeResourceFacts,
    available_pure_facts: &F,
    surface_propositions: &mut SurfacePropositionMap,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<(), String> {
    let composite_body = definition
        .composite_body()
        .expect("observing a composite resource requires a composite body");
    let Some(active) = try_select_composite_resource_body(
        definition,
        substitutions,
        parameter_binding,
        pre_state,
        fact_state,
        &ProgramValue::Int32(MachineTerm::constant(0)),
        available_pure_facts.assumptions(),
        spec_definitions,
    )?
    else {
        return Ok(());
    };
    if !active {
        return Ok(());
    }
    let parent = lower_resource_clause_at_state_with_assumptions(
        resource,
        parameter_binding,
        fact_state,
        None,
        available_pure_facts.assumptions(),
    )
    .map_err(|error| error.raw_summary().to_string())?;
    let parent_subject = resource_clause_subject(resource);
    let mut owned_children = Vec::new();
    for contained in composite_body.contains() {
        if matches!(contained, ResourceClause::Iterated(_)) {
            // An iterated clause has no `contains(...)` or `separate(...)`
            // spelling; its element facts come from indexed `unfold`.
            continue;
        }
        let contained =
            instantiate_resource_clause(contained, substitutions).map_err(|message| {
                format!(
                    "could not instantiate resource `{}` contained resource: {message}",
                    definition.name()
                )
            })?;
        let lowered = lower_resource_clause_at_state_with_assumptions(
            &contained,
            parameter_binding,
            fact_state,
            None,
            available_pure_facts.assumptions(),
        )
        .map_err(|error| error.raw_summary().to_string())?;
        if let Some(child) = lowered.owned_resource() {
            let child_subject = resource_clause_subject(&contained);
            surface_propositions
                .record_lowering(
                    &ClickProposition::Contains {
                        parent: parent_subject.clone(),
                        child: child_subject.clone(),
                    },
                    &Proposition::ResourceContains {
                        parent: Box::new(parent.resource().clone()),
                        child: Box::new(child.clone()),
                    },
                )
                .map_err(|error| error.raw_summary().to_string())?;
            owned_children.push((child.clone(), child_subject));
        }
        let (ResourceClause::ViewMemory(segment) | ResourceClause::OwnMemory(segment)) = &contained
        else {
            continue;
        };
        if let Some(range) = lowered
            .memory_view_range()
            .or_else(|| lowered.memory_own_range())
        {
            let kernel = memory_range_loadable_atom_prop(fact_state.memory(), range);
            surface_propositions
                .record_lowering(
                    &ClickProposition::Loadable {
                        segment: segment.clone(),
                    },
                    &kernel,
                )
                .map_err(|error| error.raw_summary().to_string())?;
        }
    }
    for left_index in 0..owned_children.len() {
        for (right, right_subject) in &owned_children[left_index + 1..] {
            let (left, left_subject) = &owned_children[left_index];
            surface_propositions
                .record_lowering(
                    &ClickProposition::Separate {
                        left: left_subject.clone(),
                        right: right_subject.clone(),
                    },
                    &Proposition::ResourceSeparate {
                        left: Box::new(left.clone()),
                        right: Box::new(right.clone()),
                    },
                )
                .map_err(|error| error.raw_summary().to_string())?;
        }
    }
    for (index, kernel) in &instantiated.declared {
        let fact = composite_body.facts().get(*index).ok_or_else(|| {
            format!(
                "registered resource `{}` fact index {index} has no source",
                definition.name()
            )
        })?;
        let surface = substitute_click_proposition(fact, substitutions).map_err(|message| {
            format!(
                "could not instantiate resource `{}` fact: {message}",
                definition.name()
            )
        })?;
        surface_propositions
            .record_lowering(&surface, kernel)
            .map_err(|error| error.raw_summary().to_string())?;
    }
    Ok(())
}

fn resource_clause_subject(resource: &ResourceClause) -> ResourceSubject {
    match resource {
        ResourceClause::Conditional { resource, .. } => resource_clause_subject(resource),
        ResourceClause::Named { resource, .. } => resource_clause_subject(resource),
        ResourceClause::Quantified { resource, .. } => resource_clause_subject(resource),
        ResourceClause::ViewMemory(segment) | ResourceClause::OwnMemory(segment) => {
            ResourceSubject::Memory(segment.clone())
        }
        ResourceClause::MemoryAggregate { segments, .. } => ResourceSubject::Memory(
            segments
                .first()
                .expect("aggregate resource clause has at least one segment")
                .clone(),
        ),
        // Iterated ownership has no resource-subject spelling; callers skip it
        // before asking, and the element range is the closest description.
        ResourceClause::Iterated(clause) => ResourceSubject::Memory(clause.element.clone()),
        ResourceClause::Declared {
            kind,
            name,
            arguments,
            parameter_types,
            ..
        } => ResourceSubject::Declared {
            kind: *kind,
            name: name.clone(),
            arguments: arguments.clone(),
            parameter_types: parameter_types.clone(),
        },
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn record_initial_composite_surface_facts(
    resource_environment: &ResourceEnvironment,
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    available_pure_facts: &PureFactStore,
    surface_propositions: &mut SurfacePropositionMap,
    spec_definitions: SpecDefinitions<'_>,
    active_resources: &mut BTreeSet<String>,
) -> Result<(), String> {
    let assumptions = available_pure_facts.assumptions().clone();
    let ResourceClause::Declared { name, .. } = resource else {
        return Ok(());
    };
    let Some(definition) = resource_environment.get(name) else {
        return Ok(());
    };
    let Some(body) = definition.composite_body() else {
        return Ok(());
    };
    if !active_resources.insert(name.clone()) {
        return Ok(());
    }
    let result = (|| {
        let mut substitutions =
            resource_argument_substitutions(definition, resource, "initial resource projection", 0)
                .map_err(|error| error.raw_summary().to_string())?;
        extend_substitutions_with_witnesses(
            &mut substitutions,
            definition,
            resource,
            parameter_binding,
            state,
            None,
            &assumptions,
            resource_environment,
            spec_definitions,
            None,
        )
        .map_err(|error| error.raw_summary().to_string())?;
        let Some(true) = try_select_composite_resource_body(
            definition,
            &substitutions,
            parameter_binding,
            state,
            state,
            &ProgramValue::Int32(MachineTerm::constant(0)),
            &assumptions,
            spec_definitions,
        )?
        else {
            return Ok(());
        };
        for fact in body.facts() {
            let surface = substitute_click_proposition(fact, &substitutions)?;
            if !matches!(surface, ClickProposition::Separate { .. }) {
                continue;
            }
            let kernel = lower_outcome_proposition(
                parameter_binding,
                state,
                state,
                &ProgramValue::Int32(MachineTerm::constant(0)),
                available_pure_facts,
                &surface,
                spec_definitions,
            )?;
            if available_pure_facts.contains_presented(&kernel) {
                surface_propositions
                    .record_lowering(&surface, &kernel)
                    .map_err(|error| error.raw_summary().to_string())?;
            }
        }
        Ok(())
    })();
    active_resources.remove(name);
    result
}

fn project_held_resource_observable_facts(
    resource_environment: &ResourceEnvironment,
    resource: &ResourceFact,
    parameter_binding: ParameterBinding<'_>,
    pre_state: &ExecutionState,
    state: &ExecutionState,
    result: &ProgramValue,
    available_pure_facts: &mut ProofResourcePureFacts,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<SymbolicMemory, String> {
    let (name, resource_arguments) = match resource.resource() {
        Resource::Footprint(_) | Resource::Parameter(_) | Resource::Emp | Resource::Star(_) => {
            return Ok(state.memory().clone());
        }
        Resource::Composite { name, arguments } => (name, arguments),
        Resource::Memory(_)
        | Resource::Token { .. }
        | Resource::Instance(_)
        | Resource::ConditionalMutexGuard(_)
        | Resource::MutexGuard(_)
        | Resource::MutexLive(_)
        | Resource::MutexUse(_)
        | Resource::Publication(_)
        | Resource::PopulationAuthority(_)
        | Resource::Iterated(_) => {
            return Ok(state.memory().clone());
        }
    };
    let Some(definition) = resource_environment.get(name) else {
        return Ok(state.memory().clone());
    };
    // `amount of R(..)` holds `amount` instances of `R`'s body, so its body
    // describes an instance only where `amount > 0` is known; with zero there
    // is none, and its facts need not hold. `observe` makes the same check.
    if let Some(quantity) = resource.owned_quantity_term()
        && !owned_quantity_is_positive(quantity, available_pure_facts.assumptions())
    {
        return Ok(state.memory().clone());
    }
    apply_composite_observation_law_with_facts(
        resource_environment,
        definition,
        &(resource_arguments).native_values(),
        parameter_binding,
        pre_state,
        state,
        result,
        available_pure_facts,
        spec_definitions,
        CompositeObservation::Implicit,
        None,
    )
    .map(|(memory, _, _)| memory)
}

/// Whether an owned resource's quantity is known to be positive: a constant
/// read as a signed `int32`, as `fold` reads one, or one the kernel's
/// condition decision settles.
fn owned_quantity_is_positive(quantity: &MachineTerm, assumptions: &PureFactContext) -> bool {
    quantity.as_const().is_some_and(|value| (value as i32) > 0)
        || holds_by_lookup_or_decision(
            assumptions,
            &Proposition::condition_is(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterThan,
                    left: Box::new(quantity.clone()),
                    right: Box::new(MachineTerm::constant(0)),
                },
                true,
            ),
        )
}

#[allow(clippy::too_many_arguments)]
fn try_select_composite_resource_body(
    definition: &ResourceDefinition,
    substitutions: &BTreeMap<String, ContractExpression>,
    parameter_binding: ParameterBinding<'_>,
    pre_state: &ExecutionState,
    state: &ExecutionState,
    result: &ProgramValue,
    assumptions: &PureFactContext,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Option<bool>, String> {
    let Some(condition) = definition
        .composite_body()
        .and_then(CompositeResourceBody::condition)
    else {
        return Ok(Some(true));
    };
    let condition = substitute_click_proposition(condition, substitutions).map_err(|message| {
        format!(
            "could not instantiate resource `{}` condition: {message}",
            definition.name()
        )
    })?;
    let lowered = lower_outcome_proposition_with_assumptions(
        parameter_binding,
        pre_state,
        state,
        result,
        assumptions,
        &condition,
        spec_definitions,
    )
    .map_err(|message| {
        format!(
            "could not lower resource `{}` condition `{}`: {message}",
            definition.name(),
            describe_click_proposition(&condition)
        )
    })?;
    let proves_condition = |proposition: &Proposition| match proposition {
        Proposition::ConditionIs(condition, value) => {
            assumptions.proves_condition_exact(condition.native_compat(), *value)
                || assumptions.decide(condition.native_compat()) == Some(*value)
        }
        Proposition::Not(body) => match body.as_ref() {
            Proposition::ConditionIs(condition, value) => {
                assumptions.proves_condition_exact(condition.native_compat(), !*value)
                    || assumptions.decide(condition.native_compat()) == Some(!*value)
            }
            _ => false,
        },
        _ => holds_by_lookup_or_decision(assumptions, proposition),
    };
    if proves_condition(&lowered) {
        return Ok(Some(true));
    }
    let negated = match &lowered {
        Proposition::ConditionIs(condition, value) => {
            Proposition::condition_is(condition.clone(), !value)
        }
        Proposition::Not(body) => body.as_ref().clone(),
        proposition => Proposition::Not(Box::new(proposition.clone())),
    };
    if proves_condition(&negated) {
        return Ok(Some(false));
    }
    let is_atomic_condition = matches!(&lowered, Proposition::ConditionIs(_, _))
        || matches!(
            &lowered,
            Proposition::Not(body)
                if matches!(body.as_ref(), Proposition::ConditionIs(_, _))
        );
    if is_atomic_condition {
        // Conditional resource bodies are intentionally opaque while their
        // guard is undecided. A general contradiction search here can recurse
        // through every materialized heap state in a recursive resource.
        return Ok(None);
    }
    if fact_conflicts_with_assumptions(&lowered, assumptions) {
        return Ok(Some(false));
    }
    Ok(None)
}

#[allow(clippy::too_many_arguments)]
fn composite_resource_body_is_active_with_assumptions(
    definition: &ResourceDefinition,
    substitutions: &BTreeMap<String, ContractExpression>,
    parameter_binding: ParameterBinding<'_>,
    pre_state: &ExecutionState,
    state: &ExecutionState,
    result: &ProgramValue,
    assumptions: &PureFactContext,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<bool, String> {
    try_select_composite_resource_body(
        definition,
        substitutions,
        parameter_binding,
        pre_state,
        state,
        result,
        assumptions,
        spec_definitions,
    )?
    .ok_or_else(|| {
        format!(
            "resource `{}` condition is undecided: prove it or its negation before using its body",
            definition.name()
        )
    })
}

enum CompositeObservation<'a> {
    Explicit(&'a BTreeMap<String, ContractExpression>),
    Implicit,
}

/// Applies the non-consuming observation law declared by a composite body.
/// The kernel algebra handles the folded resource fact itself; Click owns this
/// definitional layer because it requires source-level substitution and fact
/// lowering.
#[allow(clippy::too_many_arguments)]
fn apply_composite_observation_law_with_facts<F: ResourcePureFacts>(
    resource_environment: &ResourceEnvironment,
    definition: &ResourceDefinition,
    resource_arguments: &[AlgebraicValue],
    parameter_binding: ParameterBinding<'_>,
    pre_state: &ExecutionState,
    state: &ExecutionState,
    result: &ProgramValue,
    available_pure_facts: &mut F,
    spec_definitions: SpecDefinitions<'_>,
    observation: CompositeObservation<'_>,
    compiled_definitions: Option<&[CompositeResourceDefinition]>,
) -> Result<(SymbolicMemory, ResourceContext, bool), String> {
    let Some(composite_body) = definition.composite_body() else {
        return Ok((state.memory().clone(), ResourceContext::new(), false));
    };

    let substitutions = resource_value_substitutions_with_witnesses(
        definition,
        resource_arguments,
        state.memory(),
        state.resources(),
        available_pure_facts.assumptions(),
        resource_environment,
        spec_definitions,
        compiled_definitions,
    )
    .map_err(|message| {
        format!(
            "could not instantiate resource `{}` facts: {message}",
            definition.name()
        )
    })?;
    let Some(body_active) = try_select_composite_resource_body(
        definition,
        &substitutions,
        parameter_binding,
        pre_state,
        state,
        result,
        available_pure_facts.assumptions(),
        spec_definitions,
    )?
    else {
        if let CompositeObservation::Explicit(substitutions) = observation {
            let guard = composite_body
                .condition()
                .expect("only a guarded body can be undecided");
            let guard = substitute_click_proposition(guard, substitutions)?;
            return Err(format!(
                "guard `{}` is undecided: prove it or its negation before observing the body",
                describe_click_proposition(&guard)
            ));
        }
        return Ok((state.memory().clone(), ResourceContext::new(), false));
    };
    if !body_active {
        return Ok((state.memory().clone(), ResourceContext::new(), false));
    }
    let (memory, contained_resources) = instantiate_composite_resource_body_resources(
        definition.name(),
        composite_body,
        &substitutions,
        parameter_binding,
        state,
        &available_pure_facts
            .assumptions()
            .clone()
            .assume_entry_clause_spans()
            .assume_held_resource_domains(),
    )?;
    let owned_body_resources = contained_resources
        .facts()
        .iter()
        .filter(|fact| fact.is_own())
        .collect::<Vec<_>>();
    if !owned_body_resources.is_empty()
        && owned_body_resources.iter().all(|fact| {
            state
                .resources()
                .directly_supporting_fact(fact, available_pure_facts.assumptions())
                .is_some()
        })
    {
        // `with` retains the folded head for contract accounting while
        // exposing the unique owned body. Until that body is closed, do
        // not re-project its invariant at a newer memory/count state.
        return Ok((memory, ResourceContext::new(), false));
    }
    let mut fact_state = state
        .clone()
        .with_materialized_memory_at_current_point(memory.clone());
    if contained_resources
        .facts()
        .iter()
        .any(|child| matches!(child.resource(), Resource::PopulationAuthority(_)))
    {
        let owner = ResourceFact::own(Resource::Composite {
            name: definition.name().to_owned(),
            arguments: resource_arguments.to_vec().into(),
        });
        if !state.resources().contains_exact_representation(&owner) {
            return Err("Requires the owned authority control resource".into());
        }
        // Resource facts are read under the declared body. This temporary
        // state only lowers the fact; it does not publish body ownership.
        fact_state = fact_state.with_resource_context(contained_resources.clone());
    }

    append_composite_definition_observable_facts(
        definition,
        composite_body,
        &Resource::Composite {
            name: definition.name().to_string(),
            arguments: resource_arguments.to_vec().into(),
        },
        &substitutions,
        &contained_resources,
        parameter_binding,
        pre_state,
        &fact_state,
        result,
        available_pure_facts,
        spec_definitions,
        matches!(observation, CompositeObservation::Implicit),
    )?;
    Ok((memory, contained_resources, true))
}

fn append_composite_definition_observable_facts<F: ResourcePureFacts>(
    definition: &ResourceDefinition,
    composite_body: &CompositeResourceBody,
    parent_resource: &Resource,
    substitutions: &BTreeMap<String, ContractExpression>,
    contained_resources: &ResourceContext,
    parameter_binding: ParameterBinding<'_>,
    pre_state: &ExecutionState,
    fact_state: &ExecutionState,
    result: &ProgramValue,
    propositions: &mut F,
    spec_definitions: SpecDefinitions<'_>,
    lower_declared_source_facts: bool,
) -> Result<(), String> {
    append_resource_context_observable_facts_with_store(contained_resources, propositions);

    append_composite_resource_relation_facts_with_store(
        parent_resource,
        contained_resources,
        propositions,
    );

    append_composite_resource_loadable_facts(
        definition,
        composite_body,
        substitutions,
        parameter_binding,
        fact_state,
        propositions,
    )?;

    if lower_declared_source_facts {
        append_composite_resource_declared_facts(
            definition,
            composite_body,
            substitutions,
            contained_resources,
            parameter_binding,
            pre_state,
            fact_state,
            result,
            propositions,
            spec_definitions,
        )?;
    }
    Ok(())
}

fn append_composite_resource_relation_facts_with_store<F: ResourcePureFacts>(
    parent_resource: &Resource,
    contained_resources: &ResourceContext,
    propositions: &mut F,
) {
    let owned_children = contained_resources
        .facts()
        .iter()
        .filter_map(ResourceFact::owned_resource)
        .cloned()
        .collect::<Vec<_>>();
    for child in &owned_children {
        let proposition = Proposition::ResourceContains {
            parent: Box::new(parent_resource.clone()),
            child: Box::new(child.clone()),
        };
        propositions.insert(proposition);
    }
    if owned_children.len() >= 2 {
        // Keep ownership-derived separation lazy. The compact carrier is
        // checked by the kernel when a particular member pair is requested;
        // publishing every pair here makes one composite unfold quadratic.
        let owned_context = ResourceContext::new_with_equalities(propositions.assumptions())
            .unchecked_with_facts(
                contained_resources
                    .facts()
                    .iter()
                    .filter(|fact| fact.is_own())
                    .cloned(),
            );
        propositions.insert(Proposition::ResourceComposition(owned_context));
    }
}

fn append_composite_resource_loadable_facts<F: ResourcePureFacts>(
    definition: &ResourceDefinition,
    composite_body: &CompositeResourceBody,
    substitutions: &BTreeMap<String, ContractExpression>,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    propositions: &mut F,
) -> Result<(), String> {
    for contained in composite_body.contains() {
        let contained = instantiate_resource_clause(contained, substitutions).map_err(|message| {
            format!(
                "could not instantiate resource `{}` contained resource for viewability: {message}",
                definition.name()
            )
        })?;
        append_resource_clause_loadable_fact_with_store(
            &contained,
            parameter_binding,
            state,
            propositions,
        )
        .map_err(|error| {
            format!(
                "could not project resource `{}` contained `{}` viewability: {}",
                definition.name(),
                describe_resource_clause(&contained),
                error.raw_summary()
            )
        })?;
    }
    Ok(())
}

fn append_resource_clause_loadable_fact_with_store<F: ResourcePureFacts>(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    propositions: &mut F,
) -> Result<(), ClickError> {
    let Some(ranges) = resource_clause_memory_ranges_at_state(resource, parameter_binding, state)?
    else {
        return Ok(());
    };
    for range in ranges {
        for guard in crate::kernel::admitted_memory_range_span_facts(&range) {
            propositions.insert(guard);
        }
    }
    if let Some(proposition) =
        resource_clause_loadable_prop_at_state(resource, parameter_binding, state)?
    {
        propositions.insert(proposition);
    }
    Ok(())
}

pub(super) fn append_lowered_resource_clause_loadable_fact(
    resource: &ResourceClause,
    lowered: &ResourceFact,
    state: &ExecutionState,
    propositions: &mut Vec<Proposition>,
) {
    let ResourceClause::ViewMemory(_) = resource else {
        return;
    };
    let Some(range) = lowered
        .memory_view_range()
        .or_else(|| lowered.memory_own_range())
    else {
        return;
    };
    let proposition = memory_range_loadable_prop(state.memory(), range);
    if !propositions.contains(&proposition) {
        propositions.push(proposition);
    }
    for guard in crate::surface::memory_range_loadable_guards(range) {
        if !propositions.contains(&guard) {
            propositions.push(guard);
        }
    }
}

fn append_composite_resource_declared_facts<F: ResourcePureFacts>(
    definition: &ResourceDefinition,
    composite_body: &CompositeResourceBody,
    substitutions: &BTreeMap<String, ContractExpression>,
    contained_resources: &ResourceContext,
    parameter_binding: ParameterBinding<'_>,
    pre_state: &ExecutionState,
    fact_state: &ExecutionState,
    result: &ProgramValue,
    propositions: &mut F,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<(), String> {
    for fact in composite_body.facts() {
        let fact = substitute_click_proposition(fact, substitutions).map_err(|message| {
            format!(
                "could not instantiate resource `{}` fact: {message}",
                definition.name()
            )
        })?;
        let (lowered, facts) = lower_outcome_proposition_with_auxiliary_facts(
            parameter_binding,
            pre_state,
            fact_state,
            result,
            propositions.assumptions(),
            &fact,
            spec_definitions,
        )
        .map_err(|message| {
            format!(
                "could not lower resource `{}` pure fact `{}`: {message}\n  pure facts: {}\n  resource facts: {}",
                definition.name(),
                describe_click_proposition(&fact),
                describe_pure_facts(&propositions.materialize()),
                render_resource_facts_diagnostic(contained_resources.facts(), parameter_binding)
            )
        })?;
        for fact in facts {
            propositions.insert(fact);
        }
        propositions.insert(lowered);
    }
    Ok(())
}

fn append_resource_context_observable_facts_with_store<F: ResourcePureFacts>(
    resources: &ResourceContext,
    propositions: &mut F,
) {
    let facts = resources.observable_facts_assuming_valid(propositions.assumptions());
    for proposition in facts {
        propositions.insert(proposition);
    }
}

pub(super) fn resource_context_observable_facts_for_proof(
    resources: &ResourceContext,
    facts: PureFactStore,
) -> PureFactStore {
    let mut facts = ProofResourcePureFacts::new(facts);
    append_resource_context_observable_facts_with_store(resources, &mut facts);
    facts.facts
}

fn describe_resource_context_validity_error(
    error: ResourceContextValidityError,
    parameter_binding: ParameterBinding<'_>,
) -> String {
    match error {
        ResourceContextValidityError::UnsupportedOwnershipBoundary => error.to_string(),
        ResourceContextValidityError::UnestablishedOwnedBoundary(required) => {
            let mut labels = crate::surface::proof_diagnostics::render::MemoryStateLabels::naming(parameter_binding);
            format!("symbolic ownership boundary needs an explicit proof of {}",
                crate::surface::proof_diagnostics::render::render_proposition_labeled(&required, &mut labels))
        }
        ResourceContextValidityError::InvalidExclusiveAccess(_) => {
            "field-bearing resource instances and mutex guards require exclusive ownership with quantity one".into()
        }
        ResourceContextValidityError::DuplicateOwnedResourceFact(resource) => {
            format!(
                "duplicate resource fact `{}`",
                render_resource_fact_diagnostic(&resource, parameter_binding)
            )
        }
        ResourceContextValidityError::OverlappingOwnedMemoryResources { left, right } => {
            format!(
                "overlapping owned memory resource facts `owns {}` and `owns {}`",
                describe_memory_range(&left, parameter_binding),
                describe_memory_range(&right, parameter_binding)
            )
        }
    }
}

fn materialize_composite_resource_memory(
    name: &str,
    composite_body: &CompositeResourceBody,
    substitutions: &BTreeMap<String, ContractExpression>,
    parameter_binding: ParameterBinding<'_>,
    mut state: ExecutionState,
    assumptions: &PureFactContext,
) -> Result<ExecutionState, String> {
    // This pass names cells only. Tokens and nested resource heads cannot
    // materialize a cell, and their formation belongs to resource admission,
    // not to preparing the memory in which that admission will be checked.
    // All cells exposed by this body are named from its starting view.
    // Later clauses can read the cells exposed by earlier clauses.
    let naming_point = state.program_point();
    for contained in composite_body.contains() {
        if !matches!(
            contained,
            ResourceClause::OwnMemory(_) | ResourceClause::ViewMemory(_)
        ) {
            continue;
        }
        let contained =
            instantiate_resource_clause(contained, substitutions).map_err(|message| {
                format!("could not instantiate composite resource `{name}` body: {message}")
            })?;
        let lowered = lower_resource_clause_at_state_with_assumptions(
            &contained,
            parameter_binding,
            &state,
            None,
            assumptions,
        )
        .map_err(|error| {
            format!(
                "could not name resource `{name}` cells: {}",
                error.raw_summary()
            )
        })?;
        let memory = materialize_composite_resource_cells_from_state(
            state.memory().clone(),
            &naming_point,
            &contained,
            &lowered,
            parameter_binding.parameters,
            names_plain_scalar_body_at_entry(composite_body),
        );
        state = state.with_materialized_memory_at_current_point(memory);
    }
    Ok(state)
}

/// Instantiates the resource-state side of a composite definition. The result
/// is provisional until the caller composes it with assumptions and checks
/// validity through `ResourceContext`.
pub(in crate::surface) fn instantiate_composite_resource_body_resources(
    name: &str,
    composite_body: &CompositeResourceBody,
    substitutions: &BTreeMap<String, ContractExpression>,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    assumptions: &PureFactContext,
) -> Result<(SymbolicMemory, ResourceContext), String> {
    let mut resources = ResourceContext::new();
    let mut clause_base = ExecutionState::new();
    clause_base.keep_memory_of(state);
    // Keep the complete pending log for the caller's observation check.
    // Each clause sees that log as a proof-only view at the same point.
    let mut memory = state.memory().clone();
    // Every cell exposed by this one body expansion names the value it had
    // in the state before the expansion began.  Lower clauses against the
    // progressively materialized memory so a later clause can still address
    // through a cell an earlier clause exposed, but do not let those cached
    // cells become a new load-naming epoch.  The checked resource rewrite
    // independently validates every added cell against this same entry
    // state.
    let naming_point = state.program_point();
    for contained in composite_body.contains() {
        let contained =
            instantiate_resource_clause(contained, substitutions).map_err(|message| {
                format!("could not instantiate composite resource `{name}` body: {message}")
            })?;
        let clause_state = clause_base
            .clone()
            .with_materialized_memory_at_current_point(memory.clone());
        let lowered = lower_resource_clause_at_state_with_assumptions(
            &contained,
            parameter_binding,
            &clause_state,
            None,
            assumptions,
        )
        .map_err(|error| {
            format!(
                "could not lower resource `{name}` contained `{}`: {}\n  {}",
                describe_resource_clause(&contained),
                error.raw_summary(),
                describe_available_facts(&[], resources.facts(), parameter_binding, &[])
            )
        })?;
        memory = materialize_composite_resource_cells_from_state(
            memory,
            &naming_point,
            &contained,
            &lowered,
            parameter_binding.parameters,
            names_plain_scalar_body_at_entry(composite_body),
        );
        // This composite-body instantiation path has no fact assumptions yet.
        // Projection/packing paths check composition once assumptions are
        // available.
        resources = resources.unchecked_with_fact(lowered);
    }
    Ok((memory, resources))
}

fn resource_value_substitutions(
    definition: &ResourceDefinition,
    arguments: &[AlgebraicValue],
) -> Result<BTreeMap<String, ContractExpression>, String> {
    if definition.parameters().len() != arguments.len() {
        return Err(format!(
            "resource `{}` expects {} argument(s), got {}",
            definition.name(),
            definition.parameters().len(),
            arguments.len()
        ));
    }
    definition
        .parameters()
        .iter()
        .zip(arguments)
        .map(|(parameter, argument)| {
            let argument = argument
                .as_program_value()
                .ok_or_else(|| "algebraic resource bodies are not supported yet".to_string())?;
            Ok((
                parameter.name().to_string(),
                ContractExpression::ProgramExpression(ProgramExpression::Value(argument.clone())),
            ))
        })
        .collect::<Result<_, String>>()
}

/// Value substitutions for a held composite resource fact, with its
/// existential witnesses bound to the values the kernel binds them to under
/// `memory` and `assumptions`.
fn resource_value_substitutions_with_witnesses(
    definition: &ResourceDefinition,
    arguments: &[AlgebraicValue],
    memory: &SymbolicMemory,
    resources: &ResourceContext,
    assumptions: &PureFactContext,
    resource_environment: &ResourceEnvironment,
    spec_definitions: SpecDefinitions<'_>,
    compiled_definitions: Option<&[CompositeResourceDefinition]>,
) -> Result<BTreeMap<String, ContractExpression>, String> {
    let mut substitutions = resource_value_substitutions(definition, arguments)?;
    let Some(body) = definition.composite_body() else {
        return Ok(substitutions);
    };
    if body.witnesses().is_empty() {
        return Ok(substitutions);
    }
    let owned_definitions;
    let definitions = if let Some(definitions) = compiled_definitions {
        definitions
    } else {
        owned_definitions = crate::surface::verification::composite_resource_definitions(
            resource_environment,
            spec_definitions,
        )
        .map_err(|error| error.raw_summary().to_string())?;
        &owned_definitions
    };
    let fact = ResourceFact::own(Resource::Composite {
        name: definition.name().to_string(),
        arguments: arguments.to_vec().into(),
    });
    let values = crate::kernel::composite_resource_witness_values(
        &fact,
        definitions,
        memory,
        resources,
        assumptions,
    )
    .ok_or_else(|| {
        format!(
            "could not bind the witnesses of resource `{}`",
            definition.name()
        )
    })?;
    for (witness, value) in body.witnesses().iter().zip(values) {
        substitutions.insert(
            witness.name().to_string(),
            ContractExpression::ProgramExpression(ProgramExpression::Value(value)),
        );
    }
    Ok(substitutions)
}

pub(super) struct CheckedResourceUnfold {
    /// Facts this unfold publishes, including facts already known locally.
    pub(super) published_facts: Vec<Proposition>,
    pub(super) state: ExecutionState,
    pub(super) facts: PureFactStore,
    pub(super) added_facts: Vec<Proposition>,
    pub(super) selected: ResourceFact,
    pub(super) body_was_already_exposed: bool,
}

#[allow(clippy::too_many_arguments)]
pub(super) fn unfold_composite_resource_for_proof(
    resource_environment: &ResourceEnvironment,
    resource: &ResourceClause,
    source_resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    state: ExecutionState,
    facts: PureFactStore,
    surface_propositions: &mut SurfacePropositionMap,
    spec_definitions: SpecDefinitions<'_>,
    claim_label: &str,
    tactic_index: usize,
    materialize_memory: bool,
) -> Result<CheckedResourceUnfold, ClickError> {
    unfold_composite_resource_for_proof_with_access(
        resource_environment,
        resource,
        source_resource,
        parameter_binding,
        state,
        facts,
        surface_propositions,
        spec_definitions,
        claim_label,
        tactic_index,
        ResourceBodyAccess::Finalize,
        materialize_memory,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn open_composite_resource_for_proof(
    resource_environment: &ResourceEnvironment,
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    state: ExecutionState,
    facts: PureFactStore,
    surface_propositions: &mut SurfacePropositionMap,
    spec_definitions: SpecDefinitions<'_>,
    claim_label: &str,
    tactic_index: usize,
) -> Result<CheckedResourceUnfold, ClickError> {
    unfold_composite_resource_for_proof_with_access(
        resource_environment,
        resource,
        resource,
        parameter_binding,
        state,
        facts,
        surface_propositions,
        spec_definitions,
        claim_label,
        tactic_index,
        ResourceBodyAccess::Open,
        true,
    )
}

#[allow(clippy::too_many_arguments)]
fn unfold_composite_resource_for_proof_with_access(
    resource_environment: &ResourceEnvironment,
    resource: &ResourceClause,
    source_resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    state: ExecutionState,
    facts: PureFactStore,
    surface_propositions: &mut SurfacePropositionMap,
    spec_definitions: SpecDefinitions<'_>,
    claim_label: &str,
    tactic_index: usize,
    access: ResourceBodyAccess,
    materialize_memory: bool,
) -> Result<CheckedResourceUnfold, ClickError> {
    let mut facts = ProofResourcePureFacts::new(facts);
    let unfolded = unfold_composite_resource_with_facts(
        resource_environment,
        resource,
        source_resource,
        parameter_binding,
        state,
        &mut facts,
        surface_propositions,
        spec_definitions,
        claim_label,
        tactic_index,
        access,
        materialize_memory,
    )?;
    Ok(CheckedResourceUnfold {
        published_facts: facts.published,
        state: unfolded.state,
        facts: facts.facts,
        added_facts: facts.added,
        selected: unfolded.selected,
        body_was_already_exposed: unfolded.body_was_already_exposed,
    })
}

#[allow(clippy::too_many_arguments)]
/// The values a held declared resource's `let ... where` witnesses take at
/// `state`, by name, as an unfold of it binds them; empty when its body
/// declares none.
pub(super) fn declared_resource_witness_values(
    resource_environment: &ResourceEnvironment,
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    assumptions: &PureFactContext,
    spec_definitions: SpecDefinitions<'_>,
    claim_label: &str,
    tactic_index: usize,
) -> Result<Vec<(String, ProgramValue)>, ClickError> {
    let definition = composite_resource_law_definition(
        resource_environment,
        resource,
        "unfold",
        claim_label,
        tactic_index,
    )?;
    let Some(body) = definition.composite_body() else {
        return Ok(Vec::new());
    };
    let mut substitutions = BTreeMap::new();
    extend_substitutions_with_witnesses(
        &mut substitutions,
        definition,
        resource,
        parameter_binding,
        state,
        None,
        assumptions,
        resource_environment,
        spec_definitions,
        None,
    )?;
    Ok(body
        .witnesses()
        .iter()
        .filter_map(|witness| match substitutions.get(witness.name()) {
            Some(ContractExpression::ProgramExpression(ProgramExpression::Value(value))) => {
                Some((witness.name().to_string(), value.clone()))
            }
            _ => None,
        })
        .collect())
}

/// Whether the kernel's condition decision settles `required`: a condition,
/// a negated condition, or a conjunction of them.
fn decided_by_kernel_condition_decision(
    assumptions: &PureFactContext,
    required: &Proposition,
) -> bool {
    match required {
        Proposition::And(left, right) => {
            decided_by_kernel_condition_decision(assumptions, left)
                && decided_by_kernel_condition_decision(assumptions, right)
        }
        Proposition::ConditionIs(condition, value) => {
            assumptions.decide(condition.native_compat()) == Some(*value)
        }
        Proposition::Not(body) => matches!(
            body.as_ref(),
            Proposition::ConditionIs(condition, value)
                if assumptions.decide(condition.native_compat()) == Some(!*value)
        ),
        _ => false,
    }
}

thread_local! {
    static UNFOLD_WITNESS_NAMES: std::cell::RefCell<Vec<(String, String)>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// Runs an unfold whose `let ... where` witnesses the proof names, as
/// `(witness, proof name)` pairs, so its published body facts are spelled
/// with those names.
pub(super) fn with_unfold_witness_names<R>(
    names: &[(String, String)],
    operation: impl FnOnce() -> R,
) -> R {
    struct Restore(Vec<(String, String)>);
    impl Drop for Restore {
        fn drop(&mut self) {
            let previous = std::mem::take(&mut self.0);
            UNFOLD_WITNESS_NAMES.with(|names| *names.borrow_mut() = previous);
        }
    }
    let _restore = Restore(UNFOLD_WITNESS_NAMES.with(|current| current.replace(names.to_vec())));
    operation()
}

fn unfold_composite_resource_with_facts<F: ResourcePureFacts>(
    resource_environment: &ResourceEnvironment,
    resource: &ResourceClause,
    source_resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    mut state: ExecutionState,
    available_pure_facts: &mut F,
    surface_propositions: &mut SurfacePropositionMap,
    spec_definitions: SpecDefinitions<'_>,
    claim_label: &str,
    tactic_index: usize,
    access: ResourceBodyAccess,
    materialize_memory: bool,
) -> Result<UnfoldedCompositeResource, ClickError> {
    let definition = composite_resource_law_definition(
        resource_environment,
        resource,
        "unfold",
        claim_label,
        tactic_index,
    )?;
    let composite_body = definition
        .composite_body()
        .expect("composite_resource_law_definition should require a composite body");
    let mut substitutions =
        resource_argument_substitutions(definition, resource, claim_label, tactic_index)?;
    extend_substitutions_with_witnesses(
        &mut substitutions,
        definition,
        resource,
        parameter_binding,
        &state,
        None,
        available_pure_facts.assumptions(),
        resource_environment,
        spec_definitions,
        None,
    )?;
    let mut spelling_substitutions = substitutions.clone();
    spelling_substitutions.extend(resource_argument_substitutions(
        definition,
        source_resource,
        claim_label,
        tactic_index,
    )?);
    // A witness the proof names here, `let { w: name } = unfold(...)`, is
    // written by that name in the body facts this unfold publishes.
    UNFOLD_WITNESS_NAMES.with(|names| {
        for (witness, name) in names.borrow().iter() {
            if spelling_substitutions.contains_key(witness) {
                spelling_substitutions.insert(
                    witness.clone(),
                    ContractExpression::ProgramExpression(ProgramExpression::Variable(
                        name.as_str().into(),
                    )),
                );
            }
        }
    });
    let body_active = composite_resource_body_is_active_with_assumptions(
        definition,
        &substitutions,
        parameter_binding,
        &state,
        &state,
        &ProgramValue::Int32(MachineTerm::constant(0)),
        available_pure_facts.assumptions(),
        spec_definitions,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: could not select `unfold({})` body: {message}",
            describe_resource_clause(resource)
        ))
    })?;
    let contained_clauses = if body_active {
        composite_body.contains()
    } else {
        &[]
    };
    let body_facts = if body_active {
        composite_body.facts()
    } else {
        &[]
    };
    let mut abstract_resource = lower_resource_clause_at_state_with_assumptions(
        resource,
        parameter_binding,
        &state,
        None,
        available_pure_facts.assumptions(),
    )?;
    let requested_quantity = abstract_resource
        .owned_quantity_term()
        .cloned()
        .unwrap_or(MachineTerm::constant(1));
    let assumptions = available_pure_facts.assumptions().clone();
    if let Some(authority) = state
        .resources()
        .directly_supporting_fact(&abstract_resource, &assumptions)
        .or_else(|| {
            (!matches!(resource, ResourceClause::Quantified { .. }))
                .then(|| {
                    let viewed = ResourceFact::View(abstract_resource.resource().clone());
                    state
                        .resources()
                        .directly_supporting_fact(&viewed, &assumptions)
                })
                .flatten()
        })
    {
        abstract_resource = authority.clone();
    }
    let opening_view = abstract_resource.is_view();
    let borrowed_parent_binding = if opening_view {
        unique_borrowed_resource_dependency(&state, &abstract_resource).map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `unfold` cannot determine which borrow backs this view: {message}"
            ))
        })?
    } else {
        None
    };
    // An owned borrowing composite carries the hold binding of the view it
    // packages (step 7). Unfolding hands that binding, hold included, to the
    // restored piece, so the borrow stays held and a later fold reuses the
    // same hold instead of placing another.
    let held_piece_binding = if opening_view {
        None
    } else {
        unique_borrowed_resource_dependency(&state, &abstract_resource)
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `unfold` refused ambiguous hold binding: {message}"
                ))
            })?
            .filter(|binding| binding.hold.is_some())
    };
    let (requested_population_name, requested_population_arguments) =
        match abstract_resource.resource() {
            Resource::Footprint(_) | Resource::Parameter(_) | Resource::Emp | Resource::Star(_) => {
                return Err(ClickError::new(
                    "a resource descriptor does not grant ownership",
                ));
            }
            Resource::Composite { name, arguments } | Resource::Token { name, arguments } => {
                (name.clone(), arguments.clone())
            }
            Resource::Memory(_) => unreachable!("a declared resource lowered to memory"),
            Resource::Instance(_)
            | Resource::ConditionalMutexGuard(_)
            | Resource::MutexGuard(_)
            | Resource::MutexLive(_)
            | Resource::MutexUse(_)
            | Resource::Publication(_)
            | Resource::PopulationAuthority(_)
            | Resource::Iterated(_) => {
                return Err(ClickError::new(
                    "instance unfolding is not a population operation",
                ));
            }
        };
    let body_reads_counts = composite_body
        .facts()
        .iter()
        .any(proposition_contains_resource_count);
    let authority_control_body = composite_body.contains().iter().any(|contained| {
            matches!(contained, ResourceClause::Declared { name, .. } if name == "authority")
        });
    // The authority inside a folded control resource is the count witness.
    // Authenticate and project it before taking apart the folded resource;
    // this projection is used only to lower its invariant, while the kernel
    // independently checks the actual body exchange.
    let authority_projection = if authority_control_body {
        let definitions = crate::surface::verification::composite_resource_definitions(
            resource_environment,
            spec_definitions,
        )?;
        let definition = definitions
            .iter()
            .find(|definition| definition.name() == requested_population_name)
            .ok_or_else(|| ClickError::new("control resource has no compiled definition"))?;
        Some(
            state
                .checked_authority_wrapper_projection(&abstract_resource, definition, &assumptions)
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `unfold({})` {message}",
                        describe_resource_clause(resource)
                    ))
                })?,
        )
    } else {
        None
    };
    // A count read in the body is the authority's count, so a body that
    // reads one without owning an authority has nothing to read it from.
    if authority_projection.is_none() && body_reads_counts {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `unfold({})` reads a population count its body owns no authority for",
            describe_resource_clause(resource)
        )));
    }
    let (population_name, population_arguments, population_count) = (
        requested_population_name,
        requested_population_arguments,
        MachineTerm::constant(1),
    );
    if state.population_body_is_open(&population_name, &population_arguments) {
        return Err(ClickError::new("population body is already open")
            .with_proof_refusal(ProofRefusal::Tactic));
    }
    if access == ResourceBodyAccess::Finalize {
        let quantity = requested_quantity;
        let count = population_count;
        // A constant quantity is decided by reading it, as `fold` reads its
        // own; only a symbolic one needs a fact about it.
        let final_by_constant = quantity.as_const() == Some(1);
        let final_unit = Proposition::condition_is(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(count),
                right: Box::new(quantity),
            },
            true,
        );
        if !final_by_constant && !holds_by_lookup_or_decision(&assumptions, &final_unit) {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `unfold({})` Requires count({}) == {}",
                describe_resource_clause(resource),
                describe_resource_clause(match resource {
                    ResourceClause::Quantified { resource, .. } => resource,
                    _ => resource,
                }),
                match resource {
                    ResourceClause::Quantified { quantity, .. } =>
                        describe_contract_expression(quantity),
                    _ => "1".to_string(),
                }
            )));
        }
    }
    // The ordinary case holds the folded composite exactly. Removing that
    // representation must not normalize every unrelated resource in the
    // ambient context. Preserve the equality-aware fallback for callers whose
    // resource arguments are only propositionally equal.
    let witness_opening = state
        .resources()
        .open_structural_witness(&abstract_resource, &assumptions);
    let folded_resources = if access == ResourceBodyAccess::Open {
        // Opening exposes the population body but does not consume one of its
        // units. Keeping the folded unit in the context is also essential for
        // certifying execution against the enclosing function contract.
        state
            .resources()
            .satisfies_fact(&abstract_resource, &assumptions)
            .then(|| state.resources().clone())
    } else {
        state
            .resources()
            .clone()
            .without_exact_representation(&abstract_resource)
            .or_else(|| {
                state
                    .resources()
                    .clone()
                    .without_fact_incrementally(&abstract_resource, &assumptions)
            })
    };
    let already_unfolded = folded_resources.is_none();
    if already_unfolded && access == ResourceBodyAccess::Open {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `with({})` Requires {} {}",
            describe_resource_clause(resource),
            if abstract_resource.is_view() {
                "views"
            } else {
                "owns"
            },
            describe_resource_clause(resource),
        ))
        .with_proof_refusal(ProofRefusal::Tactic)
        .with_failed_tactic("with"));
    }
    let resources = if let Some(resources) = folded_resources {
        resources
    } else {
        let mut remaining = state.resources().clone();
        for contained in contained_clauses {
            let contained =
                instantiate_resource_clause(contained, &substitutions).map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: could not inspect canonical `unfold({})`: {message}",
                        describe_resource_clause(resource)
                    ))
                })?;
            let lowered = lower_resource_clause_at_state_with_assumptions(
                &contained,
                parameter_binding,
                &state,
                None,
                &assumptions,
            )?;
            let Some(next) = remaining.without_fact(&lowered, &assumptions) else {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `unfold({})` failed: {}",
                    describe_resource_clause(resource),
                    describe_missing_resource_fact(
                        &abstract_resource,
                        &available_pure_facts.materialize(),
                        state.resources().facts(),
                        parameter_binding,
                        &[]
                    )
                )));
            };
            remaining = next;
        }
        state.resources().clone()
    };
    state = state.with_resource_context(resources);

    if already_unfolded && contained_clauses.is_empty() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `unfold({})` failed: {}",
            describe_resource_clause(resource),
            describe_missing_resource_fact(
                &abstract_resource,
                &available_pure_facts.materialize(),
                state.resources().facts(),
                parameter_binding,
                &[]
            )
        )));
    }

    // Only a held head supplies the domains established when its body was
    // folded. The canonical already-unfolded path must still establish them
    // from its facts; matching wrapped child arguments is not sufficient.
    let body_assumptions = if already_unfolded {
        assumptions.clone()
    } else {
        assumptions
            .clone()
            .assume_entry_clause_spans()
            .assume_held_resource_domains()
    };
    let mut unfolded_facts = Vec::new();
    let mut witness_children = Vec::new();
    // Lower later selectors through earlier cached fields, but name every
    // exposed cell at this one rewrite's input state. Caching a read is
    // not a new program write or a new load-naming epoch.
    let naming_point = state.program_point();
    for contained in contained_clauses {
        let contained = instantiate_resource_clause(contained, &substitutions).map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: could not instantiate `unfold({})`: {message}",
                describe_resource_clause(resource)
            ))
        })?;
        let mut lowered = lower_resource_clause_at_state_with_assumptions(
            &contained,
            parameter_binding,
            &state,
            None,
            &body_assumptions,
        )?;
        if lowered.is_own() {
            witness_children.push(lowered.clone());
        }
        if opening_view {
            lowered = ResourceFact::View(lowered.resource().clone());
        }
        unfolded_facts.push(lowered.clone());
        // A completed outcome has no more C loads to execute. Its proof
        // receives loadability and symbolic loads without modifying the
        // certified program memory by installing cached cells into it.
        if materialize_memory {
            let memory = materialize_composite_resource_cells_from_state(
                state.memory().clone(),
                &naming_point,
                &contained,
                &lowered,
                parameter_binding.parameters,
                names_plain_scalar_body_at_entry(composite_body),
            );
            // Keep the program point and unrelated memory-backed views when
            // the proof rewrite gives cells names.
            state = state.with_materialized_memory_at_current_point(memory);
        }
        // The selected child was already lowered in the current state.
        // Re-lowering from memory alone loses locals such as a callback's
        // returned pointer. Project exactly that checked child's range.
        if let Some(range) = lowered
            .memory_view_range()
            .or_else(|| lowered.memory_own_range())
        {
            available_pure_facts.insert(memory_range_loadable_prop(state.memory(), range));
        }
    }

    let preexisting_child_sources = unfolded_facts
        .iter()
        .filter_map(|child| {
            state
                .resources()
                .first_exact_occurrence(child)
                .map(|occurrence| (child.clone(), occurrence))
        })
        .collect::<BTreeMap<_, _>>();
    let viewed_body_is_exposed = opening_view
        && unfolded_facts.iter().all(|child| {
            let Some(occurrence) = preexisting_child_sources.get(child) else {
                return false;
            };
            let existing = state.resources().borrow_dependency(*occurrence);
            match (borrowed_parent_binding.as_ref(), existing) {
                (Some(parent), Some(existing)) => same_borrow_authority(parent, existing),
                (Some(_), None) => !state.resources().view_occurrence_is_principal(*occurrence),
                (None, None) => true,
                _ => false,
            }
        });
    let body_was_already_exposed = composite_body.condition().is_none()
        && (already_unfolded || access == ResourceBodyAccess::Open || viewed_body_is_exposed)
        && unfolded_facts
            .iter()
            .all(|fact| preexisting_child_sources.contains_key(fact));

    // The held head supplies this separating body beside its residual frame.
    // Construct its successor once, before assuming definition facts, so a
    // contradictory body fact cannot conceal a directly known collision.
    // This never revalidates or normalizes the unchanged caller frame.
    let constructed_body = if !already_unfolded && !body_was_already_exposed {
        let emitted = if borrowed_parent_binding.is_some()
            || held_piece_binding.is_some()
            || body_reads_counts
            || access == ResourceBodyAccess::Open
        {
            unfolded_facts.clone()
        } else {
            crate::kernel::coalesce_written_resource_descriptions(
                unfolded_facts.clone(),
                &assumptions,
            )
        };
        Some(
            state
                .resources()
                .clone()
                .install_established_partition(emitted, &assumptions)
                .map_err(|error| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `unfold({})` produced {}",
                        describe_resource_clause(resource),
                        describe_resource_context_validity_error(error, parameter_binding)
                    ))
                })?,
        )
    } else {
        None
    };

    // An owned instance `with` keeps folded: the one owner whose own views
    // may support its body facts without a borrow.
    let opened_owner = (access == ResourceBodyAccess::Open && !opening_view)
        .then(|| {
            match state
                .resources()
                .owned_occurrences_for_fact(&abstract_resource)
                .as_slice()
            {
                [occurrence] => Some(*occurrence),
                _ => None,
            }
        })
        .flatten();
    for fact in body_facts {
        let written =
            substitute_click_proposition(fact, &spelling_substitutions).map_err(ClickError::new)?;
        let fact = substitute_click_proposition(fact, &substitutions).map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: could not instantiate `unfold({})` fact: {message}",
                    describe_resource_clause(resource)
                ))
            })?;
        let fact_state = if let Some((projected, _)) = &authority_projection {
            // The checked private-body projection has retired only the
            // selected head and its observations; unrelated ambient views
            // remain subject to the usual dependency checks.
            state.clone().with_resource_context(projected.clone())
        } else {
            state.clone()
        };
        let (lowered_fact, lowering_facts) = lower_outcome_proposition_with_auxiliary_facts(
            parameter_binding,
            &fact_state,
            &fact_state,
            &ProgramValue::Int32(MachineTerm::constant(0)),
            available_pure_facts.assumptions(),
            &fact,
            spec_definitions,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: could not lower `unfold({})` pure fact `{}`: {message}\n{}",
                describe_resource_clause(resource),
                describe_click_proposition(&fact),
                describe_proof_context(
                    &available_pure_facts.materialize(),
                    state.resources().facts(),
                    parameter_binding,
                    &[]
                )
            ))
        })?;
        let temporary_views = borrowed_parent_binding
            .as_ref()
            .map(|binding| {
                unfolded_facts
                    .iter()
                    .filter(|child| child.is_view())
                    .map(|child| (child.clone(), binding.clone()))
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        let temporary_unbound_views = if borrowed_parent_binding.is_none() {
            unfolded_facts
                .iter()
                .filter(|child| child.is_view())
                .cloned()
                .collect::<Vec<_>>()
        } else {
            Vec::new()
        };
        let temporary_owned = unfolded_facts
            .iter()
            .filter(|child| child.memory_own_range().is_some())
            .cloned()
            .collect::<Vec<_>>();
        let temporary_view_index = DynamicViewDependencyIndex::with_owned(
            &temporary_views,
            &temporary_unbound_views,
            &temporary_owned,
            available_pure_facts.assumptions(),
        )
        .with_opened_owner(opened_owner);
        if let Some(binding) = dynamic_body_fact_dependency(
            &lowered_fact,
            &fact_state,
            available_pure_facts.assumptions(),
            &temporary_view_index,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `unfold({})` rejected dynamic body dependency: {message}",
                describe_resource_clause(resource)
            ))
        })?
            && borrowed_parent_binding
                .as_ref()
                .is_none_or(|parent| !same_borrow_authority(parent, &binding))
        {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `unfold({})` cannot publish a current viewed-memory fact without its parent borrow",
                describe_resource_clause(resource)
            )));
        }
        // Without the folded resource, only its pieces are held: its body
        // facts are not established by holding them. An earlier `unfold`
        // of the same instance already published them, so re-opening it
        // keeps exactly the facts that are still available.
        if already_unfolded
            && !crate::kernel::proof::fact_reasoning::holds_by_lookup_or_decision(
                available_pure_facts.assumptions(),
                &lowered_fact,
            )
        {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `unfold({})` requires owns {}; its pieces are held, but its fact `{}` is not established",
                describe_resource_clause(resource),
                describe_resource_clause(resource),
                describe_click_proposition(&fact),
            )));
        }
        surface_propositions.record_lowering(&written, &lowered_fact)?;
        for fact in lowering_facts {
            available_pure_facts.insert(fact);
        }
        available_pure_facts.insert(lowered_fact);
    }

    let mut inserted_unfolded_occurrences = Vec::new();
    if let Some((resources, inserted)) = constructed_body {
        if borrowed_parent_binding.is_some() {
            inserted_unfolded_occurrences = inserted;
            state = state.with_resource_context(resources);
        } else if let Some(binding) = held_piece_binding.as_ref() {
            let assumptions = available_pure_facts.assumptions().clone();
            let ledger = state.borrow_ledger().ok_or_else(|| {
                ClickError::new("an unfolded borrowing composite has no active borrow ledger")
            })?;
            let dependencies = inserted
                .into_iter()
                .filter(|(child, _)| {
                    child.is_view()
                        && ledger
                            .selected_return_permission(
                                binding.borrow,
                                child,
                                &binding.viewed,
                                &assumptions,
                            )
                            .is_some()
                })
                .map(|(_, occurrence)| (occurrence, binding.clone()))
                .collect::<Vec<_>>();
            state = state.with_resource_context_and_borrow_dependencies(resources, dependencies);
        } else {
            state = state.with_resource_context(resources);
        }
    }

    // Finalizing a viewed composite replaces its folded occurrence with fresh
    // viewed children.  Keep the exact borrow/share/support bundle on each
    // child.  An exclusive instance view has already been rejected above by
    // the resource-kind check and never enters this projection path.
    if let Some(binding) = borrowed_parent_binding {
        let inserted_child_facts = inserted_unfolded_occurrences
            .iter()
            .map(|(fact, _)| fact.clone())
            .collect::<BTreeSet<_>>();
        let mut dependencies = inserted_unfolded_occurrences
            .into_iter()
            .filter(|(child, _)| child.is_view())
            .map(|(child, occurrence)| {
                (
                    occurrence,
                    crate::kernel::BorrowBinding {
                        viewed: child,
                        ..binding.clone()
                    },
                )
            })
            .collect::<Vec<_>>();
        for child in unfolded_facts.iter().filter(|fact| fact.is_view()) {
            // A fresh child is the destination of this exact parent. Equal
            // ambient children retain their own dependencies and identities.
            if inserted_child_facts.contains(child) {
                continue;
            }
            let occurrence = preexisting_child_sources.get(child).copied().ok_or_else(||
                ClickError::new(format!("`{claim_label}` tactic {tactic_index}: `unfold` produced no exact destination for a viewed child")))?;
            let child_binding = state.resources().borrow_dependency(occurrence);
            if child_binding.is_none()
                && !state.resources().view_occurrence_is_principal(occurrence)
            {
                dependencies.push((
                    occurrence,
                    crate::kernel::BorrowBinding {
                        viewed: child.clone(),
                        ..binding.clone()
                    },
                ));
            } else if child_binding
                .is_none_or(|existing| !same_borrow_authority(existing, &binding))
            {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `unfold` cannot reuse an unbound or differently bound child for a viewed composite"
                )));
            }
        }
        let definitions = crate::surface::verification::composite_resource_definitions(
            resource_environment,
            spec_definitions,
        )?;
        state = project_children_into_ledger(
            state,
            &binding,
            dependencies.iter().map(|(_, child)| child.viewed.clone()),
            available_pure_facts.assumptions(),
            &definitions,
            &format!("`{claim_label}` tactic {tactic_index}: `unfold`"),
        )?;
        let resources = state.resources().clone();
        state = state.with_resource_context_and_borrow_dependencies(resources, dependencies);
    }

    if !already_unfolded && !body_was_already_exposed {
        let resources = state.resources().clone().with_opened_structural_witnesses(
            witness_opening,
            &witness_children,
            opening_view,
            available_pure_facts.assumptions(),
        );
        state = state.with_resource_context(resources);
    }

    if access == ResourceBodyAccess::Open && abstract_resource.is_own() {
        let mut resources = state.resources().clone();
        if let Some(occurrence) = resources
            .structural_witness_occurrence(&abstract_resource, available_pure_facts.assumptions())
        {
            resources.forget_structural_witness(occurrence);
        }
        state = state.with_resource_context(resources);
    }

    let unfolded_resources =
        ResourceContext::new_with_equalities(available_pure_facts.assumptions())
            .unchecked_with_facts(unfolded_facts);
    append_composite_resource_relation_facts_with_store(
        abstract_resource.resource(),
        &unfolded_resources,
        available_pure_facts,
    );

    append_state_resource_context_observable_facts_with_store(&state, available_pure_facts);

    // `unfold` changes the proof representation of the final visible unit;
    // it does not itself perform the function contract's logical consumption.
    // Keep the population identity/count so execution certification and the
    // eventual resource effect can check that transition exactly.
    if access == ResourceBodyAccess::Open {
        state = state
            .open_population_body(population_name, population_arguments)
            .map_err(ClickError::new)?;
    }

    Ok(UnfoldedCompositeResource {
        state,
        selected: abstract_resource,
        body_was_already_exposed,
    })
}

#[allow(clippy::too_many_arguments)]
fn fold_composite_resources_on_outcome_with_facts(
    resource_environment: &ResourceEnvironment,
    resource_folds: &[ResourceClause],
    source_resource: Option<&ResourceClause>,
    claim_label: &str,
    path_index: usize,
    execution_pure_facts: &(impl ExecutionFactSource + ?Sized),
    pure_facts: &impl ResourcePureFacts,
    parameter_binding: ParameterBinding<'_>,
    pre_state: &ExecutionState,
    mut outcome: FunctionOutcome,
    spec_definitions: SpecDefinitions<'_>,
    closure: ResourceBodyClosure,
    family_reaches_population: bool,
) -> Result<FoldedOutcome, ClickError> {
    let mut selections = Vec::with_capacity(resource_folds.len());
    let mut borrow_holds = Vec::new();
    for resource in resource_folds {
        let definition = composite_resource_law_definition(
            resource_environment,
            resource,
            "fold",
            claim_label,
            path_index,
        )?;
        let composite_body = definition
            .composite_body()
            .expect("composite_resource_law_definition should require a composite body");
        let (guard_result, guard_state) = match &outcome {
            FunctionOutcome::Return { value, state } => (value.clone(), state.clone()),
            _ => {
                return Err(ClickError::new(format!(
                    "`{claim_label}` path {path_index}: `fold({})` requires a return outcome, got {}",
                    describe_resource_clause(resource),
                    describe_function_outcome(&outcome, parameter_binding)
                )));
            }
        };
        // A body contains executable indexed addresses. Capture an explicit
        // entry argument before substituting it there: an Old spec expression
        // cannot be embedded in a C address, and rereading it in the fold's
        // current state would select a different resource.
        let mut frozen_resource = resource.clone();
        let frozen_arguments = match &mut frozen_resource {
            ResourceClause::Quantified { resource, .. } => resource.as_mut(),
            resource => resource,
        };
        if let ResourceClause::Declared { arguments, .. } = frozen_arguments
            && arguments.iter().any(contains_old_expression)
        {
            let values = parameter_values(parameter_binding)?;
            let array_refs = array_refs_for_parameters(
                parameter_binding.parameters,
                &values,
                &guard_state.program_point(),
            );
            let retained_states = RecordedStates::new();
            for argument in arguments {
                if contains_old_expression(argument) {
                    let value = evaluate_fixed_state_expression_through_kernel(
                        argument,
                        pure_facts.assumptions(),
                        ContractEnvironment::new(&values, &array_refs)
                            .with_parameters(parameter_binding),
                        FixedStateFrame::new(
                            pre_state,
                            &guard_state,
                            Some(&guard_result.native()),
                            &retained_states,
                        ),
                        spec_definitions,
                        &BTreeSet::new(),
                    )
                    .map_err(ClickError::new)?;
                    *argument =
                        ContractExpression::ProgramExpression(ProgramExpression::Value(value));
                }
            }
        }
        let resource = &frozen_resource;
        let mut substitutions =
            resource_argument_substitutions(definition, resource, claim_label, path_index)?;
        extend_substitutions_with_witnesses(
            &mut substitutions,
            definition,
            resource,
            parameter_binding,
            &guard_state,
            Some(&guard_result.native()),
            pure_facts.assumptions(),
            resource_environment,
            spec_definitions,
            None,
        )?;
        let mut body_active = composite_resource_body_is_active_with_assumptions(
            definition,
            &substitutions,
            parameter_binding,
            pre_state,
            &guard_state,
            &guard_result.native(),
            pure_facts.assumptions(),
            spec_definitions,
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` path {path_index}: could not select `fold({})` body: {message}",
                describe_resource_clause(resource)
            ))
        })?;
        let mut closing_view = false;
        // The owned instance a `with` kept folded; its own views support
        // the body facts this closing fold re-checks.
        let mut opened_owner = None;
        let mut authority_closing_fact_state = None;
        let mut authority_control_definition = None;
        let mut folded_representation_already_present = false;
        let mut folded_authority_occurrence = None;
        let authority_control_body = composite_body.contains().iter().any(|contained| {
                matches!(contained, ResourceClause::Declared { name, .. } if name == "authority")
            });
        if closure == ResourceBodyClosure::Initialize {
            let FunctionOutcome::Return { value, state } = &mut outcome else {
                unreachable!("the return outcome was checked above");
            };
            let population = lower_resource_clause_at_state_with_assumptions(
                resource,
                parameter_binding,
                state,
                Some(&value.native()),
                pure_facts.assumptions(),
            )?;
            let quantity = population
                .owned_quantity_term()
                .expect("fold requires owned composite authority")
                .clone();
            let name = match population.resource() {
                Resource::Footprint(_)
                | Resource::Parameter(_)
                | Resource::Emp
                | Resource::Star(_) => {
                    return Err(ClickError::new(
                        "a resource descriptor does not grant ownership",
                    ));
                }
                Resource::Composite { name, .. } | Resource::Token { name, .. } => name,
                Resource::Memory(_)
                | Resource::Instance(_)
                | Resource::ConditionalMutexGuard(_)
                | Resource::MutexGuard(_)
                | Resource::MutexLive(_)
                | Resource::MutexUse(_)
                | Resource::Publication(_)
                | Resource::PopulationAuthority(_)
                | Resource::Iterated(_) => {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` path {path_index}: `fold({})` did not lower to a declared resource",
                        describe_resource_clause(resource)
                    )));
                }
            };
            let assumptions = pure_facts.assumptions();
            let (quantity_is_zero, quantity_is_positive) =
                fold_resource_quantity_activity(&quantity, assumptions);
            if !quantity_is_zero && !quantity_is_positive {
                return Err(ClickError::new(format!(
                    "`{claim_label}` path {path_index}: `fold({})` requires its quantity to be proved zero or positive",
                    describe_resource_clause(resource)
                )));
            }
            body_active &= quantity_is_positive;
            if state.resources().satisfies_fact(&population, assumptions) {
                // Exact execution preserves the abstract contract resource
                // while the proof may still carry its exposed body. This is
                // representation state, independent of whether the resource
                // needs a persistent population ledger.
                folded_representation_already_present = true;
                // Exact execution can retain this folded owner alongside
                // observations of its body. Refolding checks those same
                // observations under their existing owner, just as closing
                // `with` does; unrelated unbound views still need a borrow.
                if let [occurrence] = state
                    .resources()
                    .owned_occurrences_for_fact(&population)
                    .as_slice()
                {
                    opened_owner = Some(*occurrence);
                }
            }
            if authority_control_body {
                let definitions = crate::surface::verification::composite_resource_definitions(
                    resource_environment,
                    spec_definitions,
                )?;
                let definition = definitions
                    .iter()
                    .find(|definition| definition.name() == name)
                    .ok_or_else(|| {
                        ClickError::new("control resource has no compiled definition")
                    })?;
                state
                    .checked_authority_wrapper_fold_preflight(&population, definition, assumptions)
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` path {path_index}: `fold({})` {message}",
                            describe_resource_clause(resource)
                        ))
                    })?;
                authority_control_definition = Some(definition.clone());
            } else {
                // An ordinary wrapper transfers its existing children.
            }
        } else {
            let FunctionOutcome::Return { value, state } = &outcome else {
                unreachable!("the return outcome was checked above");
            };
            let population = lower_resource_clause_at_state_with_assumptions(
                resource,
                parameter_binding,
                state,
                Some(&value.native()),
                pure_facts.assumptions(),
            )?;
            let assumptions = pure_facts.assumptions();
            if !state.resources().satisfies_fact(&population, assumptions) {
                let viewed_population = ResourceFact::View(population.resource().clone());
                closing_view = state
                    .resources()
                    .satisfies_fact(&viewed_population, assumptions);
            } else if matches!(closure, ResourceBodyClosure::CloseOpen { .. })
                && let [occurrence] = state
                    .resources()
                    .owned_occurrences_for_fact(&population)
                    .as_slice()
            {
                opened_owner = Some(*occurrence);
            }
            let (name, _) = match population.resource() {
                Resource::Footprint(_)
                | Resource::Parameter(_)
                | Resource::Emp
                | Resource::Star(_) => {
                    return Err(ClickError::new(
                        "a resource descriptor does not grant ownership",
                    ));
                }
                Resource::Composite { name, arguments } | Resource::Token { name, arguments } => {
                    (name, arguments)
                }
                Resource::Memory(_) => unreachable!("declared resource lowered to memory"),
                Resource::Instance(_)
                | Resource::ConditionalMutexGuard(_)
                | Resource::MutexGuard(_)
                | Resource::MutexLive(_)
                | Resource::MutexUse(_)
                | Resource::Publication(_)
                | Resource::PopulationAuthority(_)
                | Resource::Iterated(_) => {
                    return Err(ClickError::new(
                        "instance folding is not a population operation",
                    ));
                }
            };
            if authority_control_body {
                let definitions = crate::surface::verification::composite_resource_definitions(
                    resource_environment,
                    spec_definitions,
                )?;
                let definition = definitions
                    .iter()
                    .find(|definition| definition.name() == name)
                    .ok_or_else(|| {
                        ClickError::new("control resource has no compiled definition")
                    })?;
                let (projected, _) = state
                    .checked_authority_wrapper_closing_projection(
                        &population,
                        definition,
                        assumptions,
                    )
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` path {path_index}: closing `with({})` {message}",
                            describe_resource_clause(resource)
                        ))
                        .with_proof_refusal(ProofRefusal::IncompleteProof)
                    })?;
                authority_closing_fact_state = Some(state.clone().with_resource_context(projected));
            } else if composite_body
                .facts()
                .iter()
                .any(proposition_contains_resource_count)
            {
                return Err(ClickError::new(format!(
                    "`{claim_label}` path {path_index}: closing `with({})` requires its resource population to remain active",
                    describe_resource_clause(resource)
                )));
            }
        }
        let body_facts = if body_active {
            composite_body.facts()
        } else {
            &[]
        };
        let contained_clauses = if body_active {
            composite_body.contains()
        } else {
            &[]
        };
        let body_assumptions = pure_facts.assumptions().clone();
        let mut body_borrow_dependency = None;
        let mut temporary_unbound_views = Vec::new();
        for contained in contained_clauses {
            let contained = instantiate_resource_clause(contained, &substitutions).map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` path {path_index}: could not instantiate `fold({})` body view: {message}",
                    describe_resource_clause(resource)
                ))
            })?;
            let lowered = lower_resource_clause_at_state_with_assumptions(
                &contained,
                parameter_binding,
                &guard_state,
                Some(&guard_result.native()),
                pure_facts.assumptions(),
            )?;
            if lowered.is_view()
                && guard_state.fold_view_dependency(&lowered, &body_assumptions)
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` path {path_index}: `fold` cannot determine which borrow backs this body view: {message}"
                        ))
                    })?
                    .is_none()
            {
                temporary_unbound_views.push(lowered);
            }
        }
        let temporary_view_index = DynamicViewDependencyIndex::new(
            &[],
            &temporary_unbound_views,
            pure_facts.assumptions(),
        )
        .with_opened_owner(opened_owner);
        let collecting = crate::surface::proof::execution_planning::collecting_step_requirements();
        for fact in body_facts {
            let source_fact = fact;
            let fact = substitute_click_proposition(fact, &substitutions).map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` path {path_index}: could not instantiate `fold({})` fact: {message}",
                        describe_resource_clause(resource)
                    ))
                })?;
            // An unqualified invariant denotes this outcome's current
            // resource population and memory. Historical source spellings
            // are not aliases for it; the checked matchers below transport
            // earlier evidence only after this exact current-state lowering.
            let required = {
                let FunctionOutcome::Return { value, state } = &outcome else {
                    unreachable!("the return outcome was checked above")
                };
                let state = authority_closing_fact_state.as_ref().unwrap_or(state);
                let lowered = lower_outcome_proposition_with_assumptions(
                    parameter_binding,
                    pre_state,
                    state,
                    &value.native(),
                    pure_facts.assumptions(),
                    &fact,
                    spec_definitions,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` path {path_index}: could not lower exact `fold({})` fact: {message}",
                        describe_resource_clause(resource)
                    ))
                })?;
                if collecting {
                    lowered
                } else {
                    Proposition::clone(&lowered)
                }
            };
            if let Some(binding) = dynamic_body_fact_dependency(
                &required,
                authority_closing_fact_state.as_ref().unwrap_or(match &outcome {
                    FunctionOutcome::Return { state, .. } => state,
                    _ => pre_state,
                }),
                &body_assumptions,
                &temporary_view_index,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` path {path_index}: `fold({})` rejected its dynamic body dependency: {message}",
                    describe_resource_clause(resource)
                ))
            })? {
                if body_borrow_dependency
                    .as_ref()
                    .is_some_and(|existing| !same_borrow_authority(existing, &binding))
                {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` path {path_index}: `fold({})` body facts depend on different stable-view authorities",
                        describe_resource_clause(resource)
                    )));
                }
                body_borrow_dependency = Some(binding);
            }
            // Available facts may write this body fact through loads recorded
            // at an earlier state. Decide those forms with the bounded
            // check matchers first: exact structural membership, the
            // state-bridging relation with this execution's effect facts as
            // framing, and the direct separation-fact matcher. All of these do
            // work proportional to the fact being checked, so an exactly
            // available body fact never rides on the open-ended kernel search
            // below, which can consume a large share of the fold's budget.
            // The kernel's condition decision settles a condition body fact
            // as it settles a step's: the difference graph, then the
            // decision's checked rules (a tagged pointer word's low bits, say).
            let exactly_available = !collecting
                && (pure_facts.exact_available_across_effects(&required, execution_pure_facts)
                    || decided_by_kernel_condition_decision(&body_assumptions, &required));
            // A body fact the exact checks miss is a requirement of this
            // `fold`, spelled as the definition's fact over the arguments as
            // written; the fold never searches the proof context for it. A
            // probe records it for the implicit `solve`, which proves it and
            // folds again.
            // A body fact reading a stored cell can hold by evaluation of the
            // value stored there (the read-over-write authority).
            let open = collecting
                || (!exactly_available
                    && !matches!(
                        normalize_proposition(&required),
                        NormalizedProposition::True
                    )
                    && !crate::kernel::holds_by_read_over_write(&required));
            // A witness the proof cannot name has no source expression, so
            // its body fact has no requirement spelling and the fold refuses
            // it. A fact read in the projected authority state is spelled as
            // any other: its `have` at the frontier is what the closing fold
            // reads.
            let spelling_resource = source_resource.unwrap_or(resource);
            let spelled = if open {
                (|| -> Result<Option<ClickProposition>, ClickError> {
                    // The arguments as written, and each witness as it was
                    // inferred or given.
                    let mut spelling_substitutions = substitutions.clone();
                    spelling_substitutions.extend(resource_argument_substitutions(
                        definition,
                        spelling_resource,
                        claim_label,
                        path_index,
                    )?);
                    // A witness bound to a semantic value is written as the proof
                    // would name that value here.
                    // At a return, the returned value is `result`, as a
                    // proof after the function exit names it.
                    let returned_state;
                    let spelling_state = match (&authority_closing_fact_state, &outcome) {
                        (Some(state), _) => state,
                        (None, FunctionOutcome::Return { state, value }) => {
                            returned_state = state.as_ref().clone().with_local(
                                crate::kernel::CONTRACT_RESULT,
                                value.clone().into_native(),
                            );
                            &returned_state
                        }
                        (None, _) => pre_state,
                    };
                    for expression in spelling_substitutions.values_mut() {
                        if let ContractExpression::ProgramExpression(ProgramExpression::Value(
                            value,
                        )) = expression
                            && let Some(spelled) =
                                crate::surface::proof::surface_synthesis::synthesize_surface_value(
                                    value,
                                    parameter_binding,
                                    spelling_state,
                                )
                        {
                            *expression = spelled;
                        }
                    }
                    // A constant prints as its literal, such as `1u64`; any
                    // other bare value has no source spelling.
                    if spelling_substitutions.values().any(|expression| {
                        matches!(
                            expression,
                            ContractExpression::ProgramExpression(ProgramExpression::Value(value))
                                if !is_integer_constant(value)
                        )
                    }) {
                        return Ok(None);
                    }
                    substitute_click_proposition(source_fact, &spelling_substitutions)
                        .map(Some)
                        .map_err(ClickError::new)
                })()?
            } else {
                None
            };
            if collecting {
                let spelled = spelled.ok_or_else(|| {
                    ClickError::new("fold body requirement has no source spelling")
                })?;
                refuse_or_record_open_obligation(
                    ClickError::new(format!(
                        "`{claim_label}` path {path_index}: `fold({})` requires {}",
                        describe_resource_clause(spelling_resource),
                        crate::surface::printing::source_click_proposition(&spelled),
                    ))
                    .with_spelled_requirement(
                        required,
                        spelled,
                        "fold body fact".to_owned(),
                    ),
                )?;
                continue;
            }
            if open {
                let available_pure_facts = pure_facts.materialize();
                let resources = match &outcome {
                    FunctionOutcome::Return { state, .. } => state.resources().facts(),
                    _ => pre_state.resources().facts(),
                };
                let required_text =
                    crate::surface::diagnostics::pure_fact_shape(&required, parameter_binding);
                let identically_printed = available_pure_facts
                    .iter()
                    .filter(|fact| {
                        crate::surface::diagnostics::pure_fact_shape(fact, parameter_binding)
                            == required_text
                    })
                    .count();
                let program_point_note = if identically_printed > 0 {
                    format!(
                        "\n  note: {identically_printed} available fact(s) print identically but carry different embedded memory states, and the recorded execution effects do not prove the states agree at the loaded pointers"
                    )
                } else {
                    String::new()
                };
                let error = if authority_control_body {
                    // Captured arguments are semantic values; render the written
                    // operand so its C names survive a failing body check.
                    let source_resource = source_resource.unwrap_or(resource);
                    let source_substitutions = resource_argument_substitutions(
                        definition,
                        source_resource,
                        claim_label,
                        path_index,
                    )?;
                    let source_fact =
                        substitute_click_proposition(source_fact, &source_substitutions)
                            .map_err(ClickError::new)?;
                    ClickError::new(format!(
                        "`{claim_label}` path {path_index}: `fold({})` Requires {}",
                        describe_resource_clause(source_resource),
                        describe_click_proposition(&source_fact),
                    ))
                } else {
                    ClickError::new(format!(
                        "`{claim_label}` path {path_index}: `fold({})` requires an exact body fact: {}{program_point_note}",
                        describe_resource_clause(resource),
                        describe_missing_pure_fact(
                            &required,
                            &available_pure_facts,
                            resources,
                            parameter_binding,
                            execution_pure_facts,
                        )
                    ))
                };
                let Some(spelled) = spelled else {
                    return Err(error);
                };
                refuse_or_record_open_obligation(error.with_spelled_requirement(
                    required,
                    spelled,
                    format!(
                        "a body fact of `fold({})`",
                        describe_resource_clause(spelling_resource)
                    ),
                ))?;
                continue;
            }
        }
        let FunctionOutcome::Return { value, state } = outcome else {
            return Err(ClickError::new(format!(
                "`{claim_label}` path {path_index}: `fold({})` requires a return outcome, got {}\n  execution pure facts: {}",
                describe_resource_clause(resource),
                describe_function_outcome(&outcome, parameter_binding),
                describe_execution_pure_facts(execution_pure_facts)
            )));
        };
        let mut post_state = state;
        // Range forms in held resource facts embed loads at their
        // creation state; carrying them to the fold state needs the
        // execution's store effect facts alongside the pure facts.
        let assumptions = pure_facts.assumptions().clone();
        let _assumptions_id_scope = crate::kernel::PureFactContextIdScope::enter(&assumptions);
        let mut lowered_contained = Vec::new();
        let mut witness_fold_children = Vec::new();
        let mut body_has_unbound_view = false;
        let mut held_view_children = BTreeSet::new();
        let mut selected_held_view = false;
        let preserve_exposed_body = matches!(
            closure,
            ResourceBodyClosure::CloseOpen {
                preserve_exposed_body: true
            }
        );
        for contained in contained_clauses {
            let contained =
                instantiate_resource_clause(contained, &substitutions).map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` path {path_index}: could not instantiate `fold({})`: {message}",
                        describe_resource_clause(resource)
                    ))
                })?;
            let mut lowered = lower_resource_clause_at_state_with_assumptions(
                &contained,
                parameter_binding,
                &post_state,
                Some(&value.native()),
                pure_facts.assumptions(),
            )?;
            // The constructor's owned-child slots determine witness height,
            // including when this fold describes them through views.
            if lowered.is_own() {
                witness_fold_children.push(lowered.clone());
            }
            if lowered.is_view() {
                let binding = post_state.fold_view_dependency(&lowered, &assumptions)
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` path {path_index}: `fold` cannot determine which borrow backs this body view: {message}"
                        ))
                    })?;
                match binding {
                    Some((occurrence, binding)) => {
                        if body_has_unbound_view
                            || body_borrow_dependency.as_ref().is_some_and(|existing| {
                                !same_borrow_authority(existing, &binding)
                                    || (existing.hold.is_some() && existing.hold != binding.hold)
                            })
                        {
                            return Err(ClickError::new(format!(
                                "`{claim_label}` path {path_index}: `fold` cannot combine its body views under one borrow hold"
                            )));
                        }
                        selected_held_view |= occurrence.is_some() && binding.hold.is_some();
                        if let Some(occurrence) = occurrence
                            && binding.hold.is_some()
                            && post_state
                                .resources()
                                .view_occurrence_is_principal(occurrence)
                            && post_state
                                .resources()
                                .view_fact_for_occurrence(occurrence)
                                .is_some_and(|held| {
                                    crate::kernel::resources_directly_match(
                                        held.resource(),
                                        lowered.resource(),
                                        &assumptions,
                                    )
                                })
                        {
                            held_view_children.insert(occurrence);
                        }
                        body_borrow_dependency = Some(binding);
                    }
                    None if body_borrow_dependency.is_some() => {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` path {path_index}: `fold` cannot combine its body views under one borrow hold"
                        )));
                    }
                    None => {
                        // A view of memory this context owns is an owner
                        // observation, and folding it would capture the
                        // body's facts beside an owner that can still write
                        // the bytes (law 6 in docs/internals/stable-views.md).
                        // A body with facts must own that memory, or the view
                        // must come in as a borrow. A body with no facts of
                        // its own packages nothing that could go stale (a
                        // nested composite's facts were checked by its own
                        // fold), so its observation stays an observation.
                        let assumptions = pure_facts.assumptions();
                        if !body_facts.is_empty()
                            && lowered.memory_view_range().is_some()
                            && post_state
                                .resources()
                                .directly_supporting_owned_entry(&lowered, assumptions)
                                .is_some()
                        {
                            return Err(ClickError::new(format!(
                                "`{claim_label}` path {path_index}: `fold({})` body views memory this context owns: `{}` is backed by an owner that can still write it, so the folded facts would not be stable; own it in the body or borrow it through a call",
                                describe_resource_clause(resource),
                                render_resource_fact_diagnostic(&lowered, parameter_binding)
                            )));
                        }
                        body_has_unbound_view = true;
                    }
                }
            }
            if preserve_exposed_body {
                // This body belonged to the active population before `with`.
                // The scope used it in place, so closing must leave that one
                // authoritative representation intact.
                continue;
            } else if closing_view {
                // A folded view already projects these duplicable view
                // cores. Opening the body makes its facts available but does
                // not create a linear representation that must be consumed
                // again when the scope closes.
                continue;
            } else if folded_representation_already_present
                && !post_state
                    .resources()
                    .satisfies_fact(&lowered, &assumptions)
            {
                // Exact execution may retain the folded contract resource
                // and downgrade its simultaneously exposed body to views.
                // Close those views when they are the representation that is
                // actually present; an absent body still fails below.
                let viewed = ResourceFact::View(lowered.resource().clone());
                if post_state.resources().satisfies_fact(&viewed, &assumptions) {
                    lowered = viewed;
                }
            }
            lowered_contained.push(lowered);
        }
        let mut witness_fold = post_state
            .resources()
            .prepare_structural_witness_fold(&witness_fold_children, &assumptions);
        let pre_fold_resources = post_state.resources().clone();
        let mut resources = post_state.resources().clone();
        for lowered in lowered_contained.as_slice() {
            let next = {
                // The kernel checks the selected exchange, with its frame intact.
                resources
                    .clone()
                    .without_fact_incrementally(lowered, &assumptions)
            };
            let Some(next) = next else {
                let diagnostic_facts = resources.facts().to_vec();
                let available_pure_facts = pure_facts.materialize();
                let target = describe_resource_clause(resource);
                let (action, refusal) = match closure {
                    ResourceBodyClosure::Initialize => {
                        (format!("`fold({target})`"), ProofRefusal::Tactic)
                    }
                    ResourceBodyClosure::CloseOpen { .. } => (
                        format!("closing `with({target})`"),
                        ProofRefusal::IncompleteProof,
                    ),
                };
                return Err(ClickError::new(format!(
                    "`{claim_label}` path {path_index}: {action} failed: {}",
                    describe_missing_resource_fact(
                        lowered,
                        &available_pure_facts,
                        &diagnostic_facts,
                        parameter_binding,
                        execution_pure_facts
                    )
                ))
                .with_proof_refusal(refusal));
            };
            resources = next;
        }
        post_state = Box::new(post_state.with_resource_context(resources));

        if closure == ResourceBodyClosure::Initialize && !folded_representation_already_present {
            let abstract_resource = lower_resource_clause_at_state_with_assumptions(
                resource,
                parameter_binding,
                &post_state,
                Some(&value.native()),
                pure_facts.assumptions(),
            )?;
            // Move only the selected principal views. A whole group can reuse
            // its hold. If siblings remain, give the head a separate hold so
            // consuming it cannot end the siblings' borrow.
            if selected_held_view && held_view_children.is_empty() && !abstract_resource.is_view() {
                return Err(ClickError::new(format!(
                    "`{claim_label}` path {path_index}: `fold` needs a directly held viewed piece to move into this resource"
                )));
            }
            if !held_view_children.is_empty() && !abstract_resource.is_view() {
                let mut resources = post_state.resources().clone();
                for occurrence in held_view_children {
                    resources = resources
                        .without_exact_representation_for_occurrence(occurrence)
                        .expect("the selected folded child is live");
                }
                post_state = Box::new(post_state.with_resource_context(resources));
            }
            let mut body_borrow_dependency = body_borrow_dependency;
            if let Some(binding) = body_borrow_dependency.as_mut()
                && !abstract_resource.is_view()
                && binding.hold.is_none_or(|hold| {
                    post_state.borrow_bindings().hold_occurrence_count(hold) != 0
                })
            {
                let (Some(ledger), Some(holder)) = (
                    post_state.borrow_ledger().cloned(),
                    post_state.borrow_participant(),
                ) else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` path {path_index}: `fold({})` packages a borrow-backed view without a borrow ledger",
                        describe_resource_clause(resource)
                    )));
                };
                let (ledger, hold, transition) = ledger
                    .hold_with_transition(binding, holder)
                    .map_err(|refusal| {
                        ClickError::new(format!(
                            "`{claim_label}` path {path_index}: `fold({})` cannot keep the borrow for its body views live: {refusal}",
                            describe_resource_clause(resource)
                        ))
                    })?;
                binding.hold = Some(hold);
                // The kernel checks the fold's ledger change against this
                // exact transition.
                borrow_holds.push(transition);
                post_state = Box::new(post_state.with_borrow_ledger(Some(ledger)));
            }
            // Authority rewrites authenticate the selected exchange only;
            // normalizing unrelated memory changes the checked frame.
            let (resources, inserted_occurrence) = {
                let (resources, inserted) = post_state
                    .resources()
                    .clone()
                    .try_compose_with_facts_delaying_normalization_with_occurrences(
                        std::iter::once(abstract_resource.clone()),
                        &assumptions,
                    )
                    .map_err(|error| {
                        ClickError::new(format!(
                            "`{claim_label}` path {path_index}: `fold({})` produced {}",
                            describe_resource_clause(resource),
                            describe_resource_context_validity_error(error, parameter_binding)
                        ))
                    })?;
                (
                    resources,
                    inserted
                        .into_iter()
                        .next()
                        .map(|(_, occurrence)| occurrence),
                )
            };
            let resources = resources.with_folded_structural_witness(
                witness_fold.take(),
                &abstract_resource,
                &assumptions,
            );
            folded_authority_occurrence = inserted_occurrence;
            post_state = Box::new(post_state.with_resource_context(resources));
            if let Some(definition) = authority_control_definition.as_ref() {
                post_state = Box::new(
                    post_state
                        .with_checked_current_control_wrapper(
                            &abstract_resource,
                            definition,
                            &assumptions,
                        )
                        .map_err(ClickError::new)?,
                );
            }

            if let (Some(occurrence), Some(binding)) =
                (folded_authority_occurrence, body_borrow_dependency.clone())
            {
                // A viewed fold describes the head itself under the borrow; an
                // owned fold keeps the packaged piece's description, which is
                // what the borrow authorizes and what an unfold restores.
                let viewed = if abstract_resource.is_view() {
                    abstract_resource.clone()
                } else {
                    binding.viewed.clone()
                };
                let resources = post_state.resources().clone();
                post_state = Box::new(post_state.with_resource_context_and_borrow_dependencies(
                    resources,
                    [(
                        occurrence,
                        crate::kernel::BorrowBinding { viewed, ..binding },
                    )],
                ));
            }
        }
        // A folded head supports views of its contained children. A
        // family that reaches a population keeps only
        // the checked exchange. Any other family keeps exactly the child
        // views the context already held, now supported by the head: the
        // fold consumed their owners and invents no new view.
        if closure == ResourceBodyClosure::Initialize
            && (!family_reaches_population)
            && !authority_control_body
            && !lowered_contained.is_empty()
        {
            let abstract_resource = lower_resource_clause_at_state_with_assumptions(
                resource,
                parameter_binding,
                &post_state,
                Some(&value.native()),
                pure_facts.assumptions(),
            )?;
            let assumptions = pure_facts.assumptions();
            let Some(authority_occurrence) = folded_authority_occurrence.or_else(|| {
                post_state
                    .resources()
                    .unique_owned_occurrence_for_fact(&abstract_resource)
                    .map(|(occurrence, _)| occurrence)
            }) else {
                return Err(ClickError::new(format!(
                    "`{claim_label}` path {path_index}: `fold({})` has an ambiguous folded authority",
                    describe_resource_clause(resource)
                )));
            };
            if !post_state
                .resources()
                .owned_occurrence_matches(authority_occurrence, &abstract_resource)
            {
                return Err(ClickError::new(format!(
                    "`{claim_label}` path {path_index}: `fold({})` changed its folded authority state",
                    describe_resource_clause(resource)
                )));
            }
            let authority = &abstract_resource;
            let projections = lowered_contained
                .iter()
                .filter_map(|fact| fact.core_with_assumptions(assumptions))
                .filter(|fact| !post_state.resources().contains_exact_representation(fact))
                .filter(|fact| pre_fold_resources.contains_exact_representation(fact))
                .collect::<BTreeSet<_>>();
            if !projections.is_empty() {
                let resources = post_state
                    .resources()
                    .clone()
                    .unchecked_with_supported_facts_from_occurrence_with_memory(
                        authority_occurrence,
                        authority,
                        projections,
                        post_state.memory(),
                    );
                post_state = Box::new(post_state.with_resource_context(resources));
            }
        }
        if matches!(closure, ResourceBodyClosure::CloseOpen { .. }) {
            let selected = lower_resource_clause_at_state_with_assumptions(
                resource,
                parameter_binding,
                &post_state,
                Some(&value.native()),
                pure_facts.assumptions(),
            )?;
            let resources = post_state
                .resources()
                .clone()
                .with_folded_structural_witness(
                    witness_fold.take(),
                    &selected,
                    pure_facts.assumptions(),
                );
            post_state = Box::new(post_state.with_resource_context(resources));
            if let Resource::Composite { name, arguments } | Resource::Token { name, arguments } =
                selected.resource()
            {
                post_state = Box::new(
                    post_state
                        .close_population_body(name.clone(), arguments.clone())
                        .map_err(ClickError::new)?,
                );
            }
        }
        // The checker must name exactly the resource whose captured arguments
        // were used for this exchange, rather than reevaluating the source
        // operand with a different state or normalization context.
        selections.push(lower_resource_clause_at_state_with_assumptions(
            resource,
            parameter_binding,
            &post_state,
            Some(&value.native()),
            pure_facts.assumptions(),
        )?);
        outcome = FunctionOutcome::Return {
            value,
            state: post_state,
        };
    }

    Ok((outcome, selections, borrow_holds))
}

pub(super) struct CheckedResourceFold {
    pub(super) selected: ResourceFact,
    pub(super) state: ExecutionState,
    pub(super) facts: PureFactStore,
    /// The hold a borrowing fold placed on the borrow behind its viewed body,
    /// which the kernel checks as the fold's only ledger change.
    pub(super) borrow_holds: Vec<crate::kernel::CheckedBorrowTransition>,
}

/// A folded outcome, the resources it selected, and the borrow holds its
/// borrowing folds placed.
type FoldedOutcome = (
    FunctionOutcome,
    Vec<ResourceFact>,
    Vec<crate::kernel::CheckedBorrowTransition>,
);

pub(super) struct CheckedOutcomeResourceFold {
    pub(super) selected: ResourceFact,
    pub(super) outcome: FunctionOutcome,
    pub(super) facts: PureFactStore,
}

/// Checks one ordinary pre-execution `fold` against a persistent Proof
/// frontier. This transition owns exactly one source step and does not
/// materialize the complete ambient fact sequence on its success path.
#[allow(clippy::too_many_arguments)]
pub(super) fn fold_composite_resource_for_proof(
    resource_environment: &ResourceEnvironment,
    resource: &ResourceClause,
    source_resource: &ResourceClause,
    claim_label: &str,
    tactic_index: usize,
    facts: PureFactStore,
    parameter_binding: ParameterBinding<'_>,
    pre_state: &ExecutionState,
    state: ExecutionState,
    spec_definitions: SpecDefinitions<'_>,
    family_reaches_population: bool,
) -> Result<CheckedResourceFold, ClickError> {
    fold_composite_resource_for_proof_with_closure(
        resource_environment,
        resource,
        source_resource,
        claim_label,
        tactic_index,
        facts,
        parameter_binding,
        pre_state,
        state,
        spec_definitions,
        ResourceBodyClosure::Initialize,
        family_reaches_population,
    )
}

/// Checks one result-aware `fold` against the persistent facts and state
/// owned by a typed function-outcome goal. The returned outcome and fact root
/// are the semantic successor; ordered finalization must not reproduce this
/// transition in a parallel mutable working set.
#[allow(clippy::too_many_arguments)]
pub(super) fn fold_composite_resource_on_outcome_for_proof(
    resource_environment: &ResourceEnvironment,
    resource: &ResourceClause,
    claim_label: &str,
    path_index: usize,
    execution_pure_facts: &(impl ExecutionFactSource + ?Sized),
    facts: PureFactStore,
    parameter_binding: ParameterBinding<'_>,
    pre_state: &ExecutionState,
    outcome: FunctionOutcome,
    spec_definitions: SpecDefinitions<'_>,
    closure: ResourceBodyClosure,
    family_reaches_population: bool,
) -> Result<CheckedOutcomeResourceFold, ClickError> {
    let mut facts = ProofResourcePureFacts::new(facts);
    // A return fold's ledger change, if any, is not presented to the kernel
    // as a hold: the return rewrite check keeps refusing it.
    let (outcome, mut selections, _) = fold_composite_resources_on_outcome_with_facts(
        resource_environment,
        std::slice::from_ref(resource),
        None,
        claim_label,
        path_index,
        execution_pure_facts,
        &facts,
        parameter_binding,
        pre_state,
        outcome,
        spec_definitions,
        closure,
        family_reaches_population,
    )?;
    let selected = selections
        .pop()
        .expect("one fold has one selected resource");
    // A scope close exposes only its restored composite's observations.
    // Unrelated resources and their observation laws are unchanged; do not
    // scan/reproject the whole outcome for each closed scope.
    if matches!(closure, ResourceBodyClosure::CloseOpen { .. })
        && let FunctionOutcome::Return { value, state } = &outcome
    {
        let requested = &selected;
        let viewed = ResourceFact::View(requested.resource().clone());
        let support = state
            .resources()
            .directly_supporting_fact(requested, facts.assumptions())
            .or_else(|| {
                state
                    .resources()
                    .directly_supporting_fact(&viewed, facts.assumptions())
            })
            .cloned();
        if let Some(support) = support {
            project_held_resource_observable_facts(
                resource_environment,
                &support,
                parameter_binding,
                pre_state,
                state,
                &value.native(),
                &mut facts,
                spec_definitions,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` path {path_index}: scope resource projection: {message}"
                ))
            })?;
        }
    }
    Ok(CheckedOutcomeResourceFold {
        selected,
        outcome,
        facts: facts.facts,
    })
}

#[allow(clippy::too_many_arguments)]
pub(super) fn close_open_resource_for_proof(
    resource_environment: &ResourceEnvironment,
    resource: &ResourceClause,
    claim_label: &str,
    tactic_index: usize,
    facts: PureFactStore,
    parameter_binding: ParameterBinding<'_>,
    pre_state: &ExecutionState,
    state: ExecutionState,
    spec_definitions: SpecDefinitions<'_>,
    preserve_exposed_body: bool,
) -> Result<CheckedResourceFold, ClickError> {
    fold_composite_resource_for_proof_with_closure(
        resource_environment,
        resource,
        resource,
        claim_label,
        tactic_index,
        facts,
        parameter_binding,
        pre_state,
        state,
        spec_definitions,
        ResourceBodyClosure::CloseOpen {
            preserve_exposed_body,
        },
        true,
    )
}

#[allow(clippy::too_many_arguments)]
fn fold_composite_resource_for_proof_with_closure(
    resource_environment: &ResourceEnvironment,
    resource: &ResourceClause,
    source_resource: &ResourceClause,
    claim_label: &str,
    tactic_index: usize,
    facts: PureFactStore,
    parameter_binding: ParameterBinding<'_>,
    pre_state: &ExecutionState,
    state: ExecutionState,
    spec_definitions: SpecDefinitions<'_>,
    closure: ResourceBodyClosure,
    family_reaches_population: bool,
) -> Result<CheckedResourceFold, ClickError> {
    let facts = ProofResourcePureFacts::new(facts);
    let outcome = FunctionOutcome::Return {
        value: ProgramValue::Int32(MachineTerm::constant(0)).into(),
        state: Box::new(state),
    };
    let (outcome, mut selections, borrow_holds) = fold_composite_resources_on_outcome_with_facts(
        resource_environment,
        std::slice::from_ref(resource),
        Some(source_resource),
        claim_label,
        tactic_index,
        &[],
        &facts,
        parameter_binding,
        pre_state,
        outcome,
        spec_definitions,
        closure,
        family_reaches_population,
    )?;
    let FunctionOutcome::Return { state, .. } = outcome else {
        unreachable!("folding a synthetic return outcome preserves its outcome kind")
    };
    Ok(CheckedResourceFold {
        selected: selections
            .pop()
            .expect("one fold has one selected resource"),
        state: *state,
        facts: facts.facts,
        borrow_holds,
    })
}

/// Lower the iterated clause of the named resource with the tactic's arguments.
pub(super) fn iterated_template_for_resource(
    resource_environment: &ResourceEnvironment,
    resource: &ResourceClause,
    action: &str,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    claim_label: &str,
    tactic_index: usize,
    assumptions: &PureFactContext,
) -> Result<crate::kernel::IteratedMemory, ClickError> {
    let definition = composite_resource_law_definition(
        resource_environment,
        resource,
        action,
        claim_label,
        tactic_index,
    )?;
    let body = definition
        .composite_body()
        .expect("composite_resource_law_definition should require a composite body");
    let Some(clause) = body.contains().iter().find_map(|clause| match clause {
        ResourceClause::Iterated(clause) => Some(clause),
        _ => None,
    }) else {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{action}` expects a resource whose body declares iterated ownership, but `{}` declares none",
            definition.name()
        )));
    };
    let substitutions =
        resource_argument_substitutions(definition, resource, claim_label, tactic_index)?;
    let clause = substitute_iterated_clause(clause, &ContractSubstitutions::new(&substitutions))
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: could not instantiate the iterated clause of `{}`: {message}",
                definition.name()
            ))
        })?;
    lower_iterated_clause_at_current_locals(&clause, parameter_binding, state, assumptions)
}

fn composite_resource_law_definition<'a>(
    resource_environment: &'a ResourceEnvironment,
    resource: &ResourceClause,
    action: &str,
    claim_label: &str,
    tactic_index: usize,
) -> Result<&'a ResourceDefinition, ClickError> {
    let resource = match resource {
        ResourceClause::Quantified { resource, .. }
            if matches!(action, "fold" | "unfold" | "observe") =>
        {
            resource.as_ref()
        }
        _ => resource,
    };
    let ResourceClause::Declared { name, .. } = resource else {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{action}` expects a composite resource"
        )));
    };
    if matches!(action, "fold" | "unfold")
        && !matches!(
            resource,
            ResourceClause::Declared {
                access: ResourceAccessMode::Own,
                ..
            }
        )
    {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{action}` expects an owned composite resource"
        )));
    }
    if !matches!(
        resource,
        ResourceClause::Declared {
            kind: ResourceKind::Composite,
            ..
        }
    ) {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{action}` expects resource `{name}` to have a body"
        )));
    }
    let definition = resource_environment.get(name).ok_or_else(|| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: unknown resource `{name}`"
        ))
    })?;
    if definition.composite_body().is_none() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: `{action}` expects composite resource `{name}` to have a body"
        )));
    }
    Ok(definition)
}

/// Extends the parameter substitutions of a composite body with its
/// existential witnesses, bound to the values the kernel binds them to for
/// this resource under `state` and `assumptions`. The substitution is a
/// value literal, so later clauses mention exactly the pointer the kernel's
/// own body instantiation uses.
fn extend_substitutions_with_witnesses(
    substitutions: &mut BTreeMap<String, ContractExpression>,
    definition: &ResourceDefinition,
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    result: Option<&ProgramValue>,
    assumptions: &PureFactContext,
    resource_environment: &ResourceEnvironment,
    spec_definitions: SpecDefinitions<'_>,
    compiled_definitions: Option<&[CompositeResourceDefinition]>,
) -> Result<(), ClickError> {
    let Some(body) = definition.composite_body() else {
        return Ok(());
    };
    if body.witnesses().is_empty() {
        return Ok(());
    }
    let resource = match resource {
        ResourceClause::Quantified { resource, .. } => resource.as_ref(),
        _ => resource,
    };
    let fact = lower_resource_clause_at_state_with_assumptions(
        resource,
        parameter_binding,
        state,
        result,
        assumptions,
    )?;
    let owned_definitions;
    let definitions = if let Some(definitions) = compiled_definitions {
        definitions
    } else {
        owned_definitions = crate::surface::verification::composite_resource_definitions(
            resource_environment,
            spec_definitions,
        )?;
        &owned_definitions
    };
    let values = crate::kernel::composite_resource_witness_values(
        &fact,
        definitions,
        state.memory(),
        state.resources(),
        assumptions,
    )
    .ok_or_else(|| {
        ClickError::new(format!(
            "could not bind the witnesses of resource `{}`",
            definition.name()
        ))
    })?;
    for (witness, value) in body.witnesses().iter().zip(values) {
        substitutions.insert(
            witness.name().to_string(),
            ContractExpression::ProgramExpression(ProgramExpression::Value(value)),
        );
    }
    Ok(())
}

/// Whether `value` is an integer constant, which a requirement spells as its
/// literal.
pub(in crate::surface::proof) fn is_integer_constant(value: &ProgramValue) -> bool {
    matches!(
        value,
        ProgramValue::Int8(term)
            | ProgramValue::Int16(term)
            | ProgramValue::Int32(term)
            | ProgramValue::Int64(term)
            | ProgramValue::UInt8(term)
            | ProgramValue::UInt16(term)
            | ProgramValue::UInt32(term)
            | ProgramValue::UInt64(term)
            if matches!(
                term,
                bits32_constant!(_)
                    | int64_constant!(_)
                    | uint64_constant!(_)
            )
    )
}

pub(super) fn resource_argument_substitutions(
    definition: &ResourceDefinition,
    resource: &ResourceClause,
    claim_label: &str,
    tactic_index: usize,
) -> Result<BTreeMap<String, ContractExpression>, ClickError> {
    let resource = match resource {
        ResourceClause::Quantified { resource, .. } => resource.as_ref(),
        _ => resource,
    };
    let ResourceClause::Declared {
        name,
        arguments,
        parameter_types,
        ..
    } = resource
    else {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: expected declared resource"
        )));
    };
    if definition.name() != name {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: resource definition mismatch for `{name}`"
        )));
    }
    if definition.parameters().len() != arguments.len() {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: resource `{name}` expects {} argument(s), got {}",
            definition.parameters().len(),
            arguments.len()
        )));
    }
    let expected_types = definition
        .parameters()
        .iter()
        .map(FunctionParameter::interface_type)
        .collect::<Vec<_>>();
    if parameter_types != &expected_types {
        return Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: resource `{name}` has malformed argument type metadata"
        )));
    }
    Ok(definition
        .parameters()
        .iter()
        .zip(arguments)
        .map(|(parameter, argument)| (parameter.name().to_string(), argument.clone()))
        .collect())
}

pub(super) fn instantiate_resource_clause(
    resource: &ResourceClause,
    substitutions: &BTreeMap<String, ContractExpression>,
) -> Result<ResourceClause, String> {
    match resource {
        ResourceClause::Conditional {
            condition,
            resource,
        } => Ok(ResourceClause::Conditional {
            condition: substitute_click_proposition(condition, substitutions)?,
            resource: Box::new(instantiate_resource_clause(resource, substitutions)?),
        }),
        ResourceClause::Named { binding, resource } => Ok(ResourceClause::Named {
            binding: binding.clone(),
            resource: Box::new(instantiate_resource_clause(resource, substitutions)?),
        }),
        ResourceClause::Quantified { quantity, resource } => Ok(ResourceClause::Quantified {
            quantity: substitute_contract_expression(quantity, substitutions)?,
            resource: Box::new(instantiate_resource_clause(resource, substitutions)?),
        }),
        ResourceClause::ViewMemory(segment) => Ok(ResourceClause::ViewMemory(
            instantiate_contract_segment(segment, substitutions)?,
        )),
        ResourceClause::OwnMemory(segment) => Ok(ResourceClause::OwnMemory(
            instantiate_contract_segment(segment, substitutions)?,
        )),
        ResourceClause::Iterated(clause) => Ok(ResourceClause::Iterated(Box::new(
            substitute_iterated_clause(clause, &ContractSubstitutions::new(substitutions))?,
        ))),
        ResourceClause::MemoryAggregate { access, segments } => {
            Ok(ResourceClause::MemoryAggregate {
                access: *access,
                segments: segments
                    .iter()
                    .map(|segment| instantiate_contract_segment(segment, substitutions))
                    .collect::<Result<Vec<_>, _>>()?,
            })
        }
        ResourceClause::Declared {
            type_schema,
            resource_type_arguments,
            resource_arguments,
            access,
            kind,
            name,
            arguments,
            parameter_types,
        } => Ok(ResourceClause::Declared {
            type_schema: type_schema.clone(),
            resource_type_arguments: resource_type_arguments
                .iter()
                .map(|resource| instantiate_resource_clause(resource, substitutions))
                .collect::<Result<_, _>>()?,
            resource_arguments: resource_arguments.clone(),
            access: *access,
            kind: *kind,
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_contract_expression(argument, substitutions))
                .collect::<Result<Vec<_>, _>>()?,
            parameter_types: parameter_types.clone(),
        }),
    }
}

fn instantiate_contract_segment(
    segment: &ContractSegment,
    substitutions: &BTreeMap<String, ContractExpression>,
) -> Result<ContractSegment, String> {
    let surface = match &segment.surface {
        ContractSegmentSurface::Range { base, start, end } => ContractSegmentSurface::Range {
            base: substitute_contract_expression(base, substitutions)?,
            start: substitute_contract_expression(start, substitutions)?,
            end: substitute_contract_expression(end, substitutions)?,
        },
        ContractSegmentSurface::StructRange {
            base,
            start,
            end,
            layout,
        } => ContractSegmentSurface::StructRange {
            base: substitute_contract_expression(base, substitutions)?,
            start: substitute_contract_expression(start, substitutions)?,
            end: substitute_contract_expression(end, substitutions)?,
            layout: layout.clone(),
        },
        surface => surface.clone(),
    };
    Ok(ContractSegment {
        uninitialized: segment.uninitialized,
        state: segment.state,
        base: substitute_program_expression(&segment.base, substitutions)?,
        start: substitute_program_expression(&segment.start, substitutions)?,
        end: substitute_program_expression(&segment.end, substitutions)?,
        surface,
    })
}

fn names_plain_scalar_body_at_entry(body: &CompositeResourceBody) -> bool {
    body.fields.is_empty()
        && body.facts().is_empty()
        && body.condition().is_none()
        && body.matched.is_none()
        && matches!(body.contains(), [ResourceClause::OwnMemory(_)])
}

fn materialize_composite_resource_cells_from_state(
    mut memory: SymbolicMemory,
    naming_point: &crate::kernel::ProgramPoint,
    resource_clause: &ResourceClause,
    lowered: &ResourceFact,
    parameters: &[crate::languages::interface::ImportedParameter],
    name_at_entry: bool,
) -> SymbolicMemory {
    let Some((segment, range)) = (match resource_clause {
        ResourceClause::Conditional { .. } => None,
        ResourceClause::Named { .. } => None,
        ResourceClause::ViewMemory(segment) => {
            lowered.memory_view_range().map(|range| (segment, range))
        }
        ResourceClause::OwnMemory(segment) => {
            lowered.memory_own_range().map(|range| (segment, range))
        }
        ResourceClause::Declared { .. }
        | ResourceClause::Quantified { .. }
        | ResourceClause::Iterated(_) => None,
        ResourceClause::MemoryAggregate { .. } => None,
    }) else {
        return memory;
    };
    // A whole object of a symbolic layout, `[p, p + sizeof(S))`, has its
    // fields at their `offsetof` terms: each is observed as a concrete
    // object's is.
    if let Some(layout) = range.symbolic_object()
        && !range.has_holes()
    {
        for field in 0..layout.field_count() {
            // An embedded record holds no one cell.
            let Some(field_type) = layout.field_type(field) else {
                continue;
            };
            let pointer = range.base().offset_by_layout(layout.field_offset(field));
            if !matches!(memory.load(&pointer), ExpressionOutcome::Value(_)) {
                memory = memory.materialize_cell_at(pointer, field_type, naming_point);
            }
        }
        return memory;
    }
    // Only signed constant spans have the bounded cell-materialization rule.
    let Some((int32_constant!(start), bits32_constant!(end))) = range.int32_bounds() else {
        return memory;
    };
    if constant_u32(*end) < constant_u32(*start) {
        return memory;
    }

    // Observe complete typed fields. In particular, an eight-byte pointer read
    // cannot reuse two independently named four-byte integer observations.
    if let Some(layout) = crate::surface::lowering::object_segment_layout(parameters, segment)
        && constant_u32(*start) == 0
    {
        for field in layout.fields().values() {
            memory = crate::surface::lowering::visit_struct_field_cells(
                field,
                range.base(),
                memory,
                |mut memory, pointer, element_type| {
                    if !matches!(memory.load(&pointer), ExpressionOutcome::Value(_)) {
                        // Function pointers retain their scalar function-name
                        // carrier. Object-pointer observations use the same
                        // selected source as the range path below.
                        let storage_type =
                            if matches!(element_type, ProgramType::FunctionPointer(_)) {
                                ProgramType::Int32
                            } else {
                                element_type
                            };
                        memory = memory.materialize_cell_at(pointer, storage_type, naming_point);
                    }
                    memory
                },
            );
        }
        return memory;
    }
    let element_width = contract_segment_element_width(parameters, segment);
    let segment_type = contract_segment_element_type(parameters, segment);
    // A scalar field's ownership span can include alignment padding. Its retained
    // declaration names only the actual scalar/array elements, not typed reads
    // of every word in that wider span.
    let (element_width, start, end) = if let Some(count) =
        crate::surface::lowering::declared_segment_observation_count(segment)
    {
        let width = segment_type.byte_width();
        let Some(first_byte) = constant_u32(*start).checked_mul(element_width) else {
            return memory;
        };
        let Some(end_byte) = constant_u32(*end).checked_mul(element_width) else {
            return memory;
        };
        if !first_byte.is_multiple_of(width) {
            return memory;
        }
        let first = first_byte / width;
        let Some(last) = first.checked_add(count) else {
            return memory;
        };
        if last.checked_mul(width).is_none_or(|bytes| bytes > end_byte) {
            return memory;
        }
        (width, first, last)
    } else {
        (element_width, constant_u32(*start), constant_u32(*end))
    };
    // Keep typed reads at their physical stride. A narrower byte/word view
    // does not authorize overlapping whole-pointer observations.
    let run_type = if !segment_type.is_pointer()
        || (segment_type.is_object_pointer() && segment_type.byte_width() <= element_width)
    {
        segment_type
    } else if element_width == 1 {
        ProgramType::UInt8
    } else {
        ProgramType::Int32
    };
    let point_named = name_at_entry
        && start == 0
        && run_type == ProgramType::Int32
        && element_width == ProgramType::Int32.byte_width()
        && matches!(&segment.base,
            ProgramExpression::Value(value) if value.program_type() == ProgramType::Int32Pointer)
        && naming_point
            .entry_integer_version(range.base(), crate::kernel::LoadKind::Int32)
            .is_some();
    if point_named && end == 1 {
        return memory.materialize_entry_integer_cell_at(range.base().clone(), naming_point);
    }
    if run_type.byte_width() <= element_width {
        let indexed_pointer_field = run_type.is_object_pointer()
            && start == 0
            && end == 1
            && naming_point
                .indexed_typed_version(range.base(), run_type)
                .is_some();
        let point_named_float = crate::kernel::KernelFloatType::from_program_type(run_type)
            .is_some()
            && naming_point.has_certified_read_view();
        let source = if point_named_float
            || indexed_pointer_field
            || naming_point
                .entry_cell_version(range.base(), run_type)
                .is_some()
        {
            naming_point.clone()
        } else {
            // Named by the memory, as a legacy read is, and recording the
            // point the cells are read at.
            crate::kernel::ProgramPoint::at_read_site(naming_point.shared_memory(), naming_point)
        };
        match memory.with_named_cell_run(
            range.base().clone(),
            element_width,
            run_type,
            start,
            end,
            source,
        ) {
            Ok(seeded) => return seeded,
            Err(unchanged) => memory = unchanged,
        }
    }
    for index in start..end {
        let pointer = offset_pointer_by_elements(
            range.base().clone(),
            MachineTerm::constant(index),
            element_width,
        );
        if matches!(memory.load(&pointer), ExpressionOutcome::Value(_)) {
            continue;
        }
        memory = memory.materialize_cell_at(pointer, run_type, naming_point);
    }
    memory
}

#[cfg(test)]
mod v11_resource_dependency_tests {
    use super::*;

    #[test]
    fn authority_body_read_projection_retires_only_its_owned_observations() {
        let source = r#"import click::integer;

authorized resource child_ref(obj: struct child*) {}
resource child_control(obj: struct child*) {
    owns allocation(obj, sizeof(struct child));
    owns *obj;
    owns authority(child_ref(obj));
    fact defined(obj->refs);
    fact defined(obj->payload);
    fact to_integer(obj->refs) == to_integer(count(child_ref(obj)));
}
verifying "control.c";
void child_release(struct child* obj) {
    requires 1 < obj->refs;
    owns child_control(obj);
    owns child_ref(obj);
    consumes child_ref(obj);
    ensures obj->payload == old(obj->payload);
} by {
    unfold(child_control(obj));
    unfold(child_ref(obj));
    have to_integer(obj->refs - 1) >= 1;
    step();
    fold(child_control(obj));
    step_until(function.exit);
    close();
}
"#;
        let project = ClickProject::new(
            "control.click",
            [ClickModuleSource::new("control.click", source, [])],
        )
        .with_c_profile(CProjectProfile {
            target: None,
            runtime: None,
        });
        let verified = crate::surface::verify_c_project(
            &project,
            &[("control.c", "struct child { int32 refs; int32 payload; }; void child_release(struct child* obj) { obj->refs = obj->refs - 1; }")],
        )
        .expect("the fixed helper's authority contract verifies");
        let execution = &verified[0].checked_execution;
        let path = &execution.paths()[0];
        let Proposition::ProgramFunctionVerifies { outcome, .. } =
            implication_body(path.theorem().proposition())
        else {
            panic!("the helper has a checked C outcome")
        };
        let FunctionOutcome::Return { state, .. } = outcome else {
            panic!("the helper returns")
        };
        let assumptions = path.assumptions();
        let head = state.resources().facts().iter().find(|fact| {
            matches!(fact.resource(), Resource::Composite { name, .. } if name == "child_control")
        }).unwrap();
        let definition = execution
            .function()
            .composite_resource_definitions()
            .iter()
            .find(|definition| definition.name() == "child_control")
            .unwrap();
        let (children, _) = state
            .checked_authority_wrapper_body(head, definition, assumptions)
            .expect("the returned control owns its authenticated body");
        let range = children
            .iter()
            .find_map(ResourceFact::memory_own_range)
            .unwrap();
        let view = ResourceFact::view_memory(range.clone());
        let occurrence = state.resources().owned_occurrences_for_fact(head)[0];
        // This is the exact owner observation published by a modular return,
        // with its support occurrence, not an independently returned view.
        let observed = state.clone().with_resource_context(
            state
                .resources()
                .clone()
                .unchecked_with_supported_facts_from_occurrence_with_memory(
                    occurrence,
                    head,
                    [view.clone()],
                    state.memory(),
                ),
        );
        assert!(
            observed
                .resources()
                .exact_projection_support(&view)
                .is_some()
        );
        let fact = Proposition::MemoryReadDefined {
            at: None,
            memory: observed.memory().clone(),
            pointer: range.base().offset_by_bytes(4),
            value_type: ProgramType::Int32,
        };
        let no_temporary_views = DynamicViewDependencyIndex::new(&[], &[], assumptions);
        assert!(
            dynamic_body_fact_dependency(&fact, &observed, assumptions, &no_temporary_views,)
                .is_err(),
            "an observation alone does not grant a stable-view borrow"
        );
        let (projected, _) = observed
            .checked_authority_wrapper_projection(head, definition, assumptions)
            .unwrap();
        let projected_state = observed.clone().with_resource_context(projected);
        assert!(dynamic_body_fact_dependency(
            &fact, &projected_state, assumptions, &no_temporary_views,
        ).unwrap().is_none(), "the checked private body grants owned memory access");
        let unbound = projected_state.clone().with_resource_context(
            projected_state
                .resources()
                .clone()
                .unchecked_with_fact(view),
        );
        assert!(
            dynamic_body_fact_dependency(&fact, &unbound, assumptions, &no_temporary_views,)
                .is_err(),
            "an unrelated unbound view must still be refused beside ownership"
        );
    }

    fn binding_for(
        support: crate::kernel::ResourceOccurrenceId,
        viewed: ResourceFact,
    ) -> crate::kernel::BorrowBinding {
        let ledger = crate::kernel::BorrowLedger::new();
        let owner = ledger.fresh_participant().unwrap();
        let reader = ledger.fresh_participant().unwrap();
        let escrow = ResourceFact::own_token("v11_surface_support".into(), Vec::new());
        let opening = ledger.lend(owner, reader, support, escrow).unwrap();
        crate::kernel::BorrowBinding {
            borrow: opening.borrow,
            scope: opening.scope,
            share: opening.root_share,
            support,
            viewed,
            hold: None,
        }
    }

    #[test]
    fn duplicate_equal_view_dependencies_fail_closed() {
        let support = ResourceFact::own_token("v11_surface_support".into(), Vec::new());
        let child = ResourceFact::view_token("v11_surface_child".into(), Vec::new());
        let resources = ResourceContext::new().unchecked_with_facts([
            support.clone(),
            child.clone(),
            child.clone(),
        ]);
        let support_occurrence = resources.owned_occurrences_for_fact(&support)[0];
        let occurrences = resources.occurrences_for_fact(&child);
        let binding = binding_for(support_occurrence, child.clone());
        let state = ExecutionState::new().with_resource_context_and_borrow_dependencies(
            resources,
            [(occurrences[0], binding.clone())],
        );
        assert!(unique_borrowed_resource_dependency(&state, &child).is_err());

        let second = ResourceFact::view_token("v11_surface_other".into(), Vec::new());
        let mut different = binding;
        different.viewed = second;
        let resources = state.resources().clone();
        let state = state.with_resource_context_and_borrow_dependencies(
            resources,
            [(occurrences[1], different)],
        );
        assert!(unique_borrowed_resource_dependency(&state, &child).is_err());
    }

    #[test]
    fn dynamic_current_fact_requires_live_view_binding_and_keeps_owner_scalar_distinct() {
        check_dynamic_current_fact_dependencies(false, false);
    }

    #[test]
    fn dynamic_definedness_requires_live_view_binding_and_keeps_owner_scalar_distinct() {
        check_dynamic_current_fact_dependencies(true, false);
    }

    #[test]
    fn dynamic_definedness_uses_the_observation_point_for_borrow_dependencies() {
        let _session = crate::kernel::VerificationSession::enter();
        let earlier = ExecutionState::new().with_memory(SymbolicMemory::new());
        let current = earlier.clone().with_memory(earlier.memory().clone());
        let earlier_point = earlier.observation_point_id().unwrap();
        let current_point = current.observation_point_id().unwrap();
        assert_ne!(earlier_point, current_point);
        assert!(earlier.memory().same_storage_roots(current.memory()));

        let assumptions = PureFactContext::new();
        let no_views = DynamicViewDependencyIndex::new(&[], &[], &assumptions);
        let dependency_at = |at| {
            let fact = Proposition::MemoryReadDefined {
                at,
                memory: earlier.memory().clone(),
                pointer: Address {
                    base: AddressBase::ExternalArgument,
                    offset: AddressOffset::Constant(0),
                },
                value_type: ProgramType::Int32,
            };
            dynamic_body_fact_dependency(&fact, &current, &assumptions, &no_views)
        };

        assert!(dependency_at(Some(earlier_point)).unwrap().is_none());
        assert!(dependency_at(Some(current_point)).is_err());
        assert!(dependency_at(None).is_err());
    }

    /// A guarded universal read depends on a view of every cell its guard
    /// admits, not on the one symbolic cell `p[k]`, which no view contains.
    #[test]
    fn dynamic_quantified_definedness_depends_on_the_guarded_range() {
        let base = Address {
            base: AddressBase::ExternalArgument,
            offset: AddressOffset::Constant(0),
        };
        let memory = SymbolicMemory::new();
        let index = Variable(2_000_000);
        let index_term = || Box::new(MachineTerm::Variable(index));
        let below = |end: u32| {
            Proposition::condition_is(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: index_term(),
                    right: Box::new(MachineTerm::constant(end)),
                },
                true,
            )
        };
        let at_least_zero = Proposition::condition_is(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left: Box::new(MachineTerm::constant(0)),
                right: index_term(),
            },
            true,
        );
        let quantified = |guard: Proposition| {
            crate::kernel::quantifiers::test_forall(
                Default::default(),
                index,
                crate::kernel::Sort::ProgramInt32,
                Proposition::Implies(
                    Box::new(guard),
                    Box::new(Proposition::MemoryReadDefined {
                        at: None,
                        memory: memory.clone(),
                        pointer: Address {
                            base: AddressBase::ExternalArgument,
                            offset: AddressOffset::Int32Scaled {
                                value: crate::kernel::SharedMachineIntegerTerm::index(
                                    crate::kernel::MachineIntegerType::Int32,
                                    *index_term(),
                                ),
                                byte_width: 4,
                            },
                        },
                        value_type: crate::kernel::ProgramType::Int32,
                    }),
                ),
            )
        };
        let range = MemoryRange::new(base, MachineTerm::constant(0), MachineTerm::constant(4));
        let own = ResourceFact::own_memory(range.clone());
        let view = ResourceFact::view_memory(range);
        let support_resources = ResourceContext::new().unchecked_with_fact(own.clone());
        let support = support_resources.owned_occurrences_for_fact(&own)[0];
        let ledger = crate::kernel::BorrowLedger::new();
        let lender = ledger.fresh_participant().unwrap();
        let opening = ledger.lend(lender, lender, support, own).unwrap();
        let ledger = ledger.apply(&opening.transition).unwrap();
        let binding = crate::kernel::BorrowBinding {
            borrow: opening.borrow,
            scope: opening.scope,
            share: opening.root_share,
            support,
            viewed: view.clone(),
            hold: None,
        };
        let bound_resources = ResourceContext::new().unchecked_with_fact(view.clone());
        let view_occurrence = bound_resources.occurrences_for_fact(&view)[0];
        let state = ExecutionState::new()
            .with_memory(memory.clone())
            .with_resource_context_and_borrow_dependencies(
                bound_resources,
                [(view_occurrence, binding)],
            )
            .with_borrow_ledger(Some(ledger))
            .with_borrow_participant(Some(lender));
        let no_temporary_views = DynamicViewDependencyIndex::new(&[], &[], &PureFactContext::new());
        let dependency = |fact: &Proposition| {
            dynamic_body_fact_dependency(fact, &state, &PureFactContext::new(), &no_temporary_views)
        };
        let within = quantified(Proposition::And(
            Box::new(at_least_zero.clone()),
            Box::new(below(4)),
        ));
        assert!(
            dependency(&within).unwrap().is_some(),
            "a guard inside the view keeps the view's borrow"
        );
        let beyond = quantified(Proposition::And(
            Box::new(at_least_zero),
            Box::new(below(5)),
        ));
        assert!(
            dependency(&beyond).is_err(),
            "a guard admitting a cell past the view is refused"
        );
        assert!(
            dependency(&quantified(below(4))).is_err(),
            "a signed index with no lower bound admits negative cells"
        );
    }

    #[test]
    fn dynamic_fact_keeps_the_binding_when_coverage_uses_a_symbolic_range() {
        check_dynamic_current_fact_dependencies(false, true);
    }

    fn check_dynamic_current_fact_dependencies(definedness: bool, symbolic_range: bool) {
        let pointer = Address {
            base: AddressBase::ExternalArgument,
            offset: AddressOffset::Constant(0),
        };
        let memory = SymbolicMemory::new().store(
            pointer.clone(),
            ProgramValue::Int32(MachineTerm::constant(0)),
        );
        let retained_state = crate::kernel::intern_memory_ref(&memory);
        let condition = ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::read_named(
                crate::kernel::ProgramPoint::at(&retained_state),
                Box::new(pointer.clone()),
                crate::kernel::LoadKind::Int32,
            )),
            right: Box::new(MachineTerm::constant(0)),
        };
        let proposition = if definedness {
            Proposition::MemoryReadDefined {
                at: None,
                memory: memory.clone(),
                pointer: pointer.clone(),
                value_type: crate::kernel::ProgramType::Int32,
            }
        } else {
            Proposition::condition_is(condition, true)
        };
        let span = if symbolic_range {
            MachineTerm::Variable(Variable(2_000_017))
        } else {
            MachineTerm::constant(1)
        };
        let assumptions = PureFactContext::new().assume_proposition(Proposition::condition_is(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(span.clone()),
                right: Box::new(MachineTerm::constant(1)),
            },
            true,
        ));
        let range = MemoryRange::new(pointer, MachineTerm::constant(0), span);
        let own = ResourceFact::own_memory(range.clone());
        let view = ResourceFact::view_memory(range.clone());
        let support_resources = ResourceContext::new().unchecked_with_fact(own.clone());
        let support = support_resources.owned_occurrences_for_fact(&own)[0];
        let ledger = crate::kernel::BorrowLedger::new();
        let lender = ledger.fresh_participant().unwrap();
        let reader = ledger.fresh_participant().unwrap();
        let opening = ledger.lend(lender, lender, support, own.clone()).unwrap();
        let ledger = ledger.apply(&opening.transition).unwrap();
        let binding = crate::kernel::BorrowBinding {
            borrow: opening.borrow,
            scope: opening.scope,
            share: opening.root_share,
            support,
            viewed: view.clone(),
            hold: None,
        };
        // The borrower receives only the view; the lender's owned support
        // remains in the caller state that supplied the exact occurrence.
        let bound_resources = ResourceContext::new().unchecked_with_fact(view.clone());
        let view_occurrence = bound_resources.occurrences_for_fact(&view)[0];
        let bound_state = ExecutionState::new()
            .with_memory(memory.clone())
            .with_resource_context_and_borrow_dependencies(
                bound_resources,
                [(view_occurrence, binding)],
            )
            .with_borrow_ledger(Some(ledger.clone()))
            .with_borrow_participant(Some(lender));
        let no_temporary_views = DynamicViewDependencyIndex::new(&[], &[], &assumptions);
        let dependency = dynamic_body_fact_dependency(
            &proposition,
            &bound_state,
            &assumptions,
            &no_temporary_views,
        )
        .unwrap();
        assert!(
            dependency.is_some(),
            "current viewed memory must retain its borrow"
        );
        if symbolic_range {
            assert!(
                dynamic_body_fact_dependency(
                    &proposition,
                    &bound_state,
                    &PureFactContext::new(),
                    &no_temporary_views,
                )
                .is_err(),
                "coverage still needs the range bound"
            );
        }

        assert!(
            dynamic_body_fact_dependency(
                &proposition,
                &bound_state.clone().with_borrow_participant(Some(reader)),
                &assumptions,
                &no_temporary_views,
            )
            .is_err(),
            "the wrong holder cannot validate the binding"
        );
        let ended = ledger
            .apply(&ledger.end(opening.scope, lender).unwrap())
            .unwrap();
        assert!(
            dynamic_body_fact_dependency(
                &proposition,
                &bound_state.clone().with_borrow_ledger(Some(ended.clone())),
                &assumptions,
                &no_temporary_views,
            )
            .is_err(),
            "an ended scope cannot validate the binding"
        );
        assert!(
            unique_borrowed_resource_dependency(
                &bound_state.with_borrow_ledger(Some(ended)),
                &view,
            )
            .is_err(),
            "a historical-only operation must still reject an ended binding"
        );

        // A view published from this exact plain-memory owner is an owned
        // read. Merely placing an unrelated view beside it remains invalid.
        let (resources, occurrences) =
            ResourceContext::new().unchecked_with_facts_and_occurrences([own.clone()]);
        let supported = resources.unchecked_with_supported_facts_from_occurrence_with_memory(
            occurrences[0].1,
            &own,
            [view.clone()],
            &memory,
        );
        let supported_state = ExecutionState::new()
            .with_memory(memory.clone())
            .with_resource_context(supported);
        assert!(
            dynamic_body_fact_dependency(
                &proposition,
                &supported_state,
                &assumptions,
                &no_temporary_views
            )
            .unwrap()
            .is_none()
        );

        let unbound_state = ExecutionState::new()
            .with_memory(memory)
            .with_resource_context(
                ResourceContext::new().unchecked_with_facts([own.clone(), view]),
            );
        assert!(
            dynamic_body_fact_dependency(
                &proposition,
                &unbound_state,
                &assumptions,
                &no_temporary_views,
            )
            .is_err()
        );

        assert!(
            dynamic_body_fact_dependency(
                &proposition,
                &ExecutionState::new().with_memory(unbound_state.memory().clone()),
                &assumptions,
                &no_temporary_views,
            )
            .is_err(),
            "a pure definedness fact cannot supply access authority"
        );

        if symbolic_range {
            // This variant exercises the borrow binding and its refusal cases;
            // the constant-range variants below cover direct owned access.
            return;
        }

        let owner_state = ExecutionState::new()
            .with_memory(unbound_state.memory().clone())
            .with_resource_context(ResourceContext::new().unchecked_with_fact(own));
        assert!(
            dynamic_body_fact_dependency(
                &proposition,
                &owner_state,
                &assumptions,
                &no_temporary_views,
            )
            .unwrap()
            .is_none()
        );

        let opaque = Proposition::Equal(
            Term::Bitvector32(
                MachineTerm::ClickFunctionApplication {
                    name: "opaque".into(),
                    arguments: Vec::new(),
                }
                .into(),
            ),
            Term::Bitvector32(MachineTerm::constant(0).into()),
        );
        assert!(
            dynamic_body_fact_dependency(&opaque, &owner_state, &assumptions, &no_temporary_views,)
                .is_err(),
            "an opaque current-load carrier must fail closed"
        );
    }
}

#[cfg(test)]
mod wide_range_reader_tests {
    use super::*;
    // A wide composite span must not be enumerated as signed constant cells.
    #[test]
    fn wide_composite_materialization_keeps_the_state_without_enumerating_cells() {
        let base = Address::symbolic(Variable(985_600));
        let wide = MemoryRange::new_wide(
            base.clone(),
            MachineTerm::uint64_constant(0),
            MachineTerm::uint64_constant(1 << 33),
            4,
        );
        let literal = || ContractExpression::IntegerLiteral("0".into());
        let segment = ContractSegment {
            uninitialized: false,
            state: ContractSegmentState::Current,
            base: ProgramExpression::Value(ProgramValue::pointer(base.clone())),
            start: crate::kernel::program_expression::uint64_literal(0),
            end: crate::kernel::program_expression::uint64_literal(1 << 33),
            surface: ContractSegmentSurface::Range {
                base: literal(),
                start: literal(),
                end: literal(),
            },
        };
        let memory = SymbolicMemory::new();
        let result = materialize_composite_resource_cells_from_state(
            memory.clone(),
            &crate::kernel::ProgramPoint::of_memory(&memory),
            &ResourceClause::OwnMemory(segment),
            &ResourceFact::own_memory(wide),
            &[],
            false,
        );
        assert_eq!(result.diagnostic_identity(), memory.diagnostic_identity());
        // The range kind also matters when the shared term representation has
        // legacy constant nodes: they must not trigger signed enumeration.
        let tagged = MemoryRange::new_wide(base, 0u32.into(), 8u32.into(), 4);
        let clause = ResourceClause::OwnMemory(ContractSegment {
            uninitialized: false,
            state: ContractSegmentState::Current,
            base: crate::kernel::program_expression::int32_literal(0),
            start: crate::kernel::program_expression::uint64_literal(0),
            end: crate::kernel::program_expression::uint64_literal(8),
            surface: ContractSegmentSurface::Range {
                base: literal(),
                start: literal(),
                end: literal(),
            },
        });
        let result = materialize_composite_resource_cells_from_state(
            memory.clone(),
            &crate::kernel::ProgramPoint::of_memory(&memory),
            &clause,
            &ResourceFact::own_memory(tagged),
            &[],
            false,
        );
        assert_eq!(result.diagnostic_identity(), memory.diagnostic_identity());
    }
}

#[cfg(test)]
mod guarded_unmatched_materialization_tests {
    use super::*;

    #[test]
    fn ordinary_composite_cell_naming_keeps_the_entry_point() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Address::symbolic(crate::kernel::Variable(88_026));
        let memory = SymbolicMemory::new().with_block(pointer.base.clone(), 4);
        let state = ExecutionState::new().with_memory(memory);
        check_composite_cell_naming(pointer, state, false);
    }

    #[test]
    fn a_held_composite_names_an_unwritten_scalar_at_function_entry() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Address {
            base: crate::kernel::AddressBase::ExternalArgument,
            offset: crate::kernel::AddressOffset::Constant(0),
        };
        let state = ExecutionState::new().begin_function_entry_memory();
        check_composite_cell_naming(pointer, state, true);
    }

    fn check_composite_cell_naming(
        pointer: Address,
        state: ExecutionState,
        names_entry_version: bool,
    ) {
        let file = crate::surface::parser::parse_file_items(
            "resource initialized_cell(p: int32*) { owns *p; }",
        )
        .unwrap();
        let resources = ResourceEnvironment::new(&file.resource_definitions);
        let functions = ClickFunctionEnvironment::new(&[]);
        let predicates = PredicateEnvironment::new(&[]);
        let specs = SpecDefinitions::new(&predicates, &functions);
        let parameters = ParameterBinding::new(&[], &[]);
        let held = ResourceFact::own_composite(
            "initialized_cell".into(),
            vec![ProgramValue::typed_pointer(
                pointer.clone(),
                ProgramType::Int32Pointer,
            )],
        );
        let state = state.with_resource_context(ResourceContext::new().unchecked_with_fact(held));
        let point = state.observation_point_id().unwrap();
        assert!(!matches!(
            state.memory().load(&pointer),
            ExpressionOutcome::Value(_)
        ));
        let named = materialize_folded_composite_resource_cells(
            &resources,
            parameters,
            state.clone(),
            "entry naming",
            specs,
            &PureFactContext::new(),
        )
        .unwrap();
        let projected = project_initial_composite_resource_cores(
            &resources,
            parameters,
            state,
            &PureFactList::from(vec![]),
            "entry projection",
            Some(OwnedCores::Standing),
            specs,
        )
        .unwrap();
        for named_view in [named, projected] {
            let ExpressionOutcome::Value(value) = named_view.memory().load(&pointer) else {
                panic!("the held resource supplies its scalar cell");
            };
            if names_entry_version {
                assert!(matches!(
                    value,
                    ProgramValue::Int32(MachineTerm::MemoryLoad(source, _, _))
                        if source.read_version_id() == Some(point)
                ));
            }
            assert_eq!(named_view.observation_point_id(), Some(point));
        }
    }

    #[test]
    fn composite_cell_naming_reads_an_earlier_clause_at_the_caller_point() {
        let _session = crate::kernel::VerificationSession::enter();
        let file = crate::surface::parser::parse_file_items(
            "resource link(p: int32**) { owns p[0..1]; owns (*p)[0..1]; }",
        )
        .unwrap();
        let resources = ResourceEnvironment::new(&file.resource_definitions);
        let functions = ClickFunctionEnvironment::new(&[]);
        let predicates = PredicateEnvironment::new(&[]);
        let pointer = Address::symbolic(crate::kernel::Variable(88_027));
        let held = ResourceFact::own_composite(
            "link".into(),
            vec![ProgramValue::typed_pointer(
                pointer.clone(),
                ProgramType::Int32PointerPointer,
            )],
        );
        let state = ExecutionState::new()
            .with_memory(SymbolicMemory::new().with_block(pointer.base.clone(), 8))
            .with_resource_context(ResourceContext::new().unchecked_with_fact(held.clone()));
        let point = state.observation_point_id().unwrap();
        let named = materialize_folded_composite_resource_cells(
            &resources,
            ParameterBinding::new(&[], &[]),
            state,
            "linked entry naming",
            SpecDefinitions::new(&predicates, &functions),
            &PureFactContext::new(),
        )
        .unwrap();
        let ExpressionOutcome::Value(ProgramValue::Pointer(link)) = named.memory().load(&pointer)
        else {
            panic!("the first clause exposes the pointer cell");
        };
        assert!(matches!(
            named.memory().load(link.address()),
            ExpressionOutcome::Value(ProgramValue::Int32(_))
        ));
        assert_eq!(named.observation_point_id(), Some(point));
        assert!(named.resources().facts().contains(&held));
    }

    #[test]
    fn composite_unfold_keeps_the_point_while_naming_a_cell() {
        check_composite_body_point(ResourceBodyAccess::Finalize);
    }

    #[test]
    fn composite_open_keeps_the_point_while_naming_a_cell() {
        check_composite_body_point(ResourceBodyAccess::Open);
    }

    fn check_composite_body_point(access: ResourceBodyAccess) {
        let _session = crate::kernel::VerificationSession::enter();
        let file = crate::surface::parse(
            r#"
            resource initialized_cell(p: int32*) { owns *p; fact defined(*p); }
            verifying "read.c";
            int32 read(int32* p) { owns initialized_cell(p); ensures true; }
            "#,
        )
        .unwrap();
        let [Requirement::Resource(resource)] = file.function_blocks()[0].requires() else {
            panic!("expected the cell resource as the only requirement");
        };
        let parsed = syntax::parse_function("int32 read(int32* p) { return *p; }").unwrap();
        let resources = ResourceEnvironment::new(file.resource_definitions());
        let functions = ClickFunctionEnvironment::new(&[]);
        let predicates = PredicateEnvironment::new(&[]);
        let specs = SpecDefinitions::new(&predicates, &functions);
        let pointer = Address::symbolic(crate::kernel::Variable(88_023));
        let arguments = [ProgramExpression::Value(ProgramValue::typed_pointer(
            pointer.clone(),
            ProgramType::Int32Pointer,
        ))];
        let state = ExecutionState::new()
            .with_memory(SymbolicMemory::new().with_block(pointer.base.clone(), 4))
            .with_resource_context(ResourceContext::new().unchecked_with_fact(
                ResourceFact::own_composite(
                    "initialized_cell".into(),
                    vec![ProgramValue::typed_pointer(
                        pointer.clone(),
                        ProgramType::Int32Pointer,
                    )],
                ),
            ));
        let point = state.observation_point_id().unwrap();
        assert!(!matches!(
            state.memory().load(&pointer),
            ExpressionOutcome::Value(_)
        ));

        let checked = unfold_composite_resource_for_proof_with_access(
            &resources,
            resource,
            resource,
            ParameterBinding::new(parsed.parameters(), &arguments),
            state,
            PureFactStore::default(),
            &mut SurfacePropositionMap::default(),
            specs,
            "expose a defined cell",
            0,
            access,
            true,
        )
        .unwrap();
        let after = &checked.state;
        assert!(matches!(
            after.memory().load(&pointer),
            ExpressionOutcome::Value(_)
        ));
        assert!(after.resources().facts().iter().any(|fact| {
            fact.memory_own_range()
                .is_some_and(|range| range.base() == &pointer)
        }));
        assert_eq!(after.observation_point_id(), Some(point));
        assert!(
            checked
                .added_facts
                .contains(&Proposition::MemoryReadDefined {
                    at: Some(point),
                    memory: after.memory().clone(),
                    pointer,
                    value_type: ProgramType::Int32,
                })
        );
    }

    #[test]
    fn implicit_projection_keeps_the_point_of_an_already_named_cell() {
        check_implicit_projection_point(true);
    }

    #[test]
    fn implicit_projection_keeps_the_point_while_naming_a_cell() {
        check_implicit_projection_point(false);
    }

    fn check_implicit_projection_point(already_named: bool) {
        let _session = crate::kernel::VerificationSession::enter();
        let file = crate::surface::parser::parse_file_items(
            "resource initialized_cell(p: int32*) { owns *p; fact defined(*p); }",
        )
        .unwrap();
        let resources = ResourceEnvironment::new(&file.resource_definitions);
        let functions = ClickFunctionEnvironment::new(&[]);
        let predicates = PredicateEnvironment::new(&[]);
        let specs = SpecDefinitions::new(&predicates, &functions);
        let pointer = crate::kernel::Address::symbolic(crate::kernel::Variable(88_021));
        let held = ResourceFact::own_composite(
            "initialized_cell".into(),
            vec![ProgramValue::typed_pointer(
                pointer.clone(),
                ProgramType::Int32Pointer,
            )],
        );
        let memory = SymbolicMemory::new().with_block(pointer.base.clone(), 4);
        let memory = if already_named {
            memory.store(pointer.clone(), crate::kernel::int32(7))
        } else {
            memory
        };
        let state = ExecutionState::new()
            .with_memory(memory)
            .with_resource_context(ResourceContext::new().unchecked_with_fact(held));
        let facts = project_initial_resource_facts(
            &resources,
            ParameterBinding::new(&[], &[]),
            &state,
            &PureFactList::from(vec![]),
            specs,
            "implicit_projection",
        )
        .unwrap()
        .into_vec();
        let defined_reads = facts
            .iter()
            .filter_map(|fact| match fact {
                Proposition::MemoryReadDefined {
                    at,
                    memory,
                    pointer: address,
                    value_type: ProgramType::Int32,
                } if address == &pointer => Some((*at, memory)),
                _ => None,
            })
            .collect::<Vec<_>>();
        let [(at, observed_memory)] = defined_reads.as_slice() else {
            panic!("expected one defined read in {facts:?}");
        };
        assert_eq!(
            matches!(state.memory().load(&pointer), ExpressionOutcome::Value(_)),
            already_named
        );
        assert!(matches!(
            observed_memory.load(&pointer),
            ExpressionOutcome::Value(_)
        ));
        assert_eq!(*at, state.observation_point_id());
    }

    #[test]
    fn instance_cell_naming_keeps_the_unfold_and_entry_points() {
        let _session = crate::kernel::VerificationSession::enter();
        let mut file = crate::surface::parser::parse_file_items(
            r#"
            resource cell(p: int32*) {
                field number: int32;
                owns *p;
                fact defined(*p);
            }
            "#,
        )
        .unwrap();
        crate::surface::lowering::check_resource_field_schemas(&mut file).unwrap();
        let resources = ResourceEnvironment::new(&file.resource_definitions);
        let functions = ClickFunctionEnvironment::new(&[]);
        let predicates = PredicateEnvironment::new(&[]);
        let specs = SpecDefinitions::new(&predicates, &functions);
        let definitions =
            crate::surface::verification::composite_resource_definitions(&resources, specs)
                .unwrap();
        let [definition] = definitions.as_slice() else {
            panic!("expected the cell resource definition");
        };
        let pointer = Address::symbolic(crate::kernel::Variable(88_024));
        let instance = ResourceInstance::new(
            crate::kernel::InstanceId::from_variable(crate::kernel::Variable(88_025)),
            "cell".into(),
            vec![AlgebraicValue::Program(ProgramValue::typed_pointer(
                pointer.clone(),
                ProgramType::Int32Pointer,
            ))]
            .into(),
            definition.instance_field_schema().unwrap().clone(),
            vec![AlgebraicValue::Program(int32(3))].into(),
        )
        .unwrap();
        let before = ExecutionState::new()
            .with_memory(SymbolicMemory::new().with_block(pointer.base.clone(), 4))
            .with_resource_context(
                ResourceContext::new()
                    .unchecked_with_fact(ResourceFact::own(Resource::Instance(instance.clone()))),
            );
        assert!(!matches!(
            before.memory().load(&pointer),
            ExpressionOutcome::Value(_)
        ));
        let point = before.observation_point_id().unwrap();
        let assumptions = PureFactContext::new();
        let rewrite = crate::kernel::rewrite_resource_instance_selecting_children(
            &before,
            &instance,
            definition,
            &definitions,
            &assumptions,
            true,
            None,
        )
        .unwrap();
        let naming_assumptions = rewrite
            .naming_facts
            .into_iter()
            .fold(assumptions.clone(), PureFactContext::assume_proposition);
        let published = Proposition::MemoryReadDefined {
            at: Some(point),
            memory: before.memory().clone(),
            pointer: pointer.clone(),
            value_type: ProgramType::Int32,
        };
        assert!(rewrite.semantic_facts.contains(&published));
        let after = materialize_unfolded_instance_arm_cells(
            &resources,
            specs,
            ParameterBinding::new(&[], &[]),
            rewrite.state,
            &instance,
            &assumptions,
            &naming_assumptions,
            rewrite.body_active,
        );
        assert!(matches!(
            after.memory().load(&pointer),
            ExpressionOutcome::Value(_)
        ));
        assert_eq!(after.observation_point_id(), Some(point));

        let entry = project_initial_composite_resource_cores(
            &resources,
            ParameterBinding::new(&[], &[]),
            before,
            &PureFactList::from(vec![]),
            "named cell at entry",
            Some(OwnedCores::AttachedToOwner),
            specs,
        )
        .unwrap();
        assert!(matches!(
            entry.memory().load(&pointer),
            ExpressionOutcome::Value(_)
        ));
        assert_eq!(entry.observation_point_id(), Some(point));
    }

    #[test]
    fn body_instantiation_keeps_a_pending_store_in_the_observation_log() {
        let _session = crate::kernel::VerificationSession::enter();
        let file = crate::surface::parser::parse_file_items(
            "resource initialized_cell(p: int32*) { owns *p; }",
        )
        .unwrap();
        let definition = &file.resource_definitions[0];
        let pointer = Address::symbolic(crate::kernel::Variable(88_028));
        let substitutions = resource_value_substitutions(
            definition,
            &[AlgebraicValue::Program(ProgramValue::typed_pointer(
                pointer.clone(),
                ProgramType::Int32Pointer,
            ))],
        )
        .unwrap();
        let slot = Address {
            base: "local:slot".into(),
            offset: crate::kernel::AddressOffset::Constant(0),
        };
        let start = ExecutionState::new()
            .with_memory(SymbolicMemory::new().with_block(slot.base.clone(), 4));
        let memory = start
            .memory()
            .clone()
            .store(slot.clone(), ProgramValue::Int32(MachineTerm::constant(7)));
        let state = start.with_materialized_memory(memory);
        let point = state.observation_point_id().unwrap();
        let (memory, _) = instantiate_composite_resource_body_resources(
            definition.name(),
            definition.composite_body().unwrap(),
            &substitutions,
            ParameterBinding::new(&[], &[]),
            &state,
            &PureFactContext::new(),
        )
        .unwrap();
        assert!(matches!(
            memory.load(&pointer),
            ExpressionOutcome::Value(ProgramValue::Int32(_))
        ));
        let named = state.with_materialized_memory_at_current_point(memory);
        assert_eq!(named.observation_point_id(), Some(point));
        assert_eq!(
            named
                .program_point()
                .indexed_integer_version(&slot, crate::kernel::LoadKind::Int32)
                .and_then(|version| version.read_version_id()),
            Some(point)
        );
    }

    #[test]
    fn guarded_cells_materialize_only_after_a_proved_active_guard() {
        let file = crate::surface::parser::parse_file_items(
            r#"
resource cell(p: int32*) {
    field number: int32;
    if p != 0 {
        owns *p;
        fact *p == number;
    }
}"#,
        )
        .unwrap();
        let resources = ResourceEnvironment::new(&file.resource_definitions);
        let functions = ClickFunctionEnvironment::new(&[]);
        let predicates = PredicateEnvironment::new(&[]);
        let specs = SpecDefinitions::new(&predicates, &functions);
        let schema = crate::kernel::ResourceFieldSchema::new(vec![(
            "number".to_string(),
            crate::kernel::ResourceFieldType::Program(ProgramType::Int32),
        )])
        .unwrap();
        for (pointer, active) in [
            (crate::kernel::Address::null(), false),
            (
                crate::kernel::Address::symbolic(crate::kernel::Variable(88_001)),
                false,
            ),
            (
                crate::kernel::Address {
                    base: "object".into(),
                    offset: crate::kernel::AddressOffset::Constant(0),
                },
                true,
            ),
        ] {
            let instance = ResourceInstance::new(
                crate::kernel::InstanceId::from_variable(crate::kernel::Variable(88_002)),
                "cell".to_string(),
                vec![AlgebraicValue::Program(ProgramValue::typed_pointer(
                    pointer.clone(),
                    ProgramType::Int32Pointer,
                ))]
                .into(),
                schema.clone(),
                vec![AlgebraicValue::Program(crate::kernel::int32(3))].into(),
            )
            .unwrap();
            let before = ExecutionState::new();
            let after = materialize_unfolded_instance_arm_cells(
                &resources,
                specs,
                ParameterBinding::new(&[], &[]),
                before.clone(),
                &instance,
                &PureFactContext::new(),
                &PureFactContext::new(),
                active,
            );
            assert_eq!(
                matches!(after.memory().load(&pointer), ExpressionOutcome::Value(_)),
                active
            );
            assert_eq!(
                after.resources().facts(),
                before.resources().facts(),
                "naming cells grants no ownership"
            );
            if !active {
                assert_eq!(after.memory(), before.memory());
            }
        }
    }
}

#[cfg(test)]
mod fold_quantity_activity_tests {
    use super::*;

    #[test]
    fn literal_counts_ignore_unrelated_assumptions_and_keep_signed_bounds() {
        let _session = crate::kernel::VerificationSession::enter();
        for size in [0, 16, 64, 256] {
            let mut assumptions = PureFactContext::new();
            for index in 0..size {
                assumptions = assumptions.assume_condition(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessEqual,
                        left: Box::new(MachineTerm::Variable(Variable(9_810_000 + index))),
                        right: Box::new(100u32.into()),
                    },
                    true,
                );
            }
            for (value, expected) in [
                (0, (true, false)),
                (1, (false, true)),
                (i32::MAX as u32, (false, true)),
                (i32::MIN as u32, (false, false)),
                (u32::MAX, (false, false)),
            ] {
                let (activity, work) = crate::instrumentation::measure_deterministic_work(|| {
                    fold_resource_quantity_activity(&value.into(), &assumptions)
                });
                assert_eq!(activity, expected);
                assert_eq!(
                    work, 0,
                    "literal classification visited ambient facts: size={size}"
                );
            }
        }
    }

    #[test]
    fn symbolic_counts_require_checked_zero_or_positive_facts() {
        let _session = crate::kernel::VerificationSession::enter();
        let count = MachineTerm::Variable(Variable(9_820_001));
        assert_eq!(
            fold_resource_quantity_activity(&count, &PureFactContext::new()),
            (false, false)
        );
        for (value, expected) in [
            (0, (true, false)),
            (1, (false, true)),
            (u32::MAX, (false, false)),
        ] {
            let assumptions = PureFactContext::new().assume_condition(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(count.clone()),
                    right: Box::new(value.into()),
                },
                true,
            );
            assert_eq!(
                fold_resource_quantity_activity(&count, &assumptions),
                expected
            );
        }
    }
}

#[cfg(test)]
mod declared_scalar_field_observation_tests {
    use super::*;

    fn field(base: ProgramExpression, element_type: ProgramType) -> ContractSegment {
        ContractSegment {
            uninitialized: false,
            state: ContractSegmentState::Current,
            base,
            start: crate::kernel::program_expression::int32_literal(0),
            end: crate::kernel::program_expression::int32_literal(0),
            surface: ContractSegmentSurface::Field {
                value_bytes: None,
                base: None,
                name: "payload".into(),
                element_width: Some(4),
                element_type: Some(element_type),
            },
        }
    }

    #[test]
    fn scalar_field_observations_do_not_initialize_owned_padding() {
        let base = Address::symbolic(Variable(985_801));
        for viewed in [false, true] {
            let mut samples = Vec::new();
            for padding in [0u32, 16, 64, 256] {
                let segment = field(
                    ProgramExpression::Value(ProgramValue::pointer(base.clone())),
                    ProgramType::Int32,
                );
                let range = MemoryRange::new(base.clone(), 0.into(), (1 + padding).into());
                let (clause, fact) = if viewed {
                    (
                        ResourceClause::ViewMemory(segment),
                        ResourceFact::view_memory(range),
                    )
                } else {
                    (
                        ResourceClause::OwnMemory(segment),
                        ResourceFact::own_memory(range),
                    )
                };
                let memory = SymbolicMemory::new();
                let (named, work) = crate::instrumentation::measure_deterministic_work(|| {
                    materialize_composite_resource_cells_from_state(
                        memory.clone(),
                        &crate::kernel::ProgramPoint::of_memory(&memory),
                        &clause,
                        &fact,
                        &[],
                        false,
                    )
                });
                assert!(matches!(
                    named.load(&base),
                    ExpressionOutcome::Value(ProgramValue::Int32(_))
                ));
                assert!(
                    !matches!(
                        named.load(&base.offset_by_bytes(4)),
                        ExpressionOutcome::Value(_)
                    ),
                    "padding must not become an initialized scalar"
                );
                samples.push(work);
            }
            assert!(
                samples.windows(2).all(|pair| pair[1] <= pair[0] + 8),
                "{samples:?}"
            );
        }
    }

    #[test]
    fn pointer_field_observation_is_one_complete_typed_read() {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Address::symbolic(Variable(985_803));
        let memory = SymbolicMemory::new();
        let segment = field(
            ProgramExpression::Value(ProgramValue::pointer(base.clone())),
            ProgramType::Int32Pointer,
        );
        let named = materialize_composite_resource_cells_from_state(
            memory.clone(),
            &crate::kernel::ProgramPoint::of_memory(&memory),
            &ResourceClause::OwnMemory(segment),
            &ResourceFact::own_memory(MemoryRange::new(base.clone(), 0.into(), 2.into())),
            &[],
            false,
        );
        let ExpressionOutcome::Value(value) = named.load(&base) else {
            panic!("observed field")
        };
        assert!(
            matches!(value, ProgramValue::Pointer(_)),
            "a pointer field must not be cached as an integer prefix"
        );
        let expected = Address::loaded(&MachineTerm::read_named(
            crate::kernel::ProgramPoint::at(&(crate::kernel::intern_memory(memory))),
            Box::new(base.clone()),
            crate::kernel::LoadKind::Int32,
        ))
        .unwrap();
        assert!(value == ProgramValue::typed_pointer(expected, ProgramType::Int32Pointer));
        assert!(!matches!(
            named.load(&base.offset_by_bytes(4)),
            ExpressionOutcome::Value(_)
        ));
        assert!(!matches!(
            named.load(&base.offset_by_bytes(8)),
            ExpressionOutcome::Value(_)
        ));
    }

    #[test]
    fn declared_pointer_field_retains_its_recorded_store() {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Address {
            base: AddressBase::ExternalArgument,
            offset: AddressOffset::Constant(0),
        };
        let ty = ProgramType::Int32Pointer;
        let stored = ExecutionState::new().with_memory(SymbolicMemory::new().store(
            base.clone(),
            ProgramValue::typed_pointer(Address::symbolic(Variable(985_804)), ty),
        ));
        let source = stored.program_point();
        let segment = field(
            ProgramExpression::Value(ProgramValue::pointer(base.clone())),
            ty,
        );
        let named = materialize_composite_resource_cells_from_state(
            SymbolicMemory::new(),
            &source,
            &ResourceClause::OwnMemory(segment),
            &ResourceFact::own_memory(MemoryRange::new(base.clone(), 0.into(), 2.into())),
            &[],
            false,
        );
        let ExpressionOutcome::Value(ProgramValue::Pointer(named)) = named.load(&base) else {
            panic!("expected a complete pointer observation");
        };
        let read = named.address().as_loaded_value().expect("pointer read");
        assert_eq!(read.point.read_version_id(), stored.observation_point_id());
        assert_eq!(read.defining_address, base);
        assert!(read.identity.is_point_named());
    }

    #[test]
    fn declared_float_field_retains_its_resource_source_point() {
        use crate::kernel::KernelFloatType;
        let _session = crate::kernel::VerificationSession::enter();
        let base = Address {
            base: AddressBase::ExternalArgument,
            offset: AddressOffset::Constant(0),
        };
        let state = ExecutionState::new().begin_function_entry_memory();
        let source = state.program_point();
        for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
            let ty = format.program_type();
            let segment = field(
                ProgramExpression::Value(ProgramValue::typed_pointer(
                    base.clone(),
                    ty.pointer_to().unwrap(),
                )),
                ty,
            );
            let named = materialize_composite_resource_cells_from_state(
                SymbolicMemory::new(),
                &source,
                &ResourceClause::OwnMemory(segment),
                &ResourceFact::own_memory(MemoryRange::new(base.clone(), 0.into(), 2.into())),
                &[],
                false,
            );
            let ExpressionOutcome::Value(value) = named.load(&base) else {
                panic!("expected an observed float field");
            };
            assert_eq!(value.program_type(), ty);
            let (ProgramValue::Float32(term) | ProgramValue::Float64(term)) = value else {
                panic!("expected a float value");
            };
            let MachineTerm::MemoryLoad(point, address, kind) = term else {
                panic!("expected a float read");
            };
            assert_eq!(point.read_version_id(), state.observation_point_id());
            assert_eq!(*address, base);
            assert_eq!(kind, format.load_kind());
        }
    }

    #[test]
    fn declared_array_elements_exclude_trailing_padding() {
        let base = Address::symbolic(Variable(985_802));
        for count in [0, 16, 64, 256] {
            let segment = field(
                crate::kernel::program_expression::typed_load(
                    ProgramExpression::Value(ProgramValue::pointer(base.clone())),
                    ProgramType::Int32Array(count),
                ),
                ProgramType::Int32,
            );
            let range = MemoryRange::new(base.clone(), 0.into(), (count + 4).into());
            let memory = SymbolicMemory::new();
            let named = materialize_composite_resource_cells_from_state(
                memory.clone(),
                &crate::kernel::ProgramPoint::of_memory(&memory),
                &ResourceClause::OwnMemory(segment),
                &ResourceFact::own_memory(range),
                &[],
                false,
            );
            if count > 0 {
                assert!(matches!(
                    named.load(&base.offset_by_bytes((count - 1) * 4)),
                    ExpressionOutcome::Value(ProgramValue::Int32(_))
                ));
            }
            assert!(!matches!(
                named.load(&base.offset_by_bytes(count * 4)),
                ExpressionOutcome::Value(_)
            ));
        }
    }
}
