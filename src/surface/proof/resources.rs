use super::*;
use crate::kernel::ExecutionFactSource;
use crate::kernel::ResourceInstance;
use crate::surface::planning::proposition_search::PropositionSearch;

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
    facts: ProofFacts,
    added: Vec<Proposition>,
}

impl ProofResourcePureFacts {
    fn new(facts: ProofFacts) -> Self {
        Self {
            facts,
            added: Vec::new(),
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
    pub(super) state: CState,
    pub(super) selected: CResourceFact,
    pub(super) body_was_already_exposed: bool,
}

/// Resolve the dependency of one viewed representation without selecting an
/// authority by equal resource spelling.  Duplicate equal views are valid
/// only when they carry the same checked loan bundle; otherwise the rewrite
/// is ambiguous and must fail closed.
fn unique_borrowed_resource_dependency(
    state: &CState,
    resource: &CResourceFact,
) -> Result<Option<crate::kernel::LoanViewBinding>, String> {
    if !state.loan_bindings_are_consistent() {
        return Err("resource and loan binding sidecars disagree".into());
    }
    let mut selected = None;
    let mut saw_unbound = false;
    let mut saw_bound = false;
    for occurrence in state.resources().occurrences_for_fact(resource) {
        let Some(binding) = state.resources().loan_dependency(occurrence) else {
            saw_unbound = true;
            continue;
        };
        saw_bound = true;
        if selected
            .as_ref()
            .is_some_and(|existing| existing != binding)
        {
            return Err(
                "equal viewed resource occurrences carry different loan dependencies".into(),
            );
        }
        selected = Some(binding.clone());
    }
    if saw_bound && saw_unbound {
        return Err("equal viewed resource occurrences mix bound and unbound authorities".into());
    }
    if let Some(binding) = &selected {
        let ledger = state
            .loan_ledger()
            .ok_or_else(|| "selected viewed resource has no active loan ledger".to_string())?;
        let holder = state
            .loan_participant()
            .ok_or_else(|| "selected viewed resource has no active loan holder".to_string())?;
        ledger
            .validate_view_binding(binding.clone(), holder)
            .map_err(|error| format!("selected viewed resource loan is not live: {error:?}"))?;
    }
    Ok(selected)
}

/// Record the children a checked rewrite exposed from a viewed composite as
/// permitted descriptions of the parent's loan. The rewrite derived them
/// from the definition in the current state, but the ledger does not take
/// that list on trust: the kernel expands the parent one level itself and
/// `project` re-checks every child against that expansion (D2 law 10).
fn project_children_into_ledger(
    state: CState,
    binding: &crate::kernel::LoanViewBinding,
    children: impl IntoIterator<Item = CResourceFact>,
    memory: &CMemory,
    assumptions: &PureFactContext,
    definitions: &[CCompositeResourceDefinition],
    context_label: &str,
) -> Result<CState, ClickError> {
    let (Some(ledger), Some(holder)) = (state.loan_ledger().cloned(), state.loan_participant())
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
        memory,
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
            .project(holder, binding.loan, &binding.viewed, &evidence, child)
            .map_err(|refusal| {
                ClickError::new(format!(
                    "{context_label} cannot project a child of the viewed composite: {refusal:?}"
                ))
            })?;
    }
    Ok(state.with_loan_ledger(Some(ledger)))
}

fn same_loan_authority(
    left: &crate::kernel::LoanViewBinding,
    right: &crate::kernel::LoanViewBinding,
) -> bool {
    left.loan == right.loan
        && left.scope == right.scope
        && left.share == right.share
        && left.support == right.support
}

/// Temporary projections are indexed once per resource rewrite.  This keeps
/// dynamic-load checking proportional to the loads and matching view ranges,
/// rather than multiplying every body fact by every temporary view.
struct DynamicViewDependencyIndex {
    bound: ResourceContext,
    bound_dependencies:
        BTreeMap<crate::kernel::ResourceOccurrenceId, crate::kernel::LoanViewBinding>,
    unbound: ResourceContext,
}

impl DynamicViewDependencyIndex {
    fn new(
        bound_views: &[(CResourceFact, crate::kernel::LoanViewBinding)],
        unbound_views: &[CResourceFact],
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
        }
    }
}

/// Find the live stable-view authority needed by the current memory loads in
/// one lowered body fact.  Loads from an older memory snapshot are historical
/// scalar facts and deliberately do not participate in this check.  The
/// caller supplies views which are about to be inserted by an observation so
/// that dependency capture does not search equal ambient occurrences.
fn dynamic_body_fact_dependency(
    required: &Proposition,
    state: &CState,
    assumptions: &PureFactContext,
    temporary_views: &DynamicViewDependencyIndex,
) -> Result<Option<crate::kernel::LoanViewBinding>, String> {
    fn check_load(
        pointer: Pointer,
        width: u32,
        state: &CState,
        assumptions: &PureFactContext,
        temporary_views: &DynamicViewDependencyIndex,
        selected: &mut Option<crate::kernel::LoanViewBinding>,
    ) -> Result<(), String> {
        let required_view = CResourceFact::view_memory(CMemoryRange::new_with_element_width(
            pointer,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
            width,
        ));
        if !temporary_views
            .unbound
            .view_occurrences_for_fact(&required_view, assumptions)
            .is_empty()
        {
            return Err("current body fact is covered by an unbound view".into());
        }
        let mut candidates = Vec::new();
        for occurrence in state
            .resources()
            .view_occurrences_for_fact(&required_view, assumptions)
        {
            let Some(candidate) = state.resources().loan_dependency(occurrence) else {
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
            if state
                .resources()
                .directly_supporting_owned_entry(&required_view, assumptions)
                .is_some()
            {
                return Ok(());
            }
            return Err(
                "current body fact reads memory outside every live viewed-memory dependency".into(),
            );
        }
        let ledger = state.loan_ledger().ok_or_else(|| {
            "current viewed-memory dependency has no active loan ledger".to_string()
        })?;
        let holder = state
            .loan_participant()
            .ok_or_else(|| "current viewed-memory dependency has no loan holder".to_string())?;
        for candidate in candidates {
            let checked = crate::kernel::LoanViewBinding {
                viewed: required_view.clone(),
                ..candidate
            };
            ledger
                .validate_view_binding(checked.clone(), holder)
                .map_err(|error| {
                    format!("current viewed-memory dependency is not live: {error:?}")
                })?;
            if selected
                .as_ref()
                .is_some_and(|existing| !same_loan_authority(existing, &checked))
            {
                return Err("one body fact depends on different stable-view authorities".into());
            }
            *selected = Some(checked);
        }
        Ok(())
    }
    fn walk_term(
        term: &Term,
        state: &CState,
        assumptions: &PureFactContext,
        temporary_views: &DynamicViewDependencyIndex,
        selected: &mut Option<crate::kernel::LoanViewBinding>,
    ) -> Result<(), String> {
        for (pointer, width) in crate::kernel::current_memory_loads_in_term(term, state.memory())? {
            check_load(
                pointer,
                width,
                state,
                assumptions,
                temporary_views,
                selected,
            )?;
        }
        Ok(())
    }
    fn walk_proposition(
        proposition: &Proposition,
        state: &CState,
        assumptions: &PureFactContext,
        temporary_views: &DynamicViewDependencyIndex,
        selected: &mut Option<crate::kernel::LoanViewBinding>,
    ) -> Result<(), String> {
        match proposition {
            Proposition::ConditionIs(condition, _) => walk_term(
                &Term::Condition(condition.clone()),
                state,
                assumptions,
                temporary_views,
                selected,
            ),
            Proposition::Equal(left, right) => {
                walk_term(left, state, assumptions, temporary_views, selected)?;
                walk_term(right, state, assumptions, temporary_views, selected)
            }
            Proposition::And(left, right)
            | Proposition::Or(left, right)
            | Proposition::Implies(left, right) => {
                walk_proposition(left, state, assumptions, temporary_views, selected)?;
                walk_proposition(right, state, assumptions, temporary_views, selected)
            }
            Proposition::Not(body)
            | Proposition::ForAll { body, .. }
            | Proposition::Exists { body, .. } => {
                walk_proposition(body, state, assumptions, temporary_views, selected)
            }
            Proposition::Predicate { arguments, .. } => {
                for argument in arguments {
                    walk_term(argument, state, assumptions, temporary_views, selected)?;
                }
                Ok(())
            }
            Proposition::CResourceSeparate { .. }
            | Proposition::CResourceComposition(_)
            | Proposition::CResourceContains { .. } => Ok(()),
            Proposition::CMemoryLoads { outcome, .. } => match outcome {
                CExpressionOutcome::Value(value) => walk_term(
                    &Term::CValue(value.clone()),
                    state,
                    assumptions,
                    temporary_views,
                    selected,
                ),
                CExpressionOutcome::UndefinedBehavior(_) | CExpressionOutcome::RuntimeError(_) => {
                    Ok(())
                }
            },
            Proposition::CMemoryReadDefined {
                memory,
                pointer,
                value_type,
            } => {
                // Definedness is an observation of the same cell as a load.
                // Retain its access dependency, including loads in its address.
                walk_term(
                    &Term::CValue(CValue::pointer(pointer.clone())),
                    state,
                    assumptions,
                    temporary_views,
                    selected,
                )?;
                if memory == state.memory() {
                    check_load(
                        pointer.clone(),
                        value_type.byte_width(),
                        state,
                        assumptions,
                        temporary_views,
                        selected,
                    )?;
                }
                Ok(())
            }
            Proposition::CMemoryLoadable { bytes, .. }
            | Proposition::CHeapAllocationFreed { bytes, .. } => walk_term(
                &Term::Bitvector32(bytes.clone()),
                state,
                assumptions,
                temporary_views,
                selected,
            ),
            Proposition::CMemoryCanStore { .. }
            | Proposition::CMemoryMutatesOnly { .. }
            | Proposition::CMemoryEffectSummary { .. }
            | Proposition::CFunctionSatisfiesSpecification { .. }
            | Proposition::CFunctionPartiallySatisfiesSpecification { .. } => Ok(()),
            _ => Err("unsupported opaque proposition in current-load dependency".into()),
        }
    }
    let mut selected = None;
    walk_proposition(required, state, assumptions, temporary_views, &mut selected)?;
    Ok(selected)
}

pub(super) fn materialize_folded_composite_resource_cells(
    resource_environment: &ResourceEnvironment,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: CState,
    claim_label: &str,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<CState, ClickError> {
    let memory = materialize_folded_composite_resource_memory(
        resource_environment,
        parameters,
        arguments,
        &state,
        spec_definitions,
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}` setup failed: {message}")))?;
    Ok(state.with_memory(memory))
}

fn materialize_folded_composite_resource_memory(
    resource_environment: &ResourceEnvironment,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<CMemory, String> {
    let mut memory = state.memory().clone();
    for resource in state.resources().facts() {
        let (name, resource_arguments) = match resource.resource() {
            CResource::Composite { name, arguments } => (name, arguments),
            CResource::Memory(_)
            | CResource::Token { .. }
            | CResource::Instance(_)
            | CResource::MutexGuard(_)
            | CResource::MutexLive(_)
            | CResource::MutexUse(_)
            | CResource::Publication(_)
            | CResource::PopulationAuthority(_)
            | CResource::Iterated(_) => {
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
            resource_arguments,
            state.memory(),
            state.resources(),
            &PureFactContext::new(),
            resource_environment,
            spec_definitions,
            None,
        )
        .map_err(|message| {
            format!("could not instantiate composite resource `{name}` body: {message}")
        })?;
        memory = materialize_composite_resource_memory(
            name,
            composite_body,
            &substitutions,
            parameters,
            arguments,
            memory,
        )?;
    }
    Ok(memory)
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
    let AlgebraicValue::Algebraic(model) = instance.fields().get(field_index)? else {
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
/// endpoint. A guarded or witness-carrying body is not unconditionally one
/// shape, and a field-free body is not an instance, so neither is selected.
fn unmatched_instance_body(
    definition: &ResourceDefinition,
    body: &CompositeResourceBody,
    instance: &ResourceInstance,
) -> Option<SelectedInstanceArm> {
    if body.condition.is_some() || !body.witnesses.is_empty() || definition.fields().is_empty() {
        return None;
    }
    let mut parameters = definition.parameters.clone();
    for field in definition.fields() {
        if matches!(field.click_type(), ClickType::C(_)) {
            parameters.push(FunctionParameter {
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

impl ResourceClausePresentation {
    pub(in crate::surface) fn matches_available_fact(&self, facts: &ProofFacts) -> bool {
        let binder_matches = match &self.source {
            ClickProposition::ForAll { name, .. } => self.checked.introductions.iter().any(
                |introduction| {
                    matches!(introduction, crate::kernel::LoweringIntroduction::WrittenUniversal { name: lowered, .. } if lowered == name)
                },
            ),
            _ => true,
        };
        binder_matches && facts.contains_top_level(&self.checked.proposition)
    }
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
    function_values: &BTreeMap<String, CValue>,
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
    let mut names_by_value = BTreeMap::<CValue, Option<String>>::new();
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
        let Some(value) = argument.as_c_value() else {
            return Err(ClickError::new(
                "resource body clause has a non-C parameter",
            ));
        };
        let expression = match names_by_value.get(value).and_then(Option::as_ref) {
            Some(name) => ContractExpression::CFragment(CExpression::Variable(name.clone())),
            None => ContractExpression::CFragment(CExpression::Value(value.clone())),
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
            substitute_click_proposition(source, &substitutions).map_err(ClickError::new)?;
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

/// Names the cells an `unfold` of a matched instance has just exposed.
///
/// Naming is atomic across producers (`docs/internals/canonicalization.md`).
/// Contract lowering already materializes the cells of the arm a section
/// selects for a held instance, so the fact it states about a cell and the
/// C's own read of that cell are one load variable. An unfold exposes the same
/// cells one layer deeper and must name them the same way. Without this, the
/// unfolded child's facts keep the unfold-time epoch while a later C read of
/// the same cell walks its own epoch, and the two differ as soon as a store
/// the assumption-free epoch walk cannot cross lies between them — a write to
/// a *separate* object, whose separation is a resource fact and not a DAG
/// edge. That is exactly the gap between `*new = *victim` and the refold after
/// `rb_set_parent(victim->rb_left, new)`.
///
/// This is the same projection contract lowering runs, so the cell layout and
/// element types are the ones already chosen there rather than a second
/// convention. It is bounded by the arm body: one cell per element of each
/// constant-bounded range the arm owns, no search, and cells the snapshot
/// already holds are left alone.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn materialize_unfolded_instance_arm_cells(
    resource_environment: &ResourceEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: CState,
    instance: &ResourceInstance,
    assumptions: &PureFactContext,
    naming_assumptions: &PureFactContext,
) -> CState {
    // An unfold consumes the instance and exposes its body, so an unmatched
    // body is the one it exposes. Its cells are named here exactly as a
    // selected arm's are; otherwise a C read of a cell the body owns, after
    // any later write, mints a second load identity for it.
    let selected = selected_resource_instance_arm(
        resource_environment,
        click_function_environment,
        instance,
        assumptions,
    )
    .or_else(|| {
        let definition = resource_environment.get(instance.name())?;
        let body = definition.composite_body()?;
        body.matched
            .is_none()
            .then(|| unmatched_instance_body(definition, body, instance))?
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
        parameters,
        arguments,
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
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    mut state: CState,
    available_pure_facts: &(impl PropositionSource + ?Sized),
    claim_label: &str,
    owned: Option<OwnedCores>,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<CState, ClickError> {
    let include_owned = owned.is_some();
    let attach_to_owner = owned == Some(OwnedCores::AttachedToOwner);
    let attach_instance_arms = attach_to_owner;
    let assumptions = assumptions_from_propositions(available_pure_facts);
    for resource in state.resources().facts().to_vec() {
        // A matched instance exposes the arm its section selects, and nothing
        // when no arm is selected (D7). The arm scope's body holds only that
        // arm's own memory clauses, so this projects cells and never a
        // contained instance.
        if let CResource::Instance(instance) = resource.resource() {
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
                                body.matched
                                    .is_none()
                                    .then(|| unmatched_instance_body(definition, body, instance))?
                            })
                {
                    state = project_selected_instance_arm_cells(
                        &selected,
                        instance,
                        parameters,
                        arguments,
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
                parameters,
                arguments,
                state,
                &assumptions,
                include_owned,
                (attach_instance_arms && resource.is_own()).then_some(&resource),
            );
            continue;
        }
        let head = resource.clone();
        let (name, resource_arguments, is_owned) = match resource {
            CResourceFact::View(CResource::Composite { name, arguments }) => {
                (name, arguments, false)
            }
            CResourceFact::Own(CResource::Composite { name, arguments }, _) => {
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
            &resource_arguments,
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
            parameters,
            arguments,
            &state,
            &state,
            &CValue::Int32(Bitvector32Term::Constant(0)),
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
            parameters,
            arguments,
            state.memory().clone(),
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
                        describe_resource_context_validity_error(error, parameters, arguments)
                    ))
                })?,
        };
        state = state.with_memory(memory).with_resource_context(resources);
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
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: CState,
    assumptions: &PureFactContext,
    include_owned: bool,
    owner: Option<&CResourceFact>,
) -> CState {
    let arm = &selected.arm;
    let Some(body) = arm.composite_body() else {
        return state;
    };
    // A pointer payload an exact equality identifies with an older pointer
    // denotes that pointer, exactly as the kernel instantiates the arm's
    // ownership and facts (`arm_binding_program_spelling`). Naming is atomic
    // across producers, so the cell this projection names must be the cell
    // the arm owns, at the one spelling.
    let bindings = selected
        .bindings
        .iter()
        .map(|binding| match binding.as_c_value() {
            Some(value) => crate::kernel::arm_binding_program_spelling(value, assumptions)
                .map_or_else(|| binding.clone(), AlgebraicValue::C),
            None => binding.clone(),
        })
        .collect::<Vec<_>>();
    let Ok(substitutions) = resource_value_substitutions_for_parameters(
        arm.name(),
        instance.arguments(),
        &bindings,
        arm.parameters(),
    ) else {
        return state;
    };
    let Ok((memory, contained_resources)) = instantiate_composite_resource_body_resources(
        arm.name(),
        body,
        &substitutions,
        parameters,
        arguments,
        state.memory().clone(),
    ) else {
        return state;
    };
    let state = state.with_materialized_memory(memory);
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
                .as_c_value()
                .ok_or_else(|| format!("resource `{name}` has a non-C argument"))?;
            Ok((
                parameter.name().to_string(),
                ContractExpression::CFragment(CExpression::Value(argument.clone())),
            ))
        })
        .collect::<Result<BTreeMap<_, _>, String>>()?;
    // Only C-typed constructor fields become arm parameters, and they are
    // pushed in field order, so one forward pass pairs them up.
    let mut binding_parameters = parameters[instance_arguments.len()..].iter();
    for binding in constructor_bindings {
        let Some(value) = binding.as_c_value() else {
            continue;
        };
        let Some(parameter) = binding_parameters.next() else {
            break;
        };
        substitutions.insert(
            parameter.name().to_string(),
            ContractExpression::CFragment(CExpression::Value(value.clone())),
        );
    }
    Ok(substitutions)
}

pub(super) fn project_initial_resource_facts(
    resource_environment: &ResourceEnvironment,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    available_pure_facts: &[Proposition],
    spec_definitions: SpecDefinitions<'_>,
    claim_label: &str,
) -> Result<Vec<Proposition>, ClickError> {
    let result = CValue::Int32(Bitvector32Term::Constant(0));
    let mut facts = ProofResourcePureFacts::new(ProofFacts::from_ordered(available_pure_facts));
    append_state_resource_context_observable_facts_with_store(
        parameters,
        arguments,
        state,
        &mut facts,
        &format!("`{claim_label}` setup"),
    )?;
    project_folded_resource_observable_facts_with_store(
        resource_environment,
        parameters,
        arguments,
        state,
        state,
        &result,
        &mut facts,
        spec_definitions,
    )
    .map_err(|message| ClickError::new(format!("`{claim_label}` setup failed: {message}")))?;
    Ok(facts.facts.to_vec())
}

pub(super) fn project_outcome_resource_facts(
    resource_environment: &ResourceEnvironment,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    outcome: &CFunctionOutcome,
    available_pure_facts: ProofFacts,
    spec_definitions: SpecDefinitions<'_>,
    claim_label: &str,
    path_index: usize,
) -> Result<ProofFacts, ClickError> {
    let CFunctionOutcome::Return { value, state } = outcome else {
        return Ok(available_pure_facts);
    };
    let mut facts = ProofResourcePureFacts::new(available_pure_facts);
    append_state_resource_context_observable_facts_with_store(
        parameters,
        arguments,
        state,
        &mut facts,
        &format!("`{claim_label}` path {path_index}"),
    )?;
    project_folded_resource_observable_facts_with_store(
        resource_environment,
        parameters,
        arguments,
        pre_state,
        state,
        value,
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
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    available_pure_facts: &mut F,
    context: &str,
) -> Result<(), ClickError> {
    let facts = state
        .resources()
        .observable_facts(available_pure_facts.assumptions())
        .map_err(|error| {
            ClickError::new(format!(
                "{context}: {}",
                describe_resource_context_validity_error(error, parameters, arguments)
            ))
        })?;
    for fact in facts {
        available_pure_facts.insert(fact);
    }
    Ok(())
}

fn project_folded_resource_observable_facts_with_store(
    resource_environment: &ResourceEnvironment,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    result: &CValue,
    propositions: &mut ProofResourcePureFacts,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<(), String> {
    for resource in state.resources().facts() {
        project_held_resource_observable_facts(
            resource_environment,
            resource,
            parameters,
            arguments,
            pre_state,
            state,
            result,
            propositions,
            spec_definitions,
        )?;
    }
    Ok(())
}

pub(super) struct CheckedResourceObservation {
    pub(super) state: CState,
    pub(super) facts: ProofFacts,
    pub(super) added_facts: Vec<Proposition>,
    pub(super) observed_resource: CResourceFact,
}

#[allow(clippy::too_many_arguments)]
pub(super) fn observe_composite_resource_for_proof(
    function: &CFunction,
    resource_environment: &ResourceEnvironment,
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: CState,
    facts: ProofFacts,
    surface_propositions: &mut SurfacePropositionMap,
    count_derivations: &mut PersistentOrderedSet<Theorem>,
    spec_definitions: SpecDefinitions<'_>,
    claim_label: &str,
    tactic_index: usize,
) -> Result<CheckedResourceObservation, ClickError> {
    let mut facts = ProofResourcePureFacts::new(facts);
    let (state, observed_resource) = observe_composite_resource_with_facts(
        function,
        resource_environment,
        resource,
        parameters,
        arguments,
        state,
        &mut facts,
        surface_propositions,
        count_derivations,
        spec_definitions,
        claim_label,
        tactic_index,
    )?;
    Ok(CheckedResourceObservation {
        state,
        facts: facts.facts,
        added_facts: facts.added,
        observed_resource,
    })
}

#[allow(clippy::too_many_arguments)]
fn observe_composite_resource_with_facts<F: ResourcePureFacts>(
    function: &CFunction,
    resource_environment: &ResourceEnvironment,
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: CState,
    available_pure_facts: &mut F,
    surface_propositions: &mut SurfacePropositionMap,
    count_derivations: &mut PersistentOrderedSet<Theorem>,
    spec_definitions: SpecDefinitions<'_>,
    claim_label: &str,
    tactic_index: usize,
) -> Result<(CState, CResourceFact), ClickError> {
    let requested_resource =
        lower_resource_clause_at_state(resource, parameters, arguments, &state)?;
    let assumptions = available_pure_facts.assumptions().clone();
    let viewed_resource = CResourceFact::View(requested_resource.resource().clone());
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
                    parameters,
                    arguments,
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
            ContractExpression::CFragment(CExpression::Value(int32(1))),
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
                parameters,
                arguments,
                &state,
                &state,
                &CValue::Int32(Bitvector32Term::Constant(0)),
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
            left: ContractExpression::CFragment(CExpression::Value(int32(0))),
            operator: ComparisonOperator::LessEqual,
            right: observed_quantity.clone(),
        };
        let nonnegative_kernel = lower_outcome_proposition_with_assumptions(
            parameters,
            arguments,
            &state,
            &state,
            &CValue::Int32(Bitvector32Term::Constant(0)),
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
            left: ContractExpression::CFragment(CExpression::Value(int32(0))),
            operator: ComparisonOperator::LessEqual,
            right: ContractExpression::ResourceCount(Box::new(counted_resource.clone())),
        };
        if let Ok(count_nonnegative_kernel) = lower_outcome_proposition_with_assumptions(
            parameters,
            arguments,
            &state,
            &state,
            &CValue::Int32(Bitvector32Term::Constant(0)),
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
        return Ok((state, abstract_resource));
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
        return Ok((state, abstract_resource));
    }
    if explicit_quantity {
        let quantity = abstract_resource
            .owned_quantity_term()
            .expect("an explicitly quantified observation lowers to owned authority");
        let positive = quantity.as_const().is_some_and(|value| value > 0)
            || assumptions.proves(&Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedGreaterThan(
                    Box::new(quantity.clone()),
                    Box::new(Bitvector32Term::Constant(0)),
                ),
                true,
            ));
        if !positive {
            // The count lower bound remains valid for zero or an undecided
            // nonnegative quantity. The population body, however, grants
            // authority only when the held quantity is proved positive.
            return Ok((state, abstract_resource));
        }
    }
    let definition = composite_resource_law_definition(
        resource_environment,
        resource,
        "observe",
        claim_label,
        tactic_index,
    )?;
    let CResource::Composite {
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
        parameters,
        arguments,
        &state,
        None,
        available_pure_facts.assumptions(),
        resource_environment,
        spec_definitions,
        Some(function.composite_resource_definitions()),
    )?;
    let observation_pre_state = state.clone();
    // A viewed composite is itself a checked loan projection.  Its children
    // are fresh occurrences, so remember the exact bundle before projecting
    // the body; equal resource terms are not sufficient to recover it later.
    let borrowed_parent_binding = unique_borrowed_resource_dependency(&state, &abstract_resource)
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `observe` refused ambiguous loan dependency: {message}"
            ))
        })?;
    let (memory, contained_resources, body_projected) = apply_composite_observation_law_with_facts(
        resource_environment,
        definition,
        resource_arguments,
        parameters,
        arguments,
        &state,
        &state,
        &CValue::Int32(Bitvector32Term::Constant(0)),
        available_pure_facts,
        spec_definitions,
        false,
        Some(function.composite_resource_definitions()),
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: could not observe `{}`: {message}",
            describe_resource_clause(resource)
        ))
    })?;
    let fact_state = observation_pre_state.clone().with_memory(memory.clone());
    let instantiated = if body_projected {
        Some(crate::kernel::instantiate_composite_resource_facts(
            &abstract_resource,
            function.composite_resource_definitions(),
            &memory,
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
            parameters,
            arguments,
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
                    .is_none_or(|parent| !same_loan_authority(parent, &binding))
                {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `observe` cannot package a current viewed-memory fact without its parent loan"
                    )));
                }
                if dynamic_dependency
                    .as_ref()
                    .is_some_and(|existing| !same_loan_authority(existing, &binding))
                {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: observed body facts depend on different stable-view authorities"
                    )));
                }
                dynamic_dependency = Some(binding);
            }
        }
    }
    let all_viewed_contained_resources = contained_resources
        .facts()
        .iter()
        .filter_map(|fact| fact.core_with_assumptions(available_pure_facts.assumptions()))
        .map(|fact| CResourceFact::View(fact.resource().clone()))
        .collect::<Vec<_>>();
    if let Some(binding) = borrowed_parent_binding.as_ref() {
        for child in &all_viewed_contained_resources {
            if !state.resources().contains_exact_representation(child) {
                continue;
            }
            let expected = crate::kernel::LoanViewBinding {
                viewed: child.clone(),
                ..binding.clone()
            };
            let existing = unique_borrowed_resource_dependency(&state, child).map_err(|message| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `observe` refused an existing child dependency: {message}"
                ))
            })?;
            if existing
                .as_ref()
                .is_none_or(|candidate| !same_loan_authority(candidate, &expected))
            {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `observe` cannot reuse an unbound or differently bound child"
                )));
            }
        }
    }
    let viewed_contained_resources = all_viewed_contained_resources
        .into_iter()
        .filter(|fact| !state.resources().contains_exact_representation(fact))
        .collect::<Vec<_>>();
    // Holding the folded composite certifies its instantiated body. Observation
    // only adds the body's duplicable cores, so it must not revalidate ownership.
    // Keep the projected views attached to that exact owned support: consuming
    // or changing the support must invalidate the observation, while unrelated
    // framed resources remain untouched. A view-only observation has no owned
    // authority to carry this relation and keeps the legacy explicit view.
    let (resources, inserted) = if let Some((support_entry, support)) = observation_support {
        state
            .resources()
            .clone()
            .unchecked_with_supported_facts_from_occurrence_with_memory_and_occurrences(
                support_entry,
                support,
                viewed_contained_resources.clone(),
                fact_state.memory(),
            )
    } else {
        state
            .resources()
            .clone()
            .unchecked_with_facts_and_occurrences(viewed_contained_resources.clone())
    };
    let mut dependency_bindings = Vec::new();
    let mut state = state;
    if let Some(binding) = borrowed_parent_binding {
        for (child, occurrence) in inserted {
            dependency_bindings.push((
                occurrence,
                crate::kernel::LoanViewBinding {
                    viewed: child,
                    ..binding.clone()
                },
            ));
        }
        state = project_children_into_ledger(
            state,
            &binding,
            dependency_bindings
                .iter()
                .map(|(_, child)| child.viewed.clone()),
            &memory,
            available_pure_facts.assumptions(),
            function.composite_resource_definitions(),
            &format!("`{claim_label}` tactic {tactic_index}: `observe`"),
        )?;
    }
    Ok((
        state
            .with_memory(memory)
            .with_resource_context_and_loan_dependencies(resources, dependency_bindings),
        abstract_resource,
    ))
}

#[allow(clippy::too_many_arguments)]
fn record_observed_composite_surface_facts<F: ResourcePureFacts>(
    definition: &ResourceDefinition,
    resource: &ResourceClause,
    substitutions: &BTreeMap<String, ContractExpression>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    fact_state: &CState,
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
        parameters,
        arguments,
        pre_state,
        fact_state,
        &CValue::Int32(Bitvector32Term::Constant(0)),
        available_pure_facts.assumptions(),
        spec_definitions,
    )?
    else {
        return Ok(());
    };
    if !active {
        return Ok(());
    }
    let parent = lower_resource_clause_at_state(resource, parameters, arguments, fact_state)
        .map_err(|error| error.raw_summary().to_string())?;
    let parent_subject = resource_clause_subject(resource);
    let mut owned_children = Vec::new();
    for contained in composite_body.contains() {
        if matches!(contained, ResourceClause::Iterated(_)) {
            // An iterated clause has no `contains(...)` or `separate(...)`
            // spelling; its element facts come only from `take`.
            continue;
        }
        let contained =
            instantiate_resource_clause(contained, substitutions).map_err(|message| {
                format!(
                    "could not instantiate resource `{}` contained resource: {message}",
                    definition.name()
                )
            })?;
        let lowered = lower_resource_clause_at_state(&contained, parameters, arguments, fact_state)
            .map_err(|error| error.raw_summary().to_string())?;
        if let Some(child) = lowered.owned_resource() {
            let child_subject = resource_clause_subject(&contained);
            surface_propositions
                .record_lowering(
                    &ClickProposition::Contains {
                        parent: parent_subject.clone(),
                        child: child_subject.clone(),
                    },
                    &Proposition::CResourceContains {
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
        if let Some(kernel) =
            resource_clause_loadable_prop_at_state(&contained, parameters, arguments, fact_state)
                .map_err(|error| error.raw_summary().to_string())?
        {
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
                    &Proposition::CResourceSeparate {
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
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    available_pure_facts: &PureFactList,
    surface_propositions: &mut SurfacePropositionMap,
    spec_definitions: SpecDefinitions<'_>,
    active_resources: &mut BTreeSet<String>,
) -> Result<(), String> {
    let assumptions = available_pure_facts.context();
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
            parameters,
            arguments,
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
            parameters,
            arguments,
            state,
            state,
            &CValue::Int32(Bitvector32Term::Constant(0)),
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
                parameters,
                arguments,
                state,
                state,
                &CValue::Int32(Bitvector32Term::Constant(0)),
                available_pure_facts,
                &surface,
                spec_definitions,
            )?;
            if available_pure_facts.contains(&kernel) {
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
    resource: &CResourceFact,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    result: &CValue,
    available_pure_facts: &mut ProofResourcePureFacts,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<CMemory, String> {
    let (name, resource_arguments) = match resource.resource() {
        CResource::Composite { name, arguments } => (name, arguments),
        CResource::Memory(_)
        | CResource::Token { .. }
        | CResource::Instance(_)
        | CResource::MutexGuard(_)
        | CResource::MutexLive(_)
        | CResource::MutexUse(_)
        | CResource::Publication(_)
        | CResource::PopulationAuthority(_)
        | CResource::Iterated(_) => {
            return Ok(state.memory().clone());
        }
    };
    let Some(definition) = resource_environment.get(name) else {
        return Ok(state.memory().clone());
    };
    apply_composite_observation_law_with_facts(
        resource_environment,
        definition,
        resource_arguments,
        parameters,
        arguments,
        pre_state,
        state,
        result,
        available_pure_facts,
        spec_definitions,
        true,
        None,
    )
    .map(|(memory, _, _)| memory)
}

#[allow(clippy::too_many_arguments)]
fn try_select_composite_resource_body(
    definition: &ResourceDefinition,
    substitutions: &BTreeMap<String, ContractExpression>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    result: &CValue,
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
        parameters,
        arguments,
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
            assumptions.proves_condition_exact_or_snapshot(condition, *value)
                || assumptions.decide(condition) == Some(*value)
        }
        Proposition::Not(body) => match body.as_ref() {
            Proposition::ConditionIs(condition, value) => {
                assumptions.proves_condition_exact_or_snapshot(condition, !*value)
                    || assumptions.decide(condition) == Some(!*value)
            }
            _ => false,
        },
        _ => assumptions.proves_exact(proposition) || assumptions.proves(proposition),
    };
    if proves_condition(&lowered) {
        return Ok(Some(true));
    }
    let negated = match &lowered {
        Proposition::ConditionIs(condition, value) => {
            Proposition::ConditionIs(condition.clone(), !value)
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
        // through every materialized heap snapshot in a recursive resource.
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
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    result: &CValue,
    assumptions: &PureFactContext,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<bool, String> {
    try_select_composite_resource_body(
        definition,
        substitutions,
        parameters,
        arguments,
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

/// Applies the non-consuming observation law declared by a composite body.
/// The kernel algebra handles the folded resource fact itself; Click owns this
/// definitional layer because it requires source-level substitution and fact
/// lowering.
#[allow(clippy::too_many_arguments)]
fn apply_composite_observation_law_with_facts<F: ResourcePureFacts>(
    resource_environment: &ResourceEnvironment,
    definition: &ResourceDefinition,
    resource_arguments: &[AlgebraicValue],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: &CState,
    result: &CValue,
    available_pure_facts: &mut F,
    spec_definitions: SpecDefinitions<'_>,
    lower_declared_source_facts: bool,
    compiled_definitions: Option<&[CCompositeResourceDefinition]>,
) -> Result<(CMemory, ResourceContext, bool), String> {
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
        parameters,
        arguments,
        pre_state,
        state,
        result,
        available_pure_facts.assumptions(),
        spec_definitions,
    )?
    else {
        return Ok((state.memory().clone(), ResourceContext::new(), false));
    };
    if !body_active {
        return Ok((state.memory().clone(), ResourceContext::new(), false));
    }
    let (memory, contained_resources) = instantiate_composite_resource_body_resources(
        definition.name(),
        composite_body,
        &substitutions,
        parameters,
        arguments,
        state.memory().clone(),
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
        // `open` retains the folded head for contract accounting while
        // exposing the unique owned body. Until that body is closed, do
        // not re-project its invariant at a newer memory/count snapshot.
        return Ok((memory, ResourceContext::new(), false));
    }
    let mut fact_state = state.clone().with_memory(memory.clone());
    if contained_resources
        .facts()
        .iter()
        .any(|child| matches!(child.resource(), CResource::PopulationAuthority(_)))
    {
        let owner = CResourceFact::own(CResource::Composite {
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
        &CResource::Composite {
            name: definition.name().to_string(),
            arguments: resource_arguments.to_vec().into(),
        },
        &substitutions,
        &contained_resources,
        parameters,
        arguments,
        pre_state,
        &fact_state,
        result,
        available_pure_facts,
        spec_definitions,
        lower_declared_source_facts,
    )?;
    Ok((memory, contained_resources, true))
}

fn append_composite_definition_observable_facts<F: ResourcePureFacts>(
    definition: &ResourceDefinition,
    composite_body: &CompositeResourceBody,
    parent_resource: &CResource,
    substitutions: &BTreeMap<String, ContractExpression>,
    contained_resources: &ResourceContext,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    fact_state: &CState,
    result: &CValue,
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
        parameters,
        arguments,
        fact_state.memory(),
        propositions,
    )?;

    if lower_declared_source_facts {
        append_composite_resource_declared_facts(
            definition,
            composite_body,
            substitutions,
            contained_resources,
            parameters,
            arguments,
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
    parent_resource: &CResource,
    contained_resources: &ResourceContext,
    propositions: &mut F,
) {
    let owned_children = contained_resources
        .facts()
        .iter()
        .filter_map(CResourceFact::owned_resource)
        .cloned()
        .collect::<Vec<_>>();
    for child in &owned_children {
        let proposition = Proposition::CResourceContains {
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
        propositions.insert(Proposition::CResourceComposition(owned_context));
    }
}

fn append_composite_resource_loadable_facts<F: ResourcePureFacts>(
    definition: &ResourceDefinition,
    composite_body: &CompositeResourceBody,
    substitutions: &BTreeMap<String, ContractExpression>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: &CMemory,
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
            parameters,
            arguments,
            memory,
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
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: &CMemory,
    propositions: &mut F,
) -> Result<(), ClickError> {
    let state = CState::new().with_memory(memory.clone());
    let Some(ranges) =
        resource_clause_memory_ranges_at_state(resource, parameters, arguments, &state)?
    else {
        return Ok(());
    };
    for range in ranges {
        for guard in crate::kernel::memory_range_extent_guard_spellings(&range) {
            propositions.insert(guard);
        }
    }
    if let Some(proposition) =
        resource_clause_loadable_prop(resource, parameters, arguments, memory)?
    {
        propositions.insert(proposition);
    }
    Ok(())
}

pub(super) fn append_lowered_resource_clause_loadable_fact(
    resource: &ResourceClause,
    _parameters: &[syntax::C0Parameter],
    lowered: &CResourceFact,
    state: &CState,
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
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    fact_state: &CState,
    result: &CValue,
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
            parameters,
            arguments,
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
                describe_resource_facts(contained_resources.facts(), parameters, arguments)
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
    facts: ProofFacts,
) -> ProofFacts {
    let mut facts = ProofResourcePureFacts::new(facts);
    append_resource_context_observable_facts_with_store(resources, &mut facts);
    facts.facts
}

fn describe_resource_context_validity_error(
    error: ResourceContextValidityError,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> String {
    match error {
        ResourceContextValidityError::InvalidExclusiveAccess(_) => {
            "field-bearing resource instances and mutex guards require exclusive ownership with quantity one".into()
        }
        ResourceContextValidityError::DuplicateOwnedResourceFact(resource) => {
            format!(
                "duplicate resource fact `{}`",
                describe_resource_fact(&resource, parameters, arguments)
            )
        }
        ResourceContextValidityError::OverlappingOwnedMemoryResources { left, right } => {
            format!(
                "overlapping owned memory resource facts `owns {}` and `owns {}`",
                describe_memory_range(&left, parameters, arguments),
                describe_memory_range(&right, parameters, arguments)
            )
        }
    }
}

fn materialize_composite_resource_memory(
    name: &str,
    composite_body: &CompositeResourceBody,
    substitutions: &BTreeMap<String, ContractExpression>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: CMemory,
) -> Result<CMemory, String> {
    let (memory, _) = instantiate_composite_resource_body_resources(
        name,
        composite_body,
        substitutions,
        parameters,
        arguments,
        memory,
    )?;
    Ok(memory)
}

/// Instantiates the resource-state side of a composite definition. The result
/// is provisional until the caller composes it with assumptions and checks
/// validity through `ResourceContext`.
pub(in crate::surface) fn instantiate_composite_resource_body_resources(
    name: &str,
    composite_body: &CompositeResourceBody,
    substitutions: &BTreeMap<String, ContractExpression>,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    mut memory: CMemory,
) -> Result<(CMemory, ResourceContext), String> {
    let mut resources = ResourceContext::new();
    // Every cell exposed by this one body expansion names the value it had
    // in the snapshot before the expansion began.  Lower clauses against the
    // progressively materialized memory so a later clause can still address
    // through a cell an earlier clause exposed, but do not let those cached
    // cells become a new load-naming epoch.  The checked resource rewrite
    // independently validates every added cell against this same entry
    // snapshot.
    let naming_memory = memory.clone();
    for contained in composite_body.contains() {
        let contained =
            instantiate_resource_clause(contained, substitutions).map_err(|message| {
                format!("could not instantiate composite resource `{name}` body: {message}")
            })?;
        let lowered =
            lower_resource_clause(&contained, parameters, arguments, &memory).map_err(|error| {
                format!(
                    "could not lower resource `{name}` contained `{}`: {}\n  {}",
                    describe_resource_clause(&contained),
                    error.raw_summary(),
                    describe_available_facts(&[], resources.facts(), parameters, arguments, &[])
                )
            })?;
        memory = materialize_composite_resource_cells_from_snapshot(
            memory,
            &naming_memory,
            &contained,
            &lowered,
            parameters,
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
                .as_c_value()
                .ok_or_else(|| "algebraic resource bodies are not supported yet".to_string())?;
            Ok((
                parameter.name().to_string(),
                ContractExpression::CFragment(CExpression::Value(argument.clone())),
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
    memory: &CMemory,
    resources: &ResourceContext,
    assumptions: &PureFactContext,
    resource_environment: &ResourceEnvironment,
    spec_definitions: SpecDefinitions<'_>,
    compiled_definitions: Option<&[CCompositeResourceDefinition]>,
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
    let fact = CResourceFact::own(CResource::Composite {
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
            ContractExpression::CFragment(CExpression::Value(value)),
        );
    }
    Ok(substitutions)
}

pub(super) struct CheckedResourceUnfold {
    pub(super) state: CState,
    pub(super) facts: ProofFacts,
    pub(super) added_facts: Vec<Proposition>,
    pub(super) selected: CResourceFact,
    pub(super) body_was_already_exposed: bool,
}

#[allow(clippy::too_many_arguments)]
pub(super) fn unfold_composite_resource_for_proof(
    resource_environment: &ResourceEnvironment,
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: CState,
    facts: ProofFacts,
    surface_propositions: &mut SurfacePropositionMap,
    spec_definitions: SpecDefinitions<'_>,
    claim_label: &str,
    tactic_index: usize,
    materialize_memory: bool,
) -> Result<CheckedResourceUnfold, ClickError> {
    unfold_composite_resource_for_proof_with_access(
        resource_environment,
        resource,
        parameters,
        arguments,
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
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: CState,
    facts: ProofFacts,
    surface_propositions: &mut SurfacePropositionMap,
    spec_definitions: SpecDefinitions<'_>,
    claim_label: &str,
    tactic_index: usize,
) -> Result<CheckedResourceUnfold, ClickError> {
    unfold_composite_resource_for_proof_with_access(
        resource_environment,
        resource,
        parameters,
        arguments,
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
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: CState,
    facts: ProofFacts,
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
        parameters,
        arguments,
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
        state: unfolded.state,
        facts: facts.facts,
        added_facts: facts.added,
        selected: unfolded.selected,
        body_was_already_exposed: unfolded.body_was_already_exposed,
    })
}

#[allow(clippy::too_many_arguments)]
fn unfold_composite_resource_with_facts<F: ResourcePureFacts>(
    resource_environment: &ResourceEnvironment,
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    mut state: CState,
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
        parameters,
        arguments,
        &state,
        None,
        available_pure_facts.assumptions(),
        resource_environment,
        spec_definitions,
        None,
    )?;
    let body_active = composite_resource_body_is_active_with_assumptions(
        definition,
        &substitutions,
        parameters,
        arguments,
        &state,
        &state,
        &CValue::Int32(Bitvector32Term::Constant(0)),
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
    let mut abstract_resource =
        lower_resource_clause_at_state(resource, parameters, arguments, &state)?;
    let requested_quantity = abstract_resource
        .owned_quantity_term()
        .cloned()
        .unwrap_or(Bitvector32Term::Constant(1));
    let assumptions = available_pure_facts.assumptions().clone();
    if let Some(authority) = state
        .resources()
        .directly_supporting_fact(&abstract_resource, &assumptions)
        .or_else(|| {
            (!matches!(resource, ResourceClause::Quantified { .. }))
                .then(|| {
                    let viewed = CResourceFact::View(abstract_resource.resource().clone());
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
                "`{claim_label}` tactic {tactic_index}: `unfold` refused ambiguous loan dependency: {message}"
            ))
        })?
    } else {
        None
    };
    // An owned borrowing composite carries the hold binding of the view it
    // packages (step 7). Unfolding hands that binding, hold included, to the
    // restored piece, so the loan stays held and a later fold reuses the
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
            CResource::Composite { name, arguments } | CResource::Token { name, arguments } => {
                (name.clone(), arguments.clone())
            }
            CResource::Memory(_) => unreachable!("a declared resource lowered to memory"),
            CResource::Instance(_)
            | CResource::MutexGuard(_)
            | CResource::MutexLive(_)
            | CResource::MutexUse(_)
            | CResource::Publication(_)
            | CResource::PopulationAuthority(_)
            | CResource::Iterated(_) => {
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
        Bitvector32Term::Constant(1),
    );
    if state.population_body_is_open(&population_name, &population_arguments) {
        return Err(ClickError::new("population body is already open"));
    }
    if access == ResourceBodyAccess::Finalize {
        let quantity = requested_quantity;
        let count = population_count;
        let final_unit = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(Box::new(count), Box::new(quantity)),
            true,
        );
        if !assumptions.proves(&final_unit) {
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
            "`{claim_label}` tactic {tactic_index}: `open({})` Requires {} {}",
            describe_resource_clause(resource),
            if abstract_resource.is_view() {
                "views"
            } else {
                "owns"
            },
            describe_resource_clause(resource),
        )));
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
            let lowered =
                lower_resource_clause_at_state(&contained, parameters, arguments, &state)?;
            let Some(next) = remaining.without_fact(&lowered, &assumptions) else {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `unfold({})` failed: {}",
                    describe_resource_clause(resource),
                    describe_missing_resource_fact(
                        &abstract_resource,
                        &available_pure_facts.materialize(),
                        state.resources().facts(),
                        parameters,
                        arguments,
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
                parameters,
                arguments,
                &[]
            )
        )));
    }

    let mut unfolded_facts = Vec::new();
    for contained in contained_clauses {
        let contained = instantiate_resource_clause(contained, &substitutions).map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: could not instantiate `unfold({})`: {message}",
                describe_resource_clause(resource)
            ))
        })?;
        let mut lowered =
            lower_resource_clause_at_state(&contained, parameters, arguments, &state)?;
        if opening_view {
            lowered = CResourceFact::View(lowered.resource().clone());
        }
        unfolded_facts.push(lowered.clone());
        // A completed outcome has no more C loads to execute. Its proof
        // receives loadability and symbolic loads without modifying the
        // certified program memory by installing cached cells into it.
        if materialize_memory {
            let memory = materialize_composite_resource_cells(
                state.memory().clone(),
                &contained,
                &lowered,
                parameters,
            );
            // Naming cells during a proof rewrite is not a C write. Keep
            // unrelated memory-backed views and their support identities.
            state = state.with_materialized_memory(memory);
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

    let body_was_already_exposed = composite_body.condition().is_none()
        && unfolded_facts
            .iter()
            .all(|fact| state.resources().contains_exact_representation(fact));

    // Validate the projected ownership before assuming facts supplied by the
    // same definition. A body may legitimately state separation that is
    // needed to normalize symbolic children, but it must not use a
    // contradictory separation claim to conceal a concretely overlapping
    // pair. This is one validity pass over the complete projection, not one
    // normalization per child.
    if !already_unfolded && !body_was_already_exposed {
        let projected = state
            .resources()
            .clone()
            .unchecked_with_facts(unfolded_facts.clone());
        if let Some(error) = projected.validity_error_ignoring_separation(&assumptions) {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `unfold({})` produced {}",
                describe_resource_clause(resource),
                describe_resource_context_validity_error(error, parameters, arguments)
            )));
        }
    }

    for fact in body_facts {
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
            parameters,
            arguments,
            &fact_state,
            &fact_state,
            &CValue::Int32(Bitvector32Term::Constant(0)),
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
                    parameters,
                    arguments,
                    &[]
                )
            ))
        })?;
        let lowered_fact = unfold_predicates_in_proposition(
            spec_definitions,
            &[],
            &lowered_fact,
            available_pure_facts.assumptions(),
        )
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: could not unfold `unfold({})` pure fact: {message}",
                describe_resource_clause(resource)
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
        let temporary_view_index = DynamicViewDependencyIndex::new(
            &temporary_views,
            &temporary_unbound_views,
            available_pure_facts.assumptions(),
        );
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
                .is_none_or(|parent| !same_loan_authority(parent, &binding))
        {
            return Err(ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: `unfold({})` cannot publish a current viewed-memory fact without its parent loan",
                describe_resource_clause(resource)
            )));
        }
        surface_propositions.record_lowering(&fact, &lowered_fact)?;
        for fact in lowering_facts {
            available_pure_facts.insert(fact);
        }
        available_pure_facts.insert(lowered_fact);
    }

    // Keep exact identities for children that were already present.  Equal
    // child facts may have different dependency state, so a later rewrite
    // must validate those identities individually rather than selecting a
    // binding by fact value.
    let preexisting_unfolded_occurrences = unfolded_facts
        .iter()
        .filter(|fact| fact.is_view())
        .flat_map(|fact| state.resources().occurrences_for_fact(fact))
        .collect::<BTreeSet<_>>();

    // Project the complete body in one checked composition. Composing each
    // child separately renormalizes the same ambient resource context once
    // per child, making one simple `unfold` depend on the accumulated proof
    // history rather than the size of the resource body. The definition's
    // pure facts are simultaneous consequences of the same composite law, so
    // make them available while canonicalizing its children.
    let mut inserted_unfolded_occurrences = Vec::new();
    if !already_unfolded && !body_was_already_exposed {
        if borrowed_parent_binding.is_some() {
            let resources = state
                .resources()
                .clone()
                .try_compose_with_facts_delaying_normalization_with_occurrences(
                    unfolded_facts.clone(),
                    available_pure_facts.assumptions(),
                )
                .map_err(|error| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `unfold({})` produced {}",
                        describe_resource_clause(resource),
                        describe_resource_context_validity_error(error, parameters, arguments)
                    ))
                })?;
            inserted_unfolded_occurrences = resources.1;
            state = state.with_resource_context(resources.0);
        } else if let Some(binding) = held_piece_binding.as_ref() {
            let (resources, inserted) = state
                .resources()
                .clone()
                .try_compose_with_facts_delaying_normalization_with_occurrences(
                    unfolded_facts.clone(),
                    available_pure_facts.assumptions(),
                )
                .map_err(|error| {
                    ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `unfold({})` produced {}",
                        describe_resource_clause(resource),
                        describe_resource_context_validity_error(error, parameters, arguments)
                    ))
                })?;
            let assumptions = available_pure_facts.assumptions().clone();
            let dependencies = inserted
                .into_iter()
                .filter(|(child, _)| {
                    child.is_view()
                        && crate::kernel::c_resources_directly_match(
                            binding.viewed.resource(),
                            child.resource(),
                            &assumptions,
                        )
                })
                // The binding keeps the loan's own description: that is what
                // the ledger authorizes, and the piece's current spelling is
                // related to it only through facts the ledger does not hold.
                .map(|(_, occurrence)| (occurrence, binding.clone()))
                .collect::<Vec<_>>();
            state = state.with_resource_context_and_loan_dependencies(resources, dependencies);
        } else {
            // Population cleanup and member private body opening
            // are certified as exact exchanges. Preserve adjacent framed
            // ranges so nested opens have the same delta as the kernel law.
            let resources = if body_reads_counts || (access == ResourceBodyAccess::Open) {
                state
                    .resources()
                    .clone()
                    .try_compose_with_facts_delaying_normalization(
                        unfolded_facts.clone(),
                        available_pure_facts.assumptions(),
                    )
            } else {
                state.resources().clone().try_compose_with_facts(
                    unfolded_facts.clone(),
                    available_pure_facts.assumptions(),
                )
            }
            .map_err(|error| {
                ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `unfold({})` produced {}",
                    describe_resource_clause(resource),
                    describe_resource_context_validity_error(error, parameters, arguments)
                ))
            })?;
            state = state.with_resource_context(resources);
        }
    }

    // Finalizing a viewed composite replaces its folded occurrence with fresh
    // viewed children.  Keep the exact loan/share/support bundle on each
    // child.  An exclusive instance view has already been rejected above by
    // the resource-kind check and never enters this projection path.
    if let Some(binding) = borrowed_parent_binding {
        let inserted_child_occurrences = inserted_unfolded_occurrences
            .iter()
            .filter(|(child, _)| child.is_view())
            .map(|(_, occurrence)| *occurrence)
            .collect::<BTreeSet<_>>();
        let mut dependencies = inserted_unfolded_occurrences
            .into_iter()
            .filter(|(child, _)| child.is_view())
            .map(|(child, occurrence)| {
                (
                    occurrence,
                    crate::kernel::LoanViewBinding {
                        viewed: child,
                        ..binding.clone()
                    },
                )
            })
            .collect::<Vec<_>>();
        for child in unfolded_facts.iter().filter(|fact| fact.is_view()) {
            let child_occurrences = state.resources().occurrences_for_fact(child);
            let mut found_destination = false;
            for occurrence in child_occurrences {
                if inserted_child_occurrences.contains(&occurrence) {
                    found_destination = true;
                    continue;
                }
                if !preexisting_unfolded_occurrences.contains(&occurrence) {
                    continue;
                }
                found_destination = true;
                let child_binding = state.resources().loan_dependency(occurrence);
                if child_binding.is_none()
                    && !state.resources().view_occurrence_is_principal(occurrence)
                {
                    dependencies.push((
                        occurrence,
                        crate::kernel::LoanViewBinding {
                            viewed: child.clone(),
                            ..binding.clone()
                        },
                    ));
                } else if child_binding
                    .as_ref()
                    .is_none_or(|existing| !same_loan_authority(existing, &binding))
                {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {tactic_index}: `unfold` cannot reuse an unbound or differently bound child for a viewed composite"
                    )));
                }
            }
            if !found_destination {
                return Err(ClickError::new(format!(
                    "`{claim_label}` tactic {tactic_index}: `unfold` produced no exact destination for a viewed child"
                )));
            }
        }
        let projection_memory = state.memory().clone();
        let definitions = crate::surface::verification::composite_resource_definitions(
            resource_environment,
            spec_definitions,
        )?;
        state = project_children_into_ledger(
            state,
            &binding,
            dependencies.iter().map(|(_, child)| child.viewed.clone()),
            &projection_memory,
            available_pure_facts.assumptions(),
            &definitions,
            &format!("`{claim_label}` tactic {tactic_index}: `unfold`"),
        )?;
        let resources = state.resources().clone();
        state = state.with_resource_context_and_loan_dependencies(resources, dependencies);
    }

    let unfolded_resources =
        ResourceContext::new_with_equalities(available_pure_facts.assumptions())
            .unchecked_with_facts(unfolded_facts);
    append_composite_resource_relation_facts_with_store(
        abstract_resource.resource(),
        &unfolded_resources,
        available_pure_facts,
    );

    append_state_resource_context_observable_facts_with_store(
        parameters,
        arguments,
        &state,
        available_pure_facts,
        &format!(
            "`{claim_label}` tactic {tactic_index}: `unfold({})`",
            describe_resource_clause(resource)
        ),
    )?;

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
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    mut outcome: CFunctionOutcome,
    spec_definitions: SpecDefinitions<'_>,
    unfolded_predicates: &[String],
    closure: ResourceBodyClosure,
    family_reaches_population: bool,
) -> Result<CFunctionOutcome, ClickError> {
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
        let mut substitutions =
            resource_argument_substitutions(definition, resource, claim_label, path_index)?;
        let (guard_result, guard_state) = match &outcome {
            CFunctionOutcome::Return { value, state } => (value.clone(), state.clone()),
            _ => {
                return Err(ClickError::new(format!(
                    "`{claim_label}` path {path_index}: `fold({})` requires a return outcome, got {}",
                    describe_resource_clause(resource),
                    describe_function_outcome(&outcome, parameters, arguments)
                )));
            }
        };
        extend_substitutions_with_witnesses(
            &mut substitutions,
            definition,
            resource,
            parameters,
            arguments,
            &guard_state,
            Some(&guard_result),
            pure_facts.assumptions(),
            resource_environment,
            spec_definitions,
            None,
        )?;
        let mut body_active = composite_resource_body_is_active_with_assumptions(
            definition,
            &substitutions,
            parameters,
            arguments,
            pre_state,
            &guard_state,
            &guard_result,
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
        let mut authority_closing_fact_state = None;
        let mut authority_control_definition = None;
        let mut folded_representation_already_present = false;
        let mut folded_authority_occurrence = None;
        let authority_control_body = composite_body.contains().iter().any(|contained| {
                matches!(contained, ResourceClause::Declared { name, .. } if name == "authority")
            });
        if closure == ResourceBodyClosure::Initialize {
            let CFunctionOutcome::Return { value, state } = &mut outcome else {
                unreachable!("the return outcome was checked above");
            };
            let population = lower_resource_clause_at_state_with_assumptions(
                resource,
                parameters,
                arguments,
                state,
                Some(value),
                pure_facts.assumptions(),
            )?;
            let quantity = population
                .owned_quantity_term()
                .expect("fold requires owned composite authority")
                .clone();
            let name = match population.resource() {
                CResource::Composite { name, .. } | CResource::Token { name, .. } => name,
                CResource::Memory(_)
                | CResource::Instance(_)
                | CResource::MutexGuard(_)
                | CResource::MutexLive(_)
                | CResource::MutexUse(_)
                | CResource::Publication(_)
                | CResource::PopulationAuthority(_)
                | CResource::Iterated(_) => {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` path {path_index}: `fold({})` did not lower to a declared resource",
                        describe_resource_clause(resource)
                    )));
                }
            };
            let assumptions = pure_facts.assumptions();
            let quantity_is_zero = quantity.as_const() == Some(0)
                || assumptions.proves(&Proposition::ConditionIs(
                    ConditionTerm::Bitvector32Equal(
                        Box::new(quantity.clone()),
                        Box::new(Bitvector32Term::Constant(0)),
                    ),
                    true,
                ));
            // A resource quantity is a signed `int32`, and `as_const` answers
            // `u32`, so `-1` read here as `4294967295` was both "positive"
            // and the thing that made the body active. The symbolic arm
            // beside it always asked the signed question; reading the
            // constant signed is what makes the two agree.
            let quantity_is_positive = quantity.as_const().is_some_and(|value| (value as i32) > 0)
                || assumptions.proves(&Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedGreaterThan(
                        Box::new(quantity.clone()),
                        Box::new(Bitvector32Term::Constant(0)),
                    ),
                    true,
                ));
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
            let CFunctionOutcome::Return { value, state } = &outcome else {
                unreachable!("the return outcome was checked above");
            };
            let population = lower_resource_clause_at_state_with_assumptions(
                resource,
                parameters,
                arguments,
                state,
                Some(value),
                pure_facts.assumptions(),
            )?;
            let assumptions = pure_facts.assumptions();
            if !state.resources().satisfies_fact(&population, assumptions) {
                let viewed_population = CResourceFact::View(population.resource().clone());
                closing_view = state
                    .resources()
                    .satisfies_fact(&viewed_population, assumptions);
            }
            let (name, _) = match population.resource() {
                CResource::Composite { name, arguments } | CResource::Token { name, arguments } => {
                    (name, arguments)
                }
                CResource::Memory(_) => unreachable!("declared resource lowered to memory"),
                CResource::Instance(_)
                | CResource::MutexGuard(_)
                | CResource::MutexLive(_)
                | CResource::MutexUse(_)
                | CResource::Publication(_)
                | CResource::PopulationAuthority(_)
                | CResource::Iterated(_) => {
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
                            "`{claim_label}` path {path_index}: closing `open({})` {message}",
                            describe_resource_clause(resource)
                        ))
                    })?;
                authority_closing_fact_state = Some(state.clone().with_resource_context(projected));
            } else if composite_body
                .facts()
                .iter()
                .any(proposition_contains_resource_count)
            {
                return Err(ClickError::new(format!(
                    "`{claim_label}` path {path_index}: closing `open({})` requires its resource population to remain active",
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
        let mut body_loan_dependency = None;
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
                parameters,
                arguments,
                &guard_state,
                Some(&guard_result),
                pure_facts.assumptions(),
            )?;
            if lowered.is_view()
                && unique_borrowed_resource_dependency(&guard_state, &lowered)
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` path {path_index}: `fold` refused ambiguous body loan dependency: {message}"
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
        );
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
                let CFunctionOutcome::Return { value, state } = &outcome else {
                    unreachable!("the return outcome was checked above")
                };
                let state = authority_closing_fact_state.as_ref().unwrap_or(state);
                let lowered = lower_outcome_proposition_with_assumptions(
                    parameters,
                    arguments,
                    pre_state,
                    state,
                    value,
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
                unfold_predicates_in_proposition(
                    spec_definitions,
                    unfolded_predicates,
                    &lowered,
                    pure_facts.assumptions(),
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "`{claim_label}` path {path_index}: could not unfold exact `fold({})` fact: {message}",
                        describe_resource_clause(resource)
                    ))
                })?
            };
            if let Some(binding) = dynamic_body_fact_dependency(
                &required,
                authority_closing_fact_state.as_ref().unwrap_or(match &outcome {
                    CFunctionOutcome::Return { state, .. } => state,
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
                if body_loan_dependency
                    .as_ref()
                    .is_some_and(|existing| !same_loan_authority(existing, &binding))
                {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` path {path_index}: `fold({})` body facts depend on different stable-view authorities",
                        describe_resource_clause(resource)
                    )));
                }
                body_loan_dependency = Some(binding);
            }
            // Available facts may write this body fact through loads recorded
            // at an earlier snapshot. Decide those forms with the bounded
            // check matchers first: exact structural membership, the
            // snapshot-bridging relation with this execution's effect facts as
            // framing, and the direct separation-fact matcher. All of these do
            // work proportional to the fact being checked, so an exactly
            // available body fact never rides on the open-ended kernel search
            // below, which can consume a large share of the fold's budget.
            let exactly_available =
                pure_facts.exact_available_across_effects(&required, execution_pure_facts);
            if !exactly_available
                && !matches!(normalize_proposition(&required), SimpProposition::True)
                && !body_assumptions.proves(&required)
            {
                // `proves` returns false when the active budget runs out
                // mid-derivation. Reporting that truncation as a missing fact
                // is misleading, so surface the budget state itself first.
                check_verification_deadline()?;
                let available_pure_facts = pure_facts.materialize();
                let resources = match &outcome {
                    CFunctionOutcome::Return { state, .. } => state.resources().facts(),
                    _ => pre_state.resources().facts(),
                };
                let required_text = describe_pure_fact(&required, parameters, arguments);
                let identically_printed = available_pure_facts
                    .iter()
                    .filter(|fact| describe_pure_fact(fact, parameters, arguments) == required_text)
                    .count();
                let snapshot_note = if identically_printed > 0 {
                    format!(
                        "\n  note: {identically_printed} available fact(s) print identically but carry different embedded memory snapshots, and the recorded execution effects do not prove the snapshots agree at the loaded pointers"
                    )
                } else {
                    String::new()
                };
                if authority_control_body {
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
                    return Err(ClickError::new(format!(
                        "`{claim_label}` path {path_index}: `fold({})` Requires {}",
                        describe_resource_clause(source_resource),
                        describe_click_proposition(&source_fact),
                    )));
                }
                return Err(ClickError::new(format!(
                    "`{claim_label}` path {path_index}: `fold({})` requires an exact body fact: {}{snapshot_note}",
                    describe_resource_clause(resource),
                    describe_missing_pure_fact(
                        &required,
                        &available_pure_facts,
                        resources,
                        parameters,
                        arguments,
                        execution_pure_facts,
                    )
                )));
            }
        }
        let CFunctionOutcome::Return { value, state } = outcome else {
            return Err(ClickError::new(format!(
                "`{claim_label}` path {path_index}: `fold({})` requires a return outcome, got {}\n  execution pure facts: {}",
                describe_resource_clause(resource),
                describe_function_outcome(&outcome, parameters, arguments),
                describe_execution_pure_facts(execution_pure_facts)
            )));
        };
        let mut post_state = state;
        // Range forms in held resource facts embed loads at their
        // creation snapshot; carrying them to the fold state needs the
        // execution's store effect facts alongside the pure facts.
        let assumptions = pure_facts.assumptions().clone();
        let _assumptions_id_scope = crate::kernel::PureFactContextIdScope::enter(&assumptions);
        let mut lowered_contained = Vec::new();
        let mut body_has_unbound_view = false;
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
                parameters,
                arguments,
                &post_state,
                Some(&value),
                pure_facts.assumptions(),
            )?;
            if lowered.is_view() {
                let binding = unique_borrowed_resource_dependency(&post_state, &lowered)
                    .map_err(|message| {
                        ClickError::new(format!(
                            "`{claim_label}` path {path_index}: `fold` refused ambiguous body loan dependency: {message}"
                        ))
                    })?;
                match binding {
                    Some(binding) => {
                        if body_has_unbound_view
                            || body_loan_dependency
                                .as_ref()
                                .is_some_and(|existing| !same_loan_authority(existing, &binding))
                        {
                            return Err(ClickError::new(format!(
                                "`{claim_label}` path {path_index}: `fold` body views carry different or incomplete loan dependencies"
                            )));
                        }
                        body_loan_dependency = Some(binding);
                    }
                    None if body_loan_dependency.is_some() => {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` path {path_index}: `fold` body views carry different or incomplete loan dependencies"
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
                                describe_resource_fact(&lowered, parameters, arguments)
                            )));
                        }
                        body_has_unbound_view = true;
                    }
                }
            }
            if preserve_exposed_body {
                // This body belonged to the active population before `open`.
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
                let viewed = CResourceFact::View(lowered.resource().clone());
                if post_state.resources().satisfies_fact(&viewed, &assumptions) {
                    lowered = viewed;
                }
            }
            lowered_contained.push(lowered);
        }
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
                let action = match closure {
                    ResourceBodyClosure::Initialize => {
                        format!("`fold({})`", describe_resource_clause(resource))
                    }
                    ResourceBodyClosure::CloseOpen { .. } => {
                        format!("closing `open({})`", describe_resource_clause(resource))
                    }
                };
                return Err(ClickError::new(format!(
                    "`{claim_label}` path {path_index}: {action} failed: {}",
                    describe_missing_resource_fact(
                        lowered,
                        &available_pure_facts,
                        &diagnostic_facts,
                        parameters,
                        arguments,
                        execution_pure_facts
                    )
                )));
            };
            resources = next;
        }
        post_state = Box::new(post_state.with_resource_context(resources));

        if closure == ResourceBodyClosure::Initialize && !folded_representation_already_present {
            let abstract_resource = lower_resource_clause_at_state_with_assumptions(
                resource,
                parameters,
                arguments,
                &post_state,
                Some(&value),
                pure_facts.assumptions(),
            )?;
            // An owned composite that packages a loan-backed view is a
            // borrowing composite (escaping borrows in docs/internals/stable-views.md). Its head keeps the
            // loan's scope open through a hold, so the owner behind the view
            // cannot be recovered and written while the composite still
            // describes it. A piece that already carries a hold (restored by
            // an earlier unfold) is folded back under the same hold.
            let mut body_loan_dependency = body_loan_dependency;
            if let Some(binding) = body_loan_dependency.as_mut()
                && !abstract_resource.is_view()
                && binding.hold.is_none()
            {
                let (Some(ledger), Some(holder)) = (
                    post_state.loan_ledger().cloned(),
                    post_state.loan_participant(),
                ) else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` path {path_index}: `fold({})` packages a loan-backed view without a loan ledger",
                        describe_resource_clause(resource)
                    )));
                };
                let (ledger, hold) = ledger.hold(binding, holder).map_err(|refusal| {
                    ClickError::new(format!(
                        "`{claim_label}` path {path_index}: `fold({})` cannot hold the loan behind its viewed body: {refusal:?}",
                        describe_resource_clause(resource)
                    ))
                })?;
                binding.hold = Some(hold);
                post_state = Box::new(post_state.with_loan_ledger(Some(ledger)));
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
                            describe_resource_context_validity_error(error, parameters, arguments)
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
                (folded_authority_occurrence, body_loan_dependency.clone())
            {
                // A viewed fold describes the head itself under the loan; an
                // owned fold keeps the packaged piece's description, which is
                // what the loan authorizes and what an unfold restores.
                let viewed = if abstract_resource.is_view() {
                    abstract_resource.clone()
                } else {
                    binding.viewed.clone()
                };
                let resources = post_state.resources().clone();
                post_state = Box::new(post_state.with_resource_context_and_loan_dependencies(
                    resources,
                    [(
                        occurrence,
                        crate::kernel::LoanViewBinding { viewed, ..binding },
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
                parameters,
                arguments,
                &post_state,
                Some(&value),
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
                    "`{claim_label}` path {path_index}: `fold({})` changed its folded authority snapshot",
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
                parameters,
                arguments,
                &post_state,
                Some(&value),
                pure_facts.assumptions(),
            )?;
            if let CResource::Composite { name, arguments } | CResource::Token { name, arguments } =
                selected.resource()
            {
                post_state = Box::new(
                    post_state
                        .close_population_body(name.clone(), arguments.clone())
                        .map_err(ClickError::new)?,
                );
            }
        }
        outcome = CFunctionOutcome::Return {
            value,
            state: post_state,
        };
    }

    Ok(outcome)
}

pub(super) struct CheckedResourceFold {
    pub(super) state: CState,
    pub(super) facts: ProofFacts,
}

pub(super) struct CheckedOutcomeResourceFold {
    pub(super) outcome: CFunctionOutcome,
    pub(super) facts: ProofFacts,
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
    facts: ProofFacts,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: CState,
    spec_definitions: SpecDefinitions<'_>,
    unfolded_predicates: &[String],
    family_reaches_population: bool,
) -> Result<CheckedResourceFold, ClickError> {
    fold_composite_resource_for_proof_with_closure(
        resource_environment,
        resource,
        source_resource,
        claim_label,
        tactic_index,
        facts,
        parameters,
        arguments,
        pre_state,
        state,
        spec_definitions,
        unfolded_predicates,
        ResourceBodyClosure::Initialize,
        family_reaches_population,
    )
}

/// Checks one result-aware `fold` against the persistent facts and snapshot
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
    facts: ProofFacts,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    outcome: CFunctionOutcome,
    spec_definitions: SpecDefinitions<'_>,
    unfolded_predicates: &[String],
    closure: ResourceBodyClosure,
    family_reaches_population: bool,
) -> Result<CheckedOutcomeResourceFold, ClickError> {
    let mut facts = ProofResourcePureFacts::new(facts);
    let outcome = fold_composite_resources_on_outcome_with_facts(
        resource_environment,
        std::slice::from_ref(resource),
        None,
        claim_label,
        path_index,
        execution_pure_facts,
        &facts,
        parameters,
        arguments,
        pre_state,
        outcome,
        spec_definitions,
        unfolded_predicates,
        closure,
        family_reaches_population,
    )?;
    // A scope close exposes only its restored composite's observations.
    // Unrelated resources and their observation laws are unchanged; do not
    // scan/reproject the whole outcome for each closed scope.
    if matches!(closure, ResourceBodyClosure::CloseOpen { .. })
        && let CFunctionOutcome::Return { value, state } = &outcome
    {
        let requested = lower_resource_clause_at_state_with_result(
            resource, parameters, arguments, state, value,
        )?;
        let viewed = CResourceFact::View(requested.resource().clone());
        let support = state
            .resources()
            .directly_supporting_fact(&requested, facts.assumptions())
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
                parameters,
                arguments,
                pre_state,
                state,
                value,
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
    facts: ProofFacts,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: CState,
    spec_definitions: SpecDefinitions<'_>,
    unfolded_predicates: &[String],
    preserve_exposed_body: bool,
) -> Result<CheckedResourceFold, ClickError> {
    fold_composite_resource_for_proof_with_closure(
        resource_environment,
        resource,
        resource,
        claim_label,
        tactic_index,
        facts,
        parameters,
        arguments,
        pre_state,
        state,
        spec_definitions,
        unfolded_predicates,
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
    facts: ProofFacts,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    state: CState,
    spec_definitions: SpecDefinitions<'_>,
    unfolded_predicates: &[String],
    closure: ResourceBodyClosure,
    family_reaches_population: bool,
) -> Result<CheckedResourceFold, ClickError> {
    let facts = ProofResourcePureFacts::new(facts);
    let outcome = CFunctionOutcome::Return {
        value: CValue::Int32(Bitvector32Term::Constant(0)),
        state: Box::new(state),
    };
    let outcome = fold_composite_resources_on_outcome_with_facts(
        resource_environment,
        std::slice::from_ref(resource),
        Some(source_resource),
        claim_label,
        tactic_index,
        &[],
        &facts,
        parameters,
        arguments,
        pre_state,
        outcome,
        spec_definitions,
        unfolded_predicates,
        closure,
        family_reaches_population,
    )?;
    let CFunctionOutcome::Return { state, .. } = outcome else {
        unreachable!("folding a synthetic return outcome preserves its outcome kind")
    };
    Ok(CheckedResourceFold {
        state: *state,
        facts: facts.facts,
    })
}

/// Resolves the source declaration that supplies fold, unfold, and observation
/// laws for a composite resource fact.
/// The hole-free iterated ownership fact the one iterated clause of
/// `resource`'s definition denotes at the tactic's own arguments, read at
/// `state`. `gather` forms it and `scatter` dissolves it.
#[allow(clippy::too_many_arguments)]
pub(super) fn iterated_template_for_resource(
    resource_environment: &ResourceEnvironment,
    resource: &ResourceClause,
    action: &str,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    claim_label: &str,
    tactic_index: usize,
) -> Result<crate::kernel::CIteratedMemory, ClickError> {
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
    let clause = instantiate_resource_clause(&ResourceClause::Iterated(clause.clone()), &substitutions)
        .map_err(|message| {
            ClickError::new(format!(
                "`{claim_label}` tactic {tactic_index}: could not instantiate the iterated clause of `{}`: {message}",
                definition.name()
            ))
        })?;
    let lowered =
        lower_resource_clause_at_current_locals(&clause, parameters, arguments, state, None)?;
    match lowered {
        CResourceFact::Own(CResource::Iterated(iterated), _) => Ok(iterated.as_ref().clone()),
        _ => Err(ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: the iterated clause of `{}` did not lower to iterated ownership",
            definition.name()
        ))),
    }
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
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    result: Option<&CValue>,
    assumptions: &PureFactContext,
    resource_environment: &ResourceEnvironment,
    spec_definitions: SpecDefinitions<'_>,
    compiled_definitions: Option<&[CCompositeResourceDefinition]>,
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
        parameters,
        arguments,
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
            ContractExpression::CFragment(CExpression::Value(value)),
        );
    }
    Ok(())
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
        .map(FunctionParameter::c_type)
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
        state: segment.state,
        base: substitute_c_fragment(&segment.base, substitutions)?,
        start: substitute_c_fragment(&segment.start, substitutions)?,
        end: substitute_c_fragment(&segment.end, substitutions)?,
        surface,
    })
}

fn materialize_composite_resource_cells(
    memory: CMemory,
    resource_clause: &ResourceClause,
    lowered: &CResourceFact,
    parameters: &[syntax::C0Parameter],
) -> CMemory {
    let naming_memory = memory.clone();
    materialize_composite_resource_cells_from_snapshot(
        memory,
        &naming_memory,
        resource_clause,
        lowered,
        parameters,
    )
}

fn materialize_composite_resource_cells_from_snapshot(
    mut memory: CMemory,
    naming_memory: &CMemory,
    resource_clause: &ResourceClause,
    lowered: &CResourceFact,
    parameters: &[syntax::C0Parameter],
) -> CMemory {
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
    // Only signed constant spans have the bounded cell-materialization rule.
    let Some((Bitvector32Term::Constant(start), Bitvector32Term::Constant(end))) =
        range.int32_bounds()
    else {
        return memory;
    };
    if end < start {
        return memory;
    }

    // `*p` is one complete struct: its cells take the layout's field
    // types, so a wide integer field reads back as itself. Pointer fields
    // keep the int32 words this projection uses everywhere: a pointer cell
    // must carry its load variable, which the load itself mints, whereas a
    // raw load term embedded in a pointer offset is not canonical.
    if let Some(layout) = crate::surface::lowering::object_segment_layout(parameters, segment)
        && *start == 0
    {
        for field in layout.fields().values() {
            memory = crate::surface::lowering::visit_struct_field_cells(
                field,
                range.base(),
                memory,
                |mut memory, pointer, element_type| {
                    let word_cells = if element_type.is_pointer() {
                        (0..element_type.byte_width())
                            .step_by(4)
                            .collect::<Vec<_>>()
                    } else {
                        vec![0]
                    };
                    for word in word_cells {
                        let pointer = pointer.offset_by_bytes(word);
                        if matches!(memory.load(&pointer), CExpressionOutcome::Value(_)) {
                            continue;
                        }
                        // A pointer field is held as its four-byte words.
                        let kind = if element_type.is_pointer() {
                            crate::kernel::LoadKind::Bits32
                        } else {
                            crate::surface::lowering::load_kind_of_element(element_type)
                        };
                        let load = crate::kernel::canonical_form_of_load(
                            crate::kernel::intern_c_memory(naming_memory.clone()),
                            pointer.clone(),
                            kind,
                        );
                        let value = if element_type.is_pointer() {
                            CValue::Int32(load)
                        } else {
                            crate::surface::lowering::symbolic_value_from_load(
                                &pointer,
                                element_type,
                                load,
                            )
                        };
                        memory = memory.materialize_named_cell(pointer, value);
                    }
                    memory
                },
            );
        }
        return memory;
    }
    let element_width = contract_segment_element_width(parameters, segment);
    let segment_type = contract_segment_element_type(parameters, segment);
    // The cells below as one run. Every element's value is its load in the
    // naming memory, typed as the element for a scalar and kept as the word
    // the load names for a pointer, so the run's element type is that word's
    // type. A value wider than the stride would overlap the next element,
    // which a run does not stand for.
    let run_type = if !segment_type.is_pointer() {
        segment_type
    } else if element_width == 1 {
        CType::UInt8
    } else {
        CType::Int32
    };
    if run_type.byte_width() <= element_width {
        match memory.with_named_cell_run(
            range.base().clone(),
            element_width,
            run_type,
            *start,
            *end,
            crate::kernel::intern_c_memory(naming_memory.clone()),
        ) {
            Ok(seeded) => return seeded,
            Err(unchanged) => memory = unchanged,
        }
    }
    for index in *start..*end {
        let pointer = offset_pointer_by_elements(
            range.base().clone(),
            Bitvector32Term::Constant(index),
            element_width,
        );
        if matches!(memory.load(&pointer), CExpressionOutcome::Value(_)) {
            continue;
        }
        // Preserve scalar pointee types, including substituted pointer values.
        // Pointer cells retain the word representation used for load origins,
        // and each cell is named as the read of its own kind.
        let element_type = contract_segment_element_type(parameters, segment);
        let kind = if !element_type.is_pointer() {
            crate::surface::lowering::load_kind_of_element(element_type)
        } else if element_width == 1 {
            crate::kernel::LoadKind::UInt8
        } else {
            crate::kernel::LoadKind::Bits32
        };
        let load = crate::kernel::canonical_form_of_load(
            crate::kernel::intern_c_memory(naming_memory.clone()),
            pointer.clone(),
            kind,
        );
        let value = match element_type {
            element_type if !element_type.is_pointer() => {
                crate::surface::lowering::symbolic_value_from_load(&pointer, element_type, load)
            }
            _ => match element_width {
                1 => CValue::UInt8(load),
                _ => CValue::Int32(load),
            },
        };
        memory = memory.materialize_named_cell(pointer, value);
    }
    memory
}

#[cfg(test)]
mod v11_resource_dependency_tests {
    use super::*;

    #[test]
    fn authority_body_read_projection_retires_only_its_owned_observations() {
        let source = r#"
authorized resource child_ref(obj: struct child*) {}
resource child_control(obj: struct child*) {
    owns allocation(obj, sizeof(struct child));
    owns *obj;
    owns authority(child_ref(obj));
    fact defined(obj->refs);
    fact defined(obj->payload);
    fact obj->refs == count(child_ref(obj));
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
    have obj->refs - 1 >= 1 by {
        apply(int32_above_one_predecessor_is_at_least_one(obj->refs)) using {
            1 < obj->refs;
        }
    }
    step();
    fold(child_control(obj));
    execute();
    simp();
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
        let verified = crate::surface::verify_c0_project(
            &project,
            &[("control.c", "struct child { int32 refs; int32 payload; }; void child_release(struct child* obj) { obj->refs = obj->refs - 1; }")],
        )
        .expect("the fixed helper's authority contract verifies");
        let execution = &verified[0].checked_execution;
        let path = &execution.paths()[0];
        let Proposition::CFunctionVerifies { outcome, .. } =
            implication_body(path.theorem().proposition())
        else {
            panic!("the helper has a checked C outcome")
        };
        let CFunctionOutcome::Return { state, .. } = outcome else {
            panic!("the helper returns")
        };
        let assumptions = path.assumptions();
        let head = state.resources().facts().iter().find(|fact| {
            matches!(fact.resource(), CResource::Composite { name, .. } if name == "child_control")
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
            .find_map(CResourceFact::memory_own_range)
            .unwrap();
        let view = CResourceFact::view_memory(range.clone());
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
        let fact = Proposition::CMemoryReadDefined {
            memory: observed.memory().clone(),
            pointer: range.base().offset_by_bytes(4),
            value_type: CType::Int32,
        };
        let no_temporary_views = DynamicViewDependencyIndex::new(&[], &[], assumptions);
        assert!(
            dynamic_body_fact_dependency(&fact, &observed, assumptions, &no_temporary_views,)
                .is_err(),
            "an observation alone does not grant a stable-view loan"
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
        viewed: CResourceFact,
    ) -> crate::kernel::LoanViewBinding {
        let ledger = crate::kernel::LoanLedger::new();
        let owner = ledger.fresh_participant().unwrap();
        let reader = ledger.fresh_participant().unwrap();
        let escrow = CResourceFact::own_token("v11_surface_support".into(), Vec::new());
        let opening = ledger.lend(owner, reader, support, escrow).unwrap();
        crate::kernel::LoanViewBinding {
            loan: opening.loan,
            scope: opening.scope,
            share: opening.root_share,
            support,
            viewed,
            hold: None,
        }
    }

    #[test]
    fn duplicate_equal_view_dependencies_fail_closed() {
        let support = CResourceFact::own_token("v11_surface_support".into(), Vec::new());
        let child = CResourceFact::view_token("v11_surface_child".into(), Vec::new());
        let resources = ResourceContext::new().unchecked_with_facts([
            support.clone(),
            child.clone(),
            child.clone(),
        ]);
        let support_occurrence = resources.owned_occurrences_for_fact(&support)[0];
        let occurrences = resources.occurrences_for_fact(&child);
        let binding = binding_for(support_occurrence, child.clone());
        let state = CState::new().with_resource_context_and_loan_dependencies(
            resources,
            [(occurrences[0], binding.clone())],
        );
        assert!(unique_borrowed_resource_dependency(&state, &child).is_err());

        let second = CResourceFact::view_token("v11_surface_other".into(), Vec::new());
        let mut different = binding;
        different.viewed = second;
        let resources = state.resources().clone();
        let state = state
            .with_resource_context_and_loan_dependencies(resources, [(occurrences[1], different)]);
        assert!(unique_borrowed_resource_dependency(&state, &child).is_err());
    }

    #[test]
    fn dynamic_current_fact_requires_live_view_binding_and_keeps_owner_scalar_distinct() {
        check_dynamic_current_fact_dependencies(false);
    }

    #[test]
    fn dynamic_definedness_requires_live_view_binding_and_keeps_owner_scalar_distinct() {
        check_dynamic_current_fact_dependencies(true);
    }

    fn check_dynamic_current_fact_dependencies(definedness: bool) {
        let pointer = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory =
            CMemory::new().store(pointer.clone(), CValue::Int32(Bitvector32Term::Constant(0)));
        let snapshot = crate::kernel::intern_c_memory_ref(&memory);
        let condition = ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::MemoryLoad(
                snapshot,
                Box::new(pointer.clone()),
                crate::kernel::LoadKind::Bits32,
            )),
            Box::new(Bitvector32Term::Constant(0)),
        );
        let proposition = if definedness {
            Proposition::CMemoryReadDefined {
                memory: memory.clone(),
                pointer: pointer.clone(),
                value_type: crate::kernel::CType::Int32,
            }
        } else {
            Proposition::ConditionIs(condition, true)
        };
        let range = CMemoryRange::new(
            pointer,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        );
        let own = CResourceFact::own_memory(range.clone());
        let view = CResourceFact::view_memory(range.clone());
        let support_resources = ResourceContext::new().unchecked_with_fact(own.clone());
        let support = support_resources.owned_occurrences_for_fact(&own)[0];
        let ledger = crate::kernel::LoanLedger::new();
        let lender = ledger.fresh_participant().unwrap();
        let reader = ledger.fresh_participant().unwrap();
        let opening = ledger.lend(lender, lender, support, own.clone()).unwrap();
        let ledger = ledger.apply(&opening.transition).unwrap();
        let binding = crate::kernel::LoanViewBinding {
            loan: opening.loan,
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
        let bound_state = CState::new()
            .with_memory(memory.clone())
            .with_resource_context_and_loan_dependencies(
                bound_resources,
                [(view_occurrence, binding)],
            )
            .with_loan_ledger(Some(ledger.clone()))
            .with_loan_participant(Some(lender));
        let no_temporary_views = DynamicViewDependencyIndex::new(&[], &[], &PureFactContext::new());
        let dependency = dynamic_body_fact_dependency(
            &proposition,
            &bound_state,
            &PureFactContext::new(),
            &no_temporary_views,
        )
        .unwrap();
        assert!(
            dependency.is_some(),
            "current viewed memory must retain its loan"
        );
        assert!(
            dynamic_body_fact_dependency(
                &proposition,
                &bound_state.clone().with_loan_participant(Some(reader)),
                &PureFactContext::new(),
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
                &bound_state.clone().with_loan_ledger(Some(ended.clone())),
                &PureFactContext::new(),
                &no_temporary_views,
            )
            .is_err(),
            "an ended scope cannot validate the binding"
        );
        assert!(
            unique_borrowed_resource_dependency(&bound_state.with_loan_ledger(Some(ended)), &view,)
                .is_err(),
            "a historical-only operation must still reject an ended binding"
        );

        let unbound_state = CState::new().with_memory(memory).with_resource_context(
            ResourceContext::new().unchecked_with_facts([own.clone(), view]),
        );
        assert!(
            dynamic_body_fact_dependency(
                &proposition,
                &unbound_state,
                &PureFactContext::new(),
                &no_temporary_views,
            )
            .is_err()
        );

        assert!(
            dynamic_body_fact_dependency(
                &proposition,
                &CState::new().with_memory(unbound_state.memory().clone()),
                &PureFactContext::new(),
                &no_temporary_views,
            )
            .is_err(),
            "a pure definedness fact cannot supply access authority"
        );

        let owner_state = CState::new()
            .with_memory(unbound_state.memory().clone())
            .with_resource_context(ResourceContext::new().unchecked_with_fact(own));
        assert!(
            dynamic_body_fact_dependency(
                &proposition,
                &owner_state,
                &PureFactContext::new(),
                &no_temporary_views,
            )
            .unwrap()
            .is_none()
        );

        let opaque = Proposition::Equal(
            Term::Bitvector32(Bitvector32Term::ClickFunctionApplication {
                name: "opaque".into(),
                arguments: Vec::new(),
            }),
            Term::Bitvector32(Bitvector32Term::Constant(0)),
        );
        assert!(
            dynamic_body_fact_dependency(
                &opaque,
                &owner_state,
                &PureFactContext::new(),
                &no_temporary_views,
            )
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
    fn wide_composite_materialization_keeps_the_snapshot_without_enumerating_cells() {
        let base = Pointer::symbolic(Variable(985_600));
        let wide = CMemoryRange::new_wide(
            base.clone(),
            Bitvector32Term::UInt64Constant(0),
            Bitvector32Term::UInt64Constant(1 << 33),
            4,
        );
        let literal = || ContractExpression::IntegerLiteral("0".into());
        let segment = ContractSegment {
            state: ContractSegmentState::Current,
            base: CExpression::Value(CValue::pointer(base.clone())),
            start: crate::kernel::c_uint64_literal(0),
            end: crate::kernel::c_uint64_literal(1 << 33),
            surface: ContractSegmentSurface::Range {
                base: literal(),
                start: literal(),
                end: literal(),
            },
        };
        let memory = CMemory::new();
        let result = materialize_composite_resource_cells_from_snapshot(
            memory.clone(),
            &memory,
            &ResourceClause::OwnMemory(segment),
            &CResourceFact::own_memory(wide),
            &[],
        );
        assert_eq!(result.diagnostic_identity(), memory.diagnostic_identity());
        // The range kind also matters when the shared term representation has
        // legacy constant nodes: they must not trigger signed enumeration.
        let tagged = CMemoryRange::new_wide(base, 0u32.into(), 8u32.into(), 4);
        let clause = ResourceClause::OwnMemory(ContractSegment {
            state: ContractSegmentState::Current,
            base: crate::kernel::c_int32_literal(0),
            start: crate::kernel::c_uint64_literal(0),
            end: crate::kernel::c_uint64_literal(8),
            surface: ContractSegmentSurface::Range {
                base: literal(),
                start: literal(),
                end: literal(),
            },
        });
        let result = materialize_composite_resource_cells_from_snapshot(
            memory.clone(),
            &memory,
            &clause,
            &CResourceFact::own_memory(tagged),
            &[],
        );
        assert_eq!(result.diagnostic_identity(), memory.diagnostic_identity());
    }
}
