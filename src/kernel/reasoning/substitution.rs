use super::*;
use crate::kernel::CompareRelation;
#[cfg(test)]
use crate::kernel::binary_node;
use crate::kernel::unary_term;
use crate::kernel::{MachineCastSpelling, cast_term};
use crate::kernel::{bits32_constant, int64_constant, native_constant, uint64_constant};
use num_traits::ToPrimitive;

/// One variable substitution, bitvector or pointer, as the structural walks
/// below see it. The walks over statements, states, resources, propositions
/// and their parts are shared; each method is a leaf where the two
/// substitutions differ, and keeps that substitution's own rule.
trait VariableSubstitution {
    /// Whether condition-evaluation and resource-composition facts are
    /// rewritten. Pointer substitution rewrites them; bitvector substitution
    /// has always left them as they are.
    const SUBSTITUTES_CONDITION_EVIDENCE: bool;

    fn from(&self) -> Variable;
    fn bitvector(&self, term: &MachineTerm) -> MachineTerm;
    fn integer(&self, term: &IntegerTerm) -> IntegerTerm;
    fn pointer(&self, pointer: &Address) -> Address;
    /// The address of a local's storage slot.
    fn local_slot(&self, pointer: &Address) -> Address;
    fn term(&self, term: &Term) -> Term;
    fn condition(&self, condition: &ConditionTerm) -> ConditionTerm;
    fn condition_root(&self, condition: &KernelTerm) -> Option<KernelTerm>;
    fn stored_condition(&self, condition: &StoredConditionTerm) -> StoredConditionTerm {
        if let Some(root) = condition.root().and_then(|root| self.condition_root(root)) {
            return StoredConditionTerm::from_root(root).expect("logical condition substitution");
        }
        self.condition(condition.native_compat()).into()
    }
    fn program_value(&self, value: &ProgramValue) -> ProgramValue;
    fn expression_value(&self, value: &ExecutionValue) -> ExecutionValue;
    /// Native program-value storage applies its existing typed literal
    /// constructor after substitution. Keep that carrier without exporting a
    /// common expression; only an atomic literal crosses this boundary.
    fn stored_program_value(&self, value: &ExecutionValue) -> ExecutionValue {
        let rewritten = self.expression_value(value);
        if let Some(root) = rewritten.shared()
            && let KernelTermNode::MachineLiteral(literal) = root.node()
            && let Some(format) = MachineIntegerType::from_program_type(rewritten.program_type())
        {
            let raw = literal.value_at(format);
            let normalized = self.program_value(&raw);
            if normalized != raw {
                return KernelTermImport::default()
                    .argument(&PureFunctionArgument::Value(normalized))
                    .into();
            }
        }
        rewritten
    }

    fn program_expression(&self, expression: &ProgramExpression) -> ProgramExpression;
    fn memory(&self, memory: &SymbolicMemory) -> SymbolicMemory;
    fn algebraic_term(&self, term: &AlgebraicTerm) -> AlgebraicTerm;
    fn spec_expression(&self, expression: &SpecExpression) -> SpecExpression;
    fn spec_integer(&self, expression: &SpecIntegerExpression) -> SpecIntegerExpression;
    fn spec_proposition(&self, proposition: &SpecProposition) -> SpecProposition;
    /// A quantifier's binder and body, renamed away from the replacement.
    fn quantifier_body(
        &self,
        binder: Variable,
        sort: &Sort,
        body: &Proposition,
    ) -> (Variable, Proposition);
    /// Held across one whole proposition.
    fn proposition_scope(&self) -> Option<SubstitutedMemoryScope>;
}

struct BitvectorSubstitution<'a> {
    from: Variable,
    to: &'a MachineTerm,
}

impl VariableSubstitution for BitvectorSubstitution<'_> {
    const SUBSTITUTES_CONDITION_EVIDENCE: bool = false;

    fn from(&self) -> Variable {
        self.from
    }
    fn bitvector(&self, term: &MachineTerm) -> MachineTerm {
        substitute_bitvector_variable(term, self.from, self.to)
    }
    fn integer(&self, term: &IntegerTerm) -> IntegerTerm {
        substitute_bitvector_variable_in_integer(term, self.from, self.to)
    }
    fn pointer(&self, pointer: &Address) -> Address {
        substitute_bitvector_variable_in_pointer(pointer, self.from, self.to)
    }
    fn local_slot(&self, pointer: &Address) -> Address {
        pointer.clone()
    }
    fn term(&self, term: &Term) -> Term {
        substitute_bitvector_variable_in_term(term, self.from, self.to)
    }
    fn condition(&self, condition: &ConditionTerm) -> ConditionTerm {
        substitute_bitvector_variable_in_condition(condition, self.from, self.to)
    }
    fn condition_root(&self, condition: &KernelTerm) -> Option<KernelTerm> {
        substitute_bitvector_variable_in_common_condition(condition, self.from, self.to)
    }
    fn program_value(&self, value: &ProgramValue) -> ProgramValue {
        substitute_bitvector_variable_in_program_value(value, self.from, self.to)
    }
    fn expression_value(&self, value: &ExecutionValue) -> ExecutionValue {
        if let Some(root) = value.shared() {
            let source = MachineTerm::Variable(self.from);
            if let Some(rewritten) =
                crate::kernel::proof::term_rewrite::TermRewrite::for_bits(&source, self.to)
                    .shared_machine_operand(root)
            {
                return rewritten.into();
            }
        }
        self.program_value(&value.native()).into()
    }
    fn program_expression(&self, expression: &ProgramExpression) -> ProgramExpression {
        substitute_bitvector_variable_in_program_expression(expression, self.from, self.to)
    }
    fn memory(&self, memory: &SymbolicMemory) -> SymbolicMemory {
        substitute_bitvector_variable_in_memory(memory, self.from, self.to)
    }
    fn algebraic_term(&self, term: &AlgebraicTerm) -> AlgebraicTerm {
        substitute_bitvector_variable_in_algebraic_term(term, self.from, self.to)
    }
    fn spec_expression(&self, expression: &SpecExpression) -> SpecExpression {
        substitute_bitvector_variable_in_spec_expression(expression, self.from, self.to)
    }
    fn spec_integer(&self, expression: &SpecIntegerExpression) -> SpecIntegerExpression {
        substitute_bitvector_variable_in_spec_integer(expression, self.from, self.to)
    }
    fn spec_proposition(&self, proposition: &SpecProposition) -> SpecProposition {
        substitute_bitvector_variable_in_spec_proposition(proposition, self.from, self.to)
    }
    fn quantifier_body(
        &self,
        binder: Variable,
        _sort: &Sort,
        body: &Proposition,
    ) -> (Variable, Proposition) {
        capture_avoiding_quantifier_body(binder, body, self.from, self.to)
    }
    fn proposition_scope(&self) -> Option<SubstitutedMemoryScope> {
        // Hold the state memo open across the whole proposition, so two
        // sibling load terms over one state rewrite it once between them.
        Some(SubstitutedMemoryScope::enter(self.from, self.to))
    }
}

struct PointerSubstitution<'a> {
    from: Variable,
    to: &'a Address,
}

impl VariableSubstitution for PointerSubstitution<'_> {
    const SUBSTITUTES_CONDITION_EVIDENCE: bool = true;

    fn from(&self) -> Variable {
        self.from
    }
    fn bitvector(&self, term: &MachineTerm) -> MachineTerm {
        term.clone()
    }
    fn integer(&self, term: &IntegerTerm) -> IntegerTerm {
        term.clone()
    }
    fn pointer(&self, pointer: &Address) -> Address {
        substitute_pointer_variable_in_pointer(pointer, self.from, self.to)
    }
    fn local_slot(&self, pointer: &Address) -> Address {
        self.pointer(pointer)
    }
    fn term(&self, term: &Term) -> Term {
        substitute_pointer_variable_in_term(term, self.from, self.to)
    }
    fn condition(&self, condition: &ConditionTerm) -> ConditionTerm {
        substitute_pointer_variable_in_condition(condition, self.from, self.to)
    }
    fn condition_root(&self, condition: &KernelTerm) -> Option<KernelTerm> {
        substitute_pointer_variable_in_common_condition(condition, self.from, self.to)
    }
    fn program_value(&self, value: &ProgramValue) -> ProgramValue {
        substitute_pointer_variable_in_program_value(value, self.from, self.to)
    }
    fn expression_value(&self, value: &ExecutionValue) -> ExecutionValue {
        if let Some(root) = value.shared()
            && let Some(rewritten) =
                crate::kernel::proof::term_rewrite::TermRewrite::for_pointer_variable(
                    self.from, self.to,
                )
                .shared_machine_operand(root)
        {
            return rewritten.into();
        }
        self.program_value(&value.native()).into()
    }
    fn program_expression(&self, expression: &ProgramExpression) -> ProgramExpression {
        substitute_pointer_variable_in_program_expression(expression, self.from, self.to)
    }
    fn memory(&self, memory: &SymbolicMemory) -> SymbolicMemory {
        substitute_pointer_variable_in_memory(memory, self.from, self.to)
    }
    fn algebraic_term(&self, term: &AlgebraicTerm) -> AlgebraicTerm {
        substitute_pointer_variable_in_algebraic_term(term, self.from, self.to)
    }
    fn spec_expression(&self, expression: &SpecExpression) -> SpecExpression {
        substitute_pointer_variable_in_spec_expression(expression, self.from, self.to)
    }
    fn spec_integer(&self, expression: &SpecIntegerExpression) -> SpecIntegerExpression {
        substitute_pointer_variable_in_spec_integer(expression, self.from, self.to)
    }
    fn spec_proposition(&self, proposition: &SpecProposition) -> SpecProposition {
        substitute_pointer_variable_in_spec_proposition(proposition, self.from, self.to)
    }
    fn quantifier_body(
        &self,
        binder: Variable,
        sort: &Sort,
        body: &Proposition,
    ) -> (Variable, Proposition) {
        let (body, binder) =
            pointer_capture_avoiding_quantifier_body(binder, sort, body, self.from, self.to);
        (binder, body)
    }
    fn proposition_scope(&self) -> Option<SubstitutedMemoryScope> {
        None
    }
}

pub(crate) fn substitute_bitvector_variable_in_proposition(
    proposition: &Proposition,
    from: Variable,
    to: &MachineTerm,
) -> Proposition {
    walk_proposition(proposition, &BitvectorSubstitution { from, to })
}

fn substitute_bitvector_variable_in_algebraic_value(
    value: &AlgebraicValue,
    from: Variable,
    to: &MachineTerm,
) -> AlgebraicValue {
    walk_algebraic_value(value, &BitvectorSubstitution { from, to })
}

fn substitute_bitvector_variable_in_pure_function_argument(
    argument: &PureFunctionArgument,
    from: Variable,
    to: &MachineTerm,
) -> PureFunctionArgument {
    walk_pure_function_argument(argument, &BitvectorSubstitution { from, to })
}

fn substitute_bitvector_variable_in_sequence(
    sequence: &SequenceTerm,
    from: Variable,
    to: &MachineTerm,
) -> SequenceTerm {
    walk_sequence(sequence, &BitvectorSubstitution { from, to })
}

#[cfg(test)]
pub(in crate::kernel) fn substitute_bitvector_variable_in_execution_statement(
    statement: &ProgramStatement,
    from: Variable,
    to: &MachineTerm,
) -> ProgramStatement {
    walk_execution_statement(statement, &BitvectorSubstitution { from, to })
}

fn substitute_bitvector_variable_in_execution_state(
    state: &ExecutionState,
    from: Variable,
    to: &MachineTerm,
) -> ExecutionState {
    walk_execution_state(state, &BitvectorSubstitution { from, to })
}

#[cfg(test)]
pub(in crate::kernel) fn substitute_bitvector_variable_in_resource(
    resource: &Resource,
    from: Variable,
    to: &MachineTerm,
) -> Resource {
    walk_resource(resource, &BitvectorSubstitution { from, to })
}

#[cfg(test)]
pub(in crate::kernel) fn substitute_bitvector_variable_in_program_function(
    function: &ProgramFunction,
    from: Variable,
    to: &MachineTerm,
) -> ProgramFunction {
    walk_program_function(function, &BitvectorSubstitution { from, to })
}

#[cfg(test)]
pub(in crate::kernel) fn substitute_bitvector_variable_in_resource_spec(
    resource: &ResourceSpec,
    from: Variable,
    to: &MachineTerm,
) -> ResourceSpec {
    walk_resource_spec(resource, &BitvectorSubstitution { from, to })
}

pub(crate) fn substitute_pointer_variable_in_proposition(
    proposition: &Proposition,
    from: Variable,
    to: &Address,
) -> Proposition {
    walk_proposition(proposition, &PointerSubstitution { from, to })
}

/// Bind a pointer witness without discarding its subobject provenance.
pub(crate) fn substitute_pointer_value_in_proposition(
    proposition: &Proposition,
    from: Variable,
    to: &Pointer,
) -> Result<Proposition, String> {
    let c = std::collections::BTreeMap::from([(
        from,
        crate::kernel::proof::term_rewrite::TypedProgramValueReplacement::Pointer(to.clone()),
    )]);
    let integers = Default::default();
    let algebraic = Default::default();
    let mut rewrite = crate::kernel::proof::term_rewrite::TermRewrite::for_typed_variables(
        &c, &integers, &algebraic,
    );
    let result = rewrite.substitute_proposition(proposition);
    match rewrite.refusal() {
        None => Ok(result),
        Some(reason) => Err(format!("pointer witness substitution refused: {reason:?}")),
    }
}

fn substitute_pointer_variable_in_algebraic_value(
    value: &AlgebraicValue,
    from: Variable,
    to: &Address,
) -> AlgebraicValue {
    walk_algebraic_value(value, &PointerSubstitution { from, to })
}

fn substitute_pointer_variable_in_pure_function_argument(
    argument: &PureFunctionArgument,
    from: Variable,
    to: &Address,
) -> PureFunctionArgument {
    walk_pure_function_argument(argument, &PointerSubstitution { from, to })
}

fn substitute_pointer_variable_in_sequence(
    sequence: &SequenceTerm,
    from: Variable,
    to: &Address,
) -> SequenceTerm {
    walk_sequence(sequence, &PointerSubstitution { from, to })
}

#[cfg(test)]
fn substitute_pointer_variable_in_execution_statement(
    statement: &ProgramStatement,
    from: Variable,
    to: &Address,
) -> ProgramStatement {
    walk_execution_statement(statement, &PointerSubstitution { from, to })
}

fn substitute_pointer_variable_in_execution_state(
    state: &ExecutionState,
    from: Variable,
    to: &Address,
) -> ExecutionState {
    walk_execution_state(state, &PointerSubstitution { from, to })
}

#[cfg(test)]
fn substitute_pointer_variable_in_resource(
    resource: &Resource,
    from: Variable,
    to: &Address,
) -> Resource {
    walk_resource(resource, &PointerSubstitution { from, to })
}

#[cfg(test)]
fn substitute_pointer_variable_in_program_function(
    function: &ProgramFunction,
    from: Variable,
    to: &Address,
) -> ProgramFunction {
    walk_program_function(function, &PointerSubstitution { from, to })
}

fn walk_algebraic_value<'a, S: VariableSubstitution + ?Sized>(
    value: impl Into<ResourceFieldValue<'a>>,
    s: &S,
) -> AlgebraicValue {
    match value.into() {
        ResourceFieldValue::Program(value) => AlgebraicValue::Program(s.program_value(value)),
        ResourceFieldValue::Integer(value) => AlgebraicValue::Integer(s.integer(value)),
        ResourceFieldValue::Algebraic(value) => AlgebraicValue::Algebraic(s.algebraic_term(value)),
    }
}

fn walk_program_expression_outcome<S: VariableSubstitution + ?Sized>(
    outcome: &ExpressionOutcome<StoredProgramValue>,
    s: &S,
) -> ExpressionOutcome<StoredProgramValue> {
    match outcome {
        ExpressionOutcome::Value(value) => ExpressionOutcome::Value(StoredProgramValue::from(
            s.stored_program_value(value.value()),
        )),
        ExpressionOutcome::UndefinedBehavior(kind) => {
            ExpressionOutcome::UndefinedBehavior(kind.clone())
        }
        ExpressionOutcome::RuntimeError(kind) => ExpressionOutcome::RuntimeError(kind.clone()),
    }
}

fn walk_program_function<S: VariableSubstitution + ?Sized>(
    function: &ProgramFunction,
    s: &S,
) -> ProgramFunction {
    let mut interface = function.contract_interface().clone();
    interface.resource_requires = function
        .resource_requires()
        .iter()
        .map(|resource| walk_resource_spec(resource, s))
        .collect();
    interface.resource_ensures = function
        .resource_ensures()
        .iter()
        .map(|resource| walk_resource_spec(resource, s))
        .collect();
    interface.resource_constructors = function
        .resource_constructors()
        .iter()
        .map(|resource| walk_resource_spec(resource, s))
        .collect();
    interface.contract_requires = function
        .contract_requires()
        .iter()
        .map(|proposition| s.spec_proposition(proposition))
        .collect();
    interface.contract_ensures = function
        .contract_ensures()
        .iter()
        .map(|proposition| s.spec_proposition(proposition))
        .collect();
    interface.exceptional_ensures = function
        .exceptional_ensures()
        .iter()
        .map(|proposition| s.spec_proposition(proposition))
        .collect();
    interface.contract_mutable = function
        .contract_mutable()
        .iter()
        .map(|segment| walk_memory_segment(segment, s))
        .collect();
    // The declared measure is read at states like a `requires` is, so it is
    // rewritten with them; leaving it behind would make a substituted
    // interface rank the recursion by the pre-substitution names.
    interface.recursion_measure = interface
        .recursion_measure
        .iter()
        .map(|measure| walk_ranking_component(measure, s))
        .collect();
    interface.composite_resource_definitions = function
        .composite_resource_definitions()
        .iter()
        .map(|definition| CompositeResourceDefinition {
            resource_parameters: definition
                .resource_parameters
                .iter()
                .map(|spec| walk_resource_spec(spec, s))
                .collect(),
            instance_schema: definition.instance_schema.clone(),
            thread_confined: definition.thread_confined,
            contains_mutex_authority: definition.contains_mutex_authority,
            authorized: definition.authorized,
            sealed: definition.sealed,
            reaches_population: definition.reaches_population,
            owned_footprint_unnamed: definition.owned_footprint_unnamed,
            fact_source_indices: definition.fact_source_indices.clone(),
            fact_source_spellings: definition.fact_source_spellings.clone(),
            name: definition.name.clone(),
            parameters: definition.parameters.clone(),
            witnesses: definition.witnesses.clone(),
            condition: definition
                .condition
                .as_ref()
                .map(|condition| s.spec_proposition(condition)),
            matched: definition.matched.as_ref().map(|body| ResourceMatchBody {
                field_index: body.field_index,
                algebraic_type: body.algebraic_type.clone(),
                arms: body
                    .arms
                    .iter()
                    .map(|arm| ResourceMatchArm {
                        children: arm
                            .children
                            .iter()
                            .map(|child| ResourceChildSpec {
                                name: child.name.clone(),
                                resource: child.resource.clone(),
                                binding: child.binding,
                                field_bindings: child.field_bindings.clone(),
                                arguments: child
                                    .arguments
                                    .iter()
                                    .map(|argument| s.spec_expression(argument))
                                    .collect(),
                            })
                            .collect(),
                        variant: arm.variant.clone(),
                        bindings: arm.bindings.clone(),
                        binding_types: arm.binding_types.clone(),
                        binding_variables: arm.binding_variables.clone(),
                        contains: arm
                            .contains
                            .iter()
                            .map(|resource| walk_resource_spec(resource, s))
                            .collect(),
                        facts: arm
                            .facts
                            .iter()
                            .map(|fact| s.spec_proposition(fact))
                            .collect(),
                    })
                    .collect(),
            }),
            recursive: definition.recursive,
            matched_recursive: definition.matched_recursive,
            facts_read_counts: definition.facts_read_counts,
            facts_claim_liveness: definition.facts_claim_liveness,
            contains: definition
                .contains
                .iter()
                .map(|resource| walk_resource_spec(resource, s))
                .collect(),
            children: definition
                .children
                .iter()
                .map(|child| ResourceChildSpec {
                    arguments: child
                        .arguments
                        .iter()
                        .map(|argument| s.spec_expression(argument))
                        .collect(),
                    ..child.clone()
                })
                .collect(),
            facts: definition
                .facts
                .iter()
                .map(|fact| s.spec_proposition(fact))
                .collect(),
        })
        .collect();
    interface.predicate_unfoldings = function
        .predicate_unfoldings()
        .iter()
        .map(|unfolding| PredicateUnfolding {
            requirement_source: unfolding.requirement_source.clone(),
            predicate: s.spec_proposition(&unfolding.predicate),
            body: s.spec_proposition(&unfolding.body),
        })
        .collect();
    interface.resource_transfer_rule = std::sync::Arc::new(
        crate::kernel::functions::SummaryResourceTransferRule::compile(&interface),
    );
    ProgramFunction {
        program_entry: function.program_entry,
        name: function.name.clone(),
        inline_body: function.inline_body,
        body: walk_execution_statement(function.body(), s),
        source_body: walk_execution_statement(function.source_body(), s),
        control_targets: std::sync::Arc::new(
            function
                .control_targets
                .iter()
                .map(|(identity, target)| {
                    (
                        *identity,
                        ControlTarget {
                            statement_index: target.statement_index,
                            remaining: std::sync::Arc::new(walk_execution_statement(
                                &target.remaining,
                                s,
                            )),
                        },
                    )
                })
                .collect(),
        ),
        contract_interface: std::sync::Arc::new(interface),
        global_variables: function.global_variables.clone(),
        global_arrays: function.global_arrays.clone(),
        static_variables: function.static_variables.clone(),
        static_storage: function.static_storage.clone(),
        string_literals: function.string_literals.clone(),
        address_taken_locals: Default::default(),
        loop_source_index: Default::default(),
        natural_loop_source: function.natural_loop_source,
    }
}

fn walk_program_function_outcome<S: VariableSubstitution + ?Sized>(
    outcome: &FunctionOutcome,
    s: &S,
) -> FunctionOutcome {
    match outcome {
        FunctionOutcome::Return { value, state } => FunctionOutcome::Return {
            value: s.expression_value(value).into(),
            state: Box::new(walk_execution_state(state, s)),
        },
        FunctionOutcome::Throw { value, state } => FunctionOutcome::Throw {
            value: s.expression_value(value).into(),
            state: Box::new(walk_execution_state(state, s)),
        },
        FunctionOutcome::VerificationDiverges => FunctionOutcome::VerificationDiverges,
        FunctionOutcome::UndefinedBehavior(kind) => {
            FunctionOutcome::UndefinedBehavior(kind.clone())
        }
        FunctionOutcome::RuntimeError(kind) => FunctionOutcome::RuntimeError(kind.clone()),
    }
}

fn walk_program_function_specification<S: VariableSubstitution + ?Sized>(
    specification: &FunctionSpecification,
    s: &S,
) -> FunctionSpecification {
    FunctionSpecification {
        state: walk_execution_state(specification.state(), s),
        arguments: specification
            .arguments()
            .iter()
            .map(|argument| s.program_expression(argument))
            .collect(),
        requires: specification
            .requires()
            .iter()
            .map(|requirement| walk_proposition(requirement, s))
            .collect(),
        outcome: walk_program_function_outcome(specification.outcome(), s),
    }
}

fn walk_memory_segment<S: VariableSubstitution + ?Sized>(
    segment: &MemorySegment,
    s: &S,
) -> MemorySegment {
    MemorySegment {
        base: s.program_expression(&segment.base),
        start: s.program_expression(&segment.start),
        end: s.program_expression(&segment.end),
        element_width: segment.element_width,
        uninitialized: segment.uninitialized,
        value_runs: segment.value_runs.clone(),
        guard: segment
            .guard
            .as_ref()
            .map(|guard| s.spec_proposition(guard)),
    }
}

fn walk_ranking_component<S: VariableSubstitution + ?Sized>(
    measure: &RankingComponent,
    s: &S,
) -> RankingComponent {
    match measure {
        RankingComponent::ProgramExpression(expression) => {
            RankingComponent::ProgramExpression(s.program_expression(expression))
        }
        RankingComponent::Pure { source, expression } => RankingComponent::Pure {
            source: source.clone(),
            expression: s.spec_expression(expression),
        },
        RankingComponent::PureInteger { source, expression } => RankingComponent::PureInteger {
            source: source.clone(),
            expression: s.spec_integer(expression),
        },
    }
}

fn walk_resource<S: VariableSubstitution + ?Sized>(resource: &Resource, s: &S) -> Resource {
    match resource {
        Resource::Star(pair) => {
            Resource::star(walk_resource(&pair.0, s), walk_resource(&pair.1, s))
        }
        Resource::Footprint(_) | Resource::Parameter(_) | Resource::Emp => resource.clone(),
        Resource::PopulationAuthority(description) => Resource::PopulationAuthority(
            description.map_values(|value| walk_algebraic_value(value, s)),
        ),
        Resource::Publication(right) => Resource::Publication(PublicationRight {
            side: right.side,
            payload: right.payload.map_values(|v| walk_algebraic_value(v, s)),
            flag: s.pointer(&right.flag),
            observed: right
                .observed
                .as_ref()
                .map(|value| StoredProgramValue::from(s.stored_program_value(value.value()))),
        }),
        Resource::MutexUse(identity) => Resource::MutexUse(MutexUseIdentity {
            protected: identity.protected.as_ref().map(|p| {
                if identity.binding.is_none() {
                    p.map_values(|v| walk_algebraic_value(v, s))
                } else {
                    p.clone()
                }
            }),
            binding: identity.binding,
            initialization: identity.initialization,
            mutex: if identity.binding.is_none() {
                s.pointer(&identity.mutex)
            } else {
                identity.mutex.clone()
            },
        }),
        Resource::ConditionalMutexGuard(carrier) => {
            let mut mapped = (**carrier).clone();
            mapped.held = s.condition(carrier.condition()).into();
            Resource::ConditionalMutexGuard(std::sync::Arc::new(mapped))
        }
        Resource::MutexGuard(identity) => Resource::MutexGuard(MutexIdentity {
            epoch: identity.epoch,
            mutex: if identity.epoch.is_none() {
                s.pointer(&identity.mutex)
            } else {
                identity.mutex.clone()
            },
        }),
        Resource::MutexLive(identity) => Resource::MutexLive(MutexIdentity {
            epoch: identity.epoch,
            mutex: if identity.epoch.is_none() {
                s.pointer(&identity.mutex)
            } else {
                identity.mutex.clone()
            },
        }),
        Resource::Instance(instance) => {
            let mut result = instance.clone();
            result.arguments = instance
                .arguments
                .iter()
                .map(|value| walk_algebraic_value(value, s))
                .collect();
            result.fields =
                ResourceFieldValues::from_stored((0..instance.fields.len()).map(|index| {
                    match instance.fields.stored_field(index).expect("field index") {
                        StoredResourceField::Input(value) => {
                            StoredResourceField::Input(walk_algebraic_value(&value, s))
                        }
                        StoredResourceField::Program(value) => {
                            StoredResourceField::from_program(s.stored_program_value(value.value()))
                        }
                        StoredResourceField::Integer(root) => {
                            StoredResourceField::from_minted(AlgebraicValue::Integer(
                                s.integer(root.integer_native_compat().expect("Integer field")),
                            ))
                        }
                        StoredResourceField::Algebraic(root) => {
                            let ProgramValue::Parameter(value) =
                                root.algebraic_native_value().expect("algebraic field")
                            else {
                                unreachable!()
                            };
                            StoredResourceField::from_minted(AlgebraicValue::Algebraic(
                                s.algebraic_term(value),
                            ))
                        }
                    }
                }));
            result.resource_arguments = crate::kernel::ResourceReference::map_captured_values(
                instance.resource_arguments(),
                |value| walk_algebraic_value(value, s),
            );
            Resource::Instance(result)
        }
        Resource::Memory(range) => Resource::Memory(walk_memory_range(range, s)),
        Resource::Iterated(iterated) => Resource::iterated(
            iterated.map_terms(|term| s.bitvector(term), |pointer| s.pointer(pointer)),
        ),
        Resource::Composite { name, arguments } => Resource::Composite {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| walk_algebraic_value(argument, s))
                .collect(),
        },
        Resource::Token { name, arguments } => Resource::Token {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| walk_algebraic_value(argument, s))
                .collect(),
        },
    }
}

fn walk_execution_state<S: VariableSubstitution + ?Sized>(
    state: &ExecutionState,
    s: &S,
) -> ExecutionState {
    let bindings = state
        .locals
        .bindings
        .iter()
        .map(|(name, binding)| {
            let binding = match binding {
                LocalBinding::Object {
                    storage_declared,
                    value,
                    program_type,
                    slot,
                    volatile,
                    pointee_volatile,
                    constant,
                    pointee_constant,
                } => LocalBinding::Object {
                    storage_declared: *storage_declared,
                    value: s.expression_value(value).into(),
                    program_type: *program_type,
                    slot: s.local_slot(slot),
                    volatile: *volatile,
                    pointee_volatile: *pointee_volatile,
                    constant: *constant,
                    pointee_constant: *pointee_constant,
                },
                LocalBinding::UninitializedObject {
                    program_type,
                    slot,
                    volatile,
                    pointee_volatile,
                    constant,
                    pointee_constant,
                } => LocalBinding::UninitializedObject {
                    program_type: *program_type,
                    slot: s.local_slot(slot),
                    volatile: *volatile,
                    pointee_volatile: *pointee_volatile,
                    constant: *constant,
                    pointee_constant: *pointee_constant,
                },
                LocalBinding::GlobalObject {
                    program_type,
                    slot,
                    volatile,
                    pointee_volatile,
                    constant,
                    pointee_constant,
                } => LocalBinding::GlobalObject {
                    program_type: *program_type,
                    slot: s.local_slot(slot),
                    volatile: *volatile,
                    pointee_volatile: *pointee_volatile,
                    constant: *constant,
                    pointee_constant: *pointee_constant,
                },
                LocalBinding::ArrayObject {
                    element_type,
                    length,
                    slot,
                    constant,
                } => LocalBinding::ArrayObject {
                    element_type: *element_type,
                    length: *length,
                    slot: s.local_slot(slot),
                    constant: *constant,
                },
                LocalBinding::AggregateObject {
                    layout,
                    slot,
                    constant,
                } => LocalBinding::AggregateObject {
                    layout: layout.clone(),
                    slot: s.local_slot(slot),
                    constant: *constant,
                },
            };
            (name.clone(), binding)
        })
        .collect::<crate::persistent::PersistentMap<_, _>>();
    let slots = state
        .locals
        .slots
        .iter()
        .map(|(pointer, name)| (s.local_slot(pointer), name.clone()))
        .collect();
    ExecutionState {
        literal_values: state.literal_values.clone(),
        aggregate_step_objects: state
            .aggregate_step_objects
            .iter()
            .map(|(step, pointer)| (*step, s.pointer(pointer)))
            .collect(),
        step_results: state.step_results.as_ref().map(|results| {
            std::sync::Arc::new(
                results
                    .iter()
                    .map(|(call, value)| (*call, s.expression_value(value).into()))
                    .collect(),
            )
        }),
        locals: LocalEnvironment::from_parts(bindings, slots),
        aggregate_destination: state.aggregate_destination.as_ref().map(|destination| {
            std::sync::Arc::new(AggregateDestination {
                pointer: s.pointer(&destination.pointer),
                layout: destination.layout.clone(),
            })
        }),
        memory: s.memory(&state.memory),
        // Renaming values leaves the state where its path put it.
        point: state.point.clone(),
        resource_bindings: state.resource_bindings.clone(),
        instance_field_scope: walk_resource_context(&state.instance_field_scope, s),
        resources: walk_resource_context(&state.resources, s),
        loan_ledger: state.loan_ledger.clone(),
        loan_participant: state.loan_participant,
        loan_view_bindings: state.loan_view_bindings.clone(),
        thread_ledger: state.thread_ledger.clone(),
        mutex_ledger: state.mutex_ledger.clone(),
        mutex_input_reservations: state.mutex_input_reservations.clone(),
        opaque_mutex_acquisitions: state.opaque_mutex_acquisitions.clone(),
        named_mutex_authorities: state.named_mutex_authorities.clone(),
        preserves_mutex_protocols: state.preserves_mutex_protocols,
        population_access: state.population_access.clone(),
        pending_thread_create: state.pending_thread_create.as_ref().map(|pending| {
            pending.map_terms(
                |status| s.bitvector(status),
                |resources| walk_resource_context(resources, s),
                |pointer| s.pointer(pointer),
                |value| s.program_value(value),
                |memory| s.memory(memory),
            )
        }),
        next_local_frame: state.next_local_frame,
        next_local_lifetime: state.next_local_lifetime,
        enclosing_frame_holds_locals: state.enclosing_frame_holds_locals,
        observed_population_families: state.observed_population_families.clone(),
        population_effects: std::sync::Arc::new(crate::kernel::primitives::PopulationEffects {
            creation: state.population_effects.creation.clone(),
            predicate_count_permissions: state
                .population_effects
                .predicate_count_permissions
                .clone(),
        }),
    }
}

fn walk_execution_statement<S: VariableSubstitution + ?Sized>(
    statement: &ProgramStatement,
    s: &S,
) -> ProgramStatement {
    match statement {
        ProgramStatement::ThrowOpaque(_)
        | ProgramStatement::Skip
        | ProgramStatement::EndAutomaticLifetimes { .. }
        | ProgramStatement::Break
        | ProgramStatement::Continue
        | ProgramStatement::Goto { .. }
        | ProgramStatement::DeclareAggregate { .. } => statement.clone(),

        ProgramStatement::Declare { .. } => {
            let mut statement = statement.clone();
            if let ProgramStatement::Declare {
                initializer,
                zero_fill,
                ..
            } = &mut statement
            {
                *initializer = initializer
                    .as_ref()
                    .map(|value| s.program_expression(value));
                if let Some(fill) = zero_fill
                    && !fill.written_elements.is_empty()
                {
                    fill.written_elements = fill
                        .written_elements
                        .iter()
                        .map(|(index, value)| (*index, s.program_expression(value)))
                        .collect();
                }
            }
            statement
        }
        ProgramStatement::Assign {
            name,
            expression,
            source,
            prior_result,
        } => ProgramStatement::Assign {
            source: source.clone(),
            name: name.clone(),
            expression: s.program_expression(expression),
            prior_result: *prior_result,
        },
        ProgramStatement::CallConstruct {
            target,
            function_name,
            arguments,
        } => ProgramStatement::CallConstruct {
            target: target.clone(),
            function_name: function_name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| s.program_expression(argument))
                .collect(),
        },
        ProgramStatement::Call {
            function_name,
            arguments,
            callee,
        } => ProgramStatement::Call {
            function_name: function_name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| s.program_expression(argument))
                .collect(),
            callee: callee.as_ref().map(|callee| Callee {
                pointer: s.program_expression(&callee.pointer),
                pointer_type: callee.pointer_type,
            }),
        },
        ProgramStatement::CallResult {
            aggregate_layout,
            call,
            function_name,
            arguments,
            result_type,
            result_aggregate_layout,
            result_pointee_constant,
            callee,
            ..
        } => ProgramStatement::CallResult {
            aggregate_layout: aggregate_layout.clone(),
            call: *call,
            function_name: function_name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| s.program_expression(argument))
                .collect(),
            result_type: *result_type,
            result_aggregate_layout: result_aggregate_layout.clone(),
            result_pointee_constant: *result_pointee_constant,
            callee: callee.as_ref().map(|callee| Callee {
                pointer: s.program_expression(&callee.pointer),
                pointer_type: callee.pointer_type,
            }),
        },
        ProgramStatement::HeapAllocate {
            target,
            bytes,
            zeroed,
            object_type,
            ends_program_on_failure,
        } => ProgramStatement::HeapAllocate {
            target: target.clone(),
            bytes: s.program_expression(bytes),
            zeroed: *zeroed,
            object_type: object_type.clone(),
            ends_program_on_failure: *ends_program_on_failure,
        },
        ProgramStatement::HeapFree { pointer } => ProgramStatement::HeapFree {
            pointer: s.program_expression(pointer),
        },
        ProgramStatement::Assert { condition, label } => ProgramStatement::Assert {
            condition: s.program_expression(condition),
            label: label.clone(),
        },
        ProgramStatement::StepValue {
            aggregate_layout,
            steps,
            expression,
            value_type,
            pointee_constant,
            ..
        } => ProgramStatement::StepValue {
            aggregate_layout: aggregate_layout.clone(),
            steps: steps.clone(),
            expression: s.program_expression(expression),
            value_type: *value_type,
            pointee_constant: *pointee_constant,
        },
        ProgramStatement::LoopTest {
            aggregate_steps,
            condition,
            ..
        } => ProgramStatement::LoopTest {
            aggregate_steps: aggregate_steps.clone(),
            condition: s.program_expression(condition),
        },
        ProgramStatement::Seq(statements) => ProgramStatement::Seq(
            statements.map(|statement| std::sync::Arc::new(walk_execution_statement(statement, s))),
        ),
        ProgramStatement::Return(expression) => {
            ProgramStatement::Return(s.program_expression(expression))
        }
        ProgramStatement::Throw(expression) => {
            ProgramStatement::Throw(s.program_expression(expression))
        }
        ProgramStatement::TryCatchInt32 {
            try_body,
            binding,
            handler,
        } => ProgramStatement::TryCatchInt32 {
            try_body: Box::new(walk_execution_statement(try_body, s)),
            binding: binding.clone(),
            handler: Box::new(walk_execution_statement(handler, s)),
        },
        ProgramStatement::UnwindCleanup { body, cleanup } => ProgramStatement::UnwindCleanup {
            body: Box::new(walk_execution_statement(body, s)),
            cleanup: Box::new(walk_execution_statement(cleanup, s)),
        },
        ProgramStatement::Store { pointer, value } => ProgramStatement::Store {
            pointer: s.program_expression(pointer),
            value: s.program_expression(value),
        },
        ProgramStatement::TypedStore {
            pointer,
            value,
            value_type,
            access_class,
            volatile,
            pointee_constant,
            source,
        } => ProgramStatement::TypedStore {
            pointer: s.program_expression(pointer),
            value: s.program_expression(value),
            value_type: *value_type,
            access_class: access_class.clone(),
            volatile: *volatile,
            pointee_constant: *pointee_constant,
            source: source.clone(),
        },
        ProgramStatement::CopyAggregate {
            target,
            source,
            layout,
        } => ProgramStatement::CopyAggregate {
            target: s.program_expression(target),
            source: s.program_expression(source),
            layout: layout.clone(),
        },
        ProgramStatement::InitializeScalarArray {
            target,
            source,
            element_type,
            count,
            copy,
            fresh,
        } => ProgramStatement::InitializeScalarArray {
            target: s.program_expression(target),
            source: s.program_expression(source),
            element_type: *element_type,
            count: *count,
            copy: *copy,
            fresh: *fresh,
        },
        ProgramStatement::Update {
            target,
            operator,
            operand,
        } => ProgramStatement::Update {
            target: s.program_expression(target),
            operator: *operator,
            operand: s.program_expression(operand),
        },
        ProgramStatement::If {
            condition,
            then_branch,
            else_branch,
        } => ProgramStatement::If {
            condition: s.program_expression(condition),
            then_branch: Box::new(walk_execution_statement(then_branch, s)),
            else_branch: Box::new(walk_execution_statement(else_branch, s)),
        },
        ProgramStatement::Loop {
            test,
            update,
            invariant,
            invariant_checks,
            effect_checks,
            resource_specs,
            ranking_measures,
            structural_measure,
            body,
            backedge_target,
            natural_exit_target,
        } => ProgramStatement::Loop {
            test: LoopTestRegion {
                statement: std::sync::Arc::new(walk_execution_statement(&test.statement, s)),
                position: test.position,
            },
            update: update
                .as_ref()
                .map(|step| std::sync::Arc::new(walk_execution_statement(step, s))),
            structural_measure: structural_measure.clone(),
            ranking_measures: ranking_measures
                .iter()
                .map(|measure| walk_ranking_component(measure, s))
                .collect(),
            resource_specs: resource_specs
                .iter()
                .map(|resource| walk_resource_spec(resource, s))
                .collect(),
            invariant: invariant
                .iter()
                .map(|proposition| walk_proposition(proposition, s))
                .collect(),
            invariant_checks: invariant_checks
                .iter()
                .map(|check| LoopInvariantCheck {
                    proposition: s.spec_proposition(check.proposition()),
                    entry_context: check.entry_context.clone(),
                    preservation_context: check.preservation_context.clone(),
                })
                .collect(),
            effect_checks: effect_checks
                .iter()
                .map(|check| LoopEffectCheck {
                    effect: walk_loop_effect(check.effect(), s),
                    span: check.span,
                    context: check.context.clone(),
                    origin: check.origin,
                    validated_ranges: check.validated_ranges.as_ref().map(|ranges| {
                        ranges
                            .iter()
                            .map(|range| walk_memory_range(range, s))
                            .collect()
                    }),
                })
                .collect(),
            backedge_target: *backedge_target,
            natural_exit_target: *natural_exit_target,
            body: Box::new(walk_execution_statement(body, s)),
        },
        ProgramStatement::Switch { expression, cases } => ProgramStatement::Switch {
            expression: s.program_expression(expression),
            cases: cases
                .iter()
                .map(|case| SwitchCase {
                    value: case.value,
                    body: Box::new(walk_execution_statement(&case.body, s)),
                })
                .collect(),
        },
    }
}

fn walk_execution_statement_outcome<S: VariableSubstitution + ?Sized>(
    outcome: &StatementOutcome,
    s: &S,
) -> StatementOutcome {
    match outcome {
        StatementOutcome::Normal(state) => {
            StatementOutcome::Normal(Box::new(walk_execution_state(state, s)))
        }
        StatementOutcome::LoopTestFalse(state) => {
            StatementOutcome::LoopTestFalse(Box::new(walk_execution_state(state, s)))
        }
        StatementOutcome::Break(state) => {
            StatementOutcome::Break(Box::new(walk_execution_state(state, s)))
        }
        StatementOutcome::Continue(state) => {
            StatementOutcome::Continue(Box::new(walk_execution_state(state, s)))
        }
        StatementOutcome::Jump { target, state } => StatementOutcome::Jump {
            target: *target,
            state: Box::new(walk_execution_state(state, s)),
        },
        StatementOutcome::Return { value, state } => StatementOutcome::Return {
            value: s.expression_value(value).into(),
            state: Box::new(walk_execution_state(state, s)),
        },
        StatementOutcome::Throw { value, state } => StatementOutcome::Throw {
            value: s.expression_value(value).into(),
            state: Box::new(walk_execution_state(state, s)),
        },
        StatementOutcome::VerificationDiverges => StatementOutcome::VerificationDiverges,
        StatementOutcome::UndefinedBehavior(kind) => {
            StatementOutcome::UndefinedBehavior(kind.clone())
        }
        StatementOutcome::RuntimeError(kind) => StatementOutcome::RuntimeError(kind.clone()),
    }
}

fn walk_loop_effect<S: VariableSubstitution + ?Sized>(effect: &LoopEffect, s: &S) -> LoopEffect {
    match effect {
        LoopEffect::Mutable(segments) => LoopEffect::Mutable(
            segments
                .iter()
                .map(|segment| MemorySegment {
                    base: s.program_expression(&segment.base),
                    start: s.program_expression(&segment.start),
                    end: s.program_expression(&segment.end),
                    element_width: segment.element_width,
                    uninitialized: segment.uninitialized,
                    value_runs: segment.value_runs.clone(),
                    guard: segment
                        .guard
                        .as_ref()
                        .map(|guard| s.spec_proposition(guard)),
                })
                .collect(),
        ),
    }
}

fn walk_proposition<S: VariableSubstitution + ?Sized>(
    proposition: &Proposition,
    s: &S,
) -> Proposition {
    let _scope = s.proposition_scope();
    match proposition {
        Proposition::VolatileAccess(event) => {
            Proposition::VolatileAccess(std::sync::Arc::new(VolatileAccess {
                pointer: s.pointer(&event.pointer),
                value: StoredProgramValue::from(s.stored_program_value(event.value.value())),
                id: event.id,
                kind: event.kind,
                value_type: event.value_type,
            }))
        }
        Proposition::Equal(left, right) => Proposition::Equal(s.term(left), s.term(right)),
        Proposition::ConditionIs(condition, value) => {
            Proposition::condition_is(s.stored_condition(condition), *value)
        }
        Proposition::Predicate { name, arguments } => Proposition::Predicate {
            name: name.clone(),
            arguments: arguments.iter().map(|argument| s.term(argument)).collect(),
        },
        Proposition::ProgramExpressionEvaluates {
            state,
            expression,
            outcome,
        } => Proposition::ProgramExpressionEvaluates {
            state: Box::new(walk_execution_state(state, s)),
            expression: s.program_expression(expression),
            outcome: walk_program_expression_outcome(outcome, s),
        },
        Proposition::ProgramConditionEvaluates {
            state,
            condition,
            outcome,
        } if S::SUBSTITUTES_CONDITION_EVIDENCE => Proposition::ProgramConditionEvaluates {
            state: Box::new(walk_execution_state(state, s)),
            condition: s.program_expression(condition),
            outcome: outcome.clone(),
        },
        Proposition::ProgramStatementVerifies {
            state,
            statement,
            outcome,
        } => Proposition::ProgramStatementVerifies {
            state: Box::new(walk_execution_state(state, s)),
            statement: Box::new(walk_execution_statement(statement, s)),
            outcome: walk_execution_statement_outcome(outcome, s),
        },
        Proposition::ProgramFunctionVerifies {
            state,
            function,
            arguments,
            outcome,
        } => {
            let state = walk_execution_state(state, s);
            let function = walk_program_function(function, s);
            let arguments = arguments
                .iter()
                .map(|argument| s.program_expression(argument))
                .collect();
            Proposition::ProgramFunctionVerifies {
                state: Box::new(state),
                function: Box::new(function),
                arguments,
                outcome: walk_program_function_outcome(outcome, s),
            }
        }
        Proposition::ProgramFunctionPartiallySatisfiesSpecification {
            function,
            specification,
        } => Proposition::ProgramFunctionPartiallySatisfiesSpecification {
            function: Box::new(walk_program_function(function, s)),
            specification: Box::new(walk_program_function_specification(specification, s)),
        },
        Proposition::MemoryLoads {
            memory,
            pointer,
            outcome,
        } => Proposition::MemoryLoads {
            memory: s.memory(memory),
            pointer: s.pointer(pointer),
            outcome: walk_program_expression_outcome(outcome, s),
        },
        Proposition::MemoryReadDefined {
            at,
            memory,
            pointer,
            value_type,
        } => Proposition::MemoryReadDefined {
            at: *at,
            memory: s.memory(memory),
            pointer: s.pointer(pointer),
            value_type: *value_type,
        },
        Proposition::MemoryCanStore {
            memory,
            pointer,
            byte_width,
        } => Proposition::MemoryCanStore {
            memory: s.memory(memory),
            pointer: s.pointer(pointer),
            byte_width: *byte_width,
        },
        Proposition::MemoryLoadable {
            memory,
            base,
            bytes,
            wide,
        } => Proposition::MemoryLoadable {
            memory: s.memory(memory),
            base: s.pointer(base),
            bytes: match bytes.value() {
                ExecutionValue::Native(_) => bytes.map_native(|term| s.bitvector(term)),
                value => crate::kernel::StoredMachineTerm::from_value(s.expression_value(value))
                    .expect("substitution preserves count type"),
            },
            wide: *wide,
        },
        Proposition::ResourceSeparate { left, right } => Proposition::ResourceSeparate {
            left: Box::new(walk_resource(left, s)),
            right: Box::new(walk_resource(right, s)),
        },
        Proposition::ResourceViewable { memory, resource } => {
            crate::kernel::resource_viewable(&s.memory(memory), walk_resource(resource, s))
        }
        Proposition::ResourceContains { parent, child } => Proposition::ResourceContains {
            parent: Box::new(walk_resource(parent, s)),
            child: Box::new(walk_resource(child, s)),
        },
        Proposition::ResourceComposition(resources) if S::SUBSTITUTES_CONDITION_EVIDENCE => {
            Proposition::ResourceComposition(walk_resource_context(resources, s))
        }
        Proposition::MemoryMutatesOnly {
            before,
            after,
            writes,
        } => Proposition::MemoryMutatesOnly {
            before: s.memory(before),
            after: s.memory(after),
            writes: writes
                .iter()
                .map(|(pointer, bytes)| (s.pointer(pointer), *bytes))
                .collect(),
        },
        Proposition::MemoryEffectSummary {
            before,
            after,
            mutable_ranges,
        } => Proposition::MemoryEffectSummary {
            before: s.memory(before),
            after: s.memory(after),
            mutable_ranges: mutable_ranges
                .iter()
                .map(|range| walk_memory_range(range, s))
                .collect(),
        },
        Proposition::HeapAllocationFreed {
            before,
            after,
            allocation_base,
            bytes,
        } => Proposition::HeapAllocationFreed {
            before: s.memory(before),
            after: s.memory(after),
            allocation_base: s.pointer(allocation_base),
            bytes: bytes.map_bytes(|bytes| s.bitvector(bytes)),
        },
        Proposition::And(left, right) => Proposition::And(
            Box::new(walk_proposition(left, s)),
            Box::new(walk_proposition(right, s)),
        ),
        Proposition::Or(left, right) => Proposition::Or(
            Box::new(walk_proposition(left, s)),
            Box::new(walk_proposition(right, s)),
        ),
        Proposition::Not(body) => Proposition::Not(Box::new(walk_proposition(body, s))),
        Proposition::Implies(left, right) => Proposition::Implies(
            Box::new(walk_proposition(left, s)),
            Box::new(walk_proposition(right, s)),
        ),
        Proposition::ForAll {
            var,
            sort,
            body,
            name,
        } if *var != s.from() => {
            let (var, body) = s.quantifier_body(*var, sort, body);
            Proposition::ForAll {
                var,
                sort: sort.clone(),
                name: name.clone(),
                body: Box::new(walk_proposition(&body, s)),
            }
        }
        Proposition::Exists {
            name,
            var,
            sort,
            body,
        } if *var != s.from() => {
            let (var, body) = s.quantifier_body(*var, sort, body);
            Proposition::Exists {
                name: name.clone(),
                var,
                sort: sort.clone(),
                body: Box::new(walk_proposition(&body, s)),
            }
        }
        proposition => proposition.clone(),
    }
}

fn walk_pure_function_argument<S: VariableSubstitution + ?Sized>(
    argument: &PureFunctionArgument,
    s: &S,
) -> PureFunctionArgument {
    match argument {
        PureFunctionArgument::Integer(value) => {
            PureFunctionArgument::Integer(s.integer(value.as_ref()).into())
        }
        PureFunctionArgument::SharedMachine(value) => PureFunctionArgument::SharedMachine(
            crate::kernel::memory_history::map_shared_pointer_index_with_fold(
                value,
                |leaf| Some(s.bitvector(leaf)),
                crate::kernel::proof::equality_rewrite::rebuild_normalized_machine_node,
                |_| true,
                |root| {
                    let result = s.expression_value(&ExecutionValue::Shared(root.clone()));
                    let (format, view) = result.machine().ok_or(())?;
                    Ok(Some(KernelTerm::retained_machine_operand(format, view)))
                },
            )
            .unwrap_or_else(|| value.clone()),
        ),
        PureFunctionArgument::Value(value) => PureFunctionArgument::Value(s.program_value(value)),
        PureFunctionArgument::Algebraic(value) => {
            PureFunctionArgument::Algebraic(s.algebraic_term(value))
        }
        PureFunctionArgument::ArrayRef {
            memory,
            pointer,
            element_type,
        } => PureFunctionArgument::ArrayRef {
            memory: s.memory(memory),
            pointer: s.program_value(pointer),
            element_type: *element_type,
        },
    }
}

fn walk_resource_fact<S: VariableSubstitution + ?Sized>(
    resource: &ResourceFact,
    s: &S,
) -> ResourceFact {
    match resource {
        ResourceFact::Own(resource, quantity) => ResourceFact::own_quantity_stored(
            walk_resource(resource, s),
            match quantity.value() {
                ExecutionValue::Native(_) => quantity.map_native(|term| s.bitvector(term)),
                value => crate::kernel::StoredMachineTerm::from_value(s.expression_value(value))
                    .expect("substitution preserves quantity type"),
            },
        ),
        ResourceFact::View(resource) => ResourceFact::View(walk_resource(resource, s)),
    }
}

fn walk_resource_context<S: VariableSubstitution + ?Sized>(
    resources: &ResourceContext,
    s: &S,
) -> ResourceContext {
    // Structural theorem/state substitution has no current proof assumptions.
    // Do not inherit the old graph: its equalities name the pre-substitution
    // variables. A resulting live proof input is published at its admission
    // boundary before execution; this helper performs no resource lookup.
    ResourceContext::new().unchecked_with_facts(
        resources
            .facts()
            .iter()
            .map(|resource| walk_resource_fact(resource, s)),
    )
}

fn walk_resource_spec<S: VariableSubstitution + ?Sized>(
    resource: &ResourceSpec,
    s: &S,
) -> ResourceSpec {
    let substituted = ResourceSpec::new(
        walk_resource_term(resource.term(), s),
        resource.access(),
        match resource.quantity() {
            ResourceQuantity::One => ResourceQuantity::One,
            ResourceQuantity::Count(quantity) => {
                ResourceQuantity::Count(s.program_expression(quantity))
            }
        },
        resource.role(),
        resource.state_source(),
    )
    .expect("pointer substitution preserves resource validity")
    .with_resource_arguments(resource.resource_arguments().to_vec());
    match resource.mutex_authority_binding() {
        Some((identity, binder)) => substituted
            .with_mutex_authority_binding(identity, binder.to_string())
            .expect("pointer substitution preserves mutex authority binding"),
        None => substituted,
    }
}

fn walk_resource_term<S: VariableSubstitution + ?Sized>(
    resource: &ResourceTerm,
    s: &S,
) -> ResourceTerm {
    match resource {
        ResourceTerm::Instance {
            identity,
            binder,
            schema,
            resource,
        } => ResourceTerm::Instance {
            identity: *identity,
            binder: binder.clone(),
            schema: schema.clone(),
            resource: Box::new(walk_resource_term(resource, s)),
        },
        ResourceTerm::PopulationAuthority {
            protected,
            population_arity,
            state_source: retained_state,
        } => ResourceTerm::PopulationAuthority {
            population_arity: *population_arity,
            protected: Box::new(ResourceTypeSpec {
                resource: Box::new(walk_resource_spec(&protected.resource, s)),
                schema: protected.schema.clone(),
            }),
            state_source: *retained_state,
        },
        ResourceTerm::MutexGuard {
            mutex,
            state_source: retained_state,
        } => ResourceTerm::MutexGuard {
            mutex: Box::new(s.program_expression(mutex)),
            state_source: *retained_state,
        },
        ResourceTerm::MutexLive {
            mutex,
            state_source: retained_state,
        } => ResourceTerm::MutexLive {
            mutex: Box::new(s.program_expression(mutex)),
            state_source: *retained_state,
        },
        ResourceTerm::Publication {
            side,
            payload,
            flag,
            state_source: retained_state,
        } => ResourceTerm::Publication {
            side: *side,
            payload: Box::new(ResourceTypeSpec {
                resource: Box::new(walk_resource_spec(&payload.resource, s)),
                schema: payload.schema.clone(),
            }),
            flag: Box::new(s.program_expression(flag)),
            state_source: *retained_state,
        },
        ResourceTerm::MutexUse {
            mutex,
            state_source: retained_state,
            protected,
        } => ResourceTerm::MutexUse {
            protected: protected.as_ref().map(|p| {
                Box::new(ResourceTypeSpec {
                    resource: Box::new(walk_resource_spec(&p.resource, s)),
                    schema: p.schema.clone(),
                })
            }),
            mutex: Box::new(s.program_expression(mutex)),
            state_source: *retained_state,
        },
        ResourceTerm::Iterated(spec) => ResourceTerm::Iterated(Box::new(
            spec.map_expressions(|expression| s.program_expression(expression)),
        )),
        ResourceTerm::Memory(segment) => ResourceTerm::Memory(MemorySegment {
            base: s.program_expression(&segment.base),
            start: s.program_expression(&segment.start),
            end: s.program_expression(&segment.end),
            element_width: segment.element_width,
            uninitialized: segment.uninitialized,
            value_runs: segment.value_runs.clone(),
            guard: segment
                .guard
                .as_ref()
                .map(|guard| s.spec_proposition(guard)),
        }),
        ResourceTerm::Composite {
            name,
            arguments,
            argument_state_sources,
            parameter_types,
        } => ResourceTerm::Composite {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| s.program_expression(argument))
                .collect(),
            argument_state_sources: argument_state_sources.clone(),
            parameter_types: parameter_types.clone(),
        },
        ResourceTerm::Token {
            name,
            arguments,
            argument_state_sources,
            parameter_types,
        } => ResourceTerm::Token {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| s.program_expression(argument))
                .collect(),
            argument_state_sources: argument_state_sources.clone(),
            parameter_types: parameter_types.clone(),
        },
    }
}

fn walk_sequence<S: VariableSubstitution + ?Sized>(sequence: &SequenceTerm, s: &S) -> SequenceTerm {
    let node = match sequence.node.as_ref() {
        SequenceTermNode::Literal(values) => SequenceTermNode::Literal(values.map_values(
            |value| s.program_value(value),
            |value| s.stored_program_value(value),
        )),
        SequenceTermNode::Concat(left, right) => {
            SequenceTermNode::Concat(walk_sequence(left, s), walk_sequence(right, s))
        }
    };
    SequenceTerm {
        element_type: sequence.element_type,
        node: std::sync::Arc::new(node),
    }
}

fn walk_memory_range<S: VariableSubstitution + ?Sized>(range: &MemoryRange, s: &S) -> MemoryRange {
    let mut result = range
        .with_bounds(
            s.pointer(&range.base),
            s.bitvector(range.bound_terms().0),
            s.bitvector(range.bound_terms().1),
        )
        .with_provenance(std::sync::Arc::new(s.pointer(&range.provenance)))
        .with_bounds_owner(
            range
                .bounds_owner
                .as_deref()
                .map(|origin| std::sync::Arc::new(s.pointer(origin))),
            range.carrier_bounds_known,
        );
    if !range.formation_coverage.is_empty() {
        result.formation_coverage = range
            .formation_coverage
            .iter()
            .map(|fact| walk_proposition(fact, s))
            .collect();
    }
    result
}

#[cfg(test)]
mod resource_frame_substitution_tests {
    use super::*;

    #[test]
    fn guard_substitution_renames_abstract_authority_but_preserves_concrete_acquisition() {
        let variable = Variable(71_900);
        let address = Address::symbolic(variable);
        let replacement = Address::symbolic(Variable(71_901));
        let abstract_guard = Resource::MutexGuard(MutexIdentity {
            epoch: None,
            mutex: address.clone(),
        });
        let concrete_guard = Resource::MutexGuard(MutexIdentity {
            epoch: Some(123),
            mutex: address,
        });
        assert_eq!(
            substitute_pointer_variable_in_resource(&abstract_guard, variable, &replacement),
            Resource::MutexGuard(MutexIdentity {
                epoch: None,
                mutex: replacement.clone()
            })
        );
        assert_eq!(
            substitute_pointer_variable_in_resource(&concrete_guard, variable, &replacement),
            concrete_guard
        );
    }

    #[test]
    fn lifetime_substitution_renames_abstract_authority_but_preserves_concrete_initialization() {
        let variable = Variable(71_900);
        let address = Address::symbolic(variable);
        let replacement = Address::symbolic(Variable(71_901));
        let abstract_guard = Resource::MutexLive(MutexIdentity {
            epoch: None,
            mutex: address.clone(),
        });
        let concrete_guard = Resource::MutexLive(MutexIdentity {
            epoch: Some(123),
            mutex: address,
        });
        assert_eq!(
            substitute_pointer_variable_in_resource(&abstract_guard, variable, &replacement),
            Resource::MutexLive(MutexIdentity {
                epoch: None,
                mutex: replacement.clone()
            })
        );
        assert_eq!(
            substitute_pointer_variable_in_resource(&concrete_guard, variable, &replacement),
            concrete_guard
        );
    }

    #[test]
    fn use_substitution_preserves_exact_share_and_diagnostic_address() {
        let variable = Variable(71_900);
        let address = Address {
            base: AddressBase::Symbolic(variable),
            offset: AddressOffset::scaled_int32_node(MachineTerm::Variable(variable), 1),
        };
        let live = ResourceFact::own(Resource::MutexLive(MutexIdentity {
            epoch: Some(123),
            mutex: address,
        }));
        let resources = ResourceContext::new()
            .try_compose_with_fact(live.clone(), &PureFactContext::new())
            .unwrap();
        let support = resources.unique_owned_occurrence_for_fact(&live).unwrap().0;
        let ledger = crate::kernel::loans::LoanLedger::new();
        let participant = ledger.fresh_participant().unwrap();
        let (ledger, loan) = ledger
            .lend_mutex_use(participant, participant, support, live)
            .unwrap();
        let fact = ledger.mutex_use_resource(loan.usage, participant).unwrap();
        let resource = fact.resource();
        assert_eq!(
            substitute_pointer_variable_in_resource(
                resource,
                variable,
                &Address::symbolic(Variable(71_901))
            ),
            *resource
        );
        assert_eq!(
            substitute_bitvector_variable_in_resource(
                resource,
                variable,
                &MachineTerm::constant(4)
            ),
            *resource
        );
    }

    #[test]
    fn unrelated_binder_preserves_nested_offset_state() {
        let base = SymbolicMemory::new();
        let metadata = Address {
            base: AddressBase::ExternalArgument,
            offset: AddressOffset::Add(
                Box::new(AddressOffset::Add(
                    Box::new(AddressOffset::scaled_int32_node(
                        MachineTerm::Variable(Variable(100_000)),
                        4,
                    )),
                    Box::new(AddressOffset::Constant(8)),
                )),
                Box::new(AddressOffset::Constant(4)),
            ),
        };
        let retained_state = crate::kernel::intern_memory(
            base.store(metadata, ProgramValue::Int32(MachineTerm::constant(7))),
        );
        let rewritten = substitute_bitvector_variable_in_shared_memory(
            &retained_state,
            Variable(2_000_000),
            &MachineTerm::Variable(Variable(3_200_000)),
        );
        assert_eq!(rewritten.arena_id(), retained_state.arena_id());
    }

    #[test]
    fn state_substitutions_preserve_the_exact_loan_ledger_root() {
        let ledger = crate::kernel::loans::LoanLedger::new();
        let participant = ledger.fresh_participant().expect("participant identity");
        let state = ExecutionState::new()
            .with_local("x", int32(MachineTerm::Variable(Variable(71_100))))
            .with_loan_ledger(Some(ledger))
            .with_loan_participant(Some(participant));
        let bitvector_substituted = substitute_bitvector_variable_in_execution_state(
            &state,
            Variable(71_100),
            &MachineTerm::constant(4),
        );
        let pointer_substituted = substitute_pointer_variable_in_execution_state(
            &state,
            Variable(71_100),
            &Address::symbolic(Variable(71_101)),
        );

        let original = state.loan_ledger().expect("state has ledger");
        assert!(
            original.shares_storage_with(
                bitvector_substituted
                    .loan_ledger()
                    .expect("bitvector substitution has ledger")
            )
        );
        assert!(
            original.shares_storage_with(
                pointer_substituted
                    .loan_ledger()
                    .expect("pointer substitution has ledger")
            )
        );
        assert_eq!(bitvector_substituted.loan_participant(), Some(participant));
        assert_eq!(pointer_substituted.loan_participant(), Some(participant));
    }

    fn inherited_check(range: MemoryRange) -> LoopEffectCheck {
        LoopEffectCheck {
            effect: LoopEffect::Mutable(Vec::new()),
            span: LoopEffectSpan::Whole,
            context: None,
            origin: LoopEffectOrigin::InheritedResourceDerived,
            validated_ranges: Some(vec![range]),
        }
    }

    #[test]
    fn bitvector_substitution_rewrites_validated_inherited_ranges() {
        let from = Variable(71_001);
        let range = MemoryRange::new(
            Address {
                base: AddressBase::Concrete("substitution:range".into()),
                offset: AddressOffset::scaled_int32_node(MachineTerm::Variable(from), 4),
            },
            MachineTerm::Variable(from),
            binary_node!(
                Int32,
                Add,
                Box::new(MachineTerm::Variable(from)),
                Box::new(MachineTerm::constant(1)),
            ),
        );
        let statement = ProgramStatement::Loop {
            test: crate::kernel::LoopTestRegion::expression(
                crate::kernel::program_expression::int32_literal(0),
                crate::kernel::LoopTestPosition::BeforeBody,
            ),
            update: None,
            invariant: Vec::new(),
            invariant_checks: Vec::new(),
            effect_checks: vec![inherited_check(range)],
            resource_specs: Vec::new(),
            ranking_measures: Vec::new(),
            structural_measure: None,
            body: Box::new(ProgramStatement::Skip),
            backedge_target: None,
            natural_exit_target: None,
        };
        let substituted = substitute_bitvector_variable_in_execution_statement(
            &statement,
            from,
            &MachineTerm::constant(4),
        );
        let ProgramStatement::Loop { effect_checks, .. } = substituted else {
            panic!("substitution changed the statement shape");
        };
        let actual = effect_checks[0]
            .validated_ranges()
            .expect("validated carrier must be retained");
        assert_eq!(actual[0].start(), &MachineTerm::constant(4));
        assert_eq!(actual[0].end(), &MachineTerm::constant(5));
        assert_eq!(actual[0].base.offset, AddressOffset::Constant(16));
    }

    #[test]
    fn pointer_substitution_rewrites_validated_ranges_and_derived_interface() {
        let from = Variable(71_002);
        let replacement = Address {
            base: AddressBase::Concrete("substitution:replacement".into()),
            offset: AddressOffset::Constant(2),
        };
        let range = MemoryRange::new(
            Address {
                base: AddressBase::Symbolic(from),
                offset: AddressOffset::Constant(0),
            },
            MachineTerm::constant(0),
            MachineTerm::constant(1),
        );
        let statement = ProgramStatement::Loop {
            test: crate::kernel::LoopTestRegion::expression(
                crate::kernel::program_expression::int32_literal(0),
                crate::kernel::LoopTestPosition::BeforeBody,
            ),
            update: None,
            invariant: Vec::new(),
            invariant_checks: Vec::new(),
            effect_checks: vec![inherited_check(range)],
            resource_specs: Vec::new(),
            ranking_measures: Vec::new(),
            structural_measure: None,
            body: Box::new(ProgramStatement::Skip),
            backedge_target: None,
            natural_exit_target: None,
        };
        let substituted =
            substitute_pointer_variable_in_execution_statement(&statement, from, &replacement);
        let ProgramStatement::Loop { effect_checks, .. } = substituted else {
            panic!("substitution changed the statement shape");
        };
        assert_eq!(
            effect_checks[0].validated_ranges().unwrap()[0].base.offset,
            replacement.offset
        );

        let derived_segment = MemorySegment::new(
            ProgramExpression::Value(ProgramValue::pointer(Address {
                base: AddressBase::Symbolic(from),
                offset: AddressOffset::Constant(0),
            })),
            ProgramExpression::Value(int32(0)),
            ProgramExpression::Value(int32(1)),
        );
        let function =
            ProgramFunction::new(ProgramType::Void, "substitution", Vec::new(), statement)
                .with_contract(
                    Vec::new(),
                    Vec::new(),
                    vec![derived_segment],
                    Vec::new(),
                    true,
                )
                .with_resource_summary(Vec::new(), Vec::new())
                .with_resource_derived_mutable_frame();
        let substituted =
            substitute_pointer_variable_in_program_function(&function, from, &replacement);
        assert!(substituted.resource_derived_mutable_frame());
        assert_eq!(
            substituted.contract_mutable()[0].base,
            ProgramExpression::Value(ProgramValue::pointer(replacement))
        );
    }
}

/// Resolves load variables in a proposition through
/// defining-equation propositions (`v == load(retained_state, ptr)`), restoring
/// the load terms. For surface-form synthesis, where the internal
/// names have no surface form but their loads do.
/// Resolves load variables in a proposition through the
/// thread-local registry, restoring the load terms the internal names
/// stand for. For surface-form synthesis when no defining equation is
/// in scope: the registry is the mint's own record of what each canonical
/// variable names.
pub fn resolve_load_variables_from_registry(proposition: &Proposition) -> Proposition {
    let mut variables = std::collections::BTreeSet::new();
    super::variable_collection::collect_proposition_bitvector_variables(
        proposition,
        &mut variables,
    );
    let mut resolved = proposition.clone();
    for variable in variables {
        if !crate::kernel::eval::is_load_variable(&variable) {
            continue;
        }
        let Some(load) = crate::kernel::eval::registered_load_origin_term_for_variable(&variable)
        else {
            continue;
        };
        resolved = substitute_bitvector_variable_in_proposition(&resolved, variable, &load);
    }
    resolved
}

/// Bounded resolution for checked surface reconstruction. A refused walk
/// returns no proposition; callers must never round-trip a partial rewrite.
pub(crate) fn try_resolve_load_variables_from_registry(
    proposition: &Proposition,
) -> Result<Proposition, IntegerPureSubstitutionError> {
    integer_work(1)?;
    let mut variables = BTreeSet::new();
    super::variable_collection::collect_proposition_bitvector_variables(
        proposition,
        &mut variables,
    );
    let mut resolved = proposition.clone();
    for variable in variables {
        integer_work(1)?;
        if !crate::kernel::eval::is_load_variable(&variable) {
            continue;
        }
        if let Some(load) = crate::kernel::eval::registered_load_origin_term_for_variable(&variable)
        {
            resolved = substitute_surface_load_binding(&resolved, variable, &load)?;
        }
    }
    Ok(resolved)
}

fn substitute_surface_load_binding(
    proposition: &Proposition,
    from: Variable,
    load: &MachineTerm,
) -> Result<Proposition, IntegerPureSubstitutionError> {
    use crate::kernel::proof::term_rewrite::{TermRewrite, TypedProgramValueReplacement};
    let mut collector =
        crate::kernel::proof::term_rewrite::IntegerSubstitutionVariableCollector::checked();
    collector.collect(proposition);
    collector.collect(&Proposition::condition_is(
        ConditionTerm::equal(MachineTerm::Variable(from), load.clone()),
        true,
    ));
    if collector.exhausted() {
        return Err(IntegerPureSubstitutionError::WorkLimitExceeded);
    }
    let mut reserved = BTreeSet::new();
    collector.extend_into(&mut reserved);
    reserved.insert(from);
    let c = BTreeMap::from([(from, TypedProgramValueReplacement::Bitvector(load.clone()))]);
    let integer = BTreeMap::new();
    let algebraic = BTreeMap::new();
    let mut walker = TermRewrite::for_typed_variables(&c, &integer, &algebraic);
    walker.reserve_integer_substitution_variables(&reserved);
    let result = substitute_pure_proposition_with_walker(proposition, from, false, &mut walker);
    integer_substitution_refusal(walker.refusal())?;
    result
}

pub fn resolve_minted_load_variables(
    proposition: &Proposition,
    facts: &(impl ExecutionFactSource + ?Sized),
) -> Result<Proposition, IntegerPureSubstitutionError> {
    let mut resolved = proposition.clone();
    for fact in facts.fact_iter() {
        integer_work(1)?;
        if !fact.certified {
            continue;
        }
        let Some((
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left,
                right,
            },
            true,
        )) = fact.proposition().condition_native()
        else {
            continue;
        };
        let (MachineTerm::Variable(variable), load @ MachineTerm::MemoryLoad(_, _, _)) =
            (left.as_ref(), right.as_ref())
        else {
            continue;
        };
        resolved = substitute_surface_load_binding(&resolved, *variable, load)?;
    }
    Ok(resolved)
}

/// Capture-avoiding substitution for an algebraic quantifier variable.
///
/// Algebraic values can contain C and Integer fields, but only algebraic
/// binders shadow this substitution.  `TermRewrite` owns the corresponding
/// capture avoidance for constructor-match binders; this traversal adds the
/// proposition-quantifier layer that its leaf-only proposition API
/// deliberately does not cross.
pub(crate) fn substitute_algebraic_variable_in_proposition(
    proposition: &Proposition,
    from: Variable,
    to: &AlgebraicTerm,
) -> Proposition {
    fn rewritten_term(term: &Term, from: Variable, to: &AlgebraicTerm) -> Term {
        let source = AlgebraicTerm {
            algebraic_type: to.algebraic_type.clone(),
            node: AlgebraicTermNode::Variable(from),
        };
        crate::kernel::proof::term_rewrite::TermRewrite::new(&source, to).term(term)
    }

    match proposition {
        Proposition::VolatileAccess(_) => {
            let source = AlgebraicTerm {
                algebraic_type: to.algebraic_type.clone(),
                node: AlgebraicTermNode::Variable(from),
            };
            crate::kernel::proof::term_rewrite::TermRewrite::new(&source, to)
                .proposition(proposition)
        }
        Proposition::Equal(left, right) => Proposition::Equal(
            rewritten_term(left, from, to),
            rewritten_term(right, from, to),
        ),
        Proposition::ConditionIs(condition, value) => {
            let leaf = Proposition::condition_is(condition.clone(), *value);
            let source = AlgebraicTerm {
                algebraic_type: to.algebraic_type.clone(),
                node: AlgebraicTermNode::Variable(from),
            };
            crate::kernel::proof::term_rewrite::TermRewrite::new(&source, to).proposition(&leaf)
        }
        Proposition::Predicate { name, arguments } => Proposition::Predicate {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| rewritten_term(argument, from, to))
                .collect(),
        },
        Proposition::And(left, right) => Proposition::And(
            Box::new(substitute_algebraic_variable_in_proposition(left, from, to)),
            Box::new(substitute_algebraic_variable_in_proposition(
                right, from, to,
            )),
        ),
        Proposition::Or(left, right) => Proposition::Or(
            Box::new(substitute_algebraic_variable_in_proposition(left, from, to)),
            Box::new(substitute_algebraic_variable_in_proposition(
                right, from, to,
            )),
        ),
        Proposition::Not(body) => Proposition::Not(Box::new(
            substitute_algebraic_variable_in_proposition(body, from, to),
        )),
        Proposition::Implies(left, right) => Proposition::Implies(
            Box::new(substitute_algebraic_variable_in_proposition(left, from, to)),
            Box::new(substitute_algebraic_variable_in_proposition(
                right, from, to,
            )),
        ),
        Proposition::ForAll {
            var,
            sort,
            body,
            name,
        } if *var != from => {
            let (var, body) = capture_avoiding_algebraic_quantifier_body(*var, body, from, to);
            Proposition::ForAll {
                var,
                sort: sort.clone(),
                name: name.clone(),
                body: Box::new(substitute_algebraic_variable_in_proposition(
                    &body, from, to,
                )),
            }
        }
        Proposition::Exists {
            name,
            var,
            sort,
            body,
        } if *var != from => {
            let (var, body) = capture_avoiding_algebraic_quantifier_body(*var, body, from, to);
            Proposition::Exists {
                name: name.clone(),
                var,
                sort: sort.clone(),
                body: Box::new(substitute_algebraic_variable_in_proposition(
                    &body, from, to,
                )),
            }
        }
        // Kernel execution propositions cannot contain algebraic terms except
        // through their proposition-valued specification fields, and those
        // are never legal directly under a Surface algebraic quantifier.
        proposition => proposition.clone(),
    }
}

fn capture_avoiding_algebraic_quantifier_body(
    binder: Variable,
    body: &Proposition,
    substituted: Variable,
    replacement: &AlgebraicTerm,
) -> (Variable, Proposition) {
    let replacement_probe = Proposition::Equal(
        Term::Algebraic(replacement.clone()),
        Term::Algebraic(replacement.clone()),
    );
    let replacement_variables = crate::kernel::proposition_variables(&replacement_probe);
    if !replacement_variables.contains(&binder) {
        return (binder, body.clone());
    }

    let mut reserved = replacement_variables;
    reserved.extend(crate::kernel::proposition_variables(body));
    collect_proposition_bound_variables(body, &mut reserved);
    reserved.insert(binder);
    reserved.insert(substituted);
    let fresh = KernelVariableGenerator::fresh_for(0, reserved).next();
    let renamed = substitute_algebraic_variable_in_proposition(
        body,
        binder,
        &AlgebraicTerm {
            algebraic_type: replacement.algebraic_type.clone(),
            node: AlgebraicTermNode::Variable(fresh),
        },
    );
    (fresh, renamed)
}

/// Applies a finite substitution to free variables simultaneously.
///
/// Sequentially applying a map is unsound when one replacement mentions a
/// variable that is also a key in the map: the later replacement rewrites the
/// value just installed by the earlier one.  Stage every source through a
/// fresh variable first, then install the requested replacements in a second
/// pass.  The ordinary substitution routine handles capture avoidance at each
/// quantifier boundary.
#[cfg(test)]
pub(in crate::kernel) fn substitute_bitvector_variables_in_proposition(
    proposition: &Proposition,
    substitutions: &BTreeMap<Variable, MachineTerm>,
) -> Proposition {
    if substitutions.is_empty() {
        return proposition.clone();
    }

    let mut reserved = BTreeSet::new();
    collect_proposition_bitvector_variables(proposition, &mut reserved);
    collect_proposition_bound_variables(proposition, &mut reserved);
    for (source, replacement) in substitutions {
        reserved.insert(*source);
        collect_bitvector_variables(replacement, &mut reserved);
    }

    let mut fresh_variables = KernelVariableGenerator::fresh_for(0, reserved);
    let staged = substitutions
        .keys()
        .map(|source| (*source, fresh_variables.next()))
        .collect::<Vec<_>>();

    let mut result = proposition.clone();
    for (source, temporary) in &staged {
        result = substitute_bitvector_variable_in_proposition(
            &result,
            *source,
            &MachineTerm::Variable(*temporary),
        );
    }
    for (source, temporary) in staged {
        result = substitute_bitvector_variable_in_proposition(
            &result,
            temporary,
            &substitutions[&source],
        );
    }
    result
}

fn capture_avoiding_quantifier_body(
    binder: Variable,
    body: &Proposition,
    substituted: Variable,
    replacement: &MachineTerm,
) -> (Variable, Proposition) {
    let mut replacement_variables = BTreeSet::new();
    collect_bitvector_variables(replacement, &mut replacement_variables);
    if !replacement_variables.contains(&binder) {
        return (binder, body.clone());
    }

    let mut reserved = replacement_variables;
    collect_proposition_bitvector_variables(body, &mut reserved);
    collect_proposition_bound_variables(body, &mut reserved);
    reserved.insert(binder);
    reserved.insert(substituted);
    let mut variables = KernelVariableGenerator::fresh_for(0, reserved);
    let fresh = variables.next();
    let renamed =
        substitute_bitvector_variable_in_proposition(body, binder, &MachineTerm::Variable(fresh));
    (fresh, renamed)
}

pub(in crate::kernel) fn collect_proposition_bound_variables(
    proposition: &Proposition,
    variables: &mut BTreeSet<Variable>,
) {
    let mut depth = 0;
    let mut current = proposition;
    while let Proposition::Implies(_, body) = current {
        depth += 1;
        current = body;
    }
    if depth > 128 {
        let mut pending = vec![proposition];
        while let Some(proposition) = pending.pop() {
            match proposition {
                Proposition::And(left, right)
                | Proposition::Or(left, right)
                | Proposition::Implies(left, right) => {
                    pending.push(right);
                    pending.push(left);
                }
                Proposition::Not(body)
                | Proposition::ForAll { body, .. }
                | Proposition::Exists { body, .. } => pending.push(body),
                proposition => collect_proposition_bound_variables_one(proposition, variables),
            }
        }
        return;
    }
    collect_proposition_bound_variables_one(proposition, variables);
}

fn collect_proposition_bound_variables_one(
    proposition: &Proposition,
    variables: &mut BTreeSet<Variable>,
) {
    match proposition {
        Proposition::VolatileAccess(event) => {
            collect_pointer_bound_variables(&event.pointer, variables);
            collect_expression_value_bound_variables(event.value.value(), variables);
        }
        Proposition::Equal(left, right) => {
            collect_term_bound_variables(left, variables);
            collect_term_bound_variables(right, variables);
        }
        Proposition::ConditionIs(condition, _) => {
            collect_condition_bound_variables(condition.native_compat(), variables);
        }
        Proposition::Predicate { arguments, .. } => {
            for argument in arguments {
                collect_term_bound_variables(argument, variables);
            }
        }
        Proposition::ProgramExpressionEvaluates {
            state,
            expression,
            outcome,
        } => {
            collect_execution_state_bound_variables(state, variables);
            collect_program_expression_bound_variables(expression, variables);
            collect_expression_outcome_bound_variables(outcome, variables);
        }
        Proposition::ProgramConditionEvaluates {
            state, condition, ..
        } => {
            collect_execution_state_bound_variables(state, variables);
            collect_program_expression_bound_variables(condition, variables);
        }
        Proposition::ProgramStatementVerifies {
            state,
            statement,
            outcome,
        } => {
            collect_execution_state_bound_variables(state, variables);
            collect_execution_statement_bound_variables(statement, variables);
            collect_statement_outcome_bound_variables(outcome, variables);
        }
        Proposition::ProgramFunctionVerifies {
            state,
            function,
            arguments,
            outcome,
        } => {
            collect_execution_state_bound_variables(state, variables);
            collect_program_function_bound_variables(function, variables);
            for argument in arguments {
                collect_program_expression_bound_variables(argument, variables);
            }
            collect_function_outcome_bound_variables(outcome, variables);
        }
        Proposition::ProgramFunctionPartiallySatisfiesSpecification {
            function,
            specification,
        } => {
            collect_program_function_bound_variables(function, variables);
            collect_program_function_specification_bound_variables(specification, variables);
        }
        Proposition::MemoryLoads {
            memory,
            pointer,
            outcome,
        } => {
            collect_memory_bound_variables(memory, variables);
            collect_pointer_bound_variables(pointer, variables);
            collect_expression_outcome_bound_variables(outcome, variables);
        }
        Proposition::MemoryReadDefined {
            memory, pointer, ..
        }
        | Proposition::MemoryCanStore {
            memory, pointer, ..
        } => {
            collect_memory_bound_variables(memory, variables);
            collect_pointer_bound_variables(pointer, variables);
        }
        Proposition::MemoryLoadable {
            memory,
            base,
            bytes,
            wide: _,
        } => {
            collect_memory_bound_variables(memory, variables);
            collect_pointer_bound_variables(base, variables);
            collect_expression_value_bound_variables(bytes.value(), variables);
        }
        Proposition::ResourceViewable { memory, resource } => {
            collect_memory_bound_variables(memory, variables);
            collect_resource_bound_variables(resource, variables);
        }
        Proposition::ResourceSeparate { left, right }
        | Proposition::ResourceContains {
            parent: left,
            child: right,
        } => {
            collect_resource_bound_variables(left, variables);
            collect_resource_bound_variables(right, variables);
        }
        Proposition::ResourceComposition(resources) => {
            for fact in resources.facts() {
                collect_resource_bound_variables(fact.resource(), variables);
            }
        }
        Proposition::MemoryMutatesOnly {
            before,
            after,
            writes,
        } => {
            collect_memory_bound_variables(before, variables);
            collect_memory_bound_variables(after, variables);
            for (pointer, _) in writes {
                collect_pointer_bound_variables(pointer, variables);
            }
        }
        Proposition::MemoryEffectSummary {
            before,
            after,
            mutable_ranges,
        } => {
            collect_memory_bound_variables(before, variables);
            collect_memory_bound_variables(after, variables);
            for range in mutable_ranges {
                collect_pointer_bound_variables(&range.base, variables);
                collect_bitvector_bound_variables(range.bound_terms().0, variables);
                collect_bitvector_bound_variables(range.bound_terms().1, variables);
            }
        }
        Proposition::HeapAllocationFreed {
            before,
            after,
            allocation_base,
            bytes,
        } => {
            collect_memory_bound_variables(before, variables);
            collect_memory_bound_variables(after, variables);
            collect_pointer_bound_variables(allocation_base, variables);
            collect_bitvector_bound_variables(bytes.bytes(), variables);
        }
        Proposition::And(left, right)
        | Proposition::Or(left, right)
        | Proposition::Implies(left, right) => {
            collect_proposition_bound_variables(left, variables);
            collect_proposition_bound_variables(right, variables);
        }
        Proposition::Not(body) => collect_proposition_bound_variables(body, variables),
        Proposition::ForAll { var, body, .. } | Proposition::Exists { var, body, .. } => {
            variables.insert(*var);
            collect_proposition_bound_variables(body, variables);
        }
    }
}

fn collect_term_bound_variables(term: &Term, variables: &mut BTreeSet<Variable>) {
    match term {
        Term::Condition(condition) => collect_condition_bound_variables(condition, variables),
        Term::Bitvector32(bits) => collect_bitvector_bound_variables(bits, variables),
        Term::Integer(integer) => collect_integer_bound_variables(integer, variables),
        Term::PointerOffset(offset) => collect_pointer_offset_bound_variables(offset, variables),
        Term::ProgramValue(value) => collect_program_value_bound_variables(value, variables),
        Term::Sequence(sequence) => collect_sequence_bound_variables(sequence, variables),
        Term::Algebraic(term) => collect_algebraic_bound_variables(term, variables),
        Term::ExecutionState(state) => collect_execution_state_bound_variables(state, variables),
        Term::Memory(memory) => collect_memory_bound_variables(memory, variables),
    }
}

fn collect_sequence_bound_variables(sequence: &SequenceTerm, variables: &mut BTreeSet<Variable>) {
    match sequence.node.as_ref() {
        SequenceTermNode::Literal(values) => {
            for index in 0..values.len() {
                if let Some(value) = values.retained_value_ref(index) {
                    collect_expression_value_bound_variables(value, variables);
                } else {
                    collect_program_value_bound_variables(values.get(index).unwrap(), variables);
                }
            }
        }
        SequenceTermNode::Concat(left, right) => {
            collect_sequence_bound_variables(left, variables);
            collect_sequence_bound_variables(right, variables);
        }
    }
}

fn collect_expression_value_bound_variables(
    value: &ExecutionValue,
    variables: &mut BTreeSet<Variable>,
) {
    if let Some((_, view @ MachineOperandView::Shared(_))) = value.machine() {
        visit_machine_operand_scoped_leaves(view, |leaf| {
            collect_scoped_leaf_bound_variables(leaf, variables)
        });
    } else {
        collect_program_value_bound_variables(&value.native(), variables);
    }
}

fn collect_program_value_bound_variables(value: &ProgramValue, variables: &mut BTreeSet<Variable>) {
    match value {
        ProgramValue::PointerInteger(record) => {
            collect_program_value_bound_variables(&record.numeric, variables);
            collect_program_value_bound_variables(
                &ProgramValue::Pointer(*record.pointer.clone()),
                variables,
            );
        }
        ProgramValue::Int8(bits) => collect_bitvector_bound_variables(bits, variables),
        ProgramValue::Bool(bits)
        | ProgramValue::Int16(bits)
        | ProgramValue::Int32(bits)
        | ProgramValue::UInt8(bits)
        | ProgramValue::UInt16(bits)
        | ProgramValue::UInt32(bits)
        | ProgramValue::Int64(bits)
        | ProgramValue::UInt64(bits)
        | ProgramValue::Int128(bits)
        | ProgramValue::UInt128(bits)
        | ProgramValue::Float32(bits)
        | ProgramValue::Float64(bits) => collect_bitvector_bound_variables(bits, variables),
        ProgramValue::Pointer(pointer) => {
            for address in pointer.pointers() {
                collect_pointer_bound_variables(address, variables);
            }
        }
        ProgramValue::Parameter(term) => collect_algebraic_bound_variables(term, variables),
        ProgramValue::Void => {}
    }
}

fn collect_algebraic_value_bound_variables<'a>(
    value: impl Into<ResourceFieldValue<'a>>,
    variables: &mut BTreeSet<Variable>,
) {
    match value.into() {
        ResourceFieldValue::Program(value) => {
            collect_program_value_bound_variables(value, variables)
        }
        ResourceFieldValue::Integer(value) => collect_integer_bound_variables(value, variables),
        ResourceFieldValue::Algebraic(value) => collect_algebraic_bound_variables(value, variables),
    }
}

fn collect_program_expression_bound_variables(
    expression: &ProgramExpression,
    variables: &mut BTreeSet<Variable>,
) {
    match expression {
        ProgramExpression::Value(value) => collect_program_value_bound_variables(value, variables),
        ProgramExpression::Variable(_)
        | ProgramExpression::StringLiteral(_)
        | ProgramExpression::FunctionAddress(_)
        | ProgramExpression::StepResult { .. } => {}
        ProgramExpression::Cast { expression, .. } => {
            collect_program_expression_bound_variables(expression, variables);
        }
        ProgramExpression::Ternary {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_program_expression_bound_variables(condition, variables);
            collect_program_expression_bound_variables(then_branch, variables);
            collect_program_expression_bound_variables(else_branch, variables);
        }
        ProgramExpression::Negate(expression)
        | ProgramExpression::FloatNegate(expression)
        | ProgramExpression::FloatClassification { expression, .. }
        | ProgramExpression::EnumField {
            value: expression, ..
        }
        | ProgramExpression::EnumIs {
            value: expression, ..
        } => {
            collect_program_expression_bound_variables(expression, variables);
        }
        ProgramExpression::EnumConstruct { fields, .. } => {
            for field in fields {
                collect_program_expression_bound_variables(field, variables);
            }
        }
        ProgramExpression::AddressOf(body)
        | ProgramExpression::CheckedObjectAddress(body)
        | ProgramExpression::Not(body)
        | ProgramExpression::Load(body)
        | ProgramExpression::BitwiseNot(body) => {
            collect_program_expression_bound_variables(body, variables)
        }
        ProgramExpression::PointerOffsetBytes { pointer, .. }
        | ProgramExpression::Subobject { pointer, .. }
        | ProgramExpression::TypedLoad { pointer, .. } => {
            collect_program_expression_bound_variables(pointer, variables)
        }
        crate::kernel::binary_c_expression!(left, right) => {
            collect_program_expression_bound_variables(left, variables);
            collect_program_expression_bound_variables(right, variables);
        }
    }
}

pub(in crate::kernel) fn collect_execution_statement_bound_variables(
    statement: &ProgramStatement,
    variables: &mut BTreeSet<Variable>,
) {
    match statement {
        ProgramStatement::ThrowOpaque(_)
        | ProgramStatement::Skip
        | ProgramStatement::EndAutomaticLifetimes { .. }
        | ProgramStatement::Break
        | ProgramStatement::Continue
        | ProgramStatement::Goto { .. }
        | ProgramStatement::DeclareAggregate { .. } => {}

        ProgramStatement::Declare {
            initializer,
            zero_fill,
            ..
        } => {
            for expression in initializer
                .iter()
                .chain(zero_fill.iter().flat_map(ZeroFill::expressions))
            {
                collect_program_expression_bound_variables(expression, variables);
            }
        }
        ProgramStatement::Assign { expression, .. }
        | ProgramStatement::Return(expression)
        | ProgramStatement::Throw(expression)
        | ProgramStatement::Assert {
            condition: expression,
            ..
        }
        | ProgramStatement::LoopTest {
            condition: expression,
            ..
        }
        | ProgramStatement::StepValue { expression, .. } => {
            collect_program_expression_bound_variables(expression, variables)
        }
        ProgramStatement::CallConstruct { arguments, .. }
        | ProgramStatement::Call { arguments, .. }
        | ProgramStatement::CallResult { arguments, .. } => {
            for argument in arguments {
                collect_program_expression_bound_variables(argument, variables);
            }
        }
        ProgramStatement::HeapAllocate { bytes, .. } => {
            collect_program_expression_bound_variables(bytes, variables)
        }
        ProgramStatement::HeapFree { pointer } => {
            collect_program_expression_bound_variables(pointer, variables)
        }
        ProgramStatement::Seq(statements) => {
            for statement in statements.iter() {
                collect_execution_statement_bound_variables(statement, variables);
            }
        }
        ProgramStatement::TryCatchInt32 {
            try_body, handler, ..
        }
        | ProgramStatement::UnwindCleanup {
            body: try_body,
            cleanup: handler,
        } => {
            collect_execution_statement_bound_variables(try_body, variables);
            collect_execution_statement_bound_variables(handler, variables);
        }
        ProgramStatement::Store { pointer, value }
        | ProgramStatement::TypedStore { pointer, value, .. } => {
            collect_program_expression_bound_variables(pointer, variables);
            collect_program_expression_bound_variables(value, variables);
        }
        ProgramStatement::CopyAggregate { target, source, .. }
        | ProgramStatement::InitializeScalarArray { target, source, .. } => {
            collect_program_expression_bound_variables(target, variables);
            collect_program_expression_bound_variables(source, variables);
        }
        ProgramStatement::Update {
            target, operand, ..
        } => {
            collect_program_expression_bound_variables(target, variables);
            collect_program_expression_bound_variables(operand, variables);
        }
        ProgramStatement::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_program_expression_bound_variables(condition, variables);
            collect_execution_statement_bound_variables(then_branch, variables);
            collect_execution_statement_bound_variables(else_branch, variables);
        }
        ProgramStatement::Loop {
            test: loop_test,
            update,
            invariant,
            invariant_checks,
            effect_checks,
            body,
            ..
        } => {
            let condition = loop_test.source_condition();
            let test = loop_test.source_region();
            if let Some(condition) = condition {
                collect_program_expression_bound_variables(condition, variables);
            }
            for proposition in invariant {
                collect_proposition_bound_variables(proposition, variables);
            }
            for check in invariant_checks {
                collect_spec_proposition_bound_variables(check.proposition(), variables);
            }
            for check in effect_checks {
                collect_loop_effect_bound_variables(check.effect(), variables);
            }
            collect_execution_statement_bound_variables(body, variables);
            if let Some(test) = test {
                collect_execution_statement_bound_variables(&test.statement, variables);
            }
            if let Some(update) = update {
                collect_execution_statement_bound_variables(update, variables);
            }
        }
        ProgramStatement::Switch { expression, cases } => {
            collect_program_expression_bound_variables(expression, variables);
            for case in cases {
                collect_execution_statement_bound_variables(&case.body, variables);
            }
        }
    }
}

fn collect_loop_effect_bound_variables(effect: &LoopEffect, variables: &mut BTreeSet<Variable>) {
    let LoopEffect::Mutable(segments) = effect;
    for segment in segments {
        collect_memory_segment_bound_variables(segment, variables);
    }
}

fn collect_memory_segment_bound_variables(
    segment: &MemorySegment,
    variables: &mut BTreeSet<Variable>,
) {
    collect_program_expression_bound_variables(&segment.base, variables);
    collect_program_expression_bound_variables(&segment.start, variables);
    collect_program_expression_bound_variables(&segment.end, variables);
    if let Some(guard) = segment.guard() {
        collect_spec_proposition_bound_variables(guard, variables);
    }
}

pub(in crate::kernel) fn collect_execution_state_bound_variables(
    state: &ExecutionState,
    variables: &mut BTreeSet<Variable>,
) {
    if let Some(destination) = &state.aggregate_destination {
        collect_pointer_bound_variables(&destination.pointer, variables);
    }
    for binding in state.locals.bindings.values() {
        if let LocalBinding::Object { value, .. } = binding {
            collect_expression_value_bound_variables(value, variables);
        }
    }
    collect_memory_bound_variables(&state.memory, variables);
    for fact in state.resources.facts() {
        collect_resource_bound_variables(fact.resource(), variables);
    }
}

pub(in crate::kernel) fn collect_statement_outcome_bound_variables(
    outcome: &StatementOutcome,
    variables: &mut BTreeSet<Variable>,
) {
    match outcome {
        StatementOutcome::Normal(state)
        | StatementOutcome::LoopTestFalse(state)
        | StatementOutcome::Break(state)
        | StatementOutcome::Continue(state)
        | StatementOutcome::Jump { state, .. } => {
            collect_execution_state_bound_variables(state, variables)
        }
        StatementOutcome::Return { value, state } | StatementOutcome::Throw { value, state } => {
            collect_expression_value_bound_variables(value, variables);
            collect_execution_state_bound_variables(state, variables);
        }
        StatementOutcome::VerificationDiverges
        | StatementOutcome::UndefinedBehavior(_)
        | StatementOutcome::RuntimeError(_) => {}
    }
}

fn collect_function_outcome_bound_variables(
    outcome: &FunctionOutcome,
    variables: &mut BTreeSet<Variable>,
) {
    match outcome {
        FunctionOutcome::Return { value, state } | FunctionOutcome::Throw { value, state } => {
            collect_expression_value_bound_variables(value, variables);
            collect_execution_state_bound_variables(state, variables);
        }
        FunctionOutcome::VerificationDiverges
        | FunctionOutcome::UndefinedBehavior(_)
        | FunctionOutcome::RuntimeError(_) => {}
    }
}

fn collect_spec_proposition_bound_variables(
    proposition: &SpecProposition,
    variables: &mut BTreeSet<Variable>,
) {
    match proposition {
        SpecProposition::ForAllMachineInteger { variable, body, .. }
        | SpecProposition::ForAllInt32 { variable, body, .. }
        | SpecProposition::ForAllPointer { variable, body, .. }
        | SpecProposition::ExistsMachineInteger { variable, body, .. }
        | SpecProposition::ExistsInt32 { variable, body, .. }
        | SpecProposition::ExistsPointer { variable, body, .. } => {
            variables.insert(*variable);
            collect_spec_proposition_bound_variables(body, variables);
        }
        SpecProposition::And(left, right)
        | SpecProposition::Or(left, right)
        | SpecProposition::Implies(left, right) => {
            collect_spec_proposition_bound_variables(left, variables);
            collect_spec_proposition_bound_variables(right, variables);
        }
        SpecProposition::Not(body) => collect_spec_proposition_bound_variables(body, variables),
        _ => {}
    }
}

fn collect_resource_spec_bound_variables(
    resource: &ResourceSpec,
    variables: &mut BTreeSet<Variable>,
) {
    match resource.term() {
        ResourceTerm::Instance { resource, .. } => {
            collect_resource_term_bound_variables(resource, variables)
        }
        ResourceTerm::PopulationAuthority { protected, .. } => {
            collect_resource_spec_bound_variables(&protected.resource, variables)
        }
        ResourceTerm::MutexGuard { mutex, .. } | ResourceTerm::MutexLive { mutex, .. } => {
            collect_program_expression_bound_variables(mutex, variables)
        }
        ResourceTerm::MutexUse {
            mutex, protected, ..
        } => {
            collect_program_expression_bound_variables(mutex, variables);
            if let Some(protected) = protected {
                collect_resource_spec_bound_variables(&protected.resource, variables);
            }
        }
        ResourceTerm::Publication { flag, payload, .. } => {
            collect_program_expression_bound_variables(flag, variables);
            collect_resource_spec_bound_variables(&payload.resource, variables);
        }
        ResourceTerm::Memory(segment) => collect_memory_segment_bound_variables(segment, variables),
        ResourceTerm::Composite { arguments, .. } | ResourceTerm::Token { arguments, .. } => {
            for argument in arguments {
                collect_program_expression_bound_variables(argument, variables);
            }
        }
        ResourceTerm::Iterated(spec) => {
            for expression in spec.expressions() {
                collect_program_expression_bound_variables(expression, variables);
            }
        }
    }
    if let ResourceQuantity::Count(quantity) = resource.quantity() {
        collect_program_expression_bound_variables(quantity, variables);
    }
}

fn collect_resource_term_bound_variables(
    resource: &ResourceTerm,
    variables: &mut BTreeSet<Variable>,
) {
    match resource {
        ResourceTerm::Instance { resource, .. } => {
            collect_resource_term_bound_variables(resource, variables)
        }
        ResourceTerm::PopulationAuthority { protected, .. } => {
            collect_resource_spec_bound_variables(&protected.resource, variables)
        }
        ResourceTerm::MutexGuard { mutex, .. } | ResourceTerm::MutexLive { mutex, .. } => {
            collect_program_expression_bound_variables(mutex, variables)
        }
        ResourceTerm::MutexUse {
            mutex, protected, ..
        } => {
            collect_program_expression_bound_variables(mutex, variables);
            if let Some(protected) = protected {
                collect_resource_spec_bound_variables(&protected.resource, variables);
            }
        }
        ResourceTerm::Publication { flag, payload, .. } => {
            collect_program_expression_bound_variables(flag, variables);
            collect_resource_spec_bound_variables(&payload.resource, variables);
        }
        ResourceTerm::Memory(segment) => collect_memory_segment_bound_variables(segment, variables),
        ResourceTerm::Composite { arguments, .. } | ResourceTerm::Token { arguments, .. } => {
            for argument in arguments {
                collect_program_expression_bound_variables(argument, variables);
            }
        }
        ResourceTerm::Iterated(spec) => {
            for expression in spec.expressions() {
                collect_program_expression_bound_variables(expression, variables);
            }
        }
    }
}

pub(in crate::kernel) fn collect_program_function_bound_variables(
    function: &ProgramFunction,
    variables: &mut BTreeSet<Variable>,
) {
    collect_program_function_contract_interface_bound_variables(
        function.contract_interface(),
        variables,
    );
    collect_execution_statement_bound_variables(function.body(), variables);
}

/// Collects only bound variables in the body-independent contract interface.
/// This is the companion to the bitvector collector used for named callback
/// contracts; no template statement or storage is traversed.
pub(in crate::kernel) fn collect_program_function_contract_interface_bound_variables(
    interface: &FunctionContractInterface,
    variables: &mut BTreeSet<Variable>,
) {
    for resource in interface
        .proof_parameters()
        .iter()
        .chain(interface.resource_requires())
        .chain(interface.resource_ensures())
        .chain(interface.resource_constructors())
    {
        collect_resource_spec_bound_variables(resource, variables);
    }
    for proposition in interface
        .contract_requires()
        .iter()
        .chain(interface.contract_ensures())
        .chain(interface.exceptional_ensures())
    {
        collect_spec_proposition_bound_variables(proposition, variables);
    }
    for segment in interface.contract_mutable() {
        collect_memory_segment_bound_variables(segment, variables);
    }
}

fn collect_program_function_specification_bound_variables(
    specification: &FunctionSpecification,
    variables: &mut BTreeSet<Variable>,
) {
    collect_execution_state_bound_variables(specification.state(), variables);
    for argument in specification.arguments() {
        collect_program_expression_bound_variables(argument, variables);
    }
    for requirement in specification.requires() {
        collect_proposition_bound_variables(requirement, variables);
    }
    collect_function_outcome_bound_variables(specification.outcome(), variables);
}

fn collect_expression_outcome_bound_variables(
    outcome: &ExpressionOutcome<StoredProgramValue>,
    variables: &mut BTreeSet<Variable>,
) {
    if let ExpressionOutcome::Value(value) = outcome {
        collect_expression_value_bound_variables(value.value(), variables);
    }
}

fn collect_pointer_bound_variables(pointer: &Address, variables: &mut BTreeSet<Variable>) {
    match &pointer.base {
        AddressBase::PureFunctionApplication(_) => {
            collect_proposition_capture_variables(
                &Proposition::condition_is(
                    ConditionTerm::AddressEqual(
                        Box::new(pointer.clone()),
                        Box::new(pointer.clone()),
                    ),
                    true,
                ),
                variables,
            );
        }
        AddressBase::FunctionSymbolic(variable)
        | AddressBase::Symbolic(variable)
        | AddressBase::ExternalObject(variable) => {
            variables.insert(*variable);
        }
        AddressBase::ContractResult
        | AddressBase::ContractException
        | AddressBase::AggregateReturn { .. }
        | AddressBase::StaticObject { .. }
        | AddressBase::AutomaticLocal { .. }
        | AddressBase::ReferenceCarrier { .. }
        | AddressBase::Concrete(_)
        | AddressBase::StringLiteral { .. }
        | AddressBase::Function(_)
        | AddressBase::ExternalArgument
        | AddressBase::LoadedPointer(_)
        | AddressBase::Heap(_)
        | AddressBase::Temporary(_) => {}
    }
    collect_pointer_offset_bound_variables(&pointer.offset, variables);
}

#[cfg(test)]
thread_local! {
    static MEMORY_BOUND_CELL_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// A debug cross-check's own whole collection is not counted.
#[cfg(test)]
fn count_memory_bound_cell_visit() {
    if !crate::instrumentation::in_uncharged_debug_check() {
        MEMORY_BOUND_CELL_VISITS.with(|count| count.set(count.get() + 1));
    }
}

/// The memory cells bound-variable collection visited on this thread so far.
#[cfg(test)]
pub(crate) fn memory_bound_cell_visits() -> usize {
    MEMORY_BOUND_CELL_VISITS.with(std::cell::Cell::get)
}

fn collect_memory_bound_variables(memory: &SymbolicMemory, variables: &mut BTreeSet<Variable>) {
    // While a fact set reserves a fact's variables, an interned state's
    // bound variables are walked once: they depend on the state alone,
    // and the set already reserves those of every state walked before.
    // A state derived from one already walked adds only the bound
    // variables of the entries it changed since.
    if let Some(shared) = crate::kernel::primitives::interned_storage_of(memory) {
        if crate::kernel::reasoning::variable_collection::bound_state_already_reserved(
            shared.arena_id(),
        ) {
            return;
        }
        if let Some(base) =
            crate::kernel::reasoning::variable_collection::bound_reserved_base(&shared)
        {
            // The whole walk this replaces charged nothing; the diffs it
            // reads charge per change, so they run uncharged.
            crate::instrumentation::without_charging(|| {
                collect_memory_bound_variables_entering(base.memory(), memory, variables);
            });
            return;
        }
    }
    for pointer in memory
        .heap
        .uninitialized_objects
        .keys()
        .chain(memory.heap.initialized.as_map().keys())
    {
        collect_pointer_bound_variables(pointer, variables);
    }
    for (pointer, byte) in memory.heap.initialized.partial_map().iter() {
        collect_pointer_bound_variables(pointer, variables);
        if let Some(value) = &byte.value {
            collect_program_value_bound_variables(value, variables);
        }
    }
    for contents in memory.blocks.values() {
        collect_bitvector_bound_variables(contents.size(), variables);
    }
    for (pointer, value) in memory.cells.concrete().iter() {
        #[cfg(test)]
        count_memory_bound_cell_visit();
        collect_pointer_bound_variables(pointer, variables);
        // The retained word fragment contains no binders.
        if !value.is_retained_word() {
            collect_program_value_bound_variables(value.native(), variables);
        }
    }
    // A run's slots are named uniformly per spelling shape wherever
    // `run_shape_representatives` says so, and then mention the same bound
    // variables as their shape's representative (a slot's own load variable
    // is never a binder); otherwise every slot is visited.
    for run in memory.cells.runs() {
        let slots = crate::kernel::reasoning::memory_resolution::run_shape_representatives(run)
            .unwrap_or_else(|| run.live_indexes().collect());
        for index in slots {
            collect_pointer_bound_variables(&run.slot_pointer(index), variables);
            collect_program_value_bound_variables(&run.value(index), variables);
        }
    }
}

/// [`collect_memory_bound_variables`] over only the entries `memory` holds
/// differently from `base`: with `base`'s bound variables these include
/// all of `memory`'s, and each is one of `memory`'s.
fn collect_memory_bound_variables_entering(
    base: &SymbolicMemory,
    memory: &SymbolicMemory,
    variables: &mut BTreeSet<Variable>,
) {
    for (before, after) in [
        (
            &base.heap.uninitialized_objects,
            &memory.heap.uninitialized_objects,
        ),
        (
            base.heap.initialized.as_map(),
            memory.heap.initialized.as_map(),
        ),
    ] {
        for change in before.diff(after) {
            let pointer = change.key();
            if after.contains_key(pointer) {
                collect_pointer_bound_variables(pointer, variables);
            }
        }
    }
    let before = base.heap.initialized.partial_map();
    let after = memory.heap.initialized.partial_map();
    for change in before.diff(after) {
        let pointer = change.key();
        if let Some(byte) = after.get(pointer) {
            collect_pointer_bound_variables(pointer, variables);
            if let Some(value) = &byte.value {
                collect_program_value_bound_variables(value, variables);
            }
        }
    }
    for change in base.blocks.diff(&memory.blocks) {
        if let Some(contents) = memory.blocks.get(change.key()) {
            collect_bitvector_bound_variables(contents.size(), variables);
        }
    }
    for change in base.cells.concrete().diff(memory.cells.concrete()) {
        let pointer = change.key();
        if let Some(value) = memory.cells.concrete().get(pointer) {
            #[cfg(test)]
            count_memory_bound_cell_visit();
            collect_pointer_bound_variables(pointer, variables);
            // The retained word fragment contains no binders.
            if !value.is_retained_word() {
                collect_program_value_bound_variables(value.native(), variables);
            }
        }
    }
    for (_, after) in base.cells.run_diff(&memory.cells) {
        let Some(run) = after else {
            continue;
        };
        let slots = crate::kernel::reasoning::memory_resolution::run_shape_representatives(run)
            .unwrap_or_else(|| run.live_indexes().collect());
        for index in slots {
            collect_pointer_bound_variables(&run.slot_pointer(index), variables);
            collect_program_value_bound_variables(&run.value(index), variables);
        }
    }
}

fn collect_resource_bound_variables(resource: &Resource, variables: &mut BTreeSet<Variable>) {
    match resource {
        Resource::Star(pair) => {
            collect_resource_bound_variables(&pair.0, variables);
            collect_resource_bound_variables(&pair.1, variables);
        }
        Resource::Emp | Resource::Footprint(_) => {}
        Resource::Parameter(v) => {
            variables.insert(*v);
        }
        Resource::PopulationAuthority(description) => {
            description
                .visit_values(|value| collect_algebraic_value_bound_variables(value, variables));
        }
        Resource::MutexUse(identity) => {
            if let Some(p) = &identity.protected {
                p.visit_values(|v| collect_algebraic_value_bound_variables(v, variables));
            }
            if identity.binding.is_none() {
                collect_pointer_bound_variables(&identity.mutex, variables);
            }
        }
        Resource::ConditionalMutexGuard(carrier) => {
            collect_condition_bound_variables(carrier.condition(), variables)
        }
        Resource::MutexGuard(identity) | Resource::MutexLive(identity) => {
            if identity.epoch.is_none() {
                let pointer = &identity.mutex;
                collect_pointer_bound_variables(pointer, variables);
            }
        }
        Resource::Publication(right) => {
            right
                .payload
                .visit_values(|v| collect_algebraic_value_bound_variables(v, variables));
            collect_pointer_bound_variables(&right.flag, variables);
            if let Some(value) = &right.observed {
                collect_expression_value_bound_variables(value.value(), variables);
            }
        }
        Resource::Instance(instance) => {
            for value in instance.arguments.iter() {
                collect_algebraic_value_bound_variables(value, variables);
            }
            for index in 0..instance.fields.len() {
                if let Some(value) = instance.fields.retained_program(index) {
                    collect_expression_value_bound_variables(value, variables);
                } else {
                    collect_algebraic_value_bound_variables(
                        instance.fields.get(index).expect("field index"),
                        variables,
                    );
                }
            }
            crate::kernel::ResourceReference::visit_captured_values(
                instance.resource_arguments(),
                |value| {
                    collect_algebraic_value_bound_variables(value, variables);
                },
            );
        }

        Resource::Memory(range) => {
            collect_pointer_bound_variables(&range.base, variables);
            collect_bitvector_bound_variables(range.bound_terms().0, variables);
            collect_bitvector_bound_variables(range.bound_terms().1, variables);
        }
        Resource::Iterated(iterated) => {
            for pointer in iterated.pointers() {
                collect_pointer_bound_variables(pointer, variables);
            }
            for term in iterated.terms() {
                collect_bitvector_bound_variables(term, variables);
            }
        }
        Resource::Composite { arguments, .. } | Resource::Token { arguments, .. } => {
            for argument in arguments.iter() {
                collect_algebraic_value_bound_variables(argument, variables);
            }
        }
    }
}

/// Collects identities introduced by `RangeFold` binders inside a term.
/// `collect_bitvector_variables` intentionally removes those identities from
/// its result because they are not free; freshness construction needs the
/// bound identities as well so a logical or fold binder cannot reuse one.
fn collect_scoped_leaf_bound_variables(
    leaf: MachineOperandView<'_>,
    variables: &mut BTreeSet<Variable>,
) {
    if let MachineOperandView::Shared(root) = leaf
        && matches!(root.node(), KernelTermNode::FloatConvert { .. })
    {
        // This freshness policy includes state contents as well as binders.
        // Keep its selected native boundary; the ordinary free-variable reader
        // intentionally has different scope and memory rules.
        collect_bitvector_bound_variables(
            &crate::kernel::KernelTermExport::machine(root).expect("float conversion"),
            variables,
        );
        return;
    }
    if let MachineOperandView::Shared(root) = leaf
        && let KernelTermNode::Fold(fold) = root.node()
    {
        variables.insert(fold.accumulator);
        variables.insert(fold.item);
        for child in &fold.arguments {
            visit_machine_operand_scoped_leaves(MachineOperandView::Shared(child), |leaf| {
                collect_scoped_leaf_bound_variables(leaf, variables)
            });
        }
    } else if let MachineOperandView::Shared(root) = leaf
        && let KernelTermNode::Match(matched) = root.node()
    {
        let mut export = crate::kernel::KernelTermExport::default();
        if let PureFunctionArgument::Algebraic(scrutinee) = export
            .argument(&matched.arguments[0])
            .expect("match scrutinee")
        {
            collect_algebraic_bound_variables(&scrutinee, variables);
        }
        for arm in &matched.arms {
            for binding in arm
                .export_bindings(&mut export)
                .expect("match declarations")
            {
                collect_algebraic_value_bound_variables(&binding, variables);
            }
        }
        for body in &matched.arguments[1..] {
            visit_machine_operand_scoped_leaves(MachineOperandView::Shared(body), |leaf| {
                collect_scoped_leaf_bound_variables(leaf, variables)
            });
        }
    } else {
        collect_bitvector_bound_variables(
            &leaf.read_source().expect("native scoped leaf"),
            variables,
        );
    }
}

fn collect_bitvector_bound_variables(term: &MachineTerm, variables: &mut BTreeSet<Variable>) {
    match term {
        MachineTerm::ThreadHandle(_) => {}
        bits32_constant!(_) | MachineTerm::Variable(_) => {}
        crate::kernel::binary_bitvector32_term!(left, right) => {
            collect_bitvector_bound_variables(left, variables);
            collect_bitvector_bound_variables(right, variables);
        }
        unary_term!(Int32, BitwiseNot, value)
        | MachineTerm::Float32Negate(value)
        | MachineTerm::Float64Negate(value) => {
            collect_bitvector_bound_variables(value, variables);
        }
        MachineTerm::BoolCast { value, .. } => collect_condition_bound_variables(value, variables),
        MachineTerm::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_bound_variables(condition, variables);
            collect_bitvector_bound_variables(then_term, variables);
            collect_bitvector_bound_variables(else_term, variables);
        }
        MachineTerm::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            collect_bitvector_bound_variables(start, variables);
            collect_bitvector_bound_variables(end, variables);
            collect_bitvector_bound_variables(initial, variables);
            variables.insert(*accumulator);
            variables.insert(*item);
            collect_bitvector_bound_variables(body, variables);
        }
        MachineTerm::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                collect_bitvector_bound_variables(argument, variables);
            }
        }
        MachineTerm::ClickFunctionApplication { arguments, .. } => {
            for argument in arguments {
                match argument {
                    PureFunctionArgument::SharedMachine(value) => {
                        visit_machine_operand_scoped_leaves(value.operand_view(), |leaf| {
                            collect_scoped_leaf_bound_variables(leaf, variables);
                        });
                    }
                    PureFunctionArgument::Value(value) => {
                        collect_program_value_bound_variables(value, variables)
                    }
                    PureFunctionArgument::Algebraic(term) => {
                        collect_algebraic_bound_variables(term, variables)
                    }
                    PureFunctionArgument::Integer(_) => {}
                    PureFunctionArgument::ArrayRef {
                        memory, pointer, ..
                    } => {
                        collect_memory_bound_variables(memory, variables);
                        collect_program_value_bound_variables(pointer, variables);
                    }
                }
            }
        }
        MachineTerm::AlgebraicMatch { scrutinee, arms } => {
            collect_algebraic_bound_variables(scrutinee, variables);
            for arm in arms {
                for binding in &arm.bindings {
                    collect_algebraic_value_bound_variables(binding, variables);
                }
                collect_bitvector_bound_variables(&arm.body, variables);
            }
        }
        MachineTerm::MemoryLoad(memory, pointer, _) => {
            // SymbolicMemory states are immutable kernel values; their free
            // variable collector remains the source of truth for state
            // contents, while the pointer can contain nested fold terms.
            collect_memory_bitvector_variables(memory.memory(), variables);
            collect_pointer_offset_bound_variables(&pointer.offset, variables);
        }
        MachineTerm::IntegerAddress(pointer, _) => {
            collect_pointer_offset_bound_variables(&pointer.offset, variables);
        }
        MachineTerm::IntegerToMachine { value, .. } => {
            collect_integer_bound_variables(value, variables);
        }
        int64_constant!(_) | uint64_constant!(_) | native_constant!(_, _) => {}
        cast_term!(Int64From32, value)
        | MachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            value,
            ..
        }
        | cast_term!(UInt64From32, value)
        | cast_term!(UInt32From64, value)
        | cast_term!(Int64FromUInt32, value)
        | cast_term!(UInt64FromInt32, value)
        | cast_term!(UInt64FromInt64, value)
        | MachineTerm::Unary { operand: value, .. } => {
            collect_bitvector_bound_variables(value, variables)
        }
        crate::kernel::binary_wide_term!(left, right)
        | MachineTerm::Float32Binary { left, right, .. }
        | MachineTerm::Float64Binary { left, right, .. } => {
            collect_bitvector_bound_variables(left, variables);
            collect_bitvector_bound_variables(right, variables);
        }
    }
}

fn collect_algebraic_bound_variables(term: &AlgebraicTerm, variables: &mut BTreeSet<Variable>) {
    match &term.node {
        AlgebraicTermNode::Variable(variable) => {
            // Algebraic variables share the kernel identity namespace with
            // scalar variables and binders. Freshness must reserve them too.
            variables.insert(*variable);
        }
        AlgebraicTermNode::MemoryLoad {
            point: memory,
            pointer,
        } => {
            collect_algebraic_value_bound_variables(
                &AlgebraicTermNode::memory_load_carrier_value(memory.shared_memory(), pointer),
                variables,
            );
        }
        AlgebraicTermNode::Constructor { fields, .. } => {
            for field in fields {
                collect_algebraic_value_bound_variables(field, variables);
            }
        }
        AlgebraicTermNode::Match { scrutinee, arms } => {
            collect_algebraic_bound_variables(scrutinee, variables);
            for arm in arms {
                for binding in &arm.bindings {
                    collect_algebraic_value_bound_variables(binding, variables);
                }
                collect_algebraic_bound_variables(&arm.body, variables);
            }
        }
        AlgebraicTermNode::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                match argument {
                    PureFunctionArgument::SharedMachine(value) => {
                        visit_machine_operand_scoped_leaves(value.operand_view(), |leaf| {
                            collect_scoped_leaf_bound_variables(leaf, variables);
                        });
                    }
                    PureFunctionArgument::Value(value) => {
                        collect_program_value_bound_variables(value, variables)
                    }
                    PureFunctionArgument::Algebraic(term) => {
                        collect_algebraic_bound_variables(term, variables)
                    }
                    PureFunctionArgument::Integer(_) => {}
                    PureFunctionArgument::ArrayRef {
                        memory, pointer, ..
                    } => {
                        collect_memory_bound_variables(memory, variables);
                        collect_program_value_bound_variables(pointer, variables);
                    }
                }
            }
        }
        AlgebraicTermNode::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_bound_variables(condition, variables);
            collect_algebraic_bound_variables(then_term, variables);
            collect_algebraic_bound_variables(else_term, variables);
        }
    }
}

fn collect_condition_bound_variables(
    condition: &ConditionTerm,
    variables: &mut BTreeSet<Variable>,
) {
    match condition {
        ConditionTerm::PointerEqual(left, right) => {
            for pointer in left.pointers().chain(right.pointers()) {
                collect_pointer_offset_bound_variables(&pointer.offset, variables);
            }
        }

        ConditionTerm::AlgebraicEqual(left, right) => {
            left.for_each_machine_operand(|view| {
                visit_machine_operand_scoped_leaves(view, |term| {
                    collect_scoped_leaf_bound_variables(term, variables)
                })
            });
            right.for_each_machine_operand(|view| {
                visit_machine_operand_scoped_leaves(view, |term| {
                    collect_scoped_leaf_bound_variables(term, variables)
                })
            });
        }
        ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => {}
        crate::kernel::binary_bitvector_condition!(left, right) => {
            collect_bitvector_bound_variables(left, variables);
            collect_bitvector_bound_variables(right, variables);
        }
        crate::kernel::integer_comparison_condition!(left, right) => {
            collect_integer_bound_variables(left, variables);
            collect_integer_bound_variables(right, variables);
        }
        ConditionTerm::Float32(float_condition) | ConditionTerm::Float64(float_condition) => {
            float_condition
                .for_each_bitvector_term(|term| collect_bitvector_bound_variables(term, variables));
        }
        ConditionTerm::AddressOffsetEqual(left, right) => {
            collect_pointer_offset_bound_variables(left, variables);
            collect_pointer_offset_bound_variables(right, variables);
        }
        ConditionTerm::AddressEqual(left, right) => {
            collect_pointer_offset_bound_variables(&left.offset, variables);
            collect_pointer_offset_bound_variables(&right.offset, variables);
        }
        ConditionTerm::BoolApplication(application) => {
            for argument in application.arguments() {
                match argument {
                    PureFunctionArgument::SharedMachine(value) => {
                        visit_machine_operand_scoped_leaves(value.operand_view(), |leaf| {
                            collect_scoped_leaf_bound_variables(leaf, variables);
                        });
                    }
                    PureFunctionArgument::Value(value) => {
                        collect_program_value_bound_variables(value, variables)
                    }
                    PureFunctionArgument::Algebraic(term) => {
                        collect_algebraic_bound_variables(term, variables)
                    }
                    PureFunctionArgument::Integer(_) => {}
                    PureFunctionArgument::ArrayRef {
                        memory, pointer, ..
                    } => {
                        collect_memory_bound_variables(memory, variables);
                        collect_program_value_bound_variables(pointer, variables);
                    }
                }
            }
        }
        ConditionTerm::BoolIf {
            condition,
            then_condition,
            else_condition,
        } => {
            for condition in [condition, then_condition, else_condition] {
                collect_condition_bound_variables(condition, variables);
            }
        }
        ConditionTerm::BoolEqual(left, right) => {
            collect_condition_bound_variables(left, variables);
            collect_condition_bound_variables(right, variables);
        }
        ConditionTerm::BoolLoad(memory, pointer) => {
            collect_memory_bitvector_variables(memory.memory(), variables);
            collect_pointer_offset_bound_variables(&pointer.offset, variables);
        }
    }
}

fn collect_pointer_offset_bound_variables(
    offset: &AddressOffset,
    variables: &mut BTreeSet<Variable>,
) {
    offset.for_each_scaled_operand(|value| {
        visit_machine_operand_scoped_leaves(value.operand_view(), |leaf| {
            collect_scoped_leaf_bound_variables(leaf, variables)
        })
    });
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_term(
    term: &Term,
    from: Variable,
    to: &MachineTerm,
) -> Term {
    match term {
        Term::Condition(condition) => Term::Condition(substitute_bitvector_variable_in_condition(
            condition, from, to,
        )),
        Term::Bitvector32(bits) => Term::Bitvector32(substitute_bitvector_variable(bits, from, to)),
        // Variable identities are shared by all logical sorts, but a
        // machine substitution must never rewrite an Integer variable with a
        // machine term. Integer binders use the dedicated function below.
        Term::Integer(integer) => {
            Term::Integer(substitute_bitvector_variable_in_integer(integer, from, to))
        }
        Term::PointerOffset(offset) => Term::PointerOffset(
            substitute_bitvector_variable_in_pointer_offset(offset, from, to),
        ),
        Term::ProgramValue(value) => Term::ProgramValue(
            substitute_bitvector_variable_in_program_value(value, from, to),
        ),
        Term::Sequence(sequence) => Term::Sequence(substitute_bitvector_variable_in_sequence(
            sequence, from, to,
        )),
        Term::Algebraic(term) => Term::Algebraic(AlgebraicTerm {
            algebraic_type: term.algebraic_type.clone(),
            node: match &term.node {
                AlgebraicTermNode::Variable(variable) => AlgebraicTermNode::Variable(*variable),
                AlgebraicTermNode::MemoryLoad {
                    point: memory,
                    pointer,
                } => {
                    match substitute_bitvector_variable_in_algebraic_value(
                        &AlgebraicTermNode::memory_load_carrier_value(
                            memory.shared_memory(),
                            pointer,
                        ),
                        from,
                        to,
                    ) {
                        AlgebraicValue::Program(value) => {
                            AlgebraicTermNode::memory_load_from_carrier(&value)
                                .unwrap_or_else(|| term.node.clone())
                        }
                        _ => term.node.clone(),
                    }
                }
                AlgebraicTermNode::Constructor { variant, fields } => {
                    AlgebraicTermNode::Constructor {
                        variant: variant.clone(),
                        fields: fields
                            .iter()
                            .map(|field| {
                                substitute_bitvector_variable_in_algebraic_value(field, from, to)
                            })
                            .collect(),
                    }
                }
                AlgebraicTermNode::Match { scrutinee, arms } => AlgebraicTermNode::Match {
                    scrutinee: Box::new(substitute_bitvector_variable_in_algebraic_term(
                        scrutinee, from, to,
                    )),
                    arms: arms
                        .iter()
                        .map(|arm| AlgebraicResultMatchArm {
                            binding_names: arm.binding_names.clone(),
                            variant: arm.variant.clone(),
                            bindings: arm
                                .bindings
                                .iter()
                                .map(|binding| {
                                    substitute_bitvector_variable_in_algebraic_value(
                                        binding, from, to,
                                    )
                                })
                                .collect(),
                            body: substitute_bitvector_variable_in_algebraic_term(
                                &arm.body, from, to,
                            ),
                        })
                        .collect(),
                },
                AlgebraicTermNode::PureFunctionApplication { name, arguments } => {
                    AlgebraicTermNode::PureFunctionApplication {
                        name: name.clone(),
                        arguments: arguments
                            .iter()
                            .map(|argument| {
                                substitute_bitvector_variable_in_pure_function_argument(
                                    argument, from, to,
                                )
                            })
                            .collect(),
                    }
                }
                AlgebraicTermNode::If {
                    condition,
                    then_term,
                    else_term,
                } => AlgebraicTermNode::If {
                    condition: Box::new(substitute_bitvector_variable_in_condition(
                        condition, from, to,
                    )),
                    then_term: Box::new(substitute_bitvector_variable_in_algebraic_term(
                        then_term, from, to,
                    )),
                    else_term: Box::new(substitute_bitvector_variable_in_algebraic_term(
                        else_term, from, to,
                    )),
                },
            },
        }),
        Term::Memory(memory) => {
            Term::Memory(substitute_bitvector_variable_in_memory(memory, from, to))
        }
        Term::ExecutionState(state) => Term::ExecutionState(Box::new(
            substitute_bitvector_variable_in_execution_state(state, from, to),
        )),
    }
}

fn substitute_bitvector_variable_in_integer(
    term: &IntegerTerm,
    from: Variable,
    to: &MachineTerm,
) -> IntegerTerm {
    match substitute_bitvector_variable_in_integer_checked(term, from, to) {
        Ok(result) => result,
        Err(error) => panic!("integer substitution refused: {error}"),
    }
}

fn substitute_bitvector_variable_in_integer_checked(
    term: &IntegerTerm,
    from: Variable,
    to: &MachineTerm,
) -> Result<IntegerTerm, IntegerPureSubstitutionError> {
    substitute_bitvector_variable_in_integer_checked_with_mode(term, from, to, false)
}

fn substitute_bitvector_variable_in_integer_checked_with_registered_loads(
    term: &IntegerTerm,
    from: Variable,
    to: &MachineTerm,
) -> Result<IntegerTerm, IntegerPureSubstitutionError> {
    substitute_bitvector_variable_in_integer_checked_with_mode(term, from, to, true)
}

fn substitute_bitvector_variable_in_integer_checked_with_mode(
    term: &IntegerTerm,
    from: Variable,
    to: &MachineTerm,
    resolve_registered_loads: bool,
) -> Result<IntegerTerm, IntegerPureSubstitutionError> {
    let source = MachineTerm::Variable(from);
    let mut rewrite =
        crate::kernel::proof::term_rewrite::TermRewrite::for_bits_checked(&source, to);
    if resolve_registered_loads {
        rewrite.enable_registered_load_resolution();
    }
    let result = match rewrite.term(&Term::Integer(term.clone())) {
        Term::Integer(result) => result,
        _ => unreachable!(),
    };
    integer_substitution_refusal(rewrite.refusal())?;
    Ok(result)
}

pub(in crate::kernel) fn collect_integer_bound_variables(
    term: &IntegerTerm,
    variables: &mut BTreeSet<Variable>,
) {
    let mut seen = BTreeSet::new();
    collect_integer_bound_variables_seen(term, variables, &mut seen);
}

fn collect_integer_bound_variables_seen(
    term: &IntegerTerm,
    variables: &mut BTreeSet<Variable>,
    seen: &mut BTreeSet<u64>,
) {
    match term {
        IntegerTerm::Constant(_) | IntegerTerm::Machine(_) => {}
        IntegerTerm::PureFunctionApplication(application) => {
            for argument in application.arguments() {
                if let PureFunctionArgument::Integer(value) = argument
                    && seen.insert(value.id())
                {
                    collect_integer_bound_variables_seen(value, variables, seen);
                }
            }
        }
        IntegerTerm::Variable(variable) => {
            variables.insert(*variable);
        }
        IntegerTerm::Negate(value) => {
            if seen.insert(value.id()) {
                collect_integer_bound_variables_seen(value, variables, seen);
            }
        }
        crate::kernel::binary_integer_term!(left, right) => {
            if seen.insert(left.id()) {
                collect_integer_bound_variables_seen(left, variables, seen);
            }
            if seen.insert(right.id()) {
                collect_integer_bound_variables_seen(right, variables, seen);
            }
        }
        IntegerTerm::AlgebraicMatch { .. } => {
            // The algebraic scrutinee and arm declarations can carry C or
            // Integer expressions; use the established carrier-aware walker
            // for this shared namespace instead of dropping either side.
            crate::kernel::prelude::collect_integer_variables(term, variables);
        }
        IntegerTerm::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_bound_variables(condition, variables);
            if seen.insert(then_term.id()) {
                collect_integer_bound_variables_seen(then_term, variables, seen);
            }
            if seen.insert(else_term.id()) {
                collect_integer_bound_variables_seen(else_term, variables, seen);
            }
        }
        IntegerTerm::RangeFold {
            index,
            initial,
            accumulator,
            item,
            body,
        } => {
            match index {
                crate::kernel::IntegerRangeFoldIndex::Int32 { start, end }
                | crate::kernel::IntegerRangeFoldIndex::UInt64 { start, end } => {
                    collect_machine_bitvector_variables(start.machine_operand(), variables);
                    collect_machine_bitvector_variables(end.machine_operand(), variables);
                }
                crate::kernel::IntegerRangeFoldIndex::Integer { start, end } => {
                    collect_integer_bound_variables_seen(start, variables, seen);
                    collect_integer_bound_variables_seen(end, variables, seen);
                }
            }
            collect_integer_bound_variables_seen(initial, variables, seen);
            let mut body_variables = BTreeSet::new();
            collect_integer_bound_variables_seen(body, &mut body_variables, &mut BTreeSet::new());
            body_variables.remove(accumulator);
            body_variables.remove(item);
            variables.extend(body_variables);
        }
    }
}

/// The proposition fragment accepted by checked mathematical-integer
/// instantiation.  Integer binders are deliberately kept separate from the
/// machine and resource proposition carriers: cloning an unsupported carrier
/// here would make a proof object appear instantiated while leaving an
/// occurrence of the old variable behind.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum IntegerPureSubstitutionError {
    UnsupportedCarrier,
    UnsupportedSort,
    FreshVariableExhausted,
    WorkLimitExceeded,
}

impl std::fmt::Display for IntegerPureSubstitutionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::UnsupportedCarrier => {
                "the proposition mentions a value the substitution cannot carry"
            }
            Self::UnsupportedSort => {
                "the substituted value has a sort the substitution does not support"
            }
            Self::FreshVariableExhausted => "the substitution ran out of fresh variable names",
            Self::WorkLimitExceeded => "the substitution exceeded its work limit",
        })
    }
}

/// Checked singleton substitution for the pure proposition fragment. One
/// carrier-aware walker owns the entire traversal, including Integer leaves
/// and quantifier scopes. A refused or exhausted walk never returns a partial
/// proposition to either the planner or its certificate checker.
pub(crate) fn substitute_machine_constant_in_pure_proposition(
    proposition: &Proposition,
    from: Variable,
    value: i64,
) -> Result<Proposition, IntegerPureSubstitutionError> {
    use crate::kernel::proof::term_rewrite::{TermRewrite, TypedProgramValueReplacement};

    let mut collector =
        crate::kernel::proof::term_rewrite::IntegerSubstitutionVariableCollector::checked();
    collector.collect(proposition);
    if collector.exhausted() {
        return Err(IntegerPureSubstitutionError::WorkLimitExceeded);
    }
    let mut reserved = BTreeSet::new();
    collector.extend_into(&mut reserved);
    reserved.insert(from);
    let c = BTreeMap::from([(
        from,
        TypedProgramValueReplacement::Bitvector(signed_i64_bitvector_constant(value)),
    )]);
    let integer = BTreeMap::new();
    let algebraic = BTreeMap::new();
    let mut walker = TermRewrite::for_typed_variables(&c, &integer, &algebraic);
    walker.reserve_integer_substitution_variables(&reserved);
    walker.enable_registered_load_resolution();
    let result = substitute_pure_proposition_with_walker(proposition, from, false, &mut walker);
    integer_substitution_refusal(walker.refusal())?;
    result
}

/// Capture-avoiding substitution for the complete pure Integer proposition
/// fragment. Validation collects the source once, and replacement uses one
/// carrier-aware walker. Its scoped Integer map gives nested binders lexical
/// scope without cloning a complete suffix environment for every binder.
pub(crate) fn substitute_integer_variable_in_pure_proposition(
    proposition: &Proposition,
    from: Variable,
    to: &IntegerTerm,
) -> Result<Proposition, IntegerPureSubstitutionError> {
    let mut reserved = BTreeSet::new();
    let mut collector =
        crate::kernel::proof::term_rewrite::IntegerSubstitutionVariableCollector::checked();
    // Traverse the replacement once, then charge only the shallow root copy
    // at each occurrence. Shared descendants are not copied by substitution.
    // `validate_integer_pure_term` uses the checked carrier collector, so the
    // replacement's selected registered-load pointers are included in this
    // one setup traversal without scanning their states.
    validate_integer_pure_term(to, &mut reserved, &mut collector)?;
    validate_integer_pure_proposition(proposition, &mut reserved, &mut collector)?;
    if collector.exhausted() {
        return Err(IntegerPureSubstitutionError::WorkLimitExceeded);
    }
    collector.extend_into(&mut reserved);
    reserved.insert(from);
    // The general proposition walker intentionally stops at binder-bearing
    // propositions.  Keep one checked walker for all atomic leaves instead
    // of rebuilding its replacement summary and fresh allocator per leaf.
    // The lexical Integer scope is pushed and popped by the recursive
    // proposition traversal below.
    let renamings = BTreeMap::new();
    let mut walker = crate::kernel::proof::term_rewrite::TermRewrite::for_integer_variables(
        from, to, false, &renamings,
    );
    // A symbolic C load is represented by a registered load variable.  The
    // selected pointer is part of the source expression for this checked
    // witness substitution, so let the shared walker remint that load at the
    // rewritten cell while retaining its original state.
    walker.enable_registered_load_resolution();
    walker.reserve_integer_substitution_variables(&reserved);
    let result = substitute_pure_proposition_with_walker(proposition, from, false, &mut walker);
    integer_substitution_refusal(walker.refusal())?;
    result
}

fn integer_substitution_refusal(
    refusal: Option<crate::kernel::proof::term_rewrite::RewriteRefusal>,
) -> Result<(), IntegerPureSubstitutionError> {
    use crate::kernel::proof::term_rewrite::RewriteRefusal;
    match refusal {
        None => Ok(()),
        Some(RewriteRefusal::WorkExhausted) => Err(IntegerPureSubstitutionError::WorkLimitExceeded),
        Some(RewriteRefusal::UnsupportedScope) => {
            Err(IntegerPureSubstitutionError::UnsupportedCarrier)
        }
    }
}

fn integer_work(units: usize) -> Result<(), IntegerPureSubstitutionError> {
    if crate::instrumentation::deadline_exceeded_with_work(units) {
        Err(IntegerPureSubstitutionError::WorkLimitExceeded)
    } else {
        Ok(())
    }
}

fn validate_integer_pure_proposition(
    proposition: &Proposition,
    variables: &mut BTreeSet<Variable>,
    collector: &mut crate::kernel::proof::term_rewrite::IntegerSubstitutionVariableCollector,
) -> Result<(), IntegerPureSubstitutionError> {
    integer_work(1)?;
    match proposition {
        Proposition::Equal(Term::Integer(left), Term::Integer(right)) => {
            validate_integer_pure_term(left, variables, collector)?;
            validate_integer_pure_term(right, variables, collector)?;
            Ok(())
        }
        Proposition::Equal(left, right)
            if integer_atomic_term_supported(left) && integer_atomic_term_supported(right) =>
        {
            validate_integer_atomic_proposition(proposition, collector)
        }
        Proposition::ConditionIs(condition, _) => {
            validate_integer_pure_condition(condition.native_compat(), collector)
        }
        Proposition::MemoryReadDefined { .. } | Proposition::MemoryLoadable { .. } => {
            // A symbolic array read contributes this obligation to the
            // existential body.  It is a supported C carrier as long as its
            // pointer and byte-count expressions are rewritten by the same
            // checked walker; the memory state remains opaque.
            integer_work(1)?;
            collector.collect(proposition);
            if collector.exhausted() {
                return Err(IntegerPureSubstitutionError::WorkLimitExceeded);
            }
            Ok(())
        }
        Proposition::And(left, right)
        | Proposition::Or(left, right)
        | Proposition::Implies(left, right) => {
            validate_integer_pure_proposition(left, variables, collector)?;
            validate_integer_pure_proposition(right, variables, collector)
        }
        Proposition::Not(body) => validate_integer_pure_proposition(body, variables, collector),
        Proposition::ForAll {
            var, sort, body, ..
        } => {
            if !matches!(
                sort,
                Sort::Integer
                    | Sort::Algebraic(_)
                    | Sort::ProgramInt32
                    | Sort::ProgramInt64
                    | Sort::ProgramInteger(_)
                    | Sort::ProgramPointer(_)
                    | Sort::ProgramObjectPointer(_, _)
            ) {
                return Err(IntegerPureSubstitutionError::UnsupportedSort);
            }
            variables.insert(*var);
            validate_integer_pure_proposition(body, variables, collector)
        }
        Proposition::Exists {
            var, sort, body, ..
        } => {
            if !matches!(
                sort,
                Sort::Integer
                    | Sort::Algebraic(_)
                    | Sort::ProgramInt32
                    | Sort::ProgramInt64
                    | Sort::ProgramInteger(_)
                    | Sort::ProgramPointer(_)
                    | Sort::ProgramObjectPointer(_, _)
            ) {
                return Err(IntegerPureSubstitutionError::UnsupportedSort);
            }
            variables.insert(*var);
            validate_integer_pure_proposition(body, variables, collector)
        }
        _ => Err(IntegerPureSubstitutionError::UnsupportedCarrier),
    }
}

fn validate_integer_pure_condition(
    condition: &ConditionTerm,
    collector: &mut crate::kernel::proof::term_rewrite::IntegerSubstitutionVariableCollector,
) -> Result<(), IntegerPureSubstitutionError> {
    validate_integer_atomic_proposition(
        &Proposition::condition_is(condition.clone(), true),
        collector,
    )
}

fn validate_integer_pure_term(
    term: &IntegerTerm,
    _variables: &mut BTreeSet<Variable>,
    collector: &mut crate::kernel::proof::term_rewrite::IntegerSubstitutionVariableCollector,
) -> Result<(), IntegerPureSubstitutionError> {
    validate_integer_atomic_proposition(
        &Proposition::Equal(
            Term::Integer(term.clone()),
            Term::Integer(IntegerTerm::constant_i64(0)),
        ),
        collector,
    )
}

fn validate_integer_atomic_proposition(
    proposition: &Proposition,
    collector: &mut crate::kernel::proof::term_rewrite::IntegerSubstitutionVariableCollector,
) -> Result<(), IntegerPureSubstitutionError> {
    rewrite_integer_atomic_proposition(
        proposition,
        Variable(0),
        &IntegerTerm::constant_i64(0),
        true,
        &BTreeMap::new(),
    )?;
    collector.collect(proposition);
    if collector.exhausted() {
        return Err(IntegerPureSubstitutionError::WorkLimitExceeded);
    }
    Ok(())
}

fn rewrite_integer_atomic_proposition(
    proposition: &Proposition,
    from: Variable,
    to: &IntegerTerm,
    shadowed: bool,
    renamings: &BTreeMap<Variable, Variable>,
) -> Result<Proposition, IntegerPureSubstitutionError> {
    integer_work(1)?;
    let mut walker = crate::kernel::proof::term_rewrite::TermRewrite::for_integer_variables(
        from, to, shadowed, renamings,
    );
    let result = walker.proposition(proposition);
    integer_substitution_refusal(walker.refusal())?;
    integer_work(0)?;
    Ok(result)
}

fn rewrite_integer_atomic_proposition_with_walker(
    proposition: &Proposition,
    walker: &mut crate::kernel::proof::term_rewrite::TermRewrite<'_>,
) -> Result<Proposition, IntegerPureSubstitutionError> {
    integer_work(1)?;
    let result = walker.proposition(proposition);
    integer_substitution_refusal(walker.refusal())?;
    integer_work(0)?;
    Ok(result)
}

enum IntegerPropositionRewriteTask<'a> {
    Visit {
        proposition: &'a Proposition,
        shadowed: bool,
    },
    FinishUnary,
    FinishBinary(PropositionBinaryOperator),
    FinishQuantifier {
        exists: bool,
        name: Option<String>,
        sort: Sort,
        new_var: Variable,
        scope: IntegerPropositionScope,
    },
}

enum PropositionBinaryOperator {
    And,
    Or,
    Implies,
}

enum IntegerPropositionScope {
    Integer(crate::kernel::proof::term_rewrite::IntegerSubstitutionScope),
    Program(crate::kernel::proof::term_rewrite::ProgramValueSubstitutionScope),
    Algebraic(crate::kernel::proof::term_rewrite::AlgebraicSubstitutionScope),
}

/// Iterative proposition traversal for checked pure substitution.  The
/// caller supplies one walker for the whole proposition. In particular, the
/// replacement's carrier summary, DAG cache, fresh allocator, and work state
/// are shared across sibling atomic propositions. An explicit task stack is
/// used here because nested quantifiers can make the recursive equivalent
/// exhaust the Rust test thread's stack even at modest source depth.
fn substitute_pure_proposition_with_walker(
    proposition: &Proposition,
    from: Variable,
    shadowed: bool,
    walker: &mut crate::kernel::proof::term_rewrite::TermRewrite<'_>,
) -> Result<Proposition, IntegerPureSubstitutionError> {
    let mut tasks = vec![IntegerPropositionRewriteTask::Visit {
        proposition,
        shadowed,
    }];
    let mut rewritten = Vec::new();

    while let Some(task) = tasks.pop() {
        match task {
            IntegerPropositionRewriteTask::Visit {
                proposition,
                shadowed,
            } => {
                integer_work(1)?;
                match proposition {
                    Proposition::Predicate { name, arguments } => {
                        let mut result = Vec::with_capacity(arguments.len());
                        for argument in arguments {
                            integer_work(1)?;
                            if !integer_atomic_term_supported(argument) {
                                return Err(IntegerPureSubstitutionError::UnsupportedCarrier);
                            }
                            let value = walker.term(argument);
                            integer_substitution_refusal(walker.refusal())?;
                            result.push(value);
                        }
                        rewritten.push(Proposition::Predicate {
                            name: name.clone(),
                            arguments: result,
                        });
                    }
                    Proposition::Equal(Term::Integer(left), Term::Integer(right)) => {
                        rewritten.push(Proposition::Equal(
                            Term::Integer(substitute_integer_pure_term_with_walker(left, walker)?),
                            Term::Integer(substitute_integer_pure_term_with_walker(right, walker)?),
                        ));
                    }
                    Proposition::Equal(left, right)
                        if integer_atomic_term_supported(left)
                            && integer_atomic_term_supported(right) =>
                    {
                        rewritten.push(rewrite_integer_atomic_proposition_with_walker(
                            proposition,
                            walker,
                        )?);
                    }
                    Proposition::ConditionIs(condition, value) => {
                        rewritten.push(Proposition::condition_is(
                            substitute_integer_pure_condition_with_walker(
                                condition.native_compat(),
                                walker,
                            )?,
                            *value,
                        ));
                    }
                    Proposition::MemoryReadDefined { .. } | Proposition::MemoryLoadable { .. } => {
                        rewritten.push(rewrite_integer_memory_loadable_with_walker(
                            proposition,
                            walker,
                        )?);
                    }
                    Proposition::And(left, right) => {
                        tasks.push(IntegerPropositionRewriteTask::FinishBinary(
                            PropositionBinaryOperator::And,
                        ));
                        tasks.push(IntegerPropositionRewriteTask::Visit {
                            proposition: right,
                            shadowed,
                        });
                        tasks.push(IntegerPropositionRewriteTask::Visit {
                            proposition: left,
                            shadowed,
                        });
                    }
                    Proposition::Or(left, right) => {
                        tasks.push(IntegerPropositionRewriteTask::FinishBinary(
                            PropositionBinaryOperator::Or,
                        ));
                        tasks.push(IntegerPropositionRewriteTask::Visit {
                            proposition: right,
                            shadowed,
                        });
                        tasks.push(IntegerPropositionRewriteTask::Visit {
                            proposition: left,
                            shadowed,
                        });
                    }
                    Proposition::Implies(left, right) => {
                        tasks.push(IntegerPropositionRewriteTask::FinishBinary(
                            PropositionBinaryOperator::Implies,
                        ));
                        tasks.push(IntegerPropositionRewriteTask::Visit {
                            proposition: right,
                            shadowed,
                        });
                        tasks.push(IntegerPropositionRewriteTask::Visit {
                            proposition: left,
                            shadowed,
                        });
                    }
                    Proposition::Not(body) => {
                        tasks.push(IntegerPropositionRewriteTask::FinishUnary);
                        tasks.push(IntegerPropositionRewriteTask::Visit {
                            proposition: body,
                            shadowed,
                        });
                    }
                    Proposition::ForAll {
                        var,
                        sort,
                        body,
                        name,
                    } => {
                        queue_integer_quantifier_rewrite(
                            false,
                            name.as_str(),
                            *var,
                            sort,
                            body,
                            from,
                            shadowed,
                            walker,
                            &mut tasks,
                        )?;
                    }
                    Proposition::Exists {
                        name,
                        var,
                        sort,
                        body,
                    } => {
                        queue_integer_quantifier_rewrite(
                            true,
                            Some(name.as_str()),
                            *var,
                            sort,
                            body,
                            from,
                            shadowed,
                            walker,
                            &mut tasks,
                        )?;
                    }
                    _ => return Err(IntegerPureSubstitutionError::UnsupportedCarrier),
                }
            }
            IntegerPropositionRewriteTask::FinishUnary => {
                let body = rewritten.pop().expect("unary rewrite result");
                rewritten.push(Proposition::Not(Box::new(body)));
            }
            IntegerPropositionRewriteTask::FinishBinary(operator) => {
                let right = rewritten.pop().expect("binary right rewrite result");
                let left = rewritten.pop().expect("binary left rewrite result");
                let proposition = match operator {
                    PropositionBinaryOperator::And => Proposition::And,
                    PropositionBinaryOperator::Or => Proposition::Or,
                    PropositionBinaryOperator::Implies => Proposition::Implies,
                };
                rewritten.push(proposition(Box::new(left), Box::new(right)));
            }
            IntegerPropositionRewriteTask::FinishQuantifier {
                exists,
                name,
                sort,
                new_var,
                scope,
            } => {
                match scope {
                    IntegerPropositionScope::Integer(scope) => {
                        walker.pop_integer_substitution_scope(scope);
                    }
                    IntegerPropositionScope::Program(scope) => {
                        walker.pop_program_substitution_scope(scope);
                    }
                    IntegerPropositionScope::Algebraic(scope) => {
                        walker.pop_algebraic_substitution_scope(scope);
                    }
                }
                let body = rewritten.pop().expect("quantifier rewrite result");
                if exists {
                    rewritten.push(Proposition::Exists {
                        name: name.unwrap_or_default(),
                        var: new_var,
                        sort,
                        body: Box::new(body),
                    });
                } else {
                    rewritten.push(Proposition::ForAll {
                        var: new_var,
                        sort,
                        body: Box::new(body),
                        name: BinderName::written(name.as_deref().unwrap_or_default()),
                    });
                }
            }
        }
    }

    Ok(rewritten.pop().expect("proposition rewrite result"))
}

#[allow(clippy::too_many_arguments)]
fn queue_integer_quantifier_rewrite<'a>(
    exists: bool,
    name: Option<&str>,
    var: Variable,
    sort: &Sort,
    body: &'a Proposition,
    from: Variable,
    shadowed: bool,
    walker: &mut crate::kernel::proof::term_rewrite::TermRewrite<'_>,
    tasks: &mut Vec<IntegerPropositionRewriteTask<'a>>,
) -> Result<(), IntegerPureSubstitutionError> {
    let is_integer = *sort == Sort::Integer;
    let is_algebraic = matches!(sort, Sort::Algebraic(_));
    let is_c = matches!(
        sort,
        Sort::ProgramInt32
            | Sort::ProgramInt64
            | Sort::ProgramInteger(_)
            | Sort::ProgramPointer(_)
            | Sort::ProgramObjectPointer(_, _)
    );
    if !is_integer && !is_c && !is_algebraic {
        return Err(IntegerPureSubstitutionError::UnsupportedSort);
    }

    let renamed = if is_integer {
        !shadowed && var != from && walker.replacement_contains_integer_variable(var)
    } else if is_algebraic {
        walker.replacement_contains_algebraic_variable(var)
    } else {
        walker.replacement_contains_program_variable(var)
    };
    if walker.work_exhausted() {
        return Err(IntegerPureSubstitutionError::WorkLimitExceeded);
    }
    let new_var = if renamed {
        let Some(variable) = walker.fresh_integer_substitution_variable() else {
            return if walker.work_exhausted() {
                Err(IntegerPureSubstitutionError::WorkLimitExceeded)
            } else {
                Err(IntegerPureSubstitutionError::FreshVariableExhausted)
            };
        };
        variable
    } else {
        var
    };
    if walker.work_exhausted() {
        return Err(IntegerPureSubstitutionError::WorkLimitExceeded);
    }

    let (scope, child_shadowed) = if is_integer {
        (
            IntegerPropositionScope::Integer(walker.push_integer_substitution_scope(
                var,
                new_var,
                shadowed || var == from,
            )),
            shadowed || var == from,
        )
    } else if is_algebraic {
        (
            IntegerPropositionScope::Algebraic(
                walker.push_algebraic_substitution_scope(var, new_var),
            ),
            shadowed,
        )
    } else {
        (
            IntegerPropositionScope::Program(walker.push_program_substitution_scope(var, new_var)),
            shadowed,
        )
    };
    tasks.push(IntegerPropositionRewriteTask::FinishQuantifier {
        exists,
        name: name.map(str::to_owned),
        sort: sort.clone(),
        new_var,
        scope,
    });
    tasks.push(IntegerPropositionRewriteTask::Visit {
        proposition: body,
        shadowed: child_shadowed,
    });
    Ok(())
}

fn substitute_integer_pure_condition_with_walker(
    condition: &ConditionTerm,
    walker: &mut crate::kernel::proof::term_rewrite::TermRewrite<'_>,
) -> Result<ConditionTerm, IntegerPureSubstitutionError> {
    let Proposition::ConditionIs(result, _) = rewrite_integer_atomic_proposition_with_walker(
        &Proposition::condition_is(condition.clone(), true),
        walker,
    )?
    else {
        unreachable!()
    };
    Ok(result.native_compat().clone())
}

fn rewrite_integer_memory_loadable_with_walker(
    proposition: &Proposition,
    walker: &mut crate::kernel::proof::term_rewrite::TermRewrite<'_>,
) -> Result<Proposition, IntegerPureSubstitutionError> {
    if let Proposition::MemoryReadDefined {
        at,
        memory,
        pointer,
        value_type,
    } = proposition
    {
        integer_work(1)?;
        let term_source_0 @ Term::ProgramValue(_) = walker.term(&Term::ProgramValue(
            ProgramValue::Pointer(Pointer::new(pointer.clone(), ProgramType::VoidPointer)),
        )) else {
            unreachable!("pointer rewrite changed its carrier")
        };
        let (Some(ProgramValue::Pointer(pointer)),) = (term_source_0.program_value_native(),)
        else {
            unreachable!("pointer rewrite changed its carrier")
        };
        integer_substitution_refusal(walker.refusal())?;
        return Ok(Proposition::MemoryReadDefined {
            at: *at,
            memory: memory.clone(),
            pointer: pointer.address().clone(),
            value_type: *value_type,
        });
    }
    let Proposition::MemoryLoadable {
        memory,
        base,
        bytes,
        wide,
    } = proposition
    else {
        unreachable!("memory-viewable helper called for another proposition carrier")
    };
    integer_work(1)?;
    let pointer = ProgramValue::Pointer(Pointer::new(base.clone(), ProgramType::VoidPointer));
    let term_source_0 @ Term::ProgramValue(_) = walker.term(&Term::ProgramValue(pointer)) else {
        unreachable!("pointer rewrite changed its carrier")
    };
    let (Some(ProgramValue::Pointer(pointer)),) = (term_source_0.program_value_native(),) else {
        unreachable!("pointer rewrite changed its carrier")
    };
    if walker.work_exhausted() {
        return Err(IntegerPureSubstitutionError::WorkLimitExceeded);
    }
    let bytes = walker.bits(bytes.native_compat());
    integer_substitution_refusal(walker.refusal())?;
    Ok(Proposition::MemoryLoadable {
        // SymbolicMemory states are immutable proof-state identities.  Keep the same
        // handle and rewrite only the selected address/width expressions.
        memory: memory.clone(),
        base: pointer.address().clone(),
        bytes: crate::kernel::StoredMachineTerm::new(
            if *wide {
                crate::kernel::MachineIntegerType::UInt64
            } else {
                crate::kernel::MachineIntegerType::Int32
            },
            bytes,
        ),
        wide: *wide,
    })
}

fn substitute_integer_pure_term_with_walker(
    term: &IntegerTerm,
    walker: &mut crate::kernel::proof::term_rewrite::TermRewrite<'_>,
) -> Result<IntegerTerm, IntegerPureSubstitutionError> {
    let Proposition::Equal(Term::Integer(result), _) =
        rewrite_integer_atomic_proposition_with_walker(
            &Proposition::Equal(
                Term::Integer(term.clone()),
                Term::Integer(IntegerTerm::constant_i64(0)),
            ),
            walker,
        )?
    else {
        unreachable!()
    };
    Ok(result)
}

fn integer_atomic_term_supported(term: &Term) -> bool {
    matches!(
        term,
        Term::Integer(_)
            | Term::Bitvector32(_)
            | Term::ProgramValue(_)
            | Term::Algebraic(_)
            | Term::Condition(_)
            | Term::PointerOffset(_)
    )
}

fn substitute_integer_pure_term(
    term: &IntegerTerm,
    from: Variable,
    to: &IntegerTerm,
    shadowed: bool,
    renamings: &BTreeMap<Variable, Variable>,
    _replacement_work: usize,
) -> Result<IntegerTerm, IntegerPureSubstitutionError> {
    let Proposition::Equal(Term::Integer(result), _) = rewrite_integer_atomic_proposition(
        &Proposition::Equal(
            Term::Integer(term.clone()),
            Term::Integer(IntegerTerm::constant_i64(0)),
        ),
        from,
        to,
        shadowed,
        renamings,
    )?
    else {
        unreachable!()
    };
    Ok(result)
}

/// Instantiate one Integer fold step without expanding the surrounding
/// range. The two binders are substituted through the existing
/// capture-avoiding DAG walker, so a nested fold cannot capture either step
/// value.
pub(in crate::kernel) fn instantiate_integer_range_fold_step(
    body: &IntegerTerm,
    accumulator: Variable,
    accumulator_value: &IntegerTerm,
    item: Variable,
    item_value: &IntegerTerm,
    machine_item: Option<MachineIntegerType>,
) -> Result<IntegerTerm, IntegerPureSubstitutionError> {
    let replacement_work = |term: &IntegerTerm| match term {
        IntegerTerm::Constant(value) => value.bits() as usize + 1,
        _ => 1,
    };
    let mut reserved = BTreeSet::new();
    collect_integer_carrier_variables(body, &mut reserved);
    collect_integer_capture_bitvector_variables(body, &mut reserved);
    collect_integer_carrier_variables(accumulator_value, &mut reserved);
    collect_integer_capture_bitvector_variables(accumulator_value, &mut reserved);
    collect_integer_carrier_variables(item_value, &mut reserved);
    collect_integer_capture_bitvector_variables(item_value, &mut reserved);
    let mut integer_binders = BTreeSet::new();
    let mut bitvector_binders = BTreeSet::new();
    collect_integer_binder_variables(body, &mut integer_binders, &mut bitvector_binders);
    collect_integer_binder_variables(
        accumulator_value,
        &mut integer_binders,
        &mut bitvector_binders,
    );
    collect_integer_binder_variables(item_value, &mut integer_binders, &mut bitvector_binders);
    reserved.extend(integer_binders);
    reserved.extend(bitvector_binders);
    reserved.insert(accumulator);
    reserved.insert(item);
    let mut generator = KernelVariableGenerator::fresh_for(0, reserved);
    let temporary = generator.next();
    let temporary_item = generator.next();
    let with_temporary = substitute_integer_pure_term(
        body,
        accumulator,
        &IntegerTerm::Variable(temporary),
        false,
        &BTreeMap::new(),
        1,
    )?;
    // Keep the two carriers separate.  An Int32 fold binds a machine
    // variable, while an Integer fold binds an Integer variable.  In
    // particular, substituting the Integer spelling of an Int32 binder would
    // leave the machine occurrence untouched (and trying both substitutions
    // would rewrite an unrelated Integer variable with the same identity).
    let with_item = if machine_item.is_some() {
        substitute_bitvector_variable_in_integer_checked_with_registered_loads(
            &with_temporary,
            item,
            &MachineTerm::Variable(temporary_item),
        )?
    } else {
        substitute_integer_pure_term(
            &with_temporary,
            item,
            &IntegerTerm::Variable(temporary_item),
            false,
            &BTreeMap::new(),
            1,
        )?
    };
    let with_accumulator = substitute_integer_pure_term(
        &with_item,
        temporary,
        accumulator_value,
        false,
        &BTreeMap::new(),
        replacement_work(accumulator_value),
    )?;
    if let Some(item_type) = machine_item {
        let Some(operand) = integer_item_operand(item_value, item_type) else {
            return Err(IntegerPureSubstitutionError::UnsupportedCarrier);
        };
        let source = MachineTerm::Variable(temporary_item);
        let mut rewrite =
            crate::kernel::proof::term_rewrite::TermRewrite::for_machine_operand_checked(
                &source,
                operand.operand_view(),
            );
        rewrite.enable_registered_load_resolution();
        let result = rewrite.integer(&with_accumulator);
        integer_substitution_refusal(rewrite.refusal())?;
        Ok(result)
    } else {
        substitute_integer_pure_term(
            &with_accumulator,
            temporary_item,
            item_value,
            false,
            &BTreeMap::new(),
            replacement_work(item_value),
        )
    }
}

/// The machine term of type `item_type` an item value denotes: the term a
/// machine observation observes, or a constant in the type's range.
fn integer_item_operand(
    value: &IntegerTerm,
    item_type: MachineIntegerType,
) -> Option<SharedMachineIntegerTerm> {
    match (value, item_type) {
        (IntegerTerm::Machine(machine), _) if machine.ty() == item_type => Some(machine.clone()),
        (IntegerTerm::Constant(value), MachineIntegerType::Int32) => value
            .to_i64()
            .filter(|value| (i64::from(i32::MIN)..=i64::from(i32::MAX)).contains(value))
            .map(|value| {
                SharedMachineIntegerTerm::intern(
                    item_type,
                    MachineTerm::constant(value as i32 as u32),
                )
            }),
        (IntegerTerm::Constant(value), MachineIntegerType::UInt64) => value.to_u64().map(|value| {
            SharedMachineIntegerTerm::intern(item_type, MachineTerm::uint64_constant(value))
        }),
        _ => None,
    }
}

fn substitute_bitvector_variable_in_algebraic_term(
    term: &AlgebraicTerm,
    from: Variable,
    to: &MachineTerm,
) -> AlgebraicTerm {
    let Term::Algebraic(term) =
        substitute_bitvector_variable_in_term(&Term::Algebraic(term.clone()), from, to)
    else {
        unreachable!()
    };
    term
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_program_expression(
    expression: &ProgramExpression,
    from: Variable,
    to: &MachineTerm,
) -> ProgramExpression {
    match expression {
        ProgramExpression::StringLiteral(_) => expression.clone(),
        ProgramExpression::Value(value) => ProgramExpression::Value(
            substitute_bitvector_variable_in_program_value(value, from, to),
        ),
        ProgramExpression::Variable(name) => ProgramExpression::Variable(name.clone()),
        ProgramExpression::FunctionAddress(name) => {
            ProgramExpression::FunctionAddress(name.clone())
        }
        ProgramExpression::StepResult { .. } => expression.clone(),
        ProgramExpression::Cast {
            expression,
            target_type,
            integer_mode,
            pointee_struct,
            pointee_volatile,
            pointee_constant,
            explicit_qualification,
        } => ProgramExpression::Cast {
            expression: Box::new(substitute_bitvector_variable_in_program_expression(
                expression, from, to,
            )),
            target_type: *target_type,
            integer_mode: *integer_mode,
            pointee_struct: pointee_struct.clone(),
            pointee_volatile: *pointee_volatile,
            pointee_constant: *pointee_constant,
            explicit_qualification: *explicit_qualification,
        },
        ProgramExpression::Ternary {
            condition,
            then_branch,
            else_branch,
        } => ProgramExpression::Ternary {
            condition: Box::new(substitute_bitvector_variable_in_program_expression(
                condition, from, to,
            )),
            then_branch: Box::new(substitute_bitvector_variable_in_program_expression(
                then_branch,
                from,
                to,
            )),
            else_branch: Box::new(substitute_bitvector_variable_in_program_expression(
                else_branch,
                from,
                to,
            )),
        },
        ProgramExpression::FloatClassification {
            expression,
            classification,
        } => ProgramExpression::FloatClassification {
            expression: Box::new(substitute_bitvector_variable_in_program_expression(
                expression, from, to,
            )),
            classification: *classification,
        },
        ProgramExpression::Negate(expression) => ProgramExpression::Negate(Box::new(
            substitute_bitvector_variable_in_program_expression(expression, from, to),
        )),
        ProgramExpression::FloatNegate(expression) => ProgramExpression::FloatNegate(Box::new(
            substitute_bitvector_variable_in_program_expression(expression, from, to),
        )),
        ProgramExpression::EnumConstruct {
            enum_type,
            variant,
            fields,
        } => ProgramExpression::EnumConstruct {
            enum_type: *enum_type,
            variant: variant.clone(),
            fields: fields
                .iter()
                .map(|field| substitute_bitvector_variable_in_program_expression(field, from, to))
                .collect(),
        },
        ProgramExpression::EnumField {
            value,
            variant,
            index,
        } => ProgramExpression::EnumField {
            value: Box::new(substitute_bitvector_variable_in_program_expression(
                value, from, to,
            )),
            variant: variant.clone(),
            index: *index,
        },
        ProgramExpression::EnumIs { value, variant } => ProgramExpression::EnumIs {
            value: Box::new(substitute_bitvector_variable_in_program_expression(
                value, from, to,
            )),
            variant: variant.clone(),
        },
        ProgramExpression::AddressOf(body) => ProgramExpression::AddressOf(Box::new(
            substitute_bitvector_variable_in_program_expression(body, from, to),
        )),
        ProgramExpression::CheckedObjectAddress(body) => {
            ProgramExpression::CheckedObjectAddress(Box::new(
                substitute_bitvector_variable_in_program_expression(body, from, to),
            ))
        }
        ProgramExpression::PointerOffsetBytes { pointer, bytes } => {
            ProgramExpression::PointerOffsetBytes {
                pointer: Box::new(substitute_bitvector_variable_in_program_expression(
                    pointer, from, to,
                )),
                bytes: *bytes,
            }
        }
        ProgramExpression::Subobject { pointer, width } => ProgramExpression::Subobject {
            pointer: Box::new(substitute_bitvector_variable_in_program_expression(
                pointer, from, to,
            )),
            width: *width,
        },
        ProgramExpression::Not(body) => ProgramExpression::Not(Box::new(
            substitute_bitvector_variable_in_program_expression(body, from, to),
        )),
        ProgramExpression::Load(body) => ProgramExpression::Load(Box::new(
            substitute_bitvector_variable_in_program_expression(body, from, to),
        )),
        ProgramExpression::TypedLoad {
            pointer,
            value_type,
            volatile,
            pointee_constant,
            access_class,
            source,
        } => ProgramExpression::TypedLoad {
            pointer: Box::new(substitute_bitvector_variable_in_program_expression(
                pointer, from, to,
            )),
            value_type: *value_type,
            volatile: *volatile,
            pointee_constant: *pointee_constant,
            access_class: access_class.clone(),
            source: source.clone(),
        },
        ProgramExpression::LessThan(left, right) => ProgramExpression::LessThan(
            Box::new(substitute_bitvector_variable_in_program_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_program_expression(
                right, from, to,
            )),
        ),
        ProgramExpression::LessEqual(left, right) => ProgramExpression::LessEqual(
            Box::new(substitute_bitvector_variable_in_program_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_program_expression(
                right, from, to,
            )),
        ),
        ProgramExpression::GreaterThan(left, right) => ProgramExpression::GreaterThan(
            Box::new(substitute_bitvector_variable_in_program_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_program_expression(
                right, from, to,
            )),
        ),
        ProgramExpression::GreaterEqual(left, right) => ProgramExpression::GreaterEqual(
            Box::new(substitute_bitvector_variable_in_program_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_program_expression(
                right, from, to,
            )),
        ),
        ProgramExpression::Equal(left, right) => ProgramExpression::Equal(
            Box::new(substitute_bitvector_variable_in_program_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_program_expression(
                right, from, to,
            )),
        ),
        ProgramExpression::NotEqual(left, right) => ProgramExpression::NotEqual(
            Box::new(substitute_bitvector_variable_in_program_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_program_expression(
                right, from, to,
            )),
        ),
        ProgramExpression::And(left, right) => ProgramExpression::And(
            Box::new(substitute_bitvector_variable_in_program_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_program_expression(
                right, from, to,
            )),
        ),
        ProgramExpression::Or(left, right) => ProgramExpression::Or(
            Box::new(substitute_bitvector_variable_in_program_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_program_expression(
                right, from, to,
            )),
        ),
        ProgramExpression::Add(left, right) => ProgramExpression::Add(
            Box::new(substitute_bitvector_variable_in_program_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_program_expression(
                right, from, to,
            )),
        ),
        ProgramExpression::Subtract(left, right) => ProgramExpression::Subtract(
            Box::new(substitute_bitvector_variable_in_program_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_program_expression(
                right, from, to,
            )),
        ),
        ProgramExpression::Multiply(left, right) => ProgramExpression::Multiply(
            Box::new(substitute_bitvector_variable_in_program_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_program_expression(
                right, from, to,
            )),
        ),
        ProgramExpression::Divide(left, right) => ProgramExpression::Divide(
            Box::new(substitute_bitvector_variable_in_program_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_program_expression(
                right, from, to,
            )),
        ),
        ProgramExpression::Remainder(left, right) => ProgramExpression::Remainder(
            Box::new(substitute_bitvector_variable_in_program_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_program_expression(
                right, from, to,
            )),
        ),
        ProgramExpression::ShiftLeft(left, right) => ProgramExpression::ShiftLeft(
            Box::new(substitute_bitvector_variable_in_program_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_program_expression(
                right, from, to,
            )),
        ),
        ProgramExpression::RustShiftLeft(left, right) => ProgramExpression::RustShiftLeft(
            Box::new(substitute_bitvector_variable_in_program_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_program_expression(
                right, from, to,
            )),
        ),
        ProgramExpression::ShiftRight(left, right) => ProgramExpression::ShiftRight(
            Box::new(substitute_bitvector_variable_in_program_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_program_expression(
                right, from, to,
            )),
        ),
        ProgramExpression::RustShiftRight(left, right) => ProgramExpression::RustShiftRight(
            Box::new(substitute_bitvector_variable_in_program_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_program_expression(
                right, from, to,
            )),
        ),
        ProgramExpression::BitwiseAnd(left, right) => ProgramExpression::BitwiseAnd(
            Box::new(substitute_bitvector_variable_in_program_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_program_expression(
                right, from, to,
            )),
        ),
        ProgramExpression::BitwiseOr(left, right) => ProgramExpression::BitwiseOr(
            Box::new(substitute_bitvector_variable_in_program_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_program_expression(
                right, from, to,
            )),
        ),
        ProgramExpression::BitwiseXor(left, right) => ProgramExpression::BitwiseXor(
            Box::new(substitute_bitvector_variable_in_program_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_program_expression(
                right, from, to,
            )),
        ),
        ProgramExpression::BitwiseNot(expression) => ProgramExpression::BitwiseNot(Box::new(
            substitute_bitvector_variable_in_program_expression(expression, from, to),
        )),
        ProgramExpression::Index(left, right) => ProgramExpression::Index(
            Box::new(substitute_bitvector_variable_in_program_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_program_expression(
                right, from, to,
            )),
        ),
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_spec_expression(
    expression: &SpecExpression,
    from: Variable,
    to: &MachineTerm,
) -> SpecExpression {
    let source = MachineTerm::Variable(from);
    let mut rewrite =
        crate::kernel::proof::term_rewrite::TermRewrite::for_bits_checked(&source, to);
    rewrite
        .spec_expression(expression)
        .unwrap_or_else(|error| panic!("spec expression substitution refused: {error}"))
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_spec_proposition(
    proposition: &SpecProposition,
    from: Variable,
    to: &MachineTerm,
) -> SpecProposition {
    let source = MachineTerm::Variable(from);
    let mut rewrite =
        crate::kernel::proof::term_rewrite::TermRewrite::for_bits_checked(&source, to);
    rewrite
        .spec_proposition(proposition)
        .unwrap_or_else(|error| panic!("spec proposition substitution refused: {error}"))
}

fn substitute_bitvector_variable_in_spec_integer(
    expression: &SpecIntegerExpression,
    from: Variable,
    to: &MachineTerm,
) -> SpecIntegerExpression {
    let source = MachineTerm::Variable(from);
    let mut rewrite =
        crate::kernel::proof::term_rewrite::TermRewrite::for_bits_checked(&source, to);
    rewrite
        .spec_integer_expression(expression)
        .unwrap_or_else(|error| panic!("spec Integer substitution refused: {error}"))
}

#[cfg(test)]
mod spec_carrier_substitution_binder_tests {
    use super::*;

    fn int32_value(variable: Variable) -> SpecExpression {
        SpecExpression::Value(ProgramValue::Int32(MachineTerm::Variable(variable)))
    }

    fn fold_body(item: Variable, source: Variable) -> SpecIntegerExpression {
        SpecIntegerExpression::Add(
            Box::new(SpecIntegerExpression::FromMachine(Box::new(int32_value(
                item,
            )))),
            Box::new(SpecIntegerExpression::Term(IntegerTerm::Machine(
                SharedMachineIntegerTerm::intern(
                    MachineIntegerType::Int32,
                    MachineTerm::Variable(source),
                ),
            ))),
        )
    }

    fn int32_fold(item: Variable, source: Variable) -> SpecExpression {
        SpecExpression::IntegerToMachine {
            value: Box::new(SpecIntegerExpression::RangeFold {
                index: SpecIntegerRangeFoldIndex::Int32 {
                    start: Box::new(int32_value(source)),
                    end: Box::new(SpecExpression::Value(ProgramValue::Int32(
                        MachineTerm::constant(8),
                    ))),
                },
                initial: Box::new(SpecIntegerExpression::Term(IntegerTerm::constant_i64(0))),
                accumulator: Variable(330),
                item,
                body: Box::new(fold_body(item, source)),
            }),
            destination: MachineIntegerType::Int32,
        }
    }

    #[test]
    fn spec_integer_fold_alpha_renames_an_item_that_would_capture() {
        let source = Variable(310);
        let item = Variable(311);
        let rewritten = substitute_bitvector_variable_in_spec_expression(
            &int32_fold(item, source),
            source,
            &MachineTerm::Variable(item),
        );
        let SpecExpression::IntegerToMachine { value, .. } = rewritten else {
            panic!("the Integer fold was dropped")
        };
        let SpecIntegerExpression::RangeFold {
            index,
            item: renamed_item,
            body,
            ..
        } = *value
        else {
            panic!("the Integer fold was dropped")
        };
        assert_ne!(
            renamed_item, item,
            "the replacement was captured by the item"
        );
        let SpecIntegerRangeFoldIndex::Int32 { start, .. } = index else {
            panic!("the fold index changed carrier")
        };
        assert_eq!(*start, int32_value(item));
        let SpecIntegerExpression::Add(bound_item, substituted_source) = *body else {
            panic!("the fold body changed shape")
        };
        assert_eq!(
            *bound_item,
            SpecIntegerExpression::FromMachine(Box::new(int32_value(renamed_item)))
        );
        let SpecIntegerExpression::Term(IntegerTerm::Machine(substituted_source)) =
            *substituted_source
        else {
            panic!("the source machine integer was silently dropped")
        };
        assert_eq!(substituted_source.value(), &MachineTerm::Variable(item));
    }

    #[test]
    fn spec_integer_fold_does_not_substitute_through_its_own_item_binder() {
        let source = Variable(320);
        let rewritten = substitute_bitvector_variable_in_spec_expression(
            &int32_fold(source, source),
            source,
            &MachineTerm::constant(5),
        );
        let SpecExpression::IntegerToMachine { value, .. } = rewritten else {
            panic!("the Integer fold was dropped")
        };
        let SpecIntegerExpression::RangeFold {
            item, index, body, ..
        } = *value
        else {
            panic!("the Integer fold was dropped")
        };
        assert_eq!(item, source);
        let SpecIntegerRangeFoldIndex::Int32 { start, .. } = index else {
            panic!("the fold index changed carrier")
        };
        assert_eq!(
            *start,
            SpecExpression::Value(ProgramValue::Int32(MachineTerm::constant(5)))
        );
        let SpecIntegerExpression::Add(bound_item, machine_source) = *body else {
            panic!("the fold body changed shape")
        };
        assert_eq!(
            *bound_item,
            SpecIntegerExpression::FromMachine(Box::new(int32_value(source)))
        );
        assert_eq!(
            *machine_source,
            SpecIntegerExpression::Term(IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int32,
                MachineTerm::Variable(source),
            ),))
        );
    }

    #[test]
    fn spec_quantifier_alpha_renames_a_binder_that_would_capture() {
        let source = Variable(330);
        let binder = Variable(331);
        let proposition = SpecProposition::ForAllInt32 {
            name: "i".into(),
            variable: binder,
            body: Box::new(SpecProposition::Comparison {
                left: int32_value(source),
                operator: ComparisonOperator::Equal,
                right: int32_value(binder),
            }),
        };
        let rewritten = substitute_bitvector_variable_in_spec_proposition(
            &proposition,
            source,
            &MachineTerm::Variable(binder),
        );
        let SpecProposition::ForAllInt32 { variable, body, .. } = rewritten else {
            panic!("the quantifier was dropped")
        };
        assert_ne!(
            variable, binder,
            "the replacement was captured by the quantifier"
        );
        assert_eq!(
            *body,
            SpecProposition::Comparison {
                left: int32_value(binder),
                operator: ComparisonOperator::Equal,
                right: int32_value(variable),
            }
        );
    }

    #[test]
    fn spec_quantifier_does_not_substitute_through_its_own_binder() {
        let source = Variable(335);
        let proposition = SpecProposition::ForAllInt32 {
            name: "i".into(),
            variable: source,
            body: Box::new(SpecProposition::Comparison {
                left: int32_value(source),
                operator: ComparisonOperator::Equal,
                right: SpecExpression::Value(ProgramValue::Int32(MachineTerm::constant(8))),
            }),
        };
        let rewritten = substitute_bitvector_variable_in_spec_proposition(
            &proposition,
            source,
            &MachineTerm::constant(5),
        );
        assert_eq!(rewritten, proposition);
    }

    #[test]
    fn integer_substitution_refuses_instead_of_returning_the_unrewritten_term() {
        let limits = crate::instrumentation::TacticWorkLimits {
            simple: 0,
            smart: 0,
            control: 0,
        };
        let refused = crate::instrumentation::with_tactic_work_limits(limits, || {
            crate::instrumentation::collect(|| {
                let tactic = crate::instrumentation::TacticEvent {
                    source_tactic_path: None,
                    claim: "integer substitution regression".into(),
                    tactic_index: 0,
                    tactic_name: "integer_substitution_regression".into(),
                    class: "simple".into(),
                    statement_index: 0,
                    source_index: 0,
                };
                crate::instrumentation::emit(
                    crate::instrumentation::VerificationEvent::TacticStarted(tactic.clone()),
                );
                let result = std::panic::catch_unwind(|| {
                    substitute_bitvector_variable_in_integer(
                        &IntegerTerm::var(Variable(340)),
                        Variable(340),
                        &MachineTerm::constant(1),
                    )
                });
                crate::instrumentation::emit(
                    crate::instrumentation::VerificationEvent::TacticFailed(tactic),
                );
                result
            })
            .0
        });
        assert!(
            refused.is_err(),
            "a failed substitution must not return its input"
        );
    }
}

#[cfg(test)]
mod machine_integer_substitution_tests {
    use super::*;

    #[test]
    fn narrow_order_substitution_retains_literal_comparisons_in_both_carriers() {
        use crate::kernel::{CompareRelation as R, MachineIntegerType as T};
        for format in [T::Int8, T::UInt8, T::Int16, T::UInt16] {
            let _session = crate::kernel::VerificationSession::enter();
            let variable = Variable(999705);
            let word = |n: i64| {
                crate::kernel::machine_integer::range::constant_word(format, &n.into()).unwrap()
            };
            for relation in [R::LessThan, R::LessEqual, R::GreaterThan, R::GreaterEqual] {
                let condition = ConditionTerm::Compare {
                    format,
                    relation,
                    left: Box::new(MachineTerm::Variable(variable)),
                    right: Box::new(word(5)),
                };
                let expected = ConditionTerm::Compare {
                    format,
                    relation,
                    left: Box::new(word(9)),
                    right: Box::new(word(5)),
                };
                assert_eq!(
                    substitute_bitvector_variable_in_condition(&condition, variable, &word(9)),
                    expected
                );
                let root = crate::kernel::KernelTermImport::default().condition(&condition);
                let mapped =
                    substitute_bitvector_variable_in_common_condition(&root, variable, &word(9))
                        .unwrap();
                assert_eq!(
                    crate::kernel::KernelTermExport::condition(&mapped).unwrap(),
                    expected
                );
            }
        }
    }

    #[cfg(test)]
    mod scaling_tests {
        include!(
            "../../scaling_tests/kernel/reasoning/substitution/machine_integer_substitution_tests.rs"
        );
    }
}

fn map_common_substitution_offsets(
    arguments: &[crate::kernel::SharedAddressOffset; 2],
    map_machine: &mut impl FnMut(&KernelTerm, MachineIntegerType) -> Option<SharedMachineIntegerTerm>,
) -> Result<[crate::kernel::SharedAddressOffset; 2], ()> {
    use crate::kernel::{KernelAddressOffset as O, SharedAddressOffset as S};
    S::try_map_pair(arguments, |original, node| {
        let (value, width, wide) = match node {
            O::Add([a, b]) => {
                return Ok::<_, ()>(
                    if matches!(original.node(), O::Add(old) if old == &[a.clone(), b.clone()]) {
                        original.clone()
                    } else {
                        S::add(a, b)
                    },
                );
            }
            O::Int32Scaled { value, byte_width } => (value, byte_width, None),
            O::Int64Scaled {
                value,
                byte_width,
                unsigned,
            } => (value, byte_width, Some(unsigned)),
            _ => return Ok(original.clone()),
        };
        let index = S::exact_index(&value);
        // The native offset substitution preserves the old index
        // on an unsupported rewrite and preserves unchanged spelling.
        let mapped = map_machine(&value, index.ty()).unwrap_or_else(|| index.clone());
        if crate::kernel::memory_history::pointer_index_syntax_equal(&index, &mapped) {
            return Ok(original.clone());
        }
        Ok(O::import(
            &crate::kernel::memory_history::rebuild_scaled_pointer_index(mapped, width, wide),
        ))
    })
}

// Prepared for the common Boolean producer/handoff slices. Atomic comparison,
// call and opaque-payload substitution keeps the established native semantics;
// the surrounding Boolean DAG is reconstructed without exporting its prefixes.
#[allow(dead_code)]
pub(in crate::kernel) fn substitute_bitvector_variable_in_common_condition(
    condition: &KernelTerm,
    from: Variable,
    to: &MachineTerm,
) -> Option<KernelTerm> {
    let mut machine_results = std::collections::HashMap::new();
    let mut map_machine = |argument: &KernelTerm, format: MachineIntegerType| {
        let operand = crate::kernel::MachineOperandView::Shared(argument).retain(format);
        crate::kernel::memory_history::map_shared_machine_substitution_with_cache(
            &operand,
            |leaf| Some(substitute_bitvector_variable(leaf, from, to)),
            crate::kernel::proof::equality_rewrite::rebuild_normalized_machine_node,
            |_| true,
            |root| {
                let source = MachineTerm::Variable(from);
                let mut rewrite =
                    crate::kernel::proof::term_rewrite::TermRewrite::for_bits(&source, to);
                rewrite.enable_registered_load_resolution();
                let result = rewrite.shared_machine_operand(root);
                result
                    .filter(|_| rewrite.refusal().is_none())
                    .map(Some)
                    .ok_or(())
            },
            &mut machine_results,
        )
    };
    condition
        .map_boolean_leaves::<()>(|leaf| {
            if let crate::kernel::KernelTermNode::BoolCompare {
                format,
                relation,
                arguments,
            } = leaf.node()
            {
                let arguments = arguments.each_ref().map(|argument| {
                    map_machine(argument, *format).and_then(|value| value.shared_operand().cloned())
                });
                let [Some(left), Some(right)] = arguments else {
                    return Err(());
                };
                let arguments = [left, right];
                let closed_order = *relation != CompareRelation::Equal
                    && matches!(
                        format,
                        MachineIntegerType::Int8
                    | MachineIntegerType::UInt8
                    | MachineIntegerType::Int16
                    | MachineIntegerType::UInt16
                    | MachineIntegerType::Int32
                            | MachineIntegerType::UInt32
                            | MachineIntegerType::Int64
                            | MachineIntegerType::UInt64
                    )
                    && arguments.iter().all(|argument| {
                        crate::kernel::MachineOperandView::Shared(argument)
                            .literal()
                            .is_some()
                    });
                if closed_order {
                    let condition = crate::kernel::machine_integer::comparison::logical_condition_for_operand_views(
                        *format,
                        *relation,
                        arguments.each_ref().map(crate::kernel::MachineOperandView::Shared),
                    );
                    return Ok(KernelTermImport::default().condition(&condition));
                }
                return Ok(
                    if *format == MachineIntegerType::Int64 && *relation == CompareRelation::Equal {
                        KernelTerm::boolean_comparison_raw(*format, *relation, arguments)
                    } else {
                        KernelTerm::boolean_comparison(*format, *relation, arguments)
                    },
                );
            }
            if let crate::kernel::KernelTermNode::BoolOverflow {
                format,
                operation,
                arguments,
            } = leaf.node()
            {
                let a = map_machine(&arguments[0], *format).ok_or(())?;
                let b = map_machine(&arguments[1], *format).ok_or(())?;
                return Ok(KernelTerm::boolean_overflow(
                    *format,
                    *operation,
                    [
                        KernelTerm::retained_machine_operand(*format, a.operand_view()),
                        KernelTerm::retained_machine_operand(*format, b.operand_view()),
                    ],
                ));
            }
            if let crate::kernel::KernelTermNode::AddressOffsetEqual { arguments } = leaf.node() {
                let offsets = map_common_substitution_offsets(arguments, &mut map_machine)?;
                return Ok(KernelTerm::address_offset_equal(offsets));
            }
            let mut map_address = |address: &crate::kernel::SharedAddress| {
                if matches!(
                    address.node().base.native_atom(),
                    AddressBase::PureFunctionApplication(_)
                ) {
                    crate::kernel::proof::term_rewrite::substitute_application_address_bits(
                        address, from, to,
                    )
                    .ok_or(())
                } else {
                    let offset = &address.node().offset;
                    let offsets = map_common_substitution_offsets(
                        &[offset.clone(), offset.clone()],
                        &mut map_machine,
                    )?;
                    Ok(crate::kernel::SharedAddress::new(
                        address.node().base.clone(),
                        offsets[0].clone(),
                    ))
                }
            };
            if let crate::kernel::KernelTermNode::BoolRead(read) = leaf.node() {
                let (point, address) = read.parts();
                return Ok(KernelTerm::boolean_read(
                    point.with_renamed_memory(substitute_bitvector_variable_in_shared_memory(
                        point.shared_memory(),
                        from,
                        to,
                    )),
                    map_address(address)?,
                ));
            }
            if let crate::kernel::KernelTermNode::PointerEqual(pair) = leaf.node() {
                let [a, b] = pair.arguments();
                return Ok(KernelTerm::pointer_equal_raw([
                    a.map_condition_addresses(&mut map_address)?,
                    b.map_condition_addresses(&mut map_address)?,
                ]));
            }
            if let crate::kernel::KernelTermNode::AddressEqual { arguments } = leaf.node() {
                return Ok(KernelTerm::address_equal([
                    map_address(&arguments[0])?,
                    map_address(&arguments[1])?,
                ]));
            }
            let native = crate::kernel::BooleanOperandView::Shared(leaf).identity_leaf();
            Ok(crate::kernel::KernelTermImport::default().condition(
                &substitute_bitvector_variable_in_condition(&native, from, to),
            ))
        })
        .ok()
}

#[allow(dead_code)]
pub(in crate::kernel) fn substitute_pointer_variable_in_common_condition(
    condition: &KernelTerm,
    from: Variable,
    to: &Address,
) -> Option<KernelTerm> {
    if crate::kernel::BooleanOperandView::Shared(condition).is_bool_value_form()
        || matches!(
            condition.node(),
            crate::kernel::KernelTermNode::PointerEqual(_)
        )
    {
        return crate::kernel::proof::term_rewrite::substitute_pointer_boolean_value(
            condition, from, to,
        );
    }
    if let crate::kernel::KernelTermNode::AddressEqual { arguments } = condition.node() {
        use crate::kernel::{
            KernelAddressOffset as O, SharedAddress as A, SharedAddressBase,
            SharedAddressOffset as S,
        };
        let mut mapped = Vec::with_capacity(2);
        for address in arguments {
            let block = address.node().base.native_atom();
            if matches!(block, AddressBase::PureFunctionApplication(_)) {
                mapped.push(
                    crate::kernel::proof::term_rewrite::substitute_application_address_pointer(
                        address, from, to,
                    )?,
                );
                continue;
            }
            let replacement = match block {
                AddressBase::Symbolic(variable) | AddressBase::FunctionSymbolic(variable)
                    if *variable == from =>
                {
                    Some(to.clone())
                }
                AddressBase::ExternalObject(variable) if *variable == from => {
                    Some(to.object_identity())
                }
                _ => None,
            };
            mapped.push(match replacement {
                Some(replacement) => A::new(
                    SharedAddressBase::import(&replacement.base),
                    S::add(
                        O::import(&replacement.offset),
                        address.node().offset.clone(),
                    ),
                ),
                None => address.clone(),
            });
        }
        return Some(KernelTerm::address_equal([
            mapped[0].clone(),
            mapped[1].clone(),
        ]));
    }
    if matches!(
        condition.node(),
        crate::kernel::KernelTermNode::AddressOffsetEqual { .. }
    ) {
        return Some(condition.clone());
    }
    if crate::kernel::BooleanOperandView::Shared(condition)
        .machine_arguments()
        .is_some()
    {
        return Some(condition.clone());
    }
    let native = crate::kernel::BooleanOperandView::Shared(condition).native();
    Some(
        crate::kernel::KernelTermImport::default()
            .condition(&substitute_pointer_variable_in_condition(&native, from, to)),
    )
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_condition(
    condition: &ConditionTerm,
    from: Variable,
    to: &MachineTerm,
) -> ConditionTerm {
    match condition {
        ConditionTerm::Constant(value) => ConditionTerm::Constant(*value),
        ConditionTerm::AlgebraicEqual(left, right) => ConditionTerm::AlgebraicEqual(
            Box::new(substitute_bitvector_variable_in_algebraic_term(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_algebraic_term(
                right, from, to,
            )),
        ),
        // A `Bool` binder (Stage 5) instantiated with a `bool` value's word
        // takes that value's truth.
        ConditionTerm::Variable(variable) if *variable == from => {
            ConditionTerm::truth_of_bool_word(to)
        }
        ConditionTerm::Variable(variable) => ConditionTerm::Variable(*variable),
        ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left,
            right,
        } => ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left: Box::new(substitute_bitvector_variable(left, from, to)),
            right: Box::new(substitute_bitvector_variable(right, from, to)),
        },
        crate::kernel::integer_comparison_condition!(left, right) => {
            let rewrite =
                |term: &IntegerTerm| substitute_bitvector_variable_in_integer(term, from, to);
            match condition {
                ConditionTerm::IntegerLessThan(_, _) => {
                    ConditionTerm::integer_less_than(rewrite(left), rewrite(right))
                }
                ConditionTerm::IntegerLessEqual(_, _) => {
                    ConditionTerm::integer_less_equal(rewrite(left), rewrite(right))
                }
                ConditionTerm::IntegerGreaterThan(_, _) => {
                    ConditionTerm::integer_greater_than(rewrite(left), rewrite(right))
                }
                ConditionTerm::IntegerGreaterEqual(_, _) => {
                    ConditionTerm::integer_greater_equal(rewrite(left), rewrite(right))
                }
                ConditionTerm::IntegerEqual(_, _) => {
                    ConditionTerm::integer_equal(rewrite(left), rewrite(right))
                }
                ConditionTerm::IntegerNotEqual(_, _) => {
                    ConditionTerm::integer_not_equal(rewrite(left), rewrite(right))
                }
                _ => unreachable!(),
            }
        }
        ConditionTerm::Float32(FloatCondition::Comparison {
            operator,
            left,
            right,
        }) => ConditionTerm::float32_compare(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
            *operator,
        ),
        ConditionTerm::Float32(FloatCondition::Classification {
            classification,
            value,
        }) => ConditionTerm::float32_classification(
            substitute_bitvector_variable(value, from, to),
            *classification,
        ),
        ConditionTerm::Float64(FloatCondition::Comparison {
            operator,
            left,
            right,
        }) => ConditionTerm::float64_compare(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
            *operator,
        ),
        ConditionTerm::Float64(FloatCondition::Classification {
            classification,
            value,
        }) => ConditionTerm::float64_classification(
            substitute_bitvector_variable(value, from, to),
            *classification,
        ),
        ConditionTerm::AddressOffsetEqual(left, right) => ConditionTerm::address_offset_equal(
            substitute_bitvector_variable_in_pointer_offset(left, from, to),
            substitute_bitvector_variable_in_pointer_offset(right, from, to),
        ),
        ConditionTerm::PointerEqual(left, right) => ConditionTerm::PointerEqual(
            Box::new(left.map_pointers(|p| substitute_bitvector_variable_in_pointer(p, from, to))),
            Box::new(right.map_pointers(|p| substitute_bitvector_variable_in_pointer(p, from, to))),
        ),
        ConditionTerm::AddressEqual(left, right) => ConditionTerm::address_equal(
            substitute_bitvector_variable_in_pointer(left, from, to),
            substitute_bitvector_variable_in_pointer(right, from, to),
        ),
        condition if condition.is_bool_value_form() => condition
            .map_bool_value_form(
                |child| substitute_bitvector_variable_in_condition(child, from, to),
                |argument| {
                    substitute_bitvector_variable_in_pure_function_argument(argument, from, to)
                },
                |memory, pointer| {
                    (
                        substitute_bitvector_variable_in_shared_memory(memory, from, to),
                        substitute_bitvector_variable_in_pointer(pointer, from, to),
                    )
                },
            )
            .expect("a `Bool` value form maps"),
        ConditionTerm::Compare {
            format,
            relation,
            left,
            right,
        } if *relation != CompareRelation::Equal
            && matches!(
                format,
                MachineIntegerType::Int8
                    | MachineIntegerType::UInt8
                    | MachineIntegerType::Int16
                    | MachineIntegerType::UInt16
                    | MachineIntegerType::Int32
                    | MachineIntegerType::UInt32
                    | MachineIntegerType::Int64
                    | MachineIntegerType::UInt64
            ) =>
        {
            let left = substitute_bitvector_variable(left, from, to);
            let right = substitute_bitvector_variable(right, from, to);
            if format.constant_from_term(&left).is_some()
                && format.constant_from_term(&right).is_some()
            {
                crate::kernel::machine_integer::comparison::logical_condition_for_operand_views(
                    *format,
                    *relation,
                    [
                        crate::kernel::MachineOperandView::Legacy(&left),
                        crate::kernel::MachineOperandView::Legacy(&right),
                    ],
                )
            } else {
                let (operator, _, _) = condition.as_bitvector_comparison().expect("native order");
                operator.build(left, right)
            }
        }
        condition => {
            let (op, left, right) = condition
                .as_bitvector_comparison()
                .expect("every other condition has its own arm");
            op.build(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
    }
}

fn substitute_through_load_variable(
    variable: Variable,
    from: Variable,
    to: &MachineTerm,
) -> Option<MachineTerm> {
    if !crate::kernel::is_load_variable(&variable) {
        return None;
    }
    let (memory, pointer) = crate::kernel::eval::registered_load_for_variable(&variable)?;
    let kind = crate::kernel::eval::registered_load_kind_for_variable(&variable)?;
    let substituted_pointer = Address {
        base: pointer.base.clone(),
        offset: substitute_bitvector_variable_in_pointer_offset(&pointer.offset, from, to),
    };
    // Deciding that this load variable is untouched means rewriting the
    // state it was minted against, whose own cells hold further load
    // variables. Going through the interned-state memo makes the common
    // "nothing changed" answer a lookup instead of a fresh rebuild of the
    // whole reachable state DAG, and compares the result by arena identity
    // rather than by deep structural equality.
    let substituted_memory = substitute_bitvector_variable_in_shared_memory(&memory, from, to);
    if substituted_pointer == pointer && substituted_memory == memory {
        return None;
    }
    // A load variable's state is the canonical projection of the state
    // the load read, cut down to what that one address can observe. The
    // projection is recorded per `(projected, address)`, and the history walk
    // reaches the source through that record. A substituted address has none,
    // so a load renamed or instantiated here would be stranded at a state
    // with no history, where the same read lowered directly for the new
    // address (an `intro`duced binder, say) crosses the steps back to the
    // source. Substitute from the source instead and let `canonical_term`
    // project it for the new address and record that projection, exactly as
    // a direct lowering does. Sound: two states with one projection agree
    // on every cell the address may observe for every value of its
    // variables, and an instance observes no more of them than that.
    let substituted_memory = if substituted_pointer == pointer {
        substituted_memory
    } else {
        match super::memory_resolution::canonical_load_projection_source(&memory, &pointer) {
            Some(source) => substitute_bitvector_variable_in_shared_memory(&source, from, to),
            None => substituted_memory,
        }
    };
    // Instantiation preserves the original read's byte dependency. Without
    // it, a four-byte scalar at the rewritten address falls back to the
    // eight-byte footprint also used by 32-bit (`Int32`) pointer coordinates.
    if let Some(bytes) = crate::kernel::registered_load_bytes_for_variable(&variable) {
        crate::kernel::eval::record_load_access_width(
            substituted_memory.memory(),
            &substituted_pointer,
            bytes,
        );
    }
    Some(crate::kernel::eval::canonical_term(
        &MachineTerm::MemoryLoad(
            ProgramPoint::at(&substituted_memory),
            Box::new(substituted_pointer),
            kind,
        ),
    ))
}

pub(crate) fn substitute_bitvector_variable(
    term: &MachineTerm,
    from: Variable,
    to: &MachineTerm,
) -> MachineTerm {
    match term {
        MachineTerm::ThreadHandle(_) => term.clone(),
        MachineTerm::Constant { .. } => term.clone(),
        MachineTerm::Variable(variable) if *variable == from => to.clone(),
        MachineTerm::Variable(variable) => {
            // A load variable can represent a load whose address mentions
            // the substituted variable (a universal's body contains `p[k]`
            // with the bound `k` inside the address). Substitution reaches
            // through the variable into the load and takes the canonical
            // form of the result, so instantiating a universal yields the
            // same load variable as a direct read of that cell.
            substitute_through_load_variable(*variable, from, to)
                .unwrap_or(MachineTerm::Variable(*variable))
        }
        MachineTerm::BoolCast { to: format, value } => MachineTerm::bool_cast(
            *format,
            substitute_bitvector_variable_in_condition(value, from, to),
        ),
        MachineTerm::If {
            condition,
            then_term,
            else_term,
        } => MachineTerm::if_then_else(
            substitute_bitvector_variable_in_condition(condition, from, to),
            substitute_bitvector_variable(then_term, from, to),
            substitute_bitvector_variable(else_term, from, to),
        ),
        MachineTerm::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            let mut body = body.as_ref().clone();
            let original_accumulator = *accumulator;
            let original_item = *item;
            let mut accumulator = *accumulator;
            let mut item = *item;
            let mut replacement_variables = BTreeSet::new();
            collect_bitvector_variables(to, &mut replacement_variables);

            // A fold binder shadows `from` in the body, so no substitution
            // enters that body in this case. Otherwise rename a binder that
            // occurs in the replacement before descending into the body.
            // The fresh names are reserved against both free and nested fold
            // variables, so the two renames cannot collide with one another.
            if original_accumulator != from && replacement_variables.contains(&accumulator) {
                let mut reserved = BTreeSet::new();
                collect_bitvector_variables(&body, &mut reserved);
                collect_bitvector_bound_variables(&body, &mut reserved);
                reserved.extend(replacement_variables.iter().copied());
                reserved.insert(from);
                reserved.insert(accumulator);
                reserved.insert(item);
                let mut fresh = KernelVariableGenerator::fresh_for(0, reserved);
                let renamed = fresh.next();
                body = substitute_bitvector_variable(
                    &body,
                    accumulator,
                    &MachineTerm::Variable(renamed),
                );
                accumulator = renamed;
            }
            if original_item != from && replacement_variables.contains(&item) {
                let mut reserved = BTreeSet::new();
                collect_bitvector_variables(&body, &mut reserved);
                collect_bitvector_bound_variables(&body, &mut reserved);
                reserved.extend(replacement_variables.iter().copied());
                reserved.insert(from);
                reserved.insert(accumulator);
                reserved.insert(item);
                let mut fresh = KernelVariableGenerator::fresh_for(0, reserved);
                let renamed = fresh.next();
                body = substitute_bitvector_variable(&body, item, &MachineTerm::Variable(renamed));
                item = renamed;
            }
            if original_accumulator != from && original_item != from {
                body = substitute_bitvector_variable(&body, from, to);
            }
            MachineTerm::range_fold(
                substitute_bitvector_variable(start, from, to),
                substitute_bitvector_variable(end, from, to),
                substitute_bitvector_variable(initial, from, to),
                accumulator,
                item,
                body,
            )
        }
        MachineTerm::PureFunctionApplication { name, arguments } => {
            MachineTerm::rebuild_pure_application(
                name.clone(),
                arguments
                    .iter()
                    .map(|argument| substitute_bitvector_variable(argument, from, to))
                    .collect(),
            )
        }
        MachineTerm::ClickFunctionApplication { name, arguments } => {
            MachineTerm::ClickFunctionApplication {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| {
                        substitute_bitvector_variable_in_pure_function_argument(argument, from, to)
                    })
                    .collect(),
            }
        }
        MachineTerm::AlgebraicMatch { scrutinee, arms } => MachineTerm::AlgebraicMatch {
            scrutinee: Box::new(substitute_bitvector_variable_in_algebraic_term(
                scrutinee, from, to,
            )),
            arms: arms
                .iter()
                .map(|arm| AlgebraicBitvectorMatchArm {
                    binding_names: arm.binding_names.clone(),
                    variant: arm.variant.clone(),
                    bindings: arm
                        .bindings
                        .iter()
                        .map(|binding| {
                            substitute_bitvector_variable_in_algebraic_value(binding, from, to)
                        })
                        .collect(),
                    body: substitute_bitvector_variable(&arm.body, from, to),
                })
                .collect(),
        },
        MachineTerm::MemoryLoad(memory, pointer, kind) => {
            let rewritten_memory =
                substitute_bitvector_variable_in_shared_memory(memory.shared_memory(), from, to);
            let rewritten_pointer = substitute_bitvector_variable_in_pointer(pointer, from, to);
            if rewritten_memory == *memory.shared_memory() && rewritten_pointer == **pointer {
                return term.clone();
            }
            let read = crate::kernel::eval::scalar_read_observation(
                crate::kernel::MachineOperandView::Legacy(term),
            )
            .expect("structural read");
            // A projected state is indexed by the address it was selected
            // for. Renaming that address must project the original source
            // again, just as direct lowering at the new binder does.
            if rewritten_pointer != **pointer
                && let Some(source) = super::memory_resolution::canonical_load_projection_source(
                    memory.shared_memory(),
                    pointer,
                )
            {
                let source = substitute_bitvector_variable_in_shared_memory(&source, from, to);
                crate::kernel::eval::record_load_access_width(
                    source.memory(),
                    &rewritten_pointer,
                    read.bytes,
                );
                return crate::kernel::eval::canonical_term(&MachineTerm::MemoryLoad(
                    ProgramPoint::at(&source),
                    Box::new(rewritten_pointer),
                    *kind,
                ));
            }
            crate::kernel::eval::scalar_read_for_exact_cell(
                &rewritten_memory,
                &rewritten_pointer,
                *kind,
                read.bytes,
            )
        }
        MachineTerm::IntegerAddress(pointer, class) => MachineTerm::object_pointer_address(
            substitute_bitvector_variable_in_pointer(pointer, from, to),
            class.class(),
        ),
        MachineTerm::IntegerToMachine { value, destination } => MachineTerm::IntegerToMachine {
            value: substitute_bitvector_variable_in_integer(value.as_ref(), from, to).into(),
            destination: *destination,
        },
        term => match (term.as_binary(), term.as_unary()) {
            (Some((op, left, right)), _) => op.build(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            ),
            (_, Some((op, value))) => op.build(substitute_bitvector_variable(value, from, to)),
            _ => unreachable!("every other variant has its own arm"),
        },
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_pointer_offset(
    offset: &AddressOffset,
    from: Variable,
    to: &MachineTerm,
) -> AddressOffset {
    substitute_bitvector_variable_in_pointer_offset_cow(offset, from, to).into_owned()
}

/// Keep an unchanged pointer spelling intact. Rebuilding every `Add` through
/// the normalizing constructor changes an otherwise untouched memory cell's
/// key, which in turn mints a different state for a binder rename that did
/// not occur anywhere in that cell.
fn substitute_bitvector_variable_in_pointer_offset_cow<'a>(
    offset: &'a AddressOffset,
    from: Variable,
    to: &MachineTerm,
) -> std::borrow::Cow<'a, AddressOffset> {
    use std::borrow::Cow;
    match offset {
        AddressOffset::Constant(_) | AddressOffset::Variable(_) => Cow::Borrowed(offset),
        AddressOffset::Add(left, right) => {
            let left = substitute_bitvector_variable_in_pointer_offset_cow(left, from, to);
            let right = substitute_bitvector_variable_in_pointer_offset_cow(right, from, to);
            if matches!((&left, &right), (Cow::Borrowed(_), Cow::Borrowed(_))) {
                Cow::Borrowed(offset)
            } else {
                Cow::Owned(AddressOffset::add(left.into_owned(), right.into_owned()))
            }
        }
        AddressOffset::Int32Scaled { value, byte_width } => {
            let rewritten = crate::kernel::memory_history::map_shared_pointer_index_with_fold(
                value,
                |leaf| Some(substitute_bitvector_variable(leaf, from, to)),
                crate::kernel::proof::equality_rewrite::rebuild_normalized_machine_node,
                |_| true,
                |root| {
                    let source = MachineTerm::Variable(from);
                    let mut rewrite =
                        crate::kernel::proof::term_rewrite::TermRewrite::for_bits(&source, to);
                    rewrite.enable_registered_load_resolution();
                    let result = rewrite.shared_machine_operand(root);
                    let refusal = rewrite.refusal();
                    result.filter(|_| refusal.is_none()).map(Some).ok_or(())
                },
            )
            .unwrap_or_else(|| value.clone());
            let unchanged =
                crate::kernel::memory_history::pointer_index_syntax_equal(value, &rewritten);
            if unchanged {
                Cow::Borrowed(offset)
            } else {
                Cow::Owned(crate::kernel::memory_history::rebuild_scaled_pointer_index(
                    rewritten,
                    *byte_width,
                    None,
                ))
            }
        }
        AddressOffset::Int64Scaled {
            value,
            byte_width,
            unsigned,
        } => {
            let rewritten = crate::kernel::memory_history::map_shared_pointer_index_with_fold(
                value,
                |leaf| Some(substitute_bitvector_variable(leaf, from, to)),
                crate::kernel::proof::equality_rewrite::rebuild_normalized_machine_node,
                |_| true,
                |root| {
                    let source = MachineTerm::Variable(from);
                    let mut rewrite =
                        crate::kernel::proof::term_rewrite::TermRewrite::for_bits(&source, to);
                    rewrite.enable_registered_load_resolution();
                    let result = rewrite.shared_machine_operand(root);
                    let refusal = rewrite.refusal();
                    result.filter(|_| refusal.is_none()).map(Some).ok_or(())
                },
            )
            .unwrap_or_else(|| value.clone());
            let unchanged =
                crate::kernel::memory_history::pointer_index_syntax_equal(value, &rewritten);
            if unchanged {
                Cow::Borrowed(offset)
            } else {
                Cow::Owned(crate::kernel::memory_history::rebuild_scaled_pointer_index(
                    rewritten,
                    *byte_width,
                    Some(*unsigned),
                ))
            }
        }
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_pointer(
    pointer: &Address,
    from: Variable,
    to: &MachineTerm,
) -> Address {
    if matches!(pointer.base, AddressBase::PureFunctionApplication(_)) {
        let source = MachineTerm::Variable(from);
        let term = Term::ProgramValue(ProgramValue::pointer(pointer.clone()));
        let Some(ProgramValue::Pointer(result)) =
            crate::kernel::proof::term_rewrite::TermRewrite::for_bits(&source, to)
                .term(&term)
                .into_program_value_native()
        else {
            unreachable!()
        };
        return result.into_pointer();
    }
    Address {
        base: pointer.base.clone(),
        offset: substitute_bitvector_variable_in_pointer_offset(&pointer.offset, from, to),
    }
}

/// One in-flight `(from, to)` substitution's already-rewritten states.
///
/// A `MemoryLoad` term carries a whole state, and a state's cells can
/// hold further `MemoryLoad` terms, so the terms a proof builds form a DAG of
/// states rather than a tree. Rewriting one variable used to walk that DAG
/// as a tree, re-deriving and re-interning every shared state once per path
/// that reaches it: in `mdtests/rb_replace_node_with_children.md`, whose three
/// nested `unfold`s name a cell at each level, 96 variable substitutions cost
/// 965,776 state rebuilds.
///
/// SymbolicMemory states are interned, so the rewrite of one is a pure function of its
/// arena id and the `(from, to)` pair. Keyed by that id, each distinct
/// state is rebuilt exactly once per substitution and the walk becomes
/// linear in the DAG's nodes. The frame holds the borrowed replacement term's
/// address: the term is alive for as long as the frame, so an equal address is
/// the same object with the same contents, the argument
/// `PureFactContextIdScope` uses.
struct SubstitutedMemoryFrame {
    from: Variable,
    to: usize,
    substituted: std::collections::HashMap<(u32, u32), SharedMemory>,
}

thread_local! {
    static SUBSTITUTED_MEMORIES: std::cell::RefCell<Vec<SubstitutedMemoryFrame>> =
        const { std::cell::RefCell::new(Vec::new()) };
    /// Interned states a variable was found not to occur in. A quantified
    /// fact over `m[p + j]` names its binder only in the address, never in
    /// the state, yet each instantiation used to rewrite the whole
    /// state again: the arena pipeline's order decisions instantiate its
    /// frames once per candidate term. The answer depends only on the
    /// immutable state and the variable, so it is kept across
    /// substitutions; the key names the arena, so a reset arena misses.
    static MEMORY_LACKS_VARIABLE: std::cell::RefCell<
        std::collections::HashSet<((u32, u32), Variable)>,
    > = std::cell::RefCell::new(std::collections::HashSet::new());
}

/// Entries kept before the absent-variable memo is cleared.
const MEMORY_LACKS_VARIABLE_LIMIT: usize = 1 << 20;

/// Opens (or joins) the state memo for one `(from, to)` substitution.
struct SubstitutedMemoryScope {
    pushed: bool,
}

impl SubstitutedMemoryScope {
    fn enter(from: Variable, to: &MachineTerm) -> Self {
        let address = to as *const MachineTerm as usize;
        let joined = SUBSTITUTED_MEMORIES.with(|frames| {
            frames
                .borrow()
                .last()
                .is_some_and(|frame| frame.from == from && frame.to == address)
        });
        if joined {
            return Self { pushed: false };
        }
        SUBSTITUTED_MEMORIES.with(|frames| {
            frames.borrow_mut().push(SubstitutedMemoryFrame {
                from,
                to: address,
                substituted: std::collections::HashMap::new(),
            });
        });
        Self { pushed: true }
    }
}

impl Drop for SubstitutedMemoryScope {
    fn drop(&mut self) {
        if self.pushed {
            SUBSTITUTED_MEMORIES.with(|frames| {
                frames.borrow_mut().pop();
            });
        }
    }
}

/// Rewrites one variable inside an interned state, reusing this
/// substitution's earlier answer for the same state.
fn substitute_bitvector_variable_in_shared_memory(
    memory: &SharedMemory,
    from: Variable,
    to: &MachineTerm,
) -> SharedMemory {
    let identity = memory.arena_id();
    if memory_lacks_variable(identity, from) {
        return memory.clone();
    }
    let _scope = SubstitutedMemoryScope::enter(from, to);
    let substituted = SUBSTITUTED_MEMORIES.with(|frames| {
        frames
            .borrow()
            .last()
            .and_then(|frame| frame.substituted.get(&identity).cloned())
    });
    if let Some(substituted) = substituted {
        return substituted;
    }
    let substituted = crate::kernel::intern_memory(rewrite_memory_state(memory.memory(), from, to));
    if substituted == *memory {
        record_memory_lacks_variable(identity, from);
    }
    SUBSTITUTED_MEMORIES.with(|frames| {
        if let Some(frame) = frames.borrow_mut().last_mut() {
            frame.substituted.insert(identity, substituted.clone());
        }
    });
    substituted
}

/// Rewrites one variable throughout a memory state.
///
/// This is the unit of work the state DAG multiplies, so it is a named
/// profiler operation charged its state's size: a rewrite that revisits one
/// shared state once per reaching path shows up as `substitution: state
/// rewrite` growing far faster than the proof, which is what `click profile`
/// could not point at before.
pub(in crate::kernel) fn substitute_bitvector_variable_in_memory(
    memory: &SymbolicMemory,
    from: Variable,
    to: &MachineTerm,
) -> SymbolicMemory {
    // A state carried by value (a loadability or effect proposition) is
    // interned only to consult and fill the absent-variable memo; interning
    // an already-registered state is a shallow lookup.
    let shared = crate::kernel::intern_memory(memory.clone());
    let identity = shared.arena_id();
    if memory_lacks_variable(identity, from) {
        return memory.clone();
    }
    let substituted = rewrite_memory_state(memory, from, to);
    if crate::kernel::intern_memory(substituted.clone()) == shared {
        record_memory_lacks_variable(identity, from);
    }
    substituted
}

/// The slot of `run` whose own load `from` is, when `from` is a load variable
/// registered at one of the run's slot pointers. A substitution of that
/// variable rewrites that slot's value and, in a run whose slots are uniform,
/// no other slot: each other slot's value is a different load variable, and
/// what it mentions (the run's base, a constant shift, the memory it is named
/// at) is what the other slots of its shape mention too.
fn run_slot_named_by_load_variable(
    run: &crate::kernel::primitives::CellRun,
    from: Variable,
) -> Option<u32> {
    if let crate::kernel::primitives::RunValueMode::Copy { source_base } = run.value_mode() {
        let source_run = crate::kernel::primitives::CellRun::new(
            source_base.clone(),
            run.element_width(),
            run.element_type(),
            run.count(),
            run.source().clone(),
            run.holes().clone(),
        );
        return run_slot_named_by_load_variable(&source_run, from);
    }
    if !crate::kernel::is_load_variable(&from) {
        return None;
    }
    let (_, pointer) = crate::kernel::eval::registered_load_for_variable(&from)?;
    // The registered pointer may spell the slot differently from the run
    // (a folded constant shift), so the slot is found by its distance from
    // the run's base.
    if let Some(index) = run.live_slot_index(&pointer) {
        return Some(index);
    }
    let crate::kernel::reasoning::memory_resolution::RunAccess::Shift(shift) =
        crate::kernel::reasoning::memory_resolution::run_access(run, &pointer)
    else {
        return None;
    };
    let width = i64::from(run.element_width());
    if shift < 0 || width == 0 || shift % width != 0 {
        return None;
    }
    let index = u32::try_from(shift / width).ok()?;
    (index < run.count() && !run.holes().contains(index)).then_some(index)
}

fn rewrite_memory_state(
    memory: &SymbolicMemory,
    from: Variable,
    to: &MachineTerm,
) -> SymbolicMemory {
    crate::instrumentation::measure_operation(
        "kernel",
        "substitution",
        "substitution: state rewrite",
        || substitute_bitvector_variable_in_memory_contents(memory, from, to),
    )
}

fn memory_lacks_variable(identity: (u32, u32), from: Variable) -> bool {
    let absent = MEMORY_LACKS_VARIABLE.with(|absent| absent.borrow().contains(&(identity, from)));
    if absent {
        crate::instrumentation::record_deterministic_work(1);
    }
    absent
}

fn record_memory_lacks_variable(identity: (u32, u32), from: Variable) {
    MEMORY_LACKS_VARIABLE.with(|absent| {
        let mut absent = absent.borrow_mut();
        if absent.len() >= MEMORY_LACKS_VARIABLE_LIMIT {
            absent.clear();
        }
        absent.insert((identity, from));
    });
}

#[cfg(test)]
#[test]
fn state_size_substitution_preserves_declared_types_and_write_protection() {
    let from = Variable(84001);
    let mut memory = SymbolicMemory::new().with_declared_scalar_block(
        "local:word".into(),
        4,
        ProgramType::UInt32,
    );
    let mut read_only = MemoryBlock::read_only(4);
    read_only.size = AllocationSize::int32(MachineTerm::Variable(from));
    std::sync::Arc::make_mut(&mut memory.blocks).insert("global:protected".into(), read_only);
    let rewritten =
        substitute_bitvector_variable_in_memory_contents(&memory, from, &MachineTerm::constant(16));
    assert_eq!(
        rewritten.blocks.get(&AddressBase::from("local:word")),
        memory.blocks.get(&AddressBase::from("local:word"))
    );
    let protected = rewritten
        .blocks
        .get(&AddressBase::from("global:protected"))
        .unwrap();
    assert!(protected.read_only);
    assert_eq!(protected.size, AllocationSize::int32(16));
}

fn substitute_bitvector_variable_in_memory_contents(
    memory: &SymbolicMemory,
    from: Variable,
    to: &MachineTerm,
) -> SymbolicMemory {
    crate::instrumentation::record_deterministic_work(
        memory.cells.representation_len() + memory.union_cells.len() + memory.blocks.len(),
    );
    let cells = std::sync::Arc::new(memory.cells.map_cells(
        |pointer, value| {
            (
                substitute_bitvector_variable_in_pointer(pointer, from, to),
                substitute_bitvector_variable_in_program_value(value, from, to),
            )
        },
        |run| run_slot_named_by_load_variable(run, from),
    ));
    let mut result = SymbolicMemory {
        construction: None,
        pending_steps: None,
        blocks: std::sync::Arc::new(
            memory
                .blocks
                .iter()
                .map(|(block, contents)| {
                    // Substitution changes the size term, not the storage
                    // declaration or its write protection. Rebuilding a bare
                    // block erased these properties, even for a constant size.
                    let mut rewritten = contents.clone();
                    rewritten.size = contents
                        .allocation_size()
                        .map_bytes(|bytes| substitute_bitvector_variable(bytes, from, to));
                    (block.clone(), rewritten)
                })
                .collect(),
        ),
        cells,
        union_cells: std::sync::Arc::new(
            memory
                .union_cells
                .iter()
                .map(|((pointer, program_type), value)| {
                    (
                        (
                            substitute_bitvector_variable_in_pointer(pointer, from, to),
                            *program_type,
                        ),
                        value.with_native_value(substitute_bitvector_variable_in_program_value(
                            value.native(),
                            from,
                            to,
                        )),
                    )
                })
                .collect(),
        ),
        // Carried unrewritten. The mark inside is an identity, not an
        // address or a value, and a rewritten state that dropped it could
        // re-intern as a state that forgot nothing.
        forgotten: memory.forgotten.clone(),
        heap: std::sync::Arc::new(HeapMemory {
            live_allocations: memory
                .heap
                .live_allocations
                .iter()
                .map(|(base, bytes)| {
                    (
                        substitute_bitvector_variable_in_pointer(base, from, to),
                        bytes.map_bytes(|bytes| substitute_bitvector_variable(bytes, from, to)),
                    )
                })
                .collect(),
            deallocated_allocations: memory
                .heap
                .deallocated_allocations
                .iter()
                .map(|(base, bytes)| {
                    (
                        substitute_bitvector_variable_in_pointer(base, from, to),
                        bytes.map_bytes(|bytes| substitute_bitvector_variable(bytes, from, to)),
                    )
                })
                .collect(),
            pending_object_classes: memory
                .heap
                .pending_object_classes
                .iter()
                .map(|(base, class)| {
                    (
                        substitute_bitvector_variable_in_pointer(base, from, to),
                        class.clone(),
                    )
                })
                .collect(),
            pending_allocations: memory
                .heap
                .pending_allocations
                .iter()
                .map(|(base, bytes)| {
                    (
                        substitute_bitvector_variable_in_pointer(base, from, to),
                        bytes.map_bytes(|bytes| substitute_bitvector_variable(bytes, from, to)),
                    )
                })
                .collect(),
            uninitialized_objects: memory
                .heap
                .uninitialized_objects
                .iter()
                .map(|(base, bytes)| {
                    (
                        substitute_bitvector_variable_in_pointer(base, from, to),
                        *bytes,
                    )
                })
                .collect(),
            uninitialized_allocations: memory
                .heap
                .uninitialized_allocations
                .iter()
                .map(|base| substitute_bitvector_variable_in_pointer(base, from, to))
                .collect(),
            initialized: memory.heap.initialized.map_pointers(
                |pointer| substitute_bitvector_variable_in_pointer(pointer, from, to),
                |value| substitute_bitvector_variable_in_program_value(value, from, to),
            ),
            zeroed_allocations: memory
                .heap
                .zeroed_allocations
                .iter()
                .map(|base| substitute_bitvector_variable_in_pointer(base, from, to))
                .collect(),
            zeroed_prefix_allocations: memory
                .heap
                .zeroed_prefix_allocations
                .iter()
                .map(|(base, prefix)| {
                    (
                        substitute_bitvector_variable_in_pointer(base, from, to),
                        substitute_bitvector_variable(prefix, from, to),
                    )
                })
                .collect(),
            zeroed_pending_allocations: memory
                .heap
                .zeroed_pending_allocations
                .iter()
                .map(|base| substitute_bitvector_variable_in_pointer(base, from, to))
                .collect(),
            pending_reallocations: memory
                .heap
                .pending_reallocations
                .iter()
                .map(|(base, pending)| {
                    (
                        substitute_bitvector_variable_in_pointer(base, from, to),
                        PendingReallocation {
                            old_pointer: substitute_bitvector_variable_in_pointer(
                                &pending.old_pointer,
                                from,
                                to,
                            ),
                            old_bytes: pending
                                .old_bytes
                                .map_bytes(|bytes| substitute_bitvector_variable(bytes, from, to)),
                            zeroed_prefix: pending
                                .zeroed_prefix
                                .as_ref()
                                .map(|prefix| substitute_bitvector_variable(prefix, from, to)),
                            retirement_separation: pending.retirement_separation.as_ref().map(
                                |goal| {
                                    std::sync::Arc::new(
                                        substitute_bitvector_variable_in_proposition(
                                            goal, from, to,
                                        ),
                                    )
                                },
                            ),
                            initialized_prefix: pending.initialized_prefix.clone(),
                            copied_cells: pending
                                .copied_cells
                                .iter()
                                .map(|(offset, value)| {
                                    (
                                        substitute_bitvector_variable_in_pointer_offset(
                                            offset, from, to,
                                        ),
                                        substitute_bitvector_variable_in_program_value(
                                            value, from, to,
                                        ),
                                    )
                                })
                                .collect(),
                        },
                    )
                })
                .collect(),
            effective_types: memory.heap.effective_types.map_entries(
                |pointer| substitute_bitvector_variable_in_pointer(pointer, from, to),
                |value| substitute_bitvector_variable_in_program_value(value, from, to),
            ),
        }),
    };
    result.record_diagnostic_transform(
        "substitute scalar variable",
        vec![memory.clone()],
        vec![
            ProgramValue::Int32(MachineTerm::Variable(from)),
            ProgramValue::Int32(to.clone()),
        ],
    );
    result
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_program_value(
    value: &ProgramValue,
    from: Variable,
    to: &MachineTerm,
) -> ProgramValue {
    match value {
        ProgramValue::PointerInteger(record) => ProgramValue::PointerInteger(PointerIntegerValue {
            kind: record.kind.clone(),
            numeric: Box::new(substitute_bitvector_variable_in_program_value(
                &record.numeric,
                from,
                to,
            )),
            pointer: Box::new(
                record
                    .pointer
                    .map_pointers(|p| substitute_bitvector_variable_in_pointer(p, from, to)),
            ),
        }),
        ProgramValue::Parameter(term) => ProgramValue::Parameter(Box::new(
            substitute_bitvector_variable_in_algebraic_term(term, from, to),
        )),
        ProgramValue::Void => ProgramValue::Void,
        ProgramValue::Bool(bits) => {
            ProgramValue::Bool(substitute_bitvector_variable(bits, from, to))
        }
        ProgramValue::Int8(bits) => int8(substitute_bitvector_variable(bits, from, to)),
        ProgramValue::Int16(bits) => int16(substitute_bitvector_variable(bits, from, to)),
        ProgramValue::Int32(bits) => int32(substitute_bitvector_variable(bits, from, to)),
        ProgramValue::UInt8(bits) => uint8(substitute_bitvector_variable(bits, from, to)),
        ProgramValue::UInt16(bits) => uint16(substitute_bitvector_variable(bits, from, to)),
        ProgramValue::UInt32(bits) => uint32(substitute_bitvector_variable(bits, from, to)),
        ProgramValue::Int64(bits) => {
            ProgramValue::Int64(substitute_bitvector_variable(bits, from, to))
        }
        ProgramValue::UInt64(bits) => {
            ProgramValue::UInt64(substitute_bitvector_variable(bits, from, to))
        }
        ProgramValue::Int128(bits) => {
            ProgramValue::Int128(substitute_bitvector_variable(bits, from, to))
        }
        ProgramValue::UInt128(bits) => {
            ProgramValue::UInt128(substitute_bitvector_variable(bits, from, to))
        }
        ProgramValue::Float32(bits) => {
            ProgramValue::Float32(substitute_bitvector_variable(bits, from, to))
        }
        ProgramValue::Float64(bits) => {
            ProgramValue::Float64(substitute_bitvector_variable(bits, from, to))
        }
        ProgramValue::Pointer(pointer) => {
            ProgramValue::Pointer(pointer.map_pointers(|address| {
                substitute_bitvector_variable_in_pointer(address, from, to)
            }))
        }
    }
}

fn pointer_capture_avoiding_quantifier_body(
    binder: Variable,
    sort: &Sort,
    body: &Proposition,
    from: Variable,
    replacement: &Address,
) -> (Proposition, Variable) {
    let mut replacement_variables = BTreeSet::new();
    collect_pointer_bound_variables(replacement, &mut replacement_variables);
    if !replacement_variables.contains(&binder)
        || !matches!(
            sort,
            Sort::ProgramPointer(_) | Sort::ProgramObjectPointer(_, _)
        )
    {
        return (body.clone(), binder);
    }
    let mut reserved = crate::kernel::proposition_variables(body);
    reserved.insert(from);
    reserved.insert(binder);
    reserved.extend(replacement_variables);
    let fresh = KernelVariableGenerator::fresh_for(0, reserved).next();
    let pointer = match sort {
        Sort::ProgramPointer(ProgramType::FunctionPointer(_)) => Address::symbolic_function(fresh),
        Sort::ProgramPointer(_) | Sort::ProgramObjectPointer(_, _) => Address::symbolic(fresh),
        _ => unreachable!("pointer capture avoidance only handles pointer binders"),
    };
    (
        substitute_pointer_variable_in_proposition(body, binder, &pointer),
        fresh,
    )
}

fn substitute_pointer_variable_in_term(term: &Term, from: Variable, to: &Address) -> Term {
    match term {
        Term::Condition(condition) => Term::Condition(substitute_pointer_variable_in_condition(
            condition, from, to,
        )),
        Term::Integer(_) => {
            crate::kernel::proof::term_rewrite::TermRewrite::for_pointer_variable(from, to)
                .term(term)
        }
        Term::Bitvector32(_) | Term::PointerOffset(_) => term.clone(),
        Term::ProgramValue(value) => Term::ProgramValue(
            substitute_pointer_variable_in_program_value(value, from, to),
        ),
        Term::Sequence(sequence) => {
            Term::Sequence(substitute_pointer_variable_in_sequence(sequence, from, to))
        }
        Term::Algebraic(term) => Term::Algebraic(AlgebraicTerm {
            algebraic_type: term.algebraic_type.clone(),
            node: substitute_pointer_variable_in_algebraic_term_node(term, from, to),
        }),
        Term::Memory(memory) => {
            Term::Memory(substitute_pointer_variable_in_memory(memory, from, to))
        }
        Term::ExecutionState(state) => Term::ExecutionState(Box::new(
            substitute_pointer_variable_in_execution_state(state, from, to),
        )),
    }
}

fn substitute_pointer_variable_in_algebraic_term_node(
    term: &AlgebraicTerm,
    from: Variable,
    to: &Address,
) -> AlgebraicTermNode {
    match &term.node {
        AlgebraicTermNode::Variable(variable) => AlgebraicTermNode::Variable(*variable),
        AlgebraicTermNode::MemoryLoad {
            point: memory,
            pointer,
        } => {
            match substitute_pointer_variable_in_algebraic_value(
                &AlgebraicTermNode::memory_load_carrier_value(memory.shared_memory(), pointer),
                from,
                to,
            ) {
                AlgebraicValue::Program(value) => {
                    AlgebraicTermNode::memory_load_from_carrier(&value)
                        .unwrap_or_else(|| term.node.clone())
                }
                _ => term.node.clone(),
            }
        }
        AlgebraicTermNode::Constructor { variant, fields } => AlgebraicTermNode::Constructor {
            variant: variant.clone(),
            fields: fields
                .iter()
                .map(|field| substitute_pointer_variable_in_algebraic_value(field, from, to))
                .collect(),
        },
        AlgebraicTermNode::Match { scrutinee, arms } => AlgebraicTermNode::Match {
            scrutinee: Box::new(substitute_pointer_variable_in_algebraic_term(
                scrutinee, from, to,
            )),
            arms: arms
                .iter()
                .map(|arm| AlgebraicResultMatchArm {
                    binding_names: arm.binding_names.clone(),
                    variant: arm.variant.clone(),
                    bindings: arm
                        .bindings
                        .iter()
                        .map(|binding| {
                            substitute_pointer_variable_in_algebraic_value(binding, from, to)
                        })
                        .collect(),
                    body: substitute_pointer_variable_in_algebraic_term(&arm.body, from, to),
                })
                .collect(),
        },
        AlgebraicTermNode::PureFunctionApplication { name, arguments } => {
            AlgebraicTermNode::PureFunctionApplication {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| {
                        substitute_pointer_variable_in_pure_function_argument(argument, from, to)
                    })
                    .collect(),
            }
        }
        AlgebraicTermNode::If {
            condition,
            then_term,
            else_term,
        } => AlgebraicTermNode::If {
            condition: Box::new(substitute_pointer_variable_in_condition(
                condition, from, to,
            )),
            then_term: Box::new(substitute_pointer_variable_in_algebraic_term(
                then_term, from, to,
            )),
            else_term: Box::new(substitute_pointer_variable_in_algebraic_term(
                else_term, from, to,
            )),
        },
    }
}

fn substitute_pointer_variable_in_algebraic_term(
    term: &AlgebraicTerm,
    from: Variable,
    to: &Address,
) -> AlgebraicTerm {
    AlgebraicTerm {
        algebraic_type: term.algebraic_type.clone(),
        node: substitute_pointer_variable_in_algebraic_term_node(term, from, to),
    }
}

fn substitute_pointer_variable_in_condition(
    condition: &ConditionTerm,
    from: Variable,
    to: &Address,
) -> ConditionTerm {
    match condition {
        ConditionTerm::IntegerLessThan(..)
        | ConditionTerm::IntegerLessEqual(..)
        | ConditionTerm::IntegerGreaterThan(..)
        | ConditionTerm::IntegerGreaterEqual(..)
        | ConditionTerm::IntegerEqual(..)
        | ConditionTerm::IntegerNotEqual(..) => {
            crate::kernel::proof::term_rewrite::TermRewrite::for_pointer_variable(from, to)
                .condition(condition)
        }
        ConditionTerm::AlgebraicEqual(left, right) => ConditionTerm::AlgebraicEqual(
            Box::new(substitute_pointer_variable_in_algebraic_term(
                left, from, to,
            )),
            Box::new(substitute_pointer_variable_in_algebraic_term(
                right, from, to,
            )),
        ),
        ConditionTerm::PointerEqual(..) => {
            crate::kernel::proof::term_rewrite::TermRewrite::for_pointer_variable(from, to)
                .condition(condition)
        }
        ConditionTerm::AddressEqual(left, right) => ConditionTerm::address_equal(
            substitute_pointer_variable_in_pointer(left, from, to),
            substitute_pointer_variable_in_pointer(right, from, to),
        ),
        // A `Bool` value's arguments and reads may name the pointer.
        condition if condition.is_bool_value_form() => {
            crate::kernel::proof::term_rewrite::TermRewrite::for_pointer_variable(from, to)
                .condition(condition)
        }
        condition => condition.clone(),
    }
}

fn substitute_pointer_variable_in_program_value(
    value: &ProgramValue,
    from: Variable,
    to: &Address,
) -> ProgramValue {
    let Term::ProgramValue(value) =
        crate::kernel::proof::term_rewrite::TermRewrite::for_pointer_variable(from, to)
            .term(&Term::ProgramValue(value.clone()))
    else {
        unreachable!("C value rewriting preserves its carrier")
    };
    value
}

fn substitute_pointer_variable_in_pointer(
    pointer: &Address,
    from: Variable,
    to: &Address,
) -> Address {
    if matches!(&pointer.base, AddressBase::PureFunctionApplication(_)) {
        let term = Term::ProgramValue(ProgramValue::pointer(pointer.clone()));
        let Some(ProgramValue::Pointer(result)) =
            crate::kernel::proof::term_rewrite::TermRewrite::for_pointer_variable(from, to)
                .term(&term)
                .into_program_value_native()
        else {
            unreachable!()
        };
        return result.into_pointer();
    }
    if matches!(pointer.base, AddressBase::ExternalObject(variable) if variable == from) {
        let identity = to.object_identity();
        return Address {
            base: identity.base,
            offset: AddressOffset::add(identity.offset, pointer.offset.clone()),
        };
    }
    let replaces_block = matches!(
        (&pointer.base, &to.base),
        (AddressBase::Symbolic(variable), _) | (AddressBase::FunctionSymbolic(variable), _)
            if *variable == from
    );
    let offset = pointer.offset.clone();
    if replaces_block {
        Address {
            base: to.base.clone(),
            offset: AddressOffset::add(to.offset.clone(), offset),
        }
    } else {
        pointer.clone()
    }
}

fn substitute_pointer_variable_in_program_expression(
    expression: &ProgramExpression,
    from: Variable,
    to: &Address,
) -> ProgramExpression {
    match expression {
        ProgramExpression::Value(value) => ProgramExpression::Value(
            substitute_pointer_variable_in_program_value(value, from, to),
        ),
        ProgramExpression::Variable(_)
        | ProgramExpression::StringLiteral(_)
        | ProgramExpression::FunctionAddress(_)
        | ProgramExpression::StepResult { .. } => expression.clone(),
        ProgramExpression::Cast {
            expression,
            target_type,
            integer_mode,
            pointee_struct,
            pointee_volatile,
            pointee_constant,
            explicit_qualification,
        } => ProgramExpression::Cast {
            expression: Box::new(substitute_pointer_variable_in_program_expression(
                expression, from, to,
            )),
            target_type: *target_type,
            integer_mode: *integer_mode,
            pointee_struct: pointee_struct.clone(),
            pointee_volatile: *pointee_volatile,
            pointee_constant: *pointee_constant,
            explicit_qualification: *explicit_qualification,
        },
        ProgramExpression::Ternary {
            condition,
            then_branch,
            else_branch,
        } => ProgramExpression::Ternary {
            condition: Box::new(substitute_pointer_variable_in_program_expression(
                condition, from, to,
            )),
            then_branch: Box::new(substitute_pointer_variable_in_program_expression(
                then_branch,
                from,
                to,
            )),
            else_branch: Box::new(substitute_pointer_variable_in_program_expression(
                else_branch,
                from,
                to,
            )),
        },
        ProgramExpression::FloatClassification {
            expression,
            classification,
        } => ProgramExpression::FloatClassification {
            expression: Box::new(substitute_pointer_variable_in_program_expression(
                expression, from, to,
            )),
            classification: *classification,
        },
        ProgramExpression::Negate(expression) => ProgramExpression::Negate(Box::new(
            substitute_pointer_variable_in_program_expression(expression, from, to),
        )),
        ProgramExpression::FloatNegate(expression) => ProgramExpression::FloatNegate(Box::new(
            substitute_pointer_variable_in_program_expression(expression, from, to),
        )),
        ProgramExpression::EnumConstruct {
            enum_type,
            variant,
            fields,
        } => ProgramExpression::EnumConstruct {
            enum_type: *enum_type,
            variant: variant.clone(),
            fields: fields
                .iter()
                .map(|field| substitute_pointer_variable_in_program_expression(field, from, to))
                .collect(),
        },
        ProgramExpression::EnumField {
            value,
            variant,
            index,
        } => ProgramExpression::EnumField {
            value: Box::new(substitute_pointer_variable_in_program_expression(
                value, from, to,
            )),
            variant: variant.clone(),
            index: *index,
        },
        ProgramExpression::EnumIs { value, variant } => ProgramExpression::EnumIs {
            value: Box::new(substitute_pointer_variable_in_program_expression(
                value, from, to,
            )),
            variant: variant.clone(),
        },
        ProgramExpression::AddressOf(body) => ProgramExpression::AddressOf(Box::new(
            substitute_pointer_variable_in_program_expression(body, from, to),
        )),
        ProgramExpression::CheckedObjectAddress(body) => {
            ProgramExpression::CheckedObjectAddress(Box::new(
                substitute_pointer_variable_in_program_expression(body, from, to),
            ))
        }
        ProgramExpression::PointerOffsetBytes { pointer, bytes } => {
            ProgramExpression::PointerOffsetBytes {
                pointer: Box::new(substitute_pointer_variable_in_program_expression(
                    pointer, from, to,
                )),
                bytes: *bytes,
            }
        }
        ProgramExpression::Subobject { pointer, width } => ProgramExpression::Subobject {
            pointer: Box::new(substitute_pointer_variable_in_program_expression(
                pointer, from, to,
            )),
            width: *width,
        },
        ProgramExpression::Load(body) => ProgramExpression::Load(Box::new(
            substitute_pointer_variable_in_program_expression(body, from, to),
        )),
        ProgramExpression::TypedLoad {
            pointer,
            value_type,
            volatile,
            pointee_constant,
            access_class,
            source,
        } => ProgramExpression::TypedLoad {
            pointer: Box::new(substitute_pointer_variable_in_program_expression(
                pointer, from, to,
            )),
            value_type: *value_type,
            volatile: *volatile,
            pointee_constant: *pointee_constant,
            access_class: access_class.clone(),
            source: source.clone(),
        },
        ProgramExpression::Not(body) | ProgramExpression::BitwiseNot(body) => {
            let body = Box::new(substitute_pointer_variable_in_program_expression(
                body, from, to,
            ));
            match expression {
                ProgramExpression::Not(_) => ProgramExpression::Not(body),
                ProgramExpression::BitwiseNot(_) => ProgramExpression::BitwiseNot(body),
                _ => unreachable!("the combined unary expression arm is exhaustive"),
            }
        }
        crate::kernel::binary_c_expression!(left, right) => {
            let left = Box::new(substitute_pointer_variable_in_program_expression(
                left, from, to,
            ));
            let right = Box::new(substitute_pointer_variable_in_program_expression(
                right, from, to,
            ));
            match expression {
                ProgramExpression::LessThan(_, _) => ProgramExpression::LessThan(left, right),
                ProgramExpression::LessEqual(_, _) => ProgramExpression::LessEqual(left, right),
                ProgramExpression::GreaterThan(_, _) => ProgramExpression::GreaterThan(left, right),
                ProgramExpression::GreaterEqual(_, _) => {
                    ProgramExpression::GreaterEqual(left, right)
                }
                ProgramExpression::Equal(_, _) => ProgramExpression::Equal(left, right),
                ProgramExpression::NotEqual(_, _) => ProgramExpression::NotEqual(left, right),
                ProgramExpression::And(_, _) => ProgramExpression::And(left, right),
                ProgramExpression::Or(_, _) => ProgramExpression::Or(left, right),
                ProgramExpression::Add(_, _) => ProgramExpression::Add(left, right),
                ProgramExpression::Subtract(_, _) => ProgramExpression::Subtract(left, right),
                ProgramExpression::Multiply(_, _) => ProgramExpression::Multiply(left, right),
                ProgramExpression::Divide(_, _) => ProgramExpression::Divide(left, right),
                ProgramExpression::Remainder(_, _) => ProgramExpression::Remainder(left, right),
                ProgramExpression::ShiftLeft(_, _) => ProgramExpression::ShiftLeft(left, right),
                ProgramExpression::RustShiftLeft(_, _) => {
                    ProgramExpression::RustShiftLeft(left, right)
                }
                ProgramExpression::ShiftRight(_, _) => ProgramExpression::ShiftRight(left, right),
                ProgramExpression::RustShiftRight(_, _) => {
                    ProgramExpression::RustShiftRight(left, right)
                }
                ProgramExpression::BitwiseAnd(_, _) => ProgramExpression::BitwiseAnd(left, right),
                ProgramExpression::BitwiseOr(_, _) => ProgramExpression::BitwiseOr(left, right),
                ProgramExpression::BitwiseXor(_, _) => ProgramExpression::BitwiseXor(left, right),
                ProgramExpression::Index(_, _) => ProgramExpression::Index(left, right),
                _ => unreachable!("the combined binary expression arm is exhaustive"),
            }
        }
    }
}

pub(crate) fn substitute_pointer_variable_in_memory(
    memory: &SymbolicMemory,
    from: Variable,
    to: &Address,
) -> SymbolicMemory {
    let mut result = SymbolicMemory {
        construction: None,
        pending_steps: None,
        blocks: std::sync::Arc::new(
            memory
                .blocks
                .iter()
                .map(|(block, contents)| {
                    (
                        substitute_pointer_variable_in_block(block, from, to),
                        contents.clone(),
                    )
                })
                .collect(),
        ),
        cells: std::sync::Arc::new(memory.cells.map_cells(
            |pointer, value| {
                (
                    substitute_pointer_variable_in_pointer(pointer, from, to),
                    substitute_pointer_variable_in_program_value(value, from, to),
                )
            },
            |_| None,
        )),
        union_cells: std::sync::Arc::new(
            memory
                .union_cells
                .iter()
                .map(|((pointer, program_type), value)| {
                    (
                        (
                            substitute_pointer_variable_in_pointer(pointer, from, to),
                            *program_type,
                        ),
                        value.with_native_value(substitute_pointer_variable_in_program_value(
                            value.native(),
                            from,
                            to,
                        )),
                    )
                })
                .collect(),
        ),
        forgotten: std::sync::Arc::new(ForgottenKnowledge {
            ended_local_blocks: memory
                .forgotten
                .ended_local_blocks
                .iter()
                .map(|block| substitute_pointer_variable_in_block(block, from, to))
                .collect(),
            // Carried unrewritten, for the reason given in
            // `substitute_bitvector_variable_in_memory_contents`.
            forgotten_from: memory.forgotten.forgotten_from,
            join_inputs: memory.forgotten.join_inputs.clone(),
        }),
        heap: std::sync::Arc::new(HeapMemory {
            live_allocations: memory
                .heap
                .live_allocations
                .iter()
                .map(|(base, bytes)| {
                    (
                        substitute_pointer_variable_in_pointer(base, from, to),
                        bytes.clone(),
                    )
                })
                .collect(),
            deallocated_allocations: memory
                .heap
                .deallocated_allocations
                .iter()
                .map(|(base, bytes)| {
                    (
                        substitute_pointer_variable_in_pointer(base, from, to),
                        bytes.clone(),
                    )
                })
                .collect(),
            pending_object_classes: memory
                .heap
                .pending_object_classes
                .iter()
                .map(|(base, class)| {
                    (
                        substitute_pointer_variable_in_pointer(base, from, to),
                        class.clone(),
                    )
                })
                .collect(),
            pending_allocations: memory
                .heap
                .pending_allocations
                .iter()
                .map(|(base, bytes)| {
                    (
                        substitute_pointer_variable_in_pointer(base, from, to),
                        bytes.clone(),
                    )
                })
                .collect(),
            uninitialized_objects: memory
                .heap
                .uninitialized_objects
                .iter()
                .map(|(base, bytes)| {
                    (
                        substitute_pointer_variable_in_pointer(base, from, to),
                        *bytes,
                    )
                })
                .collect(),
            uninitialized_allocations: memory
                .heap
                .uninitialized_allocations
                .iter()
                .map(|base| substitute_pointer_variable_in_pointer(base, from, to))
                .collect(),
            initialized: memory.heap.initialized.map_pointers(
                |pointer| substitute_pointer_variable_in_pointer(pointer, from, to),
                |value| substitute_pointer_variable_in_program_value(value, from, to),
            ),
            zeroed_allocations: memory
                .heap
                .zeroed_allocations
                .iter()
                .map(|base| substitute_pointer_variable_in_pointer(base, from, to))
                .collect(),
            zeroed_prefix_allocations: memory
                .heap
                .zeroed_prefix_allocations
                .iter()
                .map(|(base, prefix)| {
                    (
                        substitute_pointer_variable_in_pointer(base, from, to),
                        prefix.clone(),
                    )
                })
                .collect(),
            zeroed_pending_allocations: memory
                .heap
                .zeroed_pending_allocations
                .iter()
                .map(|base| substitute_pointer_variable_in_pointer(base, from, to))
                .collect(),
            pending_reallocations: memory
                .heap
                .pending_reallocations
                .iter()
                .map(|(base, pending)| {
                    (
                        substitute_pointer_variable_in_pointer(base, from, to),
                        PendingReallocation {
                            old_pointer: substitute_pointer_variable_in_pointer(
                                &pending.old_pointer,
                                from,
                                to,
                            ),
                            old_bytes: pending.old_bytes.clone(),
                            zeroed_prefix: pending.zeroed_prefix.clone(),
                            retirement_separation: pending.retirement_separation.as_ref().map(
                                |goal| {
                                    std::sync::Arc::new(substitute_pointer_variable_in_proposition(
                                        goal, from, to,
                                    ))
                                },
                            ),
                            initialized_prefix: pending.initialized_prefix.clone(),
                            copied_cells: pending
                                .copied_cells
                                .iter()
                                .map(|(offset, value)| {
                                    (
                                        offset.clone(),
                                        substitute_pointer_variable_in_program_value(
                                            value, from, to,
                                        ),
                                    )
                                })
                                .collect(),
                        },
                    )
                })
                .collect(),
            effective_types: memory.heap.effective_types.map_entries(
                |pointer| substitute_pointer_variable_in_pointer(pointer, from, to),
                |value| substitute_pointer_variable_in_program_value(value, from, to),
            ),
        }),
    };
    result.record_diagnostic_transform(
        "substitute pointer variable",
        vec![memory.clone()],
        vec![
            ProgramValue::pointer(Address::symbolic(from)),
            ProgramValue::pointer(to.clone()),
        ],
    );
    result
}

fn substitute_pointer_variable_in_block(
    block: &AddressBase,
    from: Variable,
    to: &Address,
) -> AddressBase {
    match block {
        AddressBase::PureFunctionApplication(_) => {
            substitute_pointer_variable_in_pointer(
                &Address {
                    base: block.clone(),
                    offset: AddressOffset::Constant(0),
                },
                from,
                to,
            )
            .base
        }
        AddressBase::ExternalObject(variable) if *variable == from => to.object_identity().base,
        AddressBase::Symbolic(variable) | AddressBase::FunctionSymbolic(variable)
            if *variable == from =>
        {
            to.base.clone()
        }
        block => block.clone(),
    }
}

fn substitute_pointer_variable_in_spec_point(
    spec_point: &SpecPoint,
    from: Variable,
    to: &Address,
) -> SpecPoint {
    match spec_point {
        SpecPoint::Current => SpecPoint::Current,
        SpecPoint::FunctionEntry => SpecPoint::FunctionEntry,
        SpecPoint::LoopEntry => SpecPoint::LoopEntry,
        SpecPoint::At(point) => {
            SpecPoint::At(point.with_renamed_memory(crate::kernel::intern_memory(
                substitute_pointer_variable_in_memory(point.memory(), from, to),
            )))
        }
    }
}

fn substitute_pointer_variable_in_spec_algebraic_expression(
    expression: &SpecAlgebraicExpression,
    from: Variable,
    to: &Address,
) -> SpecAlgebraicExpression {
    let node = match &expression.node {
        SpecAlgebraicExpressionNode::ResourceField(projection) => {
            SpecAlgebraicExpressionNode::ResourceField(projection.clone())
        }
        SpecAlgebraicExpressionNode::Variable(variable) => {
            SpecAlgebraicExpressionNode::Variable(*variable)
        }
        SpecAlgebraicExpressionNode::Binding(name) => {
            SpecAlgebraicExpressionNode::Binding(name.clone())
        }
        SpecAlgebraicExpressionNode::ProgramValue(value) => {
            SpecAlgebraicExpressionNode::ProgramValue(Box::new(
                substitute_pointer_variable_in_spec_expression(value, from, to),
            ))
        }
        SpecAlgebraicExpressionNode::Constructor { variant, fields } => {
            SpecAlgebraicExpressionNode::Constructor {
                variant: variant.clone(),
                fields: fields
                    .iter()
                    .map(|field| match field {
                        SpecAlgebraicValue::Program(field) => SpecAlgebraicValue::Program(
                            substitute_pointer_variable_in_spec_expression(field, from, to),
                        ),
                        SpecAlgebraicValue::Integer(field) => {
                            SpecAlgebraicValue::Integer(field.clone())
                        }
                        SpecAlgebraicValue::Algebraic(field) => SpecAlgebraicValue::Algebraic(
                            substitute_pointer_variable_in_spec_algebraic_expression(
                                field, from, to,
                            ),
                        ),
                    })
                    .collect(),
            }
        }
        SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
            SpecAlgebraicExpressionNode::Match {
                scrutinee: Box::new(substitute_pointer_variable_in_spec_algebraic_expression(
                    scrutinee, from, to,
                )),
                arms: arms
                    .iter()
                    .map(|arm| SpecAlgebraicResultMatchArm {
                        variant: arm.variant.clone(),
                        bindings: arm.bindings.clone(),
                        binding_types: arm.binding_types.clone(),
                        binding_variables: arm.binding_variables.clone(),
                        body: Box::new(substitute_pointer_variable_in_spec_algebraic_expression(
                            &arm.body, from, to,
                        )),
                    })
                    .collect(),
            }
        }
        SpecAlgebraicExpressionNode::PureFunctionApplication { name, arguments } => {
            SpecAlgebraicExpressionNode::PureFunctionApplication {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| {
                        substitute_pointer_variable_in_spec_function_argument(argument, from, to)
                    })
                    .collect(),
            }
        }
        SpecAlgebraicExpressionNode::If {
            condition,
            then_branch,
            else_branch,
        } => SpecAlgebraicExpressionNode::If {
            condition: Box::new(substitute_pointer_variable_in_spec_proposition(
                condition, from, to,
            )),
            then_branch: Box::new(substitute_pointer_variable_in_spec_algebraic_expression(
                then_branch,
                from,
                to,
            )),
            else_branch: Box::new(substitute_pointer_variable_in_spec_algebraic_expression(
                else_branch,
                from,
                to,
            )),
        },
    };
    SpecAlgebraicExpression {
        algebraic_type: expression.algebraic_type.clone(),
        node,
    }
}

fn substitute_pointer_variable_in_spec_expression(
    expression: &SpecExpression,
    from: Variable,
    to: &Address,
) -> SpecExpression {
    match expression {
        SpecExpression::ObjectAddress(address) => {
            SpecExpression::ObjectAddress(Box::new(address.with_base(
                substitute_pointer_variable_in_spec_expression(&address.base, from, to),
            )))
        }
        SpecExpression::ResourceField { .. } => expression.clone(),
        SpecExpression::IntegerToMachine { value, destination } => {
            SpecExpression::IntegerToMachine {
                value: Box::new(substitute_pointer_variable_in_spec_integer(value, from, to)),
                destination: *destination,
            }
        }
        SpecExpression::Value(value) => SpecExpression::Value(
            substitute_pointer_variable_in_program_value(value, from, to),
        ),
        SpecExpression::AlgebraicMatch { scrutinee, arms } => SpecExpression::AlgebraicMatch {
            scrutinee: Box::new(substitute_pointer_variable_in_spec_algebraic_expression(
                scrutinee, from, to,
            )),
            arms: arms
                .iter()
                .map(|arm| SpecAlgebraicMatchArm {
                    variant: arm.variant.clone(),
                    bindings: arm.bindings.clone(),
                    binding_types: arm.binding_types.clone(),
                    body: substitute_pointer_variable_in_spec_expression(&arm.body, from, to),
                })
                .collect(),
        },
        SpecExpression::ProgramExpression(expression) => SpecExpression::ProgramExpression(
            substitute_pointer_variable_in_program_expression(expression, from, to),
        ),
        SpecExpression::CountedResourceCount { name, arguments } => {
            SpecExpression::CountedResourceCount {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| {
                        argument.as_ref().map(|argument| {
                            substitute_pointer_variable_in_spec_expression(argument, from, to)
                        })
                    })
                    .collect(),
            }
        }
        crate::kernel::binary_spec_expression!(left, right) => {
            let left = Box::new(substitute_pointer_variable_in_spec_expression(
                left, from, to,
            ));
            let right = Box::new(substitute_pointer_variable_in_spec_expression(
                right, from, to,
            ));
            match expression {
                SpecExpression::Add(_, _) => SpecExpression::Add(left, right),
                SpecExpression::Subtract(_, _) => SpecExpression::Subtract(left, right),
                SpecExpression::Multiply(_, _) => SpecExpression::Multiply(left, right),
                SpecExpression::Divide(_, _) => SpecExpression::Divide(left, right),
                SpecExpression::Remainder(_, _) => SpecExpression::Remainder(left, right),
                SpecExpression::ShiftLeft(_, _) => SpecExpression::ShiftLeft(left, right),
                SpecExpression::RustShiftLeft(_, _) => SpecExpression::RustShiftLeft(left, right),
                SpecExpression::ShiftRight(_, _) => SpecExpression::ShiftRight(left, right),
                SpecExpression::RustShiftRight(_, _) => SpecExpression::RustShiftRight(left, right),
                SpecExpression::BitwiseAnd(_, _) => SpecExpression::BitwiseAnd(left, right),
                SpecExpression::BitwiseOr(_, _) => SpecExpression::BitwiseOr(left, right),
                SpecExpression::BitwiseXor(_, _) => SpecExpression::BitwiseXor(left, right),
                _ => unreachable!("the combined spec binary arm is exhaustive"),
            }
        }
        SpecExpression::Negate(expression) => SpecExpression::Negate(Box::new(
            substitute_pointer_variable_in_spec_expression(expression, from, to),
        )),
        SpecExpression::BitwiseNot(expression) => SpecExpression::BitwiseNot(Box::new(
            substitute_pointer_variable_in_spec_expression(expression, from, to),
        )),
        SpecExpression::Cast(expression, target_type) => SpecExpression::Cast(
            Box::new(substitute_pointer_variable_in_spec_expression(
                expression, from, to,
            )),
            *target_type,
        ),
        SpecExpression::NarrowArithmetic(expression, format) => SpecExpression::NarrowArithmetic(
            Box::new(substitute_pointer_variable_in_spec_expression(
                expression, from, to,
            )),
            *format,
        ),
        SpecExpression::PointerCoercion(expression, target_type) => {
            SpecExpression::PointerCoercion(
                Box::new(substitute_pointer_variable_in_spec_expression(
                    expression, from, to,
                )),
                *target_type,
            )
        }
        SpecExpression::If {
            condition,
            then_branch,
            else_branch,
        } => SpecExpression::If {
            condition: Box::new(substitute_pointer_variable_in_spec_proposition(
                condition, from, to,
            )),
            then_branch: Box::new(substitute_pointer_variable_in_spec_expression(
                then_branch,
                from,
                to,
            )),
            else_branch: Box::new(substitute_pointer_variable_in_spec_expression(
                else_branch,
                from,
                to,
            )),
        },
        SpecExpression::Requires { requirement, value } => SpecExpression::Requires {
            requirement: Box::new(substitute_pointer_variable_in_spec_proposition(
                requirement,
                from,
                to,
            )),
            value: Box::new(substitute_pointer_variable_in_spec_expression(
                value, from, to,
            )),
        },
        SpecExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => SpecExpression::RangeFold {
            start: Box::new(substitute_pointer_variable_in_spec_expression(
                start, from, to,
            )),
            end: Box::new(substitute_pointer_variable_in_spec_expression(
                end, from, to,
            )),
            initial: Box::new(substitute_pointer_variable_in_spec_expression(
                initial, from, to,
            )),
            accumulator: accumulator.clone(),
            item: item.clone(),
            body: Box::new(substitute_pointer_variable_in_spec_expression(
                body, from, to,
            )),
        },
        SpecExpression::Let { name, value, body } => SpecExpression::Let {
            name: name.clone(),
            value: Box::new(substitute_pointer_variable_in_spec_expression(
                value, from, to,
            )),
            body: Box::new(substitute_pointer_variable_in_spec_expression(
                body, from, to,
            )),
        },
        SpecExpression::PureFunctionApplication {
            name,
            arguments,
            result_type,
            pointer_result,
            result_object_class,
        } => SpecExpression::PureFunctionApplication {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| {
                    substitute_pointer_variable_in_spec_function_argument(argument, from, to)
                })
                .collect(),
            result_type: *result_type,
            pointer_result: pointer_result.clone(),
            result_object_class: result_object_class.clone(),
        },
        SpecExpression::LoopEntryState(expression) => SpecExpression::LoopEntryState(Box::new(
            substitute_pointer_variable_in_spec_expression(expression, from, to),
        )),
        SpecExpression::Subobject { pointer, width } => SpecExpression::Subobject {
            pointer: Box::new(substitute_pointer_variable_in_spec_expression(
                pointer, from, to,
            )),
            width: *width,
        },
        SpecExpression::PointerOffset {
            pointer,
            elements,
            byte_width,
        } => SpecExpression::PointerOffset {
            pointer: Box::new(substitute_pointer_variable_in_spec_expression(
                pointer, from, to,
            )),
            elements: Box::new(substitute_pointer_variable_in_spec_expression(
                elements, from, to,
            )),
            byte_width: *byte_width,
        },
        SpecExpression::AggregateFieldValue {
            parameter,
            pointer,
            value_type,
        } => SpecExpression::AggregateFieldValue {
            parameter: parameter.clone(),
            pointer: Box::new(substitute_pointer_variable_in_spec_expression(
                pointer, from, to,
            )),
            value_type: *value_type,
        },
        SpecExpression::MemoryLoad {
            point: memory,
            pointer,
            value_type,
        } => SpecExpression::MemoryLoad {
            point: substitute_pointer_variable_in_spec_point(memory, from, to),
            pointer: Box::new(substitute_pointer_variable_in_spec_expression(
                pointer, from, to,
            )),
            value_type: *value_type,
        },
    }
}

fn substitute_pointer_variable_in_spec_function_argument(
    argument: &SpecPureFunctionArgument,
    from: Variable,
    to: &Address,
) -> SpecPureFunctionArgument {
    match argument {
        SpecPureFunctionArgument::ObjectPointer {
            argument,
            object_class,
        } => SpecPureFunctionArgument::ObjectPointer {
            argument: Box::new(substitute_pointer_variable_in_spec_function_argument(
                argument, from, to,
            )),
            object_class: object_class.clone(),
        },
        SpecPureFunctionArgument::Integer(value) => SpecPureFunctionArgument::Integer(
            substitute_pointer_variable_in_spec_integer(value, from, to),
        ),
        SpecPureFunctionArgument::Value(expression) => SpecPureFunctionArgument::Value(
            substitute_pointer_variable_in_spec_expression(expression, from, to),
        ),
        SpecPureFunctionArgument::Algebraic(expression) => SpecPureFunctionArgument::Algebraic(
            substitute_pointer_variable_in_spec_algebraic_expression(expression, from, to),
        ),
        SpecPureFunctionArgument::ArrayRef {
            point: memory,
            pointer,
            element_type,
        } => SpecPureFunctionArgument::ArrayRef {
            point: substitute_pointer_variable_in_spec_point(memory, from, to),
            pointer: substitute_pointer_variable_in_spec_expression(pointer, from, to),
            element_type: *element_type,
        },
    }
}

fn substitute_pointer_variable_in_spec_integer(
    expression: &SpecIntegerExpression,
    from: Variable,
    to: &Address,
) -> SpecIntegerExpression {
    match expression {
        SpecIntegerExpression::ResourceField(_) => expression.clone(),
        SpecIntegerExpression::AlgebraicMatch { scrutinee, arms } => {
            SpecIntegerExpression::AlgebraicMatch {
                scrutinee: Box::new(substitute_pointer_variable_in_spec_algebraic_expression(
                    scrutinee, from, to,
                )),
                arms: arms
                    .iter()
                    .map(|arm| SpecIntegerMatchArm {
                        variant: arm.variant.clone(),
                        bindings: arm.bindings.clone(),
                        binding_types: arm.binding_types.clone(),
                        binding_variables: arm.binding_variables.clone(),
                        body: Box::new(substitute_pointer_variable_in_spec_integer(
                            &arm.body, from, to,
                        )),
                    })
                    .collect(),
            }
        }
        SpecIntegerExpression::PureFunctionApplication { name, arguments } => {
            SpecIntegerExpression::PureFunctionApplication {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| {
                        substitute_pointer_variable_in_spec_function_argument(argument, from, to)
                    })
                    .collect(),
            }
        }
        SpecIntegerExpression::Term(term) => {
            let Term::Integer(term) =
                crate::kernel::proof::term_rewrite::TermRewrite::for_pointer_variable(from, to)
                    .term(&Term::Integer(term.clone()))
            else {
                unreachable!()
            };
            SpecIntegerExpression::Term(term)
        }
        SpecIntegerExpression::If {
            condition,
            then_branch,
            else_branch,
        } => SpecIntegerExpression::If {
            condition: Box::new(substitute_pointer_variable_in_spec_proposition(
                condition, from, to,
            )),
            then_branch: Box::new(substitute_pointer_variable_in_spec_integer(
                then_branch,
                from,
                to,
            )),
            else_branch: Box::new(substitute_pointer_variable_in_spec_integer(
                else_branch,
                from,
                to,
            )),
        },
        SpecIntegerExpression::FromMachine(value) => SpecIntegerExpression::FromMachine(Box::new(
            substitute_pointer_variable_in_spec_expression(value, from, to),
        )),
        SpecIntegerExpression::Negate(value) => SpecIntegerExpression::Negate(Box::new(
            substitute_pointer_variable_in_spec_integer(value, from, to),
        )),
        SpecIntegerExpression::Add(left, right) => SpecIntegerExpression::Add(
            Box::new(substitute_pointer_variable_in_spec_integer(left, from, to)),
            Box::new(substitute_pointer_variable_in_spec_integer(right, from, to)),
        ),
        SpecIntegerExpression::Subtract(left, right) => SpecIntegerExpression::Subtract(
            Box::new(substitute_pointer_variable_in_spec_integer(left, from, to)),
            Box::new(substitute_pointer_variable_in_spec_integer(right, from, to)),
        ),
        SpecIntegerExpression::TruncatingQuotient(left, right) => {
            SpecIntegerExpression::TruncatingQuotient(
                Box::new(substitute_pointer_variable_in_spec_integer(left, from, to)),
                Box::new(substitute_pointer_variable_in_spec_integer(right, from, to)),
            )
        }
        SpecIntegerExpression::TruncatingRemainder(left, right) => {
            SpecIntegerExpression::TruncatingRemainder(
                Box::new(substitute_pointer_variable_in_spec_integer(left, from, to)),
                Box::new(substitute_pointer_variable_in_spec_integer(right, from, to)),
            )
        }
        SpecIntegerExpression::Multiply(left, right) => SpecIntegerExpression::Multiply(
            Box::new(substitute_pointer_variable_in_spec_integer(left, from, to)),
            Box::new(substitute_pointer_variable_in_spec_integer(right, from, to)),
        ),
        SpecIntegerExpression::RangeFold {
            index,
            initial,
            accumulator,
            item,
            body,
        } => {
            let index = match index {
                SpecIntegerRangeFoldIndex::Int32 { start, end } => {
                    SpecIntegerRangeFoldIndex::Int32 {
                        start: Box::new(substitute_pointer_variable_in_spec_expression(
                            start, from, to,
                        )),
                        end: Box::new(substitute_pointer_variable_in_spec_expression(
                            end, from, to,
                        )),
                    }
                }
                SpecIntegerRangeFoldIndex::UInt64 { start, end } => {
                    SpecIntegerRangeFoldIndex::UInt64 {
                        start: Box::new(substitute_pointer_variable_in_spec_expression(
                            start, from, to,
                        )),
                        end: Box::new(substitute_pointer_variable_in_spec_expression(
                            end, from, to,
                        )),
                    }
                }
                SpecIntegerRangeFoldIndex::Integer { start, end } => {
                    SpecIntegerRangeFoldIndex::Integer {
                        start: Box::new(substitute_pointer_variable_in_spec_integer(
                            start, from, to,
                        )),
                        end: Box::new(substitute_pointer_variable_in_spec_integer(end, from, to)),
                    }
                }
            };
            SpecIntegerExpression::RangeFold {
                index,
                initial: Box::new(substitute_pointer_variable_in_spec_integer(
                    initial, from, to,
                )),
                accumulator: *accumulator,
                item: *item,
                body: Box::new(substitute_pointer_variable_in_spec_integer(body, from, to)),
            }
        }
    }
}

fn substitute_pointer_variable_in_spec_proposition(
    proposition: &SpecProposition,
    from: Variable,
    to: &Address,
) -> SpecProposition {
    match proposition {
        SpecProposition::Truth(value) => SpecProposition::Truth(*value),
        SpecProposition::ForAllInteger {
            name,
            variable,
            body,
        } => SpecProposition::ForAllInteger {
            name: name.clone(),
            variable: *variable,
            body: Box::new(substitute_pointer_variable_in_spec_proposition(
                body, from, to,
            )),
        },
        SpecProposition::ForAllAlgebraic {
            name,
            variable,
            algebraic_type,
            body,
        } => SpecProposition::ForAllAlgebraic {
            name: name.clone(),
            variable: *variable,
            algebraic_type: algebraic_type.clone(),
            body: Box::new(substitute_pointer_variable_in_spec_proposition(
                body, from, to,
            )),
        },
        SpecProposition::IntegerComparison {
            left,
            operator,
            right,
        } => SpecProposition::IntegerComparison {
            left: substitute_pointer_variable_in_spec_integer(left, from, to),
            operator: *operator,
            right: substitute_pointer_variable_in_spec_integer(right, from, to),
        },
        SpecProposition::AlgebraicComparison { left, equal, right } => {
            SpecProposition::AlgebraicComparison {
                left: substitute_pointer_variable_in_spec_algebraic_expression(left, from, to),
                equal: *equal,
                right: substitute_pointer_variable_in_spec_algebraic_expression(right, from, to),
            }
        }
        SpecProposition::SequenceMembership { element, sequence } => {
            SpecProposition::SequenceMembership {
                element: substitute_pointer_variable_in_spec_expression(element, from, to),
                sequence: substitute_pointer_variable_in_spec_sequence(sequence, from, to),
            }
        }
        SpecProposition::SequenceComparison { left, equal, right } => {
            SpecProposition::SequenceComparison {
                left: substitute_pointer_variable_in_spec_sequence(left, from, to),
                equal: *equal,
                right: substitute_pointer_variable_in_spec_sequence(right, from, to),
            }
        }
        SpecProposition::Comparison {
            left,
            operator,
            right,
        } => SpecProposition::Comparison {
            left: substitute_pointer_variable_in_spec_expression(left, from, to),
            operator: *operator,
            right: substitute_pointer_variable_in_spec_expression(right, from, to),
        },
        SpecProposition::FloatClassification {
            expression,
            classification,
        } => SpecProposition::FloatClassification {
            expression: substitute_pointer_variable_in_spec_expression(expression, from, to),
            classification: *classification,
        },
        SpecProposition::And(left, right) => SpecProposition::And(
            Box::new(substitute_pointer_variable_in_spec_proposition(
                left, from, to,
            )),
            Box::new(substitute_pointer_variable_in_spec_proposition(
                right, from, to,
            )),
        ),
        SpecProposition::Or(left, right) => SpecProposition::Or(
            Box::new(substitute_pointer_variable_in_spec_proposition(
                left, from, to,
            )),
            Box::new(substitute_pointer_variable_in_spec_proposition(
                right, from, to,
            )),
        ),
        SpecProposition::Not(body) => SpecProposition::Not(Box::new(
            substitute_pointer_variable_in_spec_proposition(body, from, to),
        )),
        SpecProposition::Implies(left, right) => SpecProposition::Implies(
            Box::new(substitute_pointer_variable_in_spec_proposition(
                left, from, to,
            )),
            Box::new(substitute_pointer_variable_in_spec_proposition(
                right, from, to,
            )),
        ),
        SpecProposition::ForAllMachineInteger {
            name,
            variable,
            integer_type,
            body,
        } => SpecProposition::ForAllMachineInteger {
            name: name.clone(),
            variable: *variable,
            integer_type: *integer_type,
            body: Box::new(substitute_pointer_variable_in_spec_proposition(
                body, from, to,
            )),
        },
        SpecProposition::ForAllInt32 {
            name,
            variable,
            body,
        } => SpecProposition::ForAllInt32 {
            name: name.clone(),
            variable: *variable,
            body: Box::new(substitute_pointer_variable_in_spec_proposition(
                body, from, to,
            )),
        },
        SpecProposition::ForAllPointer {
            name,
            variable,
            program_type,
            body,
        } => SpecProposition::ForAllPointer {
            name: name.clone(),
            variable: *variable,
            program_type: *program_type,
            body: Box::new(substitute_pointer_variable_in_spec_proposition(
                body, from, to,
            )),
        },
        SpecProposition::ExistsInteger {
            name,
            variable,
            body,
        } => SpecProposition::ExistsInteger {
            name: name.clone(),
            variable: *variable,
            body: Box::new(substitute_pointer_variable_in_spec_proposition(
                body, from, to,
            )),
        },
        SpecProposition::ExistsAlgebraic {
            name,
            variable,
            algebraic_type,
            body,
        } => SpecProposition::ExistsAlgebraic {
            name: name.clone(),
            variable: *variable,
            algebraic_type: algebraic_type.clone(),
            body: Box::new(substitute_pointer_variable_in_spec_proposition(
                body, from, to,
            )),
        },
        SpecProposition::ExistsMachineInteger {
            name,
            variable,
            integer_type,
            body,
        } => SpecProposition::ExistsMachineInteger {
            name: name.clone(),
            variable: *variable,
            integer_type: *integer_type,
            body: Box::new(substitute_pointer_variable_in_spec_proposition(
                body, from, to,
            )),
        },
        SpecProposition::ExistsInt32 {
            name,
            variable,
            body,
        } => SpecProposition::ExistsInt32 {
            name: name.clone(),
            variable: *variable,
            body: Box::new(substitute_pointer_variable_in_spec_proposition(
                body, from, to,
            )),
        },
        SpecProposition::ExistsPointer {
            name,
            variable,
            program_type,
            body,
        } => SpecProposition::ExistsPointer {
            name: name.clone(),
            variable: *variable,
            program_type: *program_type,
            body: Box::new(substitute_pointer_variable_in_spec_proposition(
                body, from, to,
            )),
        },
        SpecProposition::Predicate {
            name,
            arguments,
            resource_state_dependent,
        } => SpecProposition::Predicate {
            resource_state_dependent: *resource_state_dependent,
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| match argument {
                    SpecPredicateArgument::Value(expression) => SpecPredicateArgument::Value(
                        substitute_pointer_variable_in_spec_expression(expression, from, to),
                    ),
                    SpecPredicateArgument::ArrayRef {
                        point: memory,
                        pointer,
                    } => SpecPredicateArgument::ArrayRef {
                        point: substitute_pointer_variable_in_spec_point(memory, from, to),
                        pointer: substitute_pointer_variable_in_spec_expression(pointer, from, to),
                    },
                })
                .collect(),
        },
        SpecProposition::ResourceSeparate { left, right } => SpecProposition::ResourceSeparate {
            left: substitute_pointer_variable_in_spec_resource(left, from, to),
            right: substitute_pointer_variable_in_spec_resource(right, from, to),
        },
        SpecProposition::ResourceViewable {
            point: memory,
            resource,
        } => SpecProposition::ResourceViewable {
            point: substitute_pointer_variable_in_spec_point(memory, from, to),
            resource: substitute_pointer_variable_in_spec_resource(resource, from, to),
        },
        SpecProposition::ResourceContains { parent, child } => SpecProposition::ResourceContains {
            parent: substitute_pointer_variable_in_spec_resource(parent, from, to),
            child: substitute_pointer_variable_in_spec_resource(child, from, to),
        },
        SpecProposition::MemoryLoadable {
            point: memory,
            base,
            start,
            end,
            element_width,
        } => SpecProposition::MemoryLoadable {
            point: substitute_pointer_variable_in_spec_point(memory, from, to),
            base: substitute_pointer_variable_in_spec_expression(base, from, to),
            start: substitute_pointer_variable_in_spec_expression(start, from, to),
            end: substitute_pointer_variable_in_spec_expression(end, from, to),
            element_width: *element_width,
        },
        SpecProposition::MutexHeld(expression) => SpecProposition::MutexHeld(Box::new(
            substitute_pointer_variable_in_spec_expression(expression, from, to),
        )),
        SpecProposition::Defined(expression) => SpecProposition::Defined(
            substitute_pointer_variable_in_spec_expression(expression, from, to),
        ),
    }
}

fn substitute_pointer_variable_in_spec_sequence(
    sequence: &SpecSequenceExpression,
    from: Variable,
    to: &Address,
) -> SpecSequenceExpression {
    match sequence {
        SpecSequenceExpression::Literal(elements) => SpecSequenceExpression::Literal(
            elements
                .iter()
                .map(|element| substitute_pointer_variable_in_spec_expression(element, from, to))
                .collect(),
        ),
        SpecSequenceExpression::Concat(left, right) => SpecSequenceExpression::Concat(
            Box::new(substitute_pointer_variable_in_spec_sequence(left, from, to)),
            Box::new(substitute_pointer_variable_in_spec_sequence(
                right, from, to,
            )),
        ),
    }
}

fn substitute_pointer_variable_in_spec_resource(
    resource: &SpecResource,
    from: Variable,
    to: &Address,
) -> SpecResource {
    match resource {
        SpecResource::Star(a, b) => SpecResource::Star(
            Box::new(substitute_pointer_variable_in_spec_resource(a, from, to)),
            Box::new(substitute_pointer_variable_in_spec_resource(b, from, to)),
        ),
        SpecResource::Instance { .. } | SpecResource::Value(_) => resource.clone(),
        SpecResource::Memory {
            base,
            start,
            end,
            element_width,
        } => SpecResource::Memory {
            base: substitute_pointer_variable_in_spec_expression(base, from, to),
            start: substitute_pointer_variable_in_spec_expression(start, from, to),
            end: substitute_pointer_variable_in_spec_expression(end, from, to),
            element_width: *element_width,
        },
        SpecResource::Composite { name, arguments } => SpecResource::Composite {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_pointer_variable_in_spec_expression(argument, from, to))
                .collect(),
        },
        SpecResource::Token { name, arguments } => SpecResource::Token {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_pointer_variable_in_spec_expression(argument, from, to))
                .collect(),
        },
    }
}

#[cfg(test)]
mod pointee_const_return_tests {
    use super::*;

    #[test]
    fn pointee_const_return_value_substitution_preserves_qualifiers_and_identity() {
        let value = ProgramValue::typed_pointer(
            Address::symbolic(Variable(918)),
            ProgramType::Int32Pointer,
        )
        .with_pointer_pointee_constant(true)
        .with_pointer_pointee_volatile(true);
        assert_eq!(
            substitute_bitvector_variable_in_program_value(
                &value,
                Variable(919),
                &MachineTerm::constant(0)
            ),
            value
        );
        assert_eq!(
            substitute_pointer_variable_in_program_value(&value, Variable(919), &Address::null()),
            value
        );
        let replaced =
            substitute_pointer_variable_in_program_value(&value, Variable(918), &Address::null());
        assert!(matches!(replaced, ProgramValue::Pointer(pointer)
            if pointer.is_null() && pointer.pointee_constant() && pointer.pointee_volatile()));
    }

    #[test]
    fn pointee_const_return_survives_both_substitutions() {
        let function = ProgramFunction::new(
            ProgramType::UInt8Pointer,
            "text",
            Vec::new(),
            program_return(crate::kernel::program_expression::int32_literal(0)),
        )
        .with_return_pointee_constant(true);
        assert!(
            substitute_bitvector_variable_in_program_function(
                &function,
                Variable(914),
                &MachineTerm::constant(0),
            )
            .return_pointee_is_constant()
        );
        assert!(
            substitute_pointer_variable_in_program_function(
                &function,
                Variable(914),
                &Address::symbolic(Variable(915)),
            )
            .return_pointee_is_constant()
        );
    }
}

#[cfg(test)]
mod integer_to_machine_substitution_tests {
    use super::*;

    #[test]
    fn integer_to_machine_substitution_descends_math_payload_and_keeps_destination() {
        let payload = crate::kernel::SharedIntegerTerm::from(IntegerTerm::Machine(
            crate::kernel::SharedMachineIntegerTerm::intern(
                crate::kernel::MachineIntegerType::Int32,
                MachineTerm::Variable(Variable(701)),
            ),
        ));
        let term = MachineTerm::IntegerToMachine {
            value: payload.clone(),
            destination: crate::kernel::MachineIntegerType::UInt32,
        };
        let replaced = substitute_bitvector_variable(
            &term,
            Variable(701),
            &MachineTerm::Variable(Variable(702)),
        );
        let MachineTerm::IntegerToMachine { value, destination } = replaced else {
            panic!("substitution changed the carrier shape")
        };
        assert_eq!(destination, crate::kernel::MachineIntegerType::UInt32);
        assert!(matches!(value.as_ref(), IntegerTerm::Machine(machine)
            if machine.ty() == crate::kernel::MachineIntegerType::Int32
                && machine.value() == &MachineTerm::Variable(Variable(702))));
    }

    #[test]
    fn integer_to_machine_substitution_reuses_unchanged_shared_payload() {
        let payload = crate::kernel::SharedIntegerTerm::from(IntegerTerm::Variable(Variable(703)));
        let term = MachineTerm::IntegerToMachine {
            value: payload.clone(),
            destination: crate::kernel::MachineIntegerType::Int32,
        };
        let replaced =
            substitute_bitvector_variable(&term, Variable(704), &MachineTerm::constant(0));
        let MachineTerm::IntegerToMachine { value, .. } = replaced else {
            panic!("substitution changed the carrier shape")
        };
        assert_eq!(value.id(), payload.id());
    }
}

#[cfg(test)]
mod machine_integer_pointer_substitution_tests {
    use super::*;

    #[test]
    fn pointer_substitution_reaches_integer_observations_and_composes_offsets() {
        let binder = Variable(610);
        let source = Address {
            base: AddressBase::Symbolic(binder),
            offset: AddressOffset::Constant(8),
        };
        let replacement = Address {
            base: AddressBase::Symbolic(Variable(611)),
            offset: AddressOffset::Constant(4),
        };
        let expected = Address {
            base: replacement.base.clone(),
            offset: AddressOffset::Constant(12),
        };
        let bits =
            MachineTerm::IntegerAddress(Box::new(source), crate::kernel::AddressObjectClass::NONE);
        let term =
            IntegerTerm::from_machine(crate::kernel::MachineIntegerType::UInt64, bits.clone())
                .unwrap();
        let proposition = Proposition::condition_is(
            ConditionTerm::integer_equal(term, IntegerTerm::constant_i64(0)),
            true,
        );
        let rewritten =
            substitute_pointer_variable_in_proposition(&proposition, binder, &replacement);
        let Some((ConditionTerm::IntegerEqual(left, _), true)) = rewritten.condition_native()
        else {
            panic!("unexpected proposition")
        };
        let IntegerTerm::Machine(observation) = left.as_ref() else {
            panic!("missing observation")
        };
        assert_eq!(
            observation.value(),
            &MachineTerm::IntegerAddress(
                Box::new(expected.clone()),
                crate::kernel::AddressObjectClass::NONE
            )
        );

        let spec = SpecProposition::IntegerComparison {
            left: SpecIntegerExpression::FromMachine(Box::new(SpecExpression::Value(
                ProgramValue::UInt64(bits),
            ))),
            operator: IntegerComparisonOperator::Equal,
            right: SpecIntegerExpression::Term(IntegerTerm::constant_i64(0)),
        };
        let rewritten =
            substitute_pointer_variable_in_spec_proposition(&spec, binder, &replacement);
        let SpecProposition::IntegerComparison {
            left: SpecIntegerExpression::FromMachine(value),
            ..
        } = rewritten
        else {
            panic!("unexpected spec proposition")
        };
        assert_eq!(
            *value,
            SpecExpression::Value(ProgramValue::UInt64(MachineTerm::IntegerAddress(
                Box::new(expected),
                crate::kernel::AddressObjectClass::NONE,
            )))
        );
    }
}

#[cfg(test)]
mod integer_function_traversal_tests {
    use super::*;

    #[test]
    fn integer_applications_rewrite_program_and_nested_integer_arguments() {
        let from = Variable(817);
        let machine = MachineTerm::Variable(from);
        let make = |machine: MachineTerm| {
            IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
                "observed".into(),
                vec![
                    PureFunctionArgument::Value(ProgramValue::Int32(machine.clone())),
                    PureFunctionArgument::Integer(
                        IntegerTerm::from_machine(MachineIntegerType::Int32, machine)
                            .unwrap()
                            .into(),
                    ),
                ],
            ))
        };
        let original = make(machine);
        let expected = make(MachineTerm::Variable(Variable(818)));
        assert_eq!(
            substitute_bitvector_variable_in_integer(
                &original,
                from,
                &MachineTerm::Variable(Variable(818))
            ),
            expected
        );
        assert_eq!(
            crate::kernel::proof::term_rewrite::TermRewrite::for_bits(
                &MachineTerm::Variable(from),
                &MachineTerm::Variable(Variable(818))
            )
            .term(&Term::Integer(original)),
            Term::Integer(expected)
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!(
            "../../scaling_tests/kernel/reasoning/substitution/integer_function_traversal_tests.rs"
        );
    }
}

#[cfg(test)]
mod integer_match_substitution_scope_tests {
    use super::*;

    fn symbolic_match(body: IntegerTerm, binding: Variable) -> IntegerTerm {
        symbolic_match_with_binding(
            body,
            AlgebraicValue::Program(ProgramValue::Int32(MachineTerm::Variable(binding))),
        )
    }

    fn symbolic_match_with_binding(body: IntegerTerm, binding: AlgebraicValue) -> IntegerTerm {
        let scrutinee = AlgebraicTerm {
            algebraic_type: AlgebraicType::parameter("MatchInput".into()),
            node: AlgebraicTermNode::Variable(Variable(9000)),
        };
        IntegerTerm::AlgebraicMatch {
            scrutinee: Box::new(scrutinee),
            arms: vec![AlgebraicIntegerMatchArm {
                binding_names: Default::default(),
                variant: "Arm".into(),
                bindings: vec![binding],
                body: body.into(),
            }],
        }
    }

    fn shared_symbolic_match(body: IntegerTerm, binding: Variable) -> IntegerTerm {
        let scrutinee = AlgebraicTerm {
            algebraic_type: AlgebraicType::parameter("SharedMatchInput".into()),
            node: AlgebraicTermNode::Variable(Variable(9060)),
        };
        IntegerTerm::AlgebraicMatch {
            scrutinee: Box::new(scrutinee),
            arms: vec![
                AlgebraicIntegerMatchArm {
                    binding_names: Default::default(),
                    variant: "Left".into(),
                    bindings: vec![AlgebraicValue::Program(ProgramValue::Int32(
                        MachineTerm::Variable(binding),
                    ))],
                    body: body.clone().into(),
                },
                AlgebraicIntegerMatchArm {
                    binding_names: Default::default(),
                    variant: "Right".into(),
                    bindings: vec![AlgebraicValue::Program(ProgramValue::Int32(
                        MachineTerm::Variable(binding),
                    ))],
                    body: body.into(),
                },
            ],
        }
    }

    #[test]
    fn substitution_freshens_match_binder_while_preserving_free_replacement() {
        let x = Variable(9001);
        let y = Variable(9002);
        let body = IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
            "observe".into(),
            vec![
                PureFunctionArgument::Value(ProgramValue::Int32(MachineTerm::Variable(y))),
                PureFunctionArgument::Value(ProgramValue::Int32(MachineTerm::Variable(x))),
                PureFunctionArgument::Value(ProgramValue::Int32(MachineTerm::Variable(Variable(
                    9003,
                )))),
            ],
        ));
        let rewritten = substitute_bitvector_variable_in_integer(
            &symbolic_match(body, y),
            x,
            &MachineTerm::Variable(y),
        );
        let IntegerTerm::AlgebraicMatch { arms, .. } = rewritten else {
            panic!("expected algebraic match")
        };
        let AlgebraicValue::Program(ProgramValue::Int32(MachineTerm::Variable(fresh))) =
            arms[0].bindings[0]
        else {
            panic!("expected C binder")
        };
        assert_ne!(fresh, y);
        let IntegerTerm::PureFunctionApplication(application) = arms[0].body.as_ref() else {
            panic!("expected application body")
        };
        let [
            PureFunctionArgument::Value(ProgramValue::Int32(MachineTerm::Variable(first))),
            PureFunctionArgument::Value(ProgramValue::Int32(MachineTerm::Variable(second))),
            PureFunctionArgument::Value(ProgramValue::Int32(MachineTerm::Variable(free))),
        ] = application.arguments()
        else {
            panic!("expected two C arguments")
        };
        assert_eq!(*first, fresh);
        assert_eq!(*second, y);
        assert_eq!(*free, Variable(9003));
        assert_ne!(fresh, Variable(9003));
    }

    #[test]
    fn substitution_reserves_match_binders_on_the_rhs_before_rewriting_lhs() {
        let source = Variable(9030);
        let replacement = Variable(9031);
        let free = Variable(9032);
        let rhs = IntegerTerm::AlgebraicMatch {
            scrutinee: Box::new(AlgebraicTerm {
                algebraic_type: AlgebraicType::parameter("RhsMatchInput".into()),
                node: AlgebraicTermNode::Variable(free),
            }),
            arms: vec![AlgebraicIntegerMatchArm {
                binding_names: Default::default(),
                variant: "Arm".into(),
                bindings: vec![AlgebraicValue::Integer(IntegerTerm::var(replacement))],
                body: IntegerTerm::Add(
                    IntegerTerm::var(replacement).into(),
                    IntegerTerm::var(free).into(),
                )
                .into(),
            }],
        };
        let proposition =
            Proposition::Equal(Term::Integer(IntegerTerm::var(source)), Term::Integer(rhs));
        let rewritten = substitute_integer_variable_in_pure_proposition(
            &proposition,
            source,
            &IntegerTerm::var(replacement),
        )
        .expect("Integer substitution should preserve the RHS match");
        let Proposition::Equal(Term::Integer(left), Term::Integer(right)) = rewritten else {
            panic!("expected Integer equality")
        };
        assert_eq!(left, IntegerTerm::var(replacement));
        let IntegerTerm::AlgebraicMatch { arms, .. } = right else {
            panic!("expected RHS algebraic match")
        };
        let AlgebraicValue::Integer(IntegerTerm::Variable(fresh)) = arms[0].bindings[0] else {
            panic!("expected Integer match binder")
        };
        assert_ne!(fresh, replacement);
        assert_ne!(fresh, free);
        assert_eq!(
            arms[0].body.as_ref(),
            &IntegerTerm::Add(
                IntegerTerm::var(fresh).into(),
                IntegerTerm::var(free).into()
            )
        );
    }

    #[test]
    fn substitution_does_not_rewrite_a_match_binder_or_its_bound_body() {
        let y = Variable(9010);
        let z = Variable(9011);
        let body = IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
            "observe".into(),
            vec![PureFunctionArgument::Value(ProgramValue::Int32(
                MachineTerm::Variable(y),
            ))],
        ));
        let rewritten = substitute_bitvector_variable_in_integer(
            &symbolic_match(body, y),
            y,
            &MachineTerm::Variable(z),
        );
        let IntegerTerm::AlgebraicMatch { arms, .. } = rewritten else {
            panic!("expected algebraic match")
        };
        assert_eq!(
            arms[0].bindings[0],
            AlgebraicValue::Program(ProgramValue::Int32(MachineTerm::Variable(y),))
        );
        let IntegerTerm::PureFunctionApplication(application) = arms[0].body.as_ref() else {
            panic!("expected application body")
        };
        assert_eq!(
            application.arguments(),
            &[PureFunctionArgument::Value(ProgramValue::Int32(
                MachineTerm::Variable(y),
            ))]
        );
    }

    #[test]
    fn substitution_freshens_each_integral_match_carrier() {
        let source = Variable(9040);
        let replacement = Variable(9041);
        let carriers = [
            ProgramValue::Bool(MachineTerm::Variable(replacement)),
            ProgramValue::Int8(MachineTerm::Variable(replacement)),
            ProgramValue::Int16(MachineTerm::Variable(replacement)),
            ProgramValue::Int32(MachineTerm::Variable(replacement)),
            ProgramValue::UInt8(MachineTerm::Variable(replacement)),
            ProgramValue::UInt16(MachineTerm::Variable(replacement)),
            ProgramValue::UInt32(MachineTerm::Variable(replacement)),
            ProgramValue::Int64(MachineTerm::Variable(replacement)),
            ProgramValue::UInt64(MachineTerm::Variable(replacement)),
        ];
        for carrier in carriers {
            let body = IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
                "observe".into(),
                vec![PureFunctionArgument::Value(ProgramValue::Int32(
                    MachineTerm::Variable(source),
                ))],
            ));
            let rewritten = substitute_bitvector_variable_in_integer(
                &symbolic_match_with_binding(body, AlgebraicValue::Program(carrier.clone())),
                source,
                &MachineTerm::Variable(replacement),
            );
            let IntegerTerm::AlgebraicMatch { arms, .. } = rewritten else {
                panic!("expected algebraic match")
            };
            assert_ne!(arms[0].bindings[0], AlgebraicValue::Program(carrier));
        }
    }

    #[test]
    fn nested_match_construction_and_diagnostics_preserve_sharing() {
        for depth in [8usize, 16, 32, 64] {
            let mut body = IntegerTerm::constant_i64(1);
            for _ in 0..depth {
                body = shared_symbolic_match(body, Variable(9070));
                let IntegerTerm::AlgebraicMatch { arms, .. } = &body else {
                    unreachable!()
                };
                assert_eq!(arms[0].body.id(), arms[1].body.id());
            }
            let copy = body.clone();
            assert_eq!(copy, body);
            let diagnostic = format!("{copy:?}");
            assert!(
                diagnostic.len() < depth * 500,
                "diagnostic expanded a shared match graph"
            );
        }
    }

    #[cfg(test)]
    mod scaling_tests {
        include!(
            "../../scaling_tests/kernel/reasoning/substitution/integer_match_substitution_scope_tests.rs"
        );
    }
}

#[cfg(test)]
mod integer_mixed_quantifier_tests {
    use super::*;

    fn application(integer: IntegerTerm, machine: MachineTerm) -> IntegerTerm {
        IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
            "opaque".into(),
            vec![
                PureFunctionArgument::Integer(integer.into()),
                PureFunctionArgument::Value(ProgramValue::Int32(machine)),
            ],
        ))
    }

    #[test]
    fn integer_substitution_descends_function_and_reverse_conversion_arguments() {
        let from = Variable(87);
        let converted = MachineTerm::IntegerToMachine {
            value: IntegerTerm::var(from).into(),
            destination: MachineIntegerType::Int32,
        };
        let source = Proposition::Equal(
            Term::Integer(application(IntegerTerm::var(from), converted)),
            Term::Integer(IntegerTerm::var(from)),
        );
        let result = substitute_integer_variable_in_pure_proposition(
            &source,
            from,
            &IntegerTerm::constant_i64(9),
        )
        .unwrap();
        assert_eq!(
            result,
            Proposition::Equal(
                Term::Integer(application(
                    IntegerTerm::constant_i64(9),
                    MachineTerm::IntegerToMachine {
                        value: IntegerTerm::constant_i64(9).into(),
                        destination: MachineIntegerType::Int32,
                    }
                )),
                Term::Integer(IntegerTerm::constant_i64(9)),
            )
        );
    }

    #[test]
    fn integer_atom_capture_avoidance_preserves_program_variable_carrier() {
        let from = Variable(88);
        let bound = Variable(89);
        let source = Proposition::ForAll {
            name: Default::default(),
            var: bound,
            sort: Sort::Integer,
            body: Box::new(Proposition::Equal(
                Term::Integer(application(
                    IntegerTerm::var(from),
                    MachineTerm::Variable(bound),
                )),
                Term::Integer(IntegerTerm::var(bound)),
            )),
        };
        let result = substitute_integer_variable_in_pure_proposition(
            &source,
            from,
            &IntegerTerm::var(bound),
        )
        .unwrap();
        let Proposition::ForAll {
            var: fresh, body, ..
        } = result
        else {
            panic!("quantifier lost")
        };
        assert_ne!(fresh, bound);
        assert_eq!(
            *body,
            Proposition::Equal(
                Term::Integer(application(
                    IntegerTerm::var(bound),
                    MachineTerm::Variable(bound)
                )),
                Term::Integer(IntegerTerm::var(fresh)),
            )
        );
    }

    #[test]
    fn integer_witness_replacement_reserves_registered_pointer_integer() {
        let memory = crate::kernel::intern_memory(
            crate::kernel::SymbolicMemory::new().with_block("integer-witness-capture", 64),
        );
        let source = Variable(9_100);
        // This ID is intentionally shared by the replacement's registered
        // pointer and the nested Integer binder. The pointer occurrence is
        // free in the replacement even though the load itself is opaque.
        let free_index = Variable(9_101);
        let load = crate::kernel::eval::load_variable_for_exact_cell(
            &memory,
            &Address {
                base: AddressBase::Concrete("integer-witness-capture".into()),
                offset: AddressOffset::scaled_int32_node(
                    MachineTerm::IntegerToMachine {
                        value: IntegerTerm::var(free_index).into(),
                        destination: MachineIntegerType::Int32,
                    },
                    4,
                ),
            },
            crate::kernel::LoadKind::Int32,
            4,
        );
        let replacement = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            MachineTerm::Variable(load),
        ));
        let proposition = Proposition::Exists {
            name: "nested".into(),
            var: free_index,
            sort: Sort::Integer,
            body: Box::new(Proposition::Equal(
                Term::Integer(IntegerTerm::var(source)),
                Term::Integer(IntegerTerm::var(free_index)),
            )),
        };

        let rewritten =
            substitute_integer_variable_in_pure_proposition(&proposition, source, &replacement)
                .expect("registered-load replacement should remain a valid Integer term");
        let Proposition::Exists {
            var: fresh, body, ..
        } = rewritten
        else {
            panic!("existential binder was dropped")
        };
        assert_ne!(
            fresh, free_index,
            "replacement pointer variable was not reserved"
        );
        let Proposition::Equal(Term::Integer(left), Term::Integer(right)) = *body else {
            panic!("witness body changed carrier")
        };
        assert_eq!(right, IntegerTerm::var(fresh));
        let IntegerTerm::Machine(machine) = left else {
            panic!("witness replacement changed Integer carrier")
        };
        let MachineTerm::Variable(rewritten_load) = machine.value() else {
            panic!("registered load was expanded into the memory state")
        };
        let (rewritten_memory, rewritten_pointer) =
            crate::kernel::eval::registered_load_for_variable(rewritten_load)
                .expect("replacement load must retain its defining pointer");
        assert_eq!(rewritten_memory, memory);
        assert!(matches!(
            rewritten_pointer.offset,
            AddressOffset::Int32Scaled { value, .. }
                if matches!(value.structural_value(), MachineTerm::IntegerToMachine { value, .. }
                    if matches!(value.as_ref(), IntegerTerm::Variable(variable)
                if *variable == free_index))
        ));
    }

    fn program_int_equality(left: Variable, right: Variable) -> Proposition {
        Proposition::Equal(
            Term::Bitvector32(MachineTerm::Variable(left)),
            Term::Bitvector32(MachineTerm::Variable(right)),
        )
    }

    #[test]
    fn integer_substitution_freshens_nested_program_binder_by_carrier() {
        let source = Variable(9_200);
        let c_binder = Variable(9_201);
        let replacement = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            MachineTerm::Variable(c_binder),
        ));
        let proposition = Proposition::ForAll {
            name: Default::default(),
            var: c_binder,
            sort: Sort::ProgramInt32,
            body: Box::new(Proposition::And(
                Box::new(Proposition::Equal(
                    Term::Integer(IntegerTerm::var(source)),
                    Term::Integer(IntegerTerm::constant_i64(0)),
                )),
                Box::new(program_int_equality(c_binder, c_binder)),
            )),
        };

        let Proposition::ForAll {
            var: fresh, body, ..
        } = substitute_integer_variable_in_pure_proposition(&proposition, source, &replacement)
            .expect("nested C quantifiers should be rewritten")
        else {
            panic!("C quantifier was lost")
        };
        assert_ne!(fresh, c_binder);
        let Proposition::And(integer_goal, c_goal) = *body else {
            panic!("nested C proposition shape changed")
        };
        assert!(matches!(&(
            *integer_goal), Proposition::Equal(
                term_source_0 @ Term::Integer(_),
                term_source_1 @ Term::Integer(_)
            ) if matches!((term_source_0.integer_native(), term_source_1.integer_native()), (Some(IntegerTerm::Machine(_)), Some(IntegerTerm::Constant(_))))));
        assert_eq!(*c_goal, program_int_equality(fresh, fresh));
    }

    #[test]
    fn integer_source_is_not_shadowed_by_same_id_program_binder() {
        let source = Variable(9_210);
        let proposition = Proposition::ForAll {
            name: Default::default(),
            var: source,
            sort: Sort::ProgramInt32,
            body: Box::new(Proposition::And(
                Box::new(Proposition::Equal(
                    Term::Integer(IntegerTerm::var(source)),
                    Term::Integer(IntegerTerm::constant_i64(0)),
                )),
                Box::new(program_int_equality(source, source)),
            )),
        };
        let Proposition::ForAll { var, body, .. } =
            substitute_integer_variable_in_pure_proposition(
                &proposition,
                source,
                &IntegerTerm::constant_i64(7),
            )
            .expect("same-ID C binder must not block Integer substitution")
        else {
            panic!("C quantifier was lost")
        };
        assert_eq!(var, source);
        let Proposition::And(integer_goal, c_goal) = *body else {
            panic!("nested C proposition shape changed")
        };
        assert_eq!(
            *integer_goal,
            Proposition::Equal(
                Term::Integer(IntegerTerm::constant_i64(7)),
                Term::Integer(IntegerTerm::constant_i64(0)),
            )
        );
        assert_eq!(*c_goal, program_int_equality(source, source));
    }

    #[test]
    fn integer_substitution_preserves_nested_program_integer_pointer_scopes() {
        let source = Variable(9_220);
        let outer_c = Variable(9_221);
        let inner_integer = outer_c;
        let inner_pointer = Variable(9_222);
        let replacement = IntegerTerm::from_machine(
            MachineIntegerType::UInt64,
            MachineTerm::IntegerAddress(
                Box::new(Address::symbolic(inner_pointer)),
                crate::kernel::AddressObjectClass::NONE,
            ),
        )
        .expect("pointer observations are Integer-valued");
        let pointer_value = |variable| {
            Term::ProgramValue(ProgramValue::Pointer(Pointer::new(
                Address::symbolic(variable),
                ProgramType::Int32Pointer,
            )))
        };
        let proposition = Proposition::ForAll {
            name: Default::default(),
            var: outer_c,
            sort: Sort::ProgramInt32,
            body: Box::new(Proposition::Exists {
                name: "inner".into(),
                var: inner_integer,
                sort: Sort::Integer,
                body: Box::new(Proposition::ForAll {
                    name: Default::default(),
                    var: inner_pointer,
                    sort: Sort::ProgramPointer(ProgramType::Int32Pointer),
                    body: Box::new(Proposition::And(
                        Box::new(Proposition::Equal(
                            Term::Integer(IntegerTerm::var(source)),
                            Term::Integer(IntegerTerm::var(inner_integer)),
                        )),
                        Box::new(Proposition::Equal(
                            pointer_value(outer_c),
                            pointer_value(inner_pointer),
                        )),
                    )),
                }),
            }),
        };
        let Proposition::ForAll {
            var: outer_after,
            body,
            ..
        } = substitute_integer_variable_in_pure_proposition(&proposition, source, &replacement)
            .expect("nested C/Integer/pointer scopes should be rewritten")
        else {
            panic!("outer C quantifier was lost")
        };
        assert_eq!(outer_after, outer_c);
        let Proposition::Exists {
            var: integer_after,
            body,
            ..
        } = *body
        else {
            panic!("Integer quantifier was lost")
        };
        assert_eq!(integer_after, inner_integer);
        let Proposition::ForAll {
            var: pointer_after,
            body,
            ..
        } = *body
        else {
            panic!("pointer quantifier was lost")
        };
        assert_ne!(pointer_after, inner_pointer);
        let Proposition::And(integer_goal, pointer_goal) = *body else {
            panic!("nested scope proposition shape changed")
        };
        assert!(matches!(&(
            *integer_goal), Proposition::Equal(term_source_0 @ Term::Integer(_), Term::Integer(_)) if matches!((term_source_0.integer_native(),), (Some(IntegerTerm::Machine(_)),))));
        assert_eq!(
            *pointer_goal,
            Proposition::Equal(pointer_value(outer_c), pointer_value(pointer_after))
        );
    }

    fn algebraic_variable(algebraic_type: &AlgebraicType, variable: Variable) -> AlgebraicTerm {
        AlgebraicTerm {
            algebraic_type: algebraic_type.clone(),
            node: AlgebraicTermNode::Variable(variable),
        }
    }

    fn algebraic_projection(algebraic_type: &AlgebraicType, variable: Variable) -> IntegerTerm {
        IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
            "projection".into(),
            vec![PureFunctionArgument::Algebraic(algebraic_variable(
                algebraic_type,
                variable,
            ))],
        ))
    }

    #[test]
    fn integer_substitution_keeps_algebraic_and_integer_binders_separate() {
        let from = Variable(9_232);
        let algebraic_type = AlgebraicType::parameter("Flag".into());
        let algebraic = algebraic_variable(&algebraic_type, from);
        let source = Proposition::Exists {
            name: "flag".into(),
            var: from,
            sort: Sort::Algebraic(algebraic_type),
            body: Box::new(Proposition::And(
                Box::new(Proposition::Equal(
                    Term::Integer(IntegerTerm::var(from)),
                    Term::Integer(IntegerTerm::constant_i64(3)),
                )),
                Box::new(Proposition::Equal(
                    Term::Algebraic(algebraic.clone()),
                    Term::Algebraic(algebraic.clone()),
                )),
            )),
        };
        let Proposition::Exists { var, body, .. } =
            substitute_integer_variable_in_pure_proposition(
                &source,
                from,
                &IntegerTerm::constant_i64(3),
            )
            .unwrap()
        else {
            panic!("the algebraic existential was lost");
        };
        assert_eq!(var, from);
        assert_eq!(
            *body,
            Proposition::And(
                Box::new(Proposition::Equal(
                    Term::Integer(IntegerTerm::constant_i64(3)),
                    Term::Integer(IntegerTerm::constant_i64(3))
                )),
                Box::new(Proposition::Equal(
                    Term::Algebraic(algebraic.clone()),
                    Term::Algebraic(algebraic)
                )),
            )
        );
    }

    #[test]
    fn integer_substitution_avoids_algebraic_capture_and_restores_sibling_scope() {
        let from = Variable(9_233);
        let bound = Variable(9_234);
        let algebraic_type = AlgebraicType::parameter("Flag".into());
        let replacement = algebraic_projection(&algebraic_type, bound);
        let leaf = Proposition::Equal(
            Term::Integer(IntegerTerm::var(from)),
            Term::Integer(replacement.clone()),
        );
        let source = Proposition::And(
            Box::new(Proposition::ForAll {
                name: Default::default(),
                var: bound,
                sort: Sort::Algebraic(algebraic_type.clone()),
                body: Box::new(leaf.clone()),
            }),
            Box::new(leaf),
        );
        let Proposition::And(quantifier, sibling) =
            substitute_integer_variable_in_pure_proposition(&source, from, &replacement).unwrap()
        else {
            panic!("the sibling propositions were lost");
        };
        let Proposition::ForAll { var, body, .. } = *quantifier else {
            panic!("the algebraic universal was lost");
        };
        assert_ne!(var, bound);
        assert_eq!(
            *body,
            Proposition::Equal(
                Term::Integer(replacement.clone()),
                Term::Integer(algebraic_projection(&algebraic_type, var))
            )
        );
        assert_eq!(
            *sibling,
            Proposition::Equal(
                Term::Integer(replacement.clone()),
                Term::Integer(replacement)
            )
        );
    }

    #[test]
    fn integer_substitution_rejects_non_term_nested_sort() {
        let proposition = Proposition::ForAll {
            name: Default::default(),
            var: Variable(9_230),
            sort: Sort::Condition,
            body: Box::new(Proposition::Equal(
                Term::Integer(IntegerTerm::var(Variable(9_231))),
                Term::Integer(IntegerTerm::constant_i64(0)),
            )),
        };
        assert_eq!(
            substitute_integer_variable_in_pure_proposition(
                &proposition,
                Variable(9_231),
                &IntegerTerm::constant_i64(1),
            ),
            Err(IntegerPureSubstitutionError::UnsupportedSort)
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!(
            "../../scaling_tests/kernel/reasoning/substitution/integer_mixed_quantifier_tests.rs"
        );
    }
}

#[cfg(test)]
mod integer_range_fold_substitution_tests {
    use super::*;

    mod scaling_tests {
        use super::*;
        include!(
            "../../scaling_tests/kernel/reasoning/substitution/integer_range_fold_substitution_tests.rs"
        );
    }

    #[test]
    fn retained_machine_replacement_freshens_a_capturing_fold_binder() {
        use crate::kernel::{KernelTerm, KernelTermExport, KernelType, MachineBinaryOp};
        let _session = crate::kernel::VerificationSession::enter();
        let source = Variable(1004100);
        let item = Variable(1004101);
        let accumulator = Variable(1004102);
        let format = MachineIntegerType::Int32;
        let leaf = KernelTerm::variable(KernelType::Program(ProgramType::Int32), item);
        let root =
            KernelTerm::machine_binary_shared(format, MachineBinaryOp::Add, [leaf.clone(), leaf]);
        let replacement = SharedMachineIntegerTerm::from_shared(format, root.clone()).unwrap();
        let fold = IntegerTerm::range_fold(
            int32_index(MachineTerm::constant(0), MachineTerm::constant(1)),
            IntegerTerm::constant_i64(0),
            accumulator,
            item,
            program_item(source),
        );
        let from = MachineTerm::Variable(source);
        let exports = KernelTermExport::machine_export_count();
        let mut rewrite =
            crate::kernel::proof::term_rewrite::TermRewrite::for_machine_operand_checked(
                &from,
                replacement.operand_view(),
            );
        let result = rewrite.integer(&fold);
        assert!(rewrite.refusal().is_none());
        let IntegerTerm::RangeFold {
            item: fresh, body, ..
        } = result
        else {
            panic!("fold scope")
        };
        assert_ne!(fresh, item);
        let IntegerTerm::Machine(value) = body.as_ref() else {
            panic!("machine body")
        };
        assert_eq!(value.shared_operand(), Some(&root));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    fn int32_index(start: MachineTerm, end: MachineTerm) -> IntegerRangeFoldIndex {
        IntegerRangeFoldIndex::Int32 {
            start: SharedIntegerRangeEndpoint::intern(start),
            end: SharedIntegerRangeEndpoint::intern(end),
        }
    }

    fn program_item(value: Variable) -> IntegerTerm {
        IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            MachineTerm::Variable(value),
        ))
    }

    fn program_item_value(value: MachineTerm) -> IntegerTerm {
        IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            value,
        ))
    }

    #[test]
    fn int32_fold_substitution_freshens_item_and_preserves_free_replacement_and_y_plus_one() {
        let source = Variable(70_000);
        let item = Variable(70_001);
        let free_y_plus_one = Variable(70_002);
        let free_zero = Variable(0);
        let accumulator = Variable(70_003);
        let body = IntegerTerm::add(
            IntegerTerm::add(
                IntegerTerm::add(program_item(source), program_item(item)),
                program_item(free_y_plus_one),
            ),
            program_item(free_zero),
        );
        let fold = IntegerTerm::range_fold(
            int32_index(MachineTerm::constant(0), MachineTerm::constant(1)),
            IntegerTerm::var(accumulator),
            accumulator,
            item,
            body,
        );

        let replaced =
            substitute_bitvector_variable_in_integer(&fold, source, &MachineTerm::Variable(item));
        let IntegerTerm::RangeFold {
            item: fresh_item,
            body,
            ..
        } = replaced
        else {
            panic!("substitution changed the fold shape")
        };
        assert_ne!(fresh_item, item);
        assert_ne!(fresh_item, free_y_plus_one);
        assert_ne!(fresh_item, free_zero);
        let IntegerTerm::Add(left, free_zero_term) = body.as_ref() else {
            panic!("missing fold body additions")
        };
        assert!(
            matches!(free_zero_term.as_ref(), IntegerTerm::Machine(machine)
            if machine.value() == &MachineTerm::Variable(free_zero))
        );
        let IntegerTerm::Add(prefix, free_item) = left.as_ref() else {
            panic!("missing free y+1 term")
        };
        assert!(matches!(free_item.as_ref(), IntegerTerm::Machine(machine)
            if machine.value() == &MachineTerm::Variable(free_y_plus_one)));
        let IntegerTerm::Add(replaced_source, bound_item) = prefix.as_ref() else {
            panic!("missing source and item terms")
        };
        assert!(
            matches!(replaced_source.as_ref(), IntegerTerm::Machine(machine)
            if machine.value() == &MachineTerm::Variable(item))
        );
        assert!(matches!(bound_item.as_ref(), IntegerTerm::Machine(machine)
            if machine.value() == &MachineTerm::Variable(fresh_item)));
    }

    #[test]
    fn int32_fold_substitution_keeps_bound_item_but_rewrites_endpoints_and_initial() {
        let source = Variable(70_010);
        let accumulator = Variable(70_011);
        let body = program_item(source);
        let fold = IntegerTerm::range_fold(
            int32_index(MachineTerm::Variable(source), MachineTerm::Variable(source)),
            program_item(source),
            accumulator,
            source,
            body,
        );

        let replaced =
            substitute_bitvector_variable_in_integer(&fold, source, &MachineTerm::constant(9));
        let IntegerTerm::RangeFold {
            index,
            initial,
            item,
            body,
            ..
        } = replaced
        else {
            panic!("substitution changed the fold shape")
        };
        assert_eq!(item, source);
        let IntegerRangeFoldIndex::Int32 { start, end } = index else {
            panic!("substitution changed the index carrier")
        };
        assert_eq!(start.value(), &MachineTerm::constant(9));
        assert_eq!(end.value(), &MachineTerm::constant(9));
        // The initial value was `to_integer(source)`, so substituting a literal
        // decides that observation: it is the mathematical 9, the same Integer
        // an evaluation of `to_integer(9)` produces. The body's observation is
        // of the bound item and stays an observation.
        assert_eq!(initial.as_ref(), &IntegerTerm::constant_i64(9));
        assert!(matches!(body.as_ref(), IntegerTerm::Machine(machine)
            if machine.value() == &MachineTerm::Variable(source)));
    }

    #[test]
    fn unchanged_nested_fold_body_reuses_shared_dag_nodes() {
        let accumulator = Variable(70_020);
        let item = Variable(70_021);
        let nested_body = IntegerTerm::add(IntegerTerm::var(accumulator), IntegerTerm::var(item));
        let nested = IntegerTerm::range_fold(
            IntegerRangeFoldIndex::Integer {
                start: IntegerTerm::constant_i64(0).into(),
                end: IntegerTerm::constant_i64(1).into(),
            },
            IntegerTerm::constant_i64(0),
            accumulator,
            item,
            nested_body,
        );
        let outer = IntegerTerm::add(nested.clone(), nested);
        let replaced = substitute_bitvector_variable_in_integer(
            &outer,
            Variable(70_022),
            &MachineTerm::constant(9),
        );
        let IntegerTerm::Add(left, right) = replaced else {
            panic!("substitution changed the shared outer shape")
        };
        assert_eq!(left.id(), right.id());
    }

    #[test]
    fn integer_substitution_shared_nested_folds_scales_with_dag_size() {
        let from = Variable(70_040);
        let accumulator = Variable(70_041);
        let item = Variable(70_042);
        for depth in [8, 16, 32, 64] {
            let mut value = IntegerTerm::var(from);
            for _ in 0..depth {
                let body = IntegerTerm::add(value.clone(), value.clone());
                value = IntegerTerm::range_fold(
                    IntegerRangeFoldIndex::Integer {
                        start: IntegerTerm::constant_i64(0).into(),
                        end: IntegerTerm::constant_i64(1).into(),
                    },
                    IntegerTerm::constant_i64(0),
                    accumulator,
                    item,
                    body,
                );
            }
            let proposition = Proposition::Equal(
                Term::Integer(value),
                Term::Integer(IntegerTerm::constant_i64(0)),
            );
            let replaced = substitute_integer_variable_in_pure_proposition(
                &proposition,
                from,
                &IntegerTerm::constant_i64(2),
            )
            .expect("fold substitution should preserve the supported Integer carrier");
            let Proposition::Equal(Term::Integer(mut value), _) = replaced else {
                panic!("equality carrier changed")
            };
            for _ in 0..depth {
                let IntegerTerm::RangeFold { body, .. } = value else {
                    panic!("nested fold shape changed")
                };
                let IntegerTerm::Add(left, right) = body.as_ref() else {
                    panic!("shared fold body shape changed")
                };
                assert_eq!(left.id(), right.id());
                value = left.as_ref().clone();
            }
            assert_eq!(value, IntegerTerm::Constant(2.into()));
        }
    }

    #[test]
    fn int32_fold_substitution_rejects_non_machine_item_value() {
        let item = Variable(70_050);
        let body = program_item(item);
        let result = instantiate_integer_range_fold_step(
            &body,
            Variable(70_051),
            &IntegerTerm::constant_i64(0),
            item,
            &IntegerTerm::var(Variable(70_052)),
            Some(MachineIntegerType::Int32),
        );
        assert_eq!(
            result,
            Err(IntegerPureSubstitutionError::UnsupportedCarrier)
        );
    }

    #[test]
    fn int32_fold_substitution_rejects_wrong_width_machine_item_value() {
        let item = Variable(70_053);
        let body = program_item(item);
        let malformed = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::UInt32,
            MachineTerm::Variable(Variable(70_054)),
        ));
        let result = instantiate_integer_range_fold_step(
            &body,
            Variable(70_055),
            &IntegerTerm::constant_i64(0),
            item,
            &malformed,
            Some(MachineIntegerType::Int32),
        );
        assert_eq!(
            result,
            Err(IntegerPureSubstitutionError::UnsupportedCarrier)
        );
    }

    #[test]
    fn quantified_structural_read_renaming_reprojects_its_source() {
        let _session = crate::kernel::VerificationSession::enter();
        let binder = Variable(70_190);
        let renamed = Variable(70_191);
        let pointer = Address {
            base: AddressBase::ExternalArgument,
            offset: AddressOffset::scale_int32(MachineTerm::Variable(binder), 4),
        };
        let source =
            crate::kernel::intern_memory(SymbolicMemory::new().with_block("unrelated", 4).store(
                Address {
                    base: AddressBase::Concrete("unrelated".into()),
                    offset: AddressOffset::Constant(0),
                },
                ProgramValue::Int32(MachineTerm::constant(7)),
            ));
        crate::kernel::eval::record_load_access_width(source.memory(), &pointer, 4);
        let original = crate::kernel::eval::canonical_term(&MachineTerm::MemoryLoad(
            ProgramPoint::at(&source),
            Box::new(pointer.clone()),
            crate::kernel::LoadKind::Int32,
        ));
        let MachineTerm::MemoryLoad(projected, _, _) = &original else {
            panic!("structural read");
        };
        assert_ne!(
            *projected.shared_memory(),
            source,
            "exercise a projected state"
        );
        let renamed_pointer = substitute_bitvector_variable_in_pointer(
            &pointer,
            binder,
            &MachineTerm::Variable(renamed),
        );
        let actual =
            substitute_bitvector_variable(&original, binder, &MachineTerm::Variable(renamed));
        crate::kernel::eval::record_load_access_width(source.memory(), &renamed_pointer, 4);
        let expected = crate::kernel::eval::canonical_term(&MachineTerm::MemoryLoad(
            ProgramPoint::at(&source),
            Box::new(renamed_pointer),
            crate::kernel::LoadKind::Int32,
        ));
        assert_eq!(actual, expected);
        assert_eq!(
            crate::kernel::eval::scalar_read_observation(
                crate::kernel::MachineOperandView::Legacy(&actual),
            )
            .unwrap()
            .bytes,
            4
        );
    }

    #[test]
    fn quantified_load_substitution_preserves_access_width() {
        let _session = crate::kernel::VerificationSession::enter();
        for bytes in [4, 8] {
            let memory = crate::kernel::intern_memory(SymbolicMemory::new());
            let binder = Variable(70_156 + u64::from(bytes));
            let pointer = Address {
                base: AddressBase::ExternalArgument,
                offset: AddressOffset::scale_int32(MachineTerm::Variable(binder), 4),
            };
            let original = crate::kernel::eval::scalar_read_for_exact_cell(
                &memory,
                &pointer,
                crate::kernel::LoadKind::Int32,
                bytes,
            );
            let substituted = substitute_bitvector_variable(
                &original,
                binder,
                &MachineTerm::Variable(Variable(70_170 + u64::from(bytes))),
            );
            assert!(matches!(substituted, MachineTerm::MemoryLoad(..)));
            let observed = crate::kernel::eval::scalar_read_observation(
                crate::kernel::MachineOperandView::Legacy(&substituted),
            )
            .unwrap();
            assert_eq!(observed.bytes, bytes);
            let renamed_pointer = observed.pointer;
            assert_eq!(
                renamed_pointer,
                Address {
                    base: AddressBase::ExternalArgument,
                    offset: AddressOffset::scale_int32(
                        MachineTerm::Variable(Variable(70_170 + u64::from(bytes))),
                        4
                    )
                }
            );
        }
    }

    #[test]
    fn int32_fold_substitution_rewrites_registered_load_address_only() {
        let item = Variable(70_056);
        let memory = crate::kernel::intern_memory(SymbolicMemory::new().with_block("array", 16));
        let pointer = Address {
            base: AddressBase::Concrete("array".into()),
            offset: AddressOffset::scaled_int32_node(MachineTerm::Variable(item), 4),
        };
        let load_variable = crate::kernel::eval::load_variable_for_cell(
            &memory,
            &pointer,
            crate::kernel::LoadKind::Int32,
        );
        let body = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            MachineTerm::Variable(load_variable),
        ));
        let result = instantiate_integer_range_fold_step(
            &body,
            Variable(70_057),
            &IntegerTerm::constant_i64(0),
            item,
            &program_item_value(MachineTerm::constant(0)),
            Some(MachineIntegerType::Int32),
        )
        .expect("the checked fold step should preserve the registered load");
        let IntegerTerm::Machine(machine) = result else {
            panic!("the machine load carrier was lost");
        };
        let (retained_state, pointer, kind) =
            machine.operand_view().read().expect("structural read");
        assert_eq!(kind, crate::kernel::LoadKind::Int32);
        assert_ne!(
            pointer,
            &crate::kernel::eval::registered_load_for_variable(&load_variable)
                .unwrap()
                .1
        );
        // A new address retains the producer's live memory, rather than
        // reusing the original address's empty version point.
        assert_eq!(retained_state, &memory);
        assert_eq!(pointer.offset, AddressOffset::Constant(0));
    }

    #[test]
    fn int32_fold_substitution_canonicalizes_nonzero_load_base() {
        let item = Variable(70_058);
        let memory = crate::kernel::intern_memory(SymbolicMemory::new().with_block("array", 16));
        let pointer = Address {
            base: AddressBase::Concrete("array".into()),
            offset: AddressOffset::Add(
                Box::new(AddressOffset::Constant(4)),
                Box::new(AddressOffset::scaled_int32_node(
                    MachineTerm::Variable(item),
                    4,
                )),
            ),
        };
        let load_variable = crate::kernel::eval::load_variable_for_cell(
            &memory,
            &pointer,
            crate::kernel::LoadKind::Int32,
        );
        let body = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            MachineTerm::Variable(load_variable),
        ));
        let result = instantiate_integer_range_fold_step(
            &body,
            Variable(70_059),
            &IntegerTerm::constant_i64(0),
            item,
            &program_item_value(MachineTerm::constant(0)),
            Some(MachineIntegerType::Int32),
        )
        .expect("the checked fold step should preserve the registered load");
        let IntegerTerm::Machine(machine) = result else {
            panic!("the machine load carrier was lost");
        };
        let (retained_state, pointer, kind) =
            machine.operand_view().read().expect("structural read");
        assert_eq!(kind, crate::kernel::LoadKind::Int32);
        assert_ne!(
            pointer,
            &crate::kernel::eval::registered_load_for_variable(&load_variable)
                .unwrap()
                .1
        );
        // A new address retains the producer's live memory, rather than
        // reusing the original address's empty version point.
        assert_eq!(retained_state, &memory);
        assert_eq!(pointer.offset, AddressOffset::Constant(4));
    }

    #[test]
    fn checked_machine_fold_substitution_rejects_work_exhaustion() {
        use crate::instrumentation::{self, TacticEvent, TacticWorkLimits, VerificationEvent};

        let source = Variable(70_060);
        let mut payload = MachineTerm::Variable(source);
        for _ in 0..64 {
            payload = binary_node!(
                Int32,
                Add,
                Box::new(payload),
                Box::new(MachineTerm::constant(1))
            );
        }
        let term = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            payload,
        ));
        let (result, _events) = instrumentation::with_tactic_work_limits(
            TacticWorkLimits {
                simple: 4,
                smart: 4,
                control: 4,
            },
            || {
                instrumentation::collect(|| {
                    let tactic = TacticEvent {
                        source_tactic_path: None,
                        claim: "integer fold checked substitution".into(),
                        tactic_index: 0,
                        tactic_name: "integer_fold_checked_substitution".into(),
                        class: "simple".into(),
                        statement_index: 0,
                        source_index: 0,
                    };
                    instrumentation::emit(VerificationEvent::TacticStarted(tactic.clone()));
                    let result = substitute_bitvector_variable_in_integer_checked(
                        &term,
                        source,
                        &MachineTerm::constant(7),
                    );
                    instrumentation::emit(VerificationEvent::TacticFailed(tactic));
                    result
                })
            },
        );
        assert_eq!(result, Err(IntegerPureSubstitutionError::WorkLimitExceeded));
    }
}

#[cfg(test)]
mod resource_reference_substitution_tests {
    use super::*;
    use crate::kernel::{ResourceFieldSchema, ResourceFieldType, ResourceReference};

    fn reference_resource() -> Resource {
        let schema = ResourceFieldSchema::new(vec![(
            "value".into(),
            ResourceFieldType::Program(ProgramType::Int32),
        )])
        .unwrap();
        let leaf = ResourceInstance::new(
            Variable(200),
            "cell".into(),
            vec![
                AlgebraicValue::Program(ProgramValue::Int32(MachineTerm::Variable(Variable(100)))),
                AlgebraicValue::Program(ProgramValue::pointer(Address::symbolic(Variable(101)))),
            ]
            .into(),
            schema.clone(),
            vec![AlgebraicValue::Program(ProgramValue::Int32(
                MachineTerm::Variable(Variable(102)),
            ))]
            .into(),
        )
        .unwrap();
        let middle = ResourceInstance::new(
            Variable(201),
            "middle".into(),
            vec![].into(),
            schema.clone(),
            vec![AlgebraicValue::Program(int32(0))].into(),
        )
        .unwrap()
        .with_resource_arguments(vec![ResourceReference::from_instance(&leaf)]);
        Resource::Instance(
            ResourceInstance::new(
                Variable(202),
                "wrapper".into(),
                vec![].into(),
                schema,
                vec![AlgebraicValue::Program(int32(0))].into(),
            )
            .unwrap()
            .with_resource_arguments(vec![ResourceReference::from_instance(&middle)]),
        )
    }

    #[test]
    fn substitutions_reach_nested_reference_values_without_changing_occurrences() {
        let source = reference_resource();
        let replaced = substitute_bitvector_variable_in_resource(
            &source,
            Variable(100),
            &MachineTerm::constant(7),
        );
        let pointer = Address::symbolic(Variable(103));
        let replaced = substitute_pointer_variable_in_resource(&replaced, Variable(101), &pointer);
        let Resource::Instance(instance) = replaced else {
            unreachable!()
        };
        assert_eq!(instance.identity(), Variable(202));
        let middle = &instance.resource_arguments()[0];
        assert_eq!(middle.identity(), Variable(201));
        let leaf = &middle.description().resource_arguments()[0];
        assert_eq!(leaf.identity(), Variable(200));
        assert_eq!(
            leaf.description().arguments(),
            &[
                AlgebraicValue::Program(int32(7)),
                AlgebraicValue::Program(ProgramValue::pointer(pointer))
            ]
        );
        let mut variables = BTreeSet::new();
        collect_resource_bound_variables(&Resource::Instance(instance), &mut variables);
        assert!(!variables.contains(&Variable(100)));
        assert!(!variables.contains(&Variable(101)));
        assert!(!variables.contains(&Variable(102)));
        assert!(variables.contains(&Variable(103)));
    }

    #[test]
    fn both_collectors_visit_captured_values_but_not_observed_fields_or_identities() {
        let resource = reference_resource();
        let mut bound = BTreeSet::new();
        collect_resource_bound_variables(&resource, &mut bound);
        let mut bitvectors = BTreeSet::new();
        crate::kernel::reasoning::collect_resource_bitvector_variables(&resource, &mut bitvectors);
        // Free scalar variables belong to the bitvector collector; the
        // bound-variable collector includes symbolic pointer identities.
        assert!(!bound.contains(&Variable(100)));
        assert!(bound.contains(&Variable(101)));
        assert!(bitvectors.contains(&Variable(100)));
        assert!(!bound.contains(&Variable(102)));
        assert!(!bitvectors.contains(&Variable(102)));
        assert!(!bound.contains(&Variable(200)));
    }
}

#[cfg(test)]
mod checked_singleton_substitution_tests {
    use super::*;
    use crate::instrumentation::{self, TacticEvent, TacticWorkLimits, VerificationEvent};

    fn pointer_value(variable: Variable) -> Pointer {
        Pointer::new(Address::symbolic(variable), ProgramType::Int32Pointer)
    }

    fn pointer_term(variable: Variable) -> Term {
        Term::ProgramValue(ProgramValue::Pointer(pointer_value(variable)))
    }

    #[test]
    fn pointer_witness_substitution_preserves_connectives_and_binder_scopes() {
        let from = Variable(70_110);
        let captured = Variable(70_111);
        let leaf = Proposition::Equal(pointer_term(from), pointer_term(captured));
        let atom = Proposition::Equal(
            Term::Integer(IntegerTerm::var(from)),
            Term::Integer(IntegerTerm::var(from)),
        );
        let compound = Proposition::And(Box::new(atom.clone()), Box::new(leaf.clone()));
        assert_eq!(
            substitute_pointer_value_in_proposition(&compound, from, &pointer_value(captured))
                .unwrap(),
            Proposition::And(
                Box::new(atom),
                Box::new(Proposition::Equal(
                    pointer_term(captured),
                    pointer_term(captured)
                ))
            )
        );

        let source = Proposition::ForAll {
            name: Default::default(),
            var: captured,
            sort: Sort::ProgramPointer(ProgramType::Int32Pointer),
            body: Box::new(leaf.clone()),
        };
        let Proposition::ForAll { var, body, .. } =
            substitute_pointer_value_in_proposition(&source, from, &pointer_value(captured))
                .unwrap()
        else {
            panic!("the quantifier must survive");
        };
        assert_ne!(var, captured);
        assert_eq!(
            *body,
            Proposition::Equal(pointer_term(captured), pointer_term(var))
        );

        let shadowed = Proposition::Exists {
            name: "shadowed".into(),
            var: from,
            sort: Sort::ProgramPointer(ProgramType::Int32Pointer),
            body: Box::new(leaf),
        };
        assert_eq!(
            substitute_pointer_value_in_proposition(&shadowed, from, &pointer_value(captured))
                .unwrap(),
            shadowed
        );
    }

    fn observed(variable: Variable) -> IntegerTerm {
        IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            MachineTerm::Variable(variable),
        ))
    }

    fn proposition(variable: Variable) -> Proposition {
        Proposition::Equal(
            Term::Integer(observed(variable)),
            Term::Integer(IntegerTerm::var(variable)),
        )
    }

    #[test]
    fn checked_singleton_substitution_preserves_quantifier_carriers() {
        let variable = Variable(70_100);
        let leaf = proposition(variable);
        let replaced = substitute_machine_constant_in_pure_proposition(&leaf, variable, 7)
            .expect("the free machine variable is supported");
        assert_eq!(
            replaced,
            Proposition::Equal(
                Term::Integer(IntegerTerm::constant_i64(7)),
                Term::Integer(IntegerTerm::var(variable)),
            )
        );
        for sort in [Sort::ProgramInt32, Sort::Integer] {
            for exists in [false, true] {
                let wrap = |body| {
                    if exists {
                        Proposition::Exists {
                            name: "bound".into(),
                            var: variable,
                            sort: sort.clone(),
                            body: Box::new(body),
                        }
                    } else {
                        Proposition::ForAll {
                            name: Default::default(),
                            var: variable,
                            sort: sort.clone(),
                            body: Box::new(body),
                        }
                    }
                };
                let expected = if sort == Sort::ProgramInt32 {
                    leaf.clone()
                } else {
                    replaced.clone()
                };
                assert_eq!(
                    substitute_machine_constant_in_pure_proposition(
                        &wrap(leaf.clone()),
                        variable,
                        7
                    ),
                    Ok(wrap(expected)),
                );
            }
        }
    }

    #[test]
    fn checked_singleton_substitution_returns_budget_refusal_without_a_partial_result() {
        let variable = Variable(70_101);
        let mut value = observed(variable);
        for _ in 0..64 {
            value = IntegerTerm::add(value.clone(), value.clone());
        }
        let source = Proposition::Equal(Term::Integer(value), Term::Integer(observed(variable)));
        assert!(substitute_machine_constant_in_pure_proposition(&source, variable, 7).is_ok());
        // These limits are below the 64 binary nodes plus their leaf. Avoid
        // a one-below-observed-work threshold: interning setup may already
        // be warm on the next invocation, independently of the traversal.
        for limit in [0, 4, 64] {
            let (result, _) = instrumentation::with_tactic_work_limits(
                TacticWorkLimits {
                    simple: limit,
                    smart: limit,
                    control: limit,
                },
                || {
                    instrumentation::collect(|| {
                        let tactic = TacticEvent {
                            source_tactic_path: None,
                            claim: "checked singleton substitution".into(),
                            tactic_index: 0,
                            tactic_name: "checked_singleton_substitution".into(),
                            class: "simple".into(),
                            statement_index: 0,
                            source_index: 0,
                        };
                        instrumentation::emit(VerificationEvent::TacticStarted(tactic.clone()));
                        let result =
                            substitute_machine_constant_in_pure_proposition(&source, variable, 7);
                        assert!(
                            instrumentation::exceeded_verification_limit_context().is_some(),
                            "limit {limit} must exhaust the selected traversal"
                        );
                        instrumentation::emit(VerificationEvent::TacticFailed(tactic));
                        result
                    })
                },
            );
            assert_eq!(result, Err(IntegerPureSubstitutionError::WorkLimitExceeded));
        }
    }

    #[test]
    fn checked_singleton_substitution_refuses_unsupported_carriers() {
        let source = Proposition::Predicate {
            name: "opaque".into(),
            arguments: vec![Term::Memory(SymbolicMemory::new())],
        };
        assert_eq!(
            substitute_machine_constant_in_pure_proposition(&source, Variable(70_103), 7),
            Err(IntegerPureSubstitutionError::UnsupportedCarrier),
        );
    }

    #[test]
    fn checked_singleton_substitution_preserves_predicate_arguments() {
        let variable = Variable(70_104);
        let source = Proposition::Predicate {
            name: "opaque".into(),
            arguments: vec![
                Term::Integer(observed(variable)),
                Term::Bitvector32(MachineTerm::Variable(variable)),
                Term::Integer(IntegerTerm::var(variable)),
            ],
        };
        assert_eq!(
            substitute_machine_constant_in_pure_proposition(&source, variable, 7),
            Ok(Proposition::Predicate {
                name: "opaque".into(),
                arguments: vec![
                    Term::Integer(IntegerTerm::constant_i64(7)),
                    Term::Bitvector32(MachineTerm::constant(7)),
                    Term::Integer(IntegerTerm::var(variable)),
                ],
            }),
        );
    }

    #[test]
    fn checked_singleton_substitution_bounds_deep_quantifier_setup() {
        let variable = Variable(70_105);
        let mut source = proposition(variable);
        for index in 0..2048 {
            source = Proposition::ForAll {
                name: Default::default(),
                var: Variable(80_000 + index),
                sort: Sort::ProgramInt32,
                body: Box::new(source),
            };
        }
        // Borrow the source so its recursive drop occurs on the parent stack.
        // Setup must stop at its first checkpoint, before descending the chain.
        std::thread::scope(|scope| {
            std::thread::Builder::new()
                .stack_size(192 * 1024)
                .spawn_scoped(scope, || {
                    let (result, _) = instrumentation::with_tactic_work_limits(
                        TacticWorkLimits {
                            simple: 0,
                            smart: 0,
                            control: 0,
                        },
                        || {
                            instrumentation::collect(|| {
                                let tactic = TacticEvent {
                                    source_tactic_path: None,
                                    claim: "deep singleton setup".into(),
                                    tactic_index: 0,
                                    tactic_name: "deep_singleton_setup".into(),
                                    class: "simple".into(),
                                    statement_index: 0,
                                    source_index: 0,
                                };
                                instrumentation::emit(VerificationEvent::TacticStarted(
                                    tactic.clone(),
                                ));
                                let result = substitute_machine_constant_in_pure_proposition(
                                    &source, variable, 7,
                                );
                                instrumentation::emit(VerificationEvent::TacticFailed(tactic));
                                result
                            })
                        },
                    );
                    assert_eq!(result, Err(IntegerPureSubstitutionError::WorkLimitExceeded));
                })
                .unwrap()
                .join()
                .unwrap();
        });
    }

    #[cfg(test)]
    mod scaling_tests {
        include!(
            "../../scaling_tests/kernel/reasoning/substitution/checked_singleton_substitution_tests.rs"
        );
    }
}

#[cfg(test)]
mod checked_surface_load_resolution_tests {
    use super::*;

    fn observed(variable: Variable) -> IntegerTerm {
        IntegerTerm::from_machine(MachineIntegerType::Int32, MachineTerm::Variable(variable))
            .unwrap()
    }

    #[test]
    fn surface_load_binding_rewrites_machine_observations_without_integer_binder_capture() {
        let variable = Variable(70_300);
        let source = Proposition::Equal(
            Term::Integer(observed(variable)),
            Term::Integer(IntegerTerm::var(variable)),
        );
        let result =
            substitute_surface_load_binding(&source, variable, &MachineTerm::constant(7)).unwrap();
        assert_eq!(
            result,
            Proposition::Equal(
                Term::Integer(IntegerTerm::constant_i64(7)),
                Term::Integer(IntegerTerm::var(variable)),
            )
        );
    }

    #[test]
    fn checked_surface_load_resolution_returns_work_refusal_without_a_partial_proposition() {
        use crate::instrumentation::{self, TacticEvent, TacticWorkLimits, VerificationEvent};
        let variable = Variable(70_301);
        let source = Proposition::Equal(
            Term::Integer(observed(variable)),
            Term::Integer(IntegerTerm::constant_i64(0)),
        );
        let ((binding, registry), _) = instrumentation::with_tactic_work_limits(
            TacticWorkLimits {
                simple: 0,
                smart: 0,
                control: 0,
            },
            || {
                instrumentation::collect(|| {
                    let event = TacticEvent {
                        source_tactic_path: None,
                        claim: "checked surface load refusal".into(),
                        tactic_index: 0,
                        tactic_name: "checked_surface_load_resolution".into(),
                        class: "simple".into(),
                        statement_index: 0,
                        source_index: 0,
                    };
                    instrumentation::emit(VerificationEvent::TacticStarted(event.clone()));
                    let binding = substitute_surface_load_binding(
                        &source,
                        variable,
                        &MachineTerm::constant(7),
                    );
                    let registry = try_resolve_load_variables_from_registry(&source);
                    instrumentation::emit(VerificationEvent::TacticFailed(event));
                    (binding, registry)
                })
            },
        );
        assert_eq!(
            binding,
            Err(IntegerPureSubstitutionError::WorkLimitExceeded)
        );
        assert_eq!(
            registry,
            Err(IntegerPureSubstitutionError::WorkLimitExceeded)
        );
    }
}

#[cfg(test)]
#[test]
fn float_conversion_substitution_matches_direct_constant_cast() {
    let _session = crate::kernel::VerificationSession::enter();
    let variable = Variable(999950);
    let evaluate_cast = |value: ProgramValue, target_type: ProgramType| {
        let state = ExecutionState::new();
        let expression = SpecExpression::ProgramExpression(ProgramExpression::Cast {
            expression: Box::new(ProgramExpression::Value(value)),
            target_type,
            integer_mode: crate::kernel::IntegerCastMode::CConversion,
            pointee_struct: None,
            pointee_volatile: false,
            pointee_constant: false,
            explicit_qualification: false,
        });
        crate::kernel::program_evaluate_speresource_expression_with_checked_obligations(
            &state,
            &expression,
            Some(&state),
            &PureFactContext::new(),
        )
        .unwrap()
        .0
    };
    let sources = [
        crate::kernel::int8(u32::MAX),
        crate::kernel::uint8(0xff),
        crate::kernel::int16(u32::MAX),
        crate::kernel::uint16(0xffff),
        ProgramValue::Int32(MachineTerm::constant(16_777_217)),
        ProgramValue::Int32(MachineTerm::constant(i32::MIN as u32)),
        ProgramValue::UInt32(MachineTerm::uint32_constant(u32::MAX)),
        ProgramValue::Int64(MachineTerm::int64_constant(i64::MIN)),
        ProgramValue::UInt64(MachineTerm::uint64_constant(u64::MAX)),
        ProgramValue::Float32(MachineTerm::constant(0x80000000)),
        ProgramValue::Float32(MachineTerm::constant(1)),
        ProgramValue::Float32(MachineTerm::constant(0x7f800000)),
        ProgramValue::Float32(MachineTerm::constant(0x7f800123)),
        ProgramValue::Float64(MachineTerm::uint64_constant(0x8000000000000000)),
        ProgramValue::Float64(MachineTerm::uint64_constant(0x3ff0000010000000)),
        ProgramValue::Float64(MachineTerm::uint64_constant(0x7ff0000000000000)),
        ProgramValue::Float64(MachineTerm::uint64_constant(0xfff8000000000123)),
    ];
    for value in sources {
        for target in [ProgramType::Float32, ProgramType::Float64] {
            let (symbolic_value, literal) = match &value {
                ProgramValue::Float32(term) => {
                    (ProgramValue::Float32(MachineTerm::Variable(variable)), term)
                }
                ProgramValue::Float64(term) => {
                    (ProgramValue::Float64(MachineTerm::Variable(variable)), term)
                }
                crate::kernel::integer64_c_value!(term) => (
                    MachineIntegerType::from_program_type(value.program_type())
                        .unwrap()
                        .value_from_term(MachineTerm::Variable(variable)),
                    term,
                ),
                _ => unreachable!(),
            };
            let symbolic = evaluate_cast(symbolic_value, target);
            let term = match symbolic {
                ProgramValue::Float32(term) | ProgramValue::Float64(term) => term,
                _ => unreachable!(),
            };
            let instantiated = substitute_bitvector_variable(&term, variable, literal);
            let actual = if target == ProgramType::Float32 {
                ProgramValue::Float32(instantiated)
            } else {
                ProgramValue::Float64(instantiated)
            };
            assert_eq!(
                actual,
                evaluate_cast(value.clone(), target),
                "{:?} -> {target:?}",
                value
            );
        }
    }
    let nested = evaluate_cast(
        evaluate_cast(
            ProgramValue::Int32(MachineTerm::Variable(variable)),
            ProgramType::Float32,
        ),
        ProgramType::Float64,
    );
    let ProgramValue::Float64(nested) = nested else {
        unreachable!()
    };
    assert_eq!(
        ProgramValue::Float64(substitute_bitvector_variable(
            &nested,
            variable,
            &MachineTerm::constant(16_777_217)
        )),
        evaluate_cast(
            evaluate_cast(
                ProgramValue::Int32(MachineTerm::constant(16_777_217)),
                ProgramType::Float32
            ),
            ProgramType::Float64
        ),
    );
    for source in [
        ProgramValue::Float32(MachineTerm::constant(0x3fe00000)),
        ProgramValue::Float64(MachineTerm::uint64_constant(0x3ffc000000000000)),
    ] {
        for target in [
            MachineIntegerType::Int8,
            MachineIntegerType::UInt8,
            MachineIntegerType::Int16,
            MachineIntegerType::UInt16,
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let (symbolic, literal) = match &source {
                ProgramValue::Float32(term) => {
                    (ProgramValue::Float32(MachineTerm::Variable(variable)), term)
                }
                ProgramValue::Float64(term) => {
                    (ProgramValue::Float64(MachineTerm::Variable(variable)), term)
                }
                _ => unreachable!(),
            };
            let crate::kernel::integer64_c_value!(term) =
                evaluate_cast(symbolic, target.program_type())
            else {
                unreachable!()
            };
            let actual =
                target.value_from_term(substitute_bitvector_variable(&term, variable, literal));
            assert_eq!(actual, evaluate_cast(source.clone(), target.program_type()));
        }
    }
}

#[cfg(test)]
mod float_conversion_freshness_tests {
    use super::*;

    #[test]
    fn retained_float_conversion_freshness_preserves_nested_binders() {
        let _session = crate::kernel::VerificationSession::enter();
        let native = MachineTerm::opaque_conversion(
            "c_float32_to_int32",
            MachineTerm::opaque_conversion(
                "c_int32_to_float32",
                MachineTerm::RangeFold {
                    start: Box::new(MachineTerm::constant(0)),
                    end: Box::new(MachineTerm::Variable(Variable(999982))),
                    initial: Box::new(MachineTerm::constant(0)),
                    accumulator: Variable(999983),
                    item: Variable(999984),
                    body: Box::new(MachineTerm::Variable(Variable(999983))),
                },
            ),
        );
        let root =
            crate::kernel::KernelTermImport::default().machine(MachineIntegerType::Int32, &native);
        let mut expected = BTreeSet::new();
        collect_bitvector_bound_variables(&native, &mut expected);
        let mut actual = BTreeSet::new();
        collect_scoped_leaf_bound_variables(MachineOperandView::Shared(&root), &mut actual);
        assert!(expected.contains(&Variable(999983)) && expected.contains(&Variable(999984)));
        assert_eq!(actual, expected);
    }
}
