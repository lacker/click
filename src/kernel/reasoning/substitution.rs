use super::*;
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
    fn bitvector(&self, term: &Bitvector32Term) -> Bitvector32Term;
    fn integer(&self, term: &IntegerTerm) -> IntegerTerm;
    fn pointer(&self, pointer: &Pointer) -> Pointer;
    /// The address of a local's storage slot.
    fn local_slot(&self, pointer: &Pointer) -> Pointer;
    fn term(&self, term: &Term) -> Term;
    fn condition(&self, condition: &ConditionTerm) -> ConditionTerm;
    fn c_value(&self, value: &CValue) -> CValue;
    fn c_expression(&self, expression: &CExpression) -> CExpression;
    fn memory(&self, memory: &CMemory) -> CMemory;
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
    to: &'a Bitvector32Term,
}

impl VariableSubstitution for BitvectorSubstitution<'_> {
    const SUBSTITUTES_CONDITION_EVIDENCE: bool = false;

    fn from(&self) -> Variable {
        self.from
    }
    fn bitvector(&self, term: &Bitvector32Term) -> Bitvector32Term {
        substitute_bitvector_variable(term, self.from, self.to)
    }
    fn integer(&self, term: &IntegerTerm) -> IntegerTerm {
        substitute_bitvector_variable_in_integer(term, self.from, self.to)
    }
    fn pointer(&self, pointer: &Pointer) -> Pointer {
        substitute_bitvector_variable_in_pointer(pointer, self.from, self.to)
    }
    fn local_slot(&self, pointer: &Pointer) -> Pointer {
        pointer.clone()
    }
    fn term(&self, term: &Term) -> Term {
        substitute_bitvector_variable_in_term(term, self.from, self.to)
    }
    fn condition(&self, condition: &ConditionTerm) -> ConditionTerm {
        substitute_bitvector_variable_in_condition(condition, self.from, self.to)
    }
    fn c_value(&self, value: &CValue) -> CValue {
        substitute_bitvector_variable_in_c_value(value, self.from, self.to)
    }
    fn c_expression(&self, expression: &CExpression) -> CExpression {
        substitute_bitvector_variable_in_c_expression(expression, self.from, self.to)
    }
    fn memory(&self, memory: &CMemory) -> CMemory {
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
        // Hold the snapshot memo open across the whole proposition, so two
        // sibling load terms over one snapshot rewrite it once between them.
        Some(SubstitutedMemoryScope::enter(self.from, self.to))
    }
}

struct PointerSubstitution<'a> {
    from: Variable,
    to: &'a Pointer,
}

impl VariableSubstitution for PointerSubstitution<'_> {
    const SUBSTITUTES_CONDITION_EVIDENCE: bool = true;

    fn from(&self) -> Variable {
        self.from
    }
    fn bitvector(&self, term: &Bitvector32Term) -> Bitvector32Term {
        term.clone()
    }
    fn integer(&self, term: &IntegerTerm) -> IntegerTerm {
        term.clone()
    }
    fn pointer(&self, pointer: &Pointer) -> Pointer {
        substitute_pointer_variable_in_pointer(pointer, self.from, self.to)
    }
    fn local_slot(&self, pointer: &Pointer) -> Pointer {
        self.pointer(pointer)
    }
    fn term(&self, term: &Term) -> Term {
        substitute_pointer_variable_in_term(term, self.from, self.to)
    }
    fn condition(&self, condition: &ConditionTerm) -> ConditionTerm {
        substitute_pointer_variable_in_condition(condition, self.from, self.to)
    }
    fn c_value(&self, value: &CValue) -> CValue {
        substitute_pointer_variable_in_c_value(value, self.from, self.to)
    }
    fn c_expression(&self, expression: &CExpression) -> CExpression {
        substitute_pointer_variable_in_c_expression(expression, self.from, self.to)
    }
    fn memory(&self, memory: &CMemory) -> CMemory {
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
    to: &Bitvector32Term,
) -> Proposition {
    walk_proposition(proposition, &BitvectorSubstitution { from, to })
}

fn substitute_bitvector_variable_in_algebraic_value(
    value: &AlgebraicValue,
    from: Variable,
    to: &Bitvector32Term,
) -> AlgebraicValue {
    walk_algebraic_value(value, &BitvectorSubstitution { from, to })
}

fn substitute_bitvector_variable_in_pure_function_argument(
    argument: &PureFunctionArgument,
    from: Variable,
    to: &Bitvector32Term,
) -> PureFunctionArgument {
    walk_pure_function_argument(argument, &BitvectorSubstitution { from, to })
}

fn substitute_bitvector_variable_in_sequence(
    sequence: &SequenceTerm,
    from: Variable,
    to: &Bitvector32Term,
) -> SequenceTerm {
    walk_sequence(sequence, &BitvectorSubstitution { from, to })
}

#[cfg(test)]
pub(in crate::kernel) fn substitute_bitvector_variable_in_c_statement(
    statement: &CStatement,
    from: Variable,
    to: &Bitvector32Term,
) -> CStatement {
    walk_c_statement(statement, &BitvectorSubstitution { from, to })
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_c_expression_outcome(
    outcome: &CExpressionOutcome,
    from: Variable,
    to: &Bitvector32Term,
) -> CExpressionOutcome {
    walk_c_expression_outcome(outcome, &BitvectorSubstitution { from, to })
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_c_statement_outcome(
    outcome: &CStatementOutcome,
    from: Variable,
    to: &Bitvector32Term,
) -> CStatementOutcome {
    walk_c_statement_outcome(outcome, &BitvectorSubstitution { from, to })
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_c_function_outcome(
    outcome: &CFunctionOutcome,
    from: Variable,
    to: &Bitvector32Term,
) -> CFunctionOutcome {
    walk_c_function_outcome(outcome, &BitvectorSubstitution { from, to })
}

fn substitute_bitvector_variable_in_c_state(
    state: &CState,
    from: Variable,
    to: &Bitvector32Term,
) -> CState {
    walk_c_state(state, &BitvectorSubstitution { from, to })
}

#[cfg(test)]
pub(in crate::kernel) fn substitute_bitvector_variable_in_c_resource(
    resource: &CResource,
    from: Variable,
    to: &Bitvector32Term,
) -> CResource {
    walk_c_resource(resource, &BitvectorSubstitution { from, to })
}

#[cfg(test)]
pub(in crate::kernel) fn substitute_bitvector_variable_in_c_function(
    function: &CFunction,
    from: Variable,
    to: &Bitvector32Term,
) -> CFunction {
    walk_c_function(function, &BitvectorSubstitution { from, to })
}

#[cfg(test)]
pub(in crate::kernel) fn substitute_bitvector_variable_in_resource_spec(
    resource: &CResourceSpec,
    from: Variable,
    to: &Bitvector32Term,
) -> CResourceSpec {
    walk_resource_spec(resource, &BitvectorSubstitution { from, to })
}

pub(crate) fn substitute_pointer_variable_in_proposition(
    proposition: &Proposition,
    from: Variable,
    to: &Pointer,
) -> Proposition {
    walk_proposition(proposition, &PointerSubstitution { from, to })
}

fn substitute_pointer_variable_in_algebraic_value(
    value: &AlgebraicValue,
    from: Variable,
    to: &Pointer,
) -> AlgebraicValue {
    walk_algebraic_value(value, &PointerSubstitution { from, to })
}

fn substitute_pointer_variable_in_pure_function_argument(
    argument: &PureFunctionArgument,
    from: Variable,
    to: &Pointer,
) -> PureFunctionArgument {
    walk_pure_function_argument(argument, &PointerSubstitution { from, to })
}

fn substitute_pointer_variable_in_sequence(
    sequence: &SequenceTerm,
    from: Variable,
    to: &Pointer,
) -> SequenceTerm {
    walk_sequence(sequence, &PointerSubstitution { from, to })
}

#[cfg(test)]
fn substitute_pointer_variable_in_c_statement(
    statement: &CStatement,
    from: Variable,
    to: &Pointer,
) -> CStatement {
    walk_c_statement(statement, &PointerSubstitution { from, to })
}

fn substitute_pointer_variable_in_c_expression_outcome(
    outcome: &CExpressionOutcome,
    from: Variable,
    to: &Pointer,
) -> CExpressionOutcome {
    walk_c_expression_outcome(outcome, &PointerSubstitution { from, to })
}

fn substitute_pointer_variable_in_c_statement_outcome(
    outcome: &CStatementOutcome,
    from: Variable,
    to: &Pointer,
) -> CStatementOutcome {
    walk_c_statement_outcome(outcome, &PointerSubstitution { from, to })
}

fn substitute_pointer_variable_in_c_function_outcome(
    outcome: &CFunctionOutcome,
    from: Variable,
    to: &Pointer,
) -> CFunctionOutcome {
    walk_c_function_outcome(outcome, &PointerSubstitution { from, to })
}

fn substitute_pointer_variable_in_c_state(state: &CState, from: Variable, to: &Pointer) -> CState {
    walk_c_state(state, &PointerSubstitution { from, to })
}

#[cfg(test)]
fn substitute_pointer_variable_in_c_resource(
    resource: &CResource,
    from: Variable,
    to: &Pointer,
) -> CResource {
    walk_c_resource(resource, &PointerSubstitution { from, to })
}

#[cfg(test)]
fn substitute_pointer_variable_in_c_function(
    function: &CFunction,
    from: Variable,
    to: &Pointer,
) -> CFunction {
    walk_c_function(function, &PointerSubstitution { from, to })
}

fn walk_algebraic_value<S: VariableSubstitution + ?Sized>(
    value: &AlgebraicValue,
    s: &S,
) -> AlgebraicValue {
    match value {
        AlgebraicValue::C(value) => AlgebraicValue::C(s.c_value(value)),
        AlgebraicValue::Integer(value) => AlgebraicValue::Integer(s.integer(value)),
        AlgebraicValue::Algebraic(value) => AlgebraicValue::Algebraic(s.algebraic_term(value)),
    }
}

fn walk_c_expression_outcome<S: VariableSubstitution + ?Sized>(
    outcome: &CExpressionOutcome,
    s: &S,
) -> CExpressionOutcome {
    match outcome {
        CExpressionOutcome::Value(value) => CExpressionOutcome::Value(s.c_value(value)),
        CExpressionOutcome::UndefinedBehavior(kind) => {
            CExpressionOutcome::UndefinedBehavior(kind.clone())
        }
        CExpressionOutcome::RuntimeError(kind) => CExpressionOutcome::RuntimeError(kind.clone()),
    }
}

fn walk_c_function<S: VariableSubstitution + ?Sized>(function: &CFunction, s: &S) -> CFunction {
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
        .map(|segment| walk_c_memory_segment(segment, s))
        .collect();
    // The declared measure is read at states like a `requires` is, so it is
    // rewritten with them; leaving it behind would make a substituted
    // interface rank the recursion by the pre-substitution names.
    interface.recursion_measure = interface
        .recursion_measure
        .as_ref()
        .map(|measure| walk_c_ranking_component(measure, s));
    interface.composite_resource_definitions = function
        .composite_resource_definitions()
        .iter()
        .map(|definition| CCompositeResourceDefinition {
            resource_parameters: definition
                .resource_parameters
                .iter()
                .map(|spec| walk_resource_spec(spec, s))
                .collect(),
            instance_schema: definition.instance_schema.clone(),
            thread_confined: definition.thread_confined,
            contains_mutex_authority: definition.contains_mutex_authority,
            authorized: definition.authorized,
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
            matched: definition.matched.as_ref().map(|body| CResourceMatchBody {
                field_index: body.field_index,
                algebraic_type: body.algebraic_type.clone(),
                arms: body
                    .arms
                    .iter()
                    .map(|arm| CResourceMatchArm {
                        children: arm
                            .children
                            .iter()
                            .map(|child| CResourceChildSpec {
                                name: child.name.clone(),
                                resource: child.resource.clone(),
                                binding: child.binding,
                                field_bindings: child.field_bindings.clone(),
                                arguments: child
                                    .arguments
                                    .iter()
                                    .map(|argument| s.c_expression(argument))
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
                .map(|child| CResourceChildSpec {
                    arguments: child
                        .arguments
                        .iter()
                        .map(|argument| s.c_expression(argument))
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
        .map(|unfolding| CPredicateUnfolding {
            predicate: s.spec_proposition(&unfolding.predicate),
            body: s.spec_proposition(&unfolding.body),
        })
        .collect();
    CFunction {
        program_entry: function.program_entry,
        name: function.name.clone(),
        inline_body: function.inline_body,
        body: walk_c_statement(function.body(), s),
        source_body: walk_c_statement(function.source_body(), s),
        control_targets: std::sync::Arc::new(
            function
                .control_targets
                .iter()
                .map(|(identity, target)| {
                    (
                        *identity,
                        CControlTarget {
                            statement_index: target.statement_index,
                            remaining: std::sync::Arc::new(walk_c_statement(&target.remaining, s)),
                        },
                    )
                })
                .collect(),
        ),
        contract_interface: interface,
        global_variables: function.global_variables.clone(),
        global_arrays: function.global_arrays.clone(),
        static_variables: function.static_variables.clone(),
        static_storage: function.static_storage.clone(),
        string_literals: function.string_literals.clone(),
    }
}

fn walk_c_function_outcome<S: VariableSubstitution + ?Sized>(
    outcome: &CFunctionOutcome,
    s: &S,
) -> CFunctionOutcome {
    match outcome {
        CFunctionOutcome::Return { value, state } => CFunctionOutcome::Return {
            value: s.c_value(value),
            state: Box::new(walk_c_state(state, s)),
        },
        CFunctionOutcome::Throw { value, state } => CFunctionOutcome::Throw {
            value: s.c_value(value),
            state: Box::new(walk_c_state(state, s)),
        },
        CFunctionOutcome::VerificationDiverges => CFunctionOutcome::VerificationDiverges,
        CFunctionOutcome::UndefinedBehavior(kind) => {
            CFunctionOutcome::UndefinedBehavior(kind.clone())
        }
        CFunctionOutcome::RuntimeError(kind) => CFunctionOutcome::RuntimeError(kind.clone()),
    }
}

fn walk_c_function_specification<S: VariableSubstitution + ?Sized>(
    specification: &CFunctionSpecification,
    s: &S,
) -> CFunctionSpecification {
    CFunctionSpecification {
        state: walk_c_state(specification.state(), s),
        arguments: specification
            .arguments()
            .iter()
            .map(|argument| s.c_expression(argument))
            .collect(),
        requires: specification
            .requires()
            .iter()
            .map(|requirement| walk_proposition(requirement, s))
            .collect(),
        outcome: walk_c_function_outcome(specification.outcome(), s),
    }
}

fn walk_c_memory_segment<S: VariableSubstitution + ?Sized>(
    segment: &CMemorySegment,
    s: &S,
) -> CMemorySegment {
    CMemorySegment {
        base: s.c_expression(&segment.base),
        start: s.c_expression(&segment.start),
        end: s.c_expression(&segment.end),
        element_width: segment.element_width,
        guard: segment
            .guard
            .as_ref()
            .map(|guard| s.spec_proposition(guard)),
    }
}

fn walk_c_ranking_component<S: VariableSubstitution + ?Sized>(
    measure: &CRankingComponent,
    s: &S,
) -> CRankingComponent {
    match measure {
        CRankingComponent::CExpression(expression) => {
            CRankingComponent::CExpression(s.c_expression(expression))
        }
        CRankingComponent::Pure { source, expression } => CRankingComponent::Pure {
            source: source.clone(),
            expression: s.spec_expression(expression),
        },
        CRankingComponent::PureInteger { source, expression } => CRankingComponent::PureInteger {
            source: source.clone(),
            expression: s.spec_integer(expression),
        },
    }
}

fn walk_c_resource<S: VariableSubstitution + ?Sized>(resource: &CResource, s: &S) -> CResource {
    match resource {
        CResource::PopulationAuthority(description) => CResource::PopulationAuthority(
            description.map_values(|value| walk_algebraic_value(value, s)),
        ),
        CResource::Publication(right) => CResource::Publication(PublicationRight {
            side: right.side,
            payload: right.payload.map_values(|v| walk_algebraic_value(v, s)),
            flag: s.pointer(&right.flag),
            observed: right.observed.as_ref().map(|value| s.c_value(value)),
        }),
        CResource::MutexUse(identity) => CResource::MutexUse(MutexUseIdentity {
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
        CResource::MutexGuard(identity) => CResource::MutexGuard(MutexIdentity {
            epoch: identity.epoch,
            mutex: if identity.epoch.is_none() {
                s.pointer(&identity.mutex)
            } else {
                identity.mutex.clone()
            },
        }),
        CResource::MutexLive(identity) => CResource::MutexLive(MutexIdentity {
            epoch: identity.epoch,
            mutex: if identity.epoch.is_none() {
                s.pointer(&identity.mutex)
            } else {
                identity.mutex.clone()
            },
        }),
        CResource::Instance(instance) => {
            let mut result = instance.clone();
            result.arguments = instance
                .arguments
                .iter()
                .map(|value| walk_algebraic_value(value, s))
                .collect();
            result.fields = instance
                .fields
                .iter()
                .map(|value| walk_algebraic_value(value, s))
                .collect();
            result.resource_arguments = crate::kernel::ResourceReference::map_captured_values(
                instance.resource_arguments(),
                |value| walk_algebraic_value(value, s),
            );
            CResource::Instance(result)
        }
        CResource::Memory(range) => CResource::Memory(walk_c_memory_range(range, s)),
        CResource::Iterated(iterated) => CResource::iterated(
            iterated.map_terms(|term| s.bitvector(term), |pointer| s.pointer(pointer)),
        ),
        CResource::Composite { name, arguments } => CResource::Composite {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| walk_algebraic_value(argument, s))
                .collect(),
        },
        CResource::Token { name, arguments } => CResource::Token {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| walk_algebraic_value(argument, s))
                .collect(),
        },
    }
}

fn walk_c_state<S: VariableSubstitution + ?Sized>(state: &CState, s: &S) -> CState {
    let bindings = std::sync::Arc::new(
        state
            .locals
            .bindings
            .iter()
            .map(|(name, binding)| {
                let binding = match binding {
                    CLocalBinding::Object {
                        storage_declared,
                        value,
                        c_type,
                        slot,
                        volatile,
                        pointee_volatile,
                        constant,
                        pointee_constant,
                    } => CLocalBinding::Object {
                        storage_declared: *storage_declared,
                        value: s.c_value(value),
                        c_type: *c_type,
                        slot: s.local_slot(slot),
                        volatile: *volatile,
                        pointee_volatile: *pointee_volatile,
                        constant: *constant,
                        pointee_constant: *pointee_constant,
                    },
                    CLocalBinding::UninitializedObject {
                        c_type,
                        slot,
                        volatile,
                        pointee_volatile,
                        constant,
                        pointee_constant,
                    } => CLocalBinding::UninitializedObject {
                        c_type: *c_type,
                        slot: s.local_slot(slot),
                        volatile: *volatile,
                        pointee_volatile: *pointee_volatile,
                        constant: *constant,
                        pointee_constant: *pointee_constant,
                    },
                    CLocalBinding::GlobalObject {
                        c_type,
                        slot,
                        volatile,
                        pointee_volatile,
                        constant,
                        pointee_constant,
                    } => CLocalBinding::GlobalObject {
                        c_type: *c_type,
                        slot: s.local_slot(slot),
                        volatile: *volatile,
                        pointee_volatile: *pointee_volatile,
                        constant: *constant,
                        pointee_constant: *pointee_constant,
                    },
                    CLocalBinding::ArrayObject {
                        element_type,
                        length,
                        slot,
                        constant,
                    } => CLocalBinding::ArrayObject {
                        element_type: *element_type,
                        length: *length,
                        slot: s.local_slot(slot),
                        constant: *constant,
                    },
                    CLocalBinding::AggregateObject {
                        layout,
                        slot,
                        constant,
                    } => CLocalBinding::AggregateObject {
                        layout: layout.clone(),
                        slot: s.local_slot(slot),
                        constant: *constant,
                    },
                };
                (name.clone(), binding)
            })
            .collect(),
    );
    let slots = std::sync::Arc::new(
        state
            .locals
            .slots
            .iter()
            .map(|(pointer, name)| (s.local_slot(pointer), name.clone()))
            .collect(),
    );
    CState {
        typed_access_policy: state.typed_access_policy,
        locals: CLocalEnvironment { bindings, slots },
        aggregate_destination: state.aggregate_destination.as_ref().map(|destination| {
            std::sync::Arc::new(CAggregateDestination {
                pointer: s.pointer(&destination.pointer),
                layout: destination.layout.clone(),
            })
        }),
        memory: s.memory(&state.memory),
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
                |value| s.c_value(value),
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

fn walk_c_statement<S: VariableSubstitution + ?Sized>(statement: &CStatement, s: &S) -> CStatement {
    match statement {
        CStatement::Scope { body } => CStatement::Scope {
            body: Box::new(walk_c_statement(body, s)),
        },
        CStatement::Skip
        | CStatement::EndAutomaticLifetimes { .. }
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Goto { .. }
        | CStatement::Declare {
            initializer: None, ..
        }
        | CStatement::DeclareAggregate { .. } => statement.clone(),
        CStatement::ForStep {
            step,
            exited_locals,
            continue_after,
        } => CStatement::ForStep {
            exited_locals: exited_locals.clone(),
            continue_after: *continue_after,
            step: Box::new(walk_c_statement(step, s)),
        },
        CStatement::Declare {
            initializer: Some(expression),
            ..
        } => {
            let mut statement = statement.clone();
            if let CStatement::Declare { initializer, .. } = &mut statement {
                *initializer = Some(s.c_expression(expression));
            }
            statement
        }
        CStatement::Assign { name, expression } => CStatement::Assign {
            name: name.clone(),
            expression: s.c_expression(expression),
        },
        CStatement::CallAssign {
            target,
            function_name,
            arguments,
        } => CStatement::CallAssign {
            target: target.clone(),
            function_name: function_name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| s.c_expression(argument))
                .collect(),
        },
        CStatement::Call {
            function_name,
            arguments,
        } => CStatement::Call {
            function_name: function_name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| s.c_expression(argument))
                .collect(),
        },
        CStatement::HeapAllocate {
            target,
            bytes,
            zeroed,
            allocated_scalar_type,
        } => CStatement::HeapAllocate {
            target: target.clone(),
            bytes: s.c_expression(bytes),
            zeroed: *zeroed,
            allocated_scalar_type: *allocated_scalar_type,
        },
        CStatement::HeapFree { pointer } => CStatement::HeapFree {
            pointer: s.c_expression(pointer),
        },
        CStatement::Assert { condition, label } => CStatement::Assert {
            condition: s.c_expression(condition),
            label: label.clone(),
        },
        CStatement::Seq(first, second) => {
            c_seq(walk_c_statement(first, s), walk_c_statement(second, s))
        }
        CStatement::Return(expression) => CStatement::Return(s.c_expression(expression)),
        CStatement::Throw(expression) => CStatement::Throw(s.c_expression(expression)),
        CStatement::TryCatchInt32 {
            try_body,
            binding,
            handler,
            cleanup_unwind,
        } => CStatement::TryCatchInt32 {
            try_body: Box::new(walk_c_statement(try_body, s)),
            binding: binding.clone(),
            handler: Box::new(walk_c_statement(handler, s)),
            cleanup_unwind: *cleanup_unwind,
        },
        CStatement::Store { pointer, value } => CStatement::Store {
            pointer: s.c_expression(pointer),
            value: s.c_expression(value),
        },
        CStatement::TypedStore {
            pointer,
            value,
            value_type,
            volatile,
            pointee_constant,
        } => CStatement::TypedStore {
            pointer: s.c_expression(pointer),
            value: s.c_expression(value),
            value_type: *value_type,
            volatile: *volatile,
            pointee_constant: *pointee_constant,
        },
        CStatement::CopyAggregate {
            target,
            source,
            layout,
        } => CStatement::CopyAggregate {
            target: s.c_expression(target),
            source: s.c_expression(source),
            layout: layout.clone(),
        },
        CStatement::InitializeScalarArray {
            target,
            source,
            element_type,
            count,
            copy,
            fresh,
        } => CStatement::InitializeScalarArray {
            target: s.c_expression(target),
            source: s.c_expression(source),
            element_type: *element_type,
            count: *count,
            copy: *copy,
            fresh: *fresh,
        },
        CStatement::Update {
            target,
            operator,
            operand,
        } => CStatement::Update {
            target: s.c_expression(target),
            operator: *operator,
            operand: s.c_expression(operand),
        },
        CStatement::If {
            condition,
            then_branch,
            else_branch,
        } => CStatement::If {
            condition: s.c_expression(condition),
            then_branch: Box::new(walk_c_statement(then_branch, s)),
            else_branch: Box::new(walk_c_statement(else_branch, s)),
        },
        CStatement::While {
            condition,
            invariant,
            invariant_checks,
            effect_checks,
            resource_specs,
            ranking_measures,
            structural_measure,
            body,
            do_while,
            backedge_target,
            natural_exit_target,
        } => CStatement::While {
            structural_measure: structural_measure.clone(),
            condition: s.c_expression(condition),
            ranking_measures: ranking_measures
                .iter()
                .map(|measure| walk_c_ranking_component(measure, s))
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
                .map(|check| CLoopInvariantCheck {
                    proposition: s.spec_proposition(check.proposition()),
                    entry_context: check.entry_context.clone(),
                    preservation_context: check.preservation_context.clone(),
                })
                .collect(),
            effect_checks: effect_checks
                .iter()
                .map(|check| CLoopEffectCheck {
                    effect: walk_loop_effect(check.effect(), s),
                    span: check.span,
                    context: check.context.clone(),
                    origin: check.origin,
                    validated_ranges: check.validated_ranges.as_ref().map(|ranges| {
                        ranges
                            .iter()
                            .map(|range| walk_c_memory_range(range, s))
                            .collect()
                    }),
                })
                .collect(),
            do_while: *do_while,
            backedge_target: *backedge_target,
            natural_exit_target: *natural_exit_target,
            body: Box::new(walk_c_statement(body, s)),
        },
        CStatement::Switch { expression, cases } => CStatement::Switch {
            expression: s.c_expression(expression),
            cases: cases
                .iter()
                .map(|case| CSwitchCase {
                    value: case.value,
                    body: Box::new(walk_c_statement(&case.body, s)),
                })
                .collect(),
        },
    }
}

fn walk_c_statement_outcome<S: VariableSubstitution + ?Sized>(
    outcome: &CStatementOutcome,
    s: &S,
) -> CStatementOutcome {
    match outcome {
        CStatementOutcome::Normal(state) => {
            CStatementOutcome::Normal(Box::new(walk_c_state(state, s)))
        }
        CStatementOutcome::Break(state) => {
            CStatementOutcome::Break(Box::new(walk_c_state(state, s)))
        }
        CStatementOutcome::Continue(state) => {
            CStatementOutcome::Continue(Box::new(walk_c_state(state, s)))
        }
        CStatementOutcome::Jump { target, state } => CStatementOutcome::Jump {
            target: *target,
            state: Box::new(walk_c_state(state, s)),
        },
        CStatementOutcome::Return { value, state } => CStatementOutcome::Return {
            value: s.c_value(value),
            state: Box::new(walk_c_state(state, s)),
        },
        CStatementOutcome::Throw { value, state } => CStatementOutcome::Throw {
            value: s.c_value(value),
            state: Box::new(walk_c_state(state, s)),
        },
        CStatementOutcome::VerificationDiverges => CStatementOutcome::VerificationDiverges,
        CStatementOutcome::UndefinedBehavior(kind) => {
            CStatementOutcome::UndefinedBehavior(kind.clone())
        }
        CStatementOutcome::RuntimeError(kind) => CStatementOutcome::RuntimeError(kind.clone()),
    }
}

fn walk_loop_effect<S: VariableSubstitution + ?Sized>(effect: &CLoopEffect, s: &S) -> CLoopEffect {
    match effect {
        CLoopEffect::Immutable => CLoopEffect::Immutable,
        CLoopEffect::Mutable(segments) => CLoopEffect::Mutable(
            segments
                .iter()
                .map(|segment| CMemorySegment {
                    base: s.c_expression(&segment.base),
                    start: s.c_expression(&segment.start),
                    end: s.c_expression(&segment.end),
                    element_width: segment.element_width,
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
        Proposition::Equal(left, right) => Proposition::Equal(s.term(left), s.term(right)),
        Proposition::ConditionIs(condition, value) => {
            Proposition::ConditionIs(s.condition(condition), *value)
        }
        Proposition::Predicate { name, arguments } => Proposition::Predicate {
            name: name.clone(),
            arguments: arguments.iter().map(|argument| s.term(argument)).collect(),
        },
        Proposition::CExpressionEvaluates {
            state,
            expression,
            outcome,
        } => Proposition::CExpressionEvaluates {
            state: Box::new(walk_c_state(state, s)),
            expression: s.c_expression(expression),
            outcome: walk_c_expression_outcome(outcome, s),
        },
        Proposition::CConditionEvaluates {
            state,
            condition,
            outcome,
        } if S::SUBSTITUTES_CONDITION_EVIDENCE => Proposition::CConditionEvaluates {
            state: Box::new(walk_c_state(state, s)),
            condition: s.c_expression(condition),
            outcome: outcome.clone(),
        },
        Proposition::CStatementExecutes {
            state,
            statement,
            outcome,
        }
        | Proposition::CStatementVerifies {
            state,
            statement,
            outcome,
        } => {
            let state = walk_c_state(state, s);
            let statement = walk_c_statement(statement, s);
            let outcome = walk_c_statement_outcome(outcome, s);
            match proposition {
                Proposition::CStatementExecutes { .. } => Proposition::CStatementExecutes {
                    state: Box::new(state),
                    statement: Box::new(statement),
                    outcome,
                },
                Proposition::CStatementVerifies { .. } => Proposition::CStatementVerifies {
                    state: Box::new(state),
                    statement: Box::new(statement),
                    outcome,
                },
                _ => unreachable!("the combined statement proposition arm is exhaustive"),
            }
        }
        Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome,
        }
        | Proposition::CFunctionVerifies {
            state,
            function,
            arguments,
            outcome,
        } => {
            let state = walk_c_state(state, s);
            let function = walk_c_function(function, s);
            let arguments = arguments
                .iter()
                .map(|argument| s.c_expression(argument))
                .collect();
            let outcome = walk_c_function_outcome(outcome, s);
            match proposition {
                Proposition::CFunctionExecutes { .. } => Proposition::CFunctionExecutes {
                    state: Box::new(state),
                    function: Box::new(function),
                    arguments,
                    outcome,
                },
                Proposition::CFunctionVerifies { .. } => Proposition::CFunctionVerifies {
                    state: Box::new(state),
                    function: Box::new(function),
                    arguments,
                    outcome,
                },
                _ => unreachable!("the combined function proposition arm is exhaustive"),
            }
        }
        Proposition::CFunctionSatisfiesSpecification {
            function,
            specification,
        } => Proposition::CFunctionSatisfiesSpecification {
            function: Box::new(walk_c_function(function, s)),
            specification: Box::new(walk_c_function_specification(specification, s)),
        },
        Proposition::CFunctionPartiallySatisfiesSpecification {
            function,
            specification,
        } => Proposition::CFunctionPartiallySatisfiesSpecification {
            function: Box::new(walk_c_function(function, s)),
            specification: Box::new(walk_c_function_specification(specification, s)),
        },
        Proposition::CMemoryLoads {
            memory,
            pointer,
            outcome,
        } => Proposition::CMemoryLoads {
            memory: s.memory(memory),
            pointer: s.pointer(pointer),
            outcome: walk_c_expression_outcome(outcome, s),
        },
        Proposition::CMemoryInitialized {
            memory,
            base,
            bytes,
        } => Proposition::CMemoryInitialized {
            memory: s.memory(memory),
            base: s.pointer(base),
            bytes: *bytes,
        },
        Proposition::CMemoryReadDefined {
            memory,
            pointer,
            value_type,
        } => Proposition::CMemoryReadDefined {
            memory: s.memory(memory),
            pointer: s.pointer(pointer),
            value_type: *value_type,
        },
        Proposition::CMemoryCanStore {
            memory,
            pointer,
            byte_width,
        } => Proposition::CMemoryCanStore {
            memory: s.memory(memory),
            pointer: s.pointer(pointer),
            byte_width: *byte_width,
        },
        Proposition::CMemoryLoadable {
            memory,
            base,
            bytes,
            wide,
        } => Proposition::CMemoryLoadable {
            memory: s.memory(memory),
            base: s.pointer(base),
            bytes: s.bitvector(bytes),
            wide: *wide,
        },
        Proposition::CResourceSeparate { left, right } => Proposition::CResourceSeparate {
            left: Box::new(walk_c_resource(left, s)),
            right: Box::new(walk_c_resource(right, s)),
        },
        Proposition::CResourceContains { parent, child } => Proposition::CResourceContains {
            parent: Box::new(walk_c_resource(parent, s)),
            child: Box::new(walk_c_resource(child, s)),
        },
        Proposition::CResourceComposition(resources) if S::SUBSTITUTES_CONDITION_EVIDENCE => {
            Proposition::CResourceComposition(walk_resource_context(resources, s))
        }
        Proposition::CMemoryMutatesOnly {
            before,
            after,
            writes,
        } => Proposition::CMemoryMutatesOnly {
            before: s.memory(before),
            after: s.memory(after),
            writes: writes
                .iter()
                .map(|(pointer, bytes)| (s.pointer(pointer), *bytes))
                .collect(),
        },
        Proposition::CMemoryEffectSummary {
            before,
            after,
            mutable_ranges,
        } => Proposition::CMemoryEffectSummary {
            before: s.memory(before),
            after: s.memory(after),
            mutable_ranges: mutable_ranges
                .iter()
                .map(|range| walk_c_memory_range(range, s))
                .collect(),
        },
        Proposition::CHeapAllocationFreed {
            before,
            after,
            allocation_base,
            bytes,
        } => Proposition::CHeapAllocationFreed {
            before: s.memory(before),
            after: s.memory(after),
            allocation_base: s.pointer(allocation_base),
            bytes: s.bitvector(bytes),
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
        Proposition::ForAll { var, sort, body } if *var != s.from() => {
            let (var, body) = s.quantifier_body(*var, sort, body);
            Proposition::ForAll {
                var,
                sort: sort.clone(),
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
        PureFunctionArgument::Value(value) => PureFunctionArgument::Value(s.c_value(value)),
        PureFunctionArgument::Algebraic(value) => {
            PureFunctionArgument::Algebraic(s.algebraic_term(value))
        }
        PureFunctionArgument::ArrayRef {
            memory,
            pointer,
            element_type,
        } => PureFunctionArgument::ArrayRef {
            memory: s.memory(memory),
            pointer: s.c_value(pointer),
            element_type: *element_type,
        },
    }
}

fn walk_resource<S: VariableSubstitution + ?Sized>(
    resource: &CResourceFact,
    s: &S,
) -> CResourceFact {
    match resource {
        CResourceFact::Own(resource, quantity) => CResourceFact::Own(
            walk_c_resource(resource, s),
            Box::new(s.bitvector(quantity)),
        ),
        CResourceFact::View(resource) => CResourceFact::View(walk_c_resource(resource, s)),
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
            .map(|resource| walk_resource(resource, s)),
    )
}

fn walk_resource_spec<S: VariableSubstitution + ?Sized>(
    resource: &CResourceSpec,
    s: &S,
) -> CResourceSpec {
    let substituted = CResourceSpec::new(
        walk_resource_term(resource.term(), s),
        resource.access(),
        match resource.quantity() {
            CResourceQuantity::One => CResourceQuantity::One,
            CResourceQuantity::Count(quantity) => {
                CResourceQuantity::Count(s.c_expression(quantity))
            }
        },
        resource.role(),
        resource.snapshot(),
    )
    .expect("pointer substitution preserves resource validity")
    .with_resource_arguments(resource.resource_arguments().to_vec())
    .with_native_record_places(
        resource
            .native_record_places()
            .iter()
            .map(|place| CNativeRecordPlaceRequirement {
                carrier: s.c_expression(&place.carrier),
                layout: place.layout.clone(),
                prefix_count: place
                    .prefix_count
                    .as_ref()
                    .map(|count| s.c_expression(count)),
            })
            .collect(),
    )
    .with_native_span_requirements(
        resource
            .native_span_requirements()
            .iter()
            .map(|span| CNativeSpanRequirement {
                access_policy: span.access_policy,
                carrier: s.c_expression(&span.carrier),
                element_type: span.element_type,
                count: s.c_expression(&span.count),
            })
            .collect(),
    );
    match resource.mutex_authority_binding() {
        Some((identity, binder)) => substituted
            .with_mutex_authority_binding(identity, binder.to_string())
            .expect("pointer substitution preserves mutex authority binding"),
        None => substituted,
    }
}

fn walk_resource_term<S: VariableSubstitution + ?Sized>(
    resource: &CResourceTerm,
    s: &S,
) -> CResourceTerm {
    match resource {
        CResourceTerm::Instance {
            identity,
            binder,
            schema,
            resource,
        } => CResourceTerm::Instance {
            identity: *identity,
            binder: binder.clone(),
            schema: schema.clone(),
            resource: Box::new(walk_resource_term(resource, s)),
        },
        CResourceTerm::PopulationAuthority {
            protected,
            population_arity,
            snapshot,
        } => CResourceTerm::PopulationAuthority {
            population_arity: *population_arity,
            protected: Box::new(CResourceTypeSpec {
                resource: Box::new(walk_resource_spec(&protected.resource, s)),
                schema: protected.schema.clone(),
            }),
            snapshot: *snapshot,
        },
        CResourceTerm::MutexGuard { mutex, snapshot } => CResourceTerm::MutexGuard {
            mutex: Box::new(s.c_expression(mutex)),
            snapshot: *snapshot,
        },
        CResourceTerm::MutexLive { mutex, snapshot } => CResourceTerm::MutexLive {
            mutex: Box::new(s.c_expression(mutex)),
            snapshot: *snapshot,
        },
        CResourceTerm::Publication {
            side,
            payload,
            flag,
            snapshot,
        } => CResourceTerm::Publication {
            side: *side,
            payload: Box::new(CResourceTypeSpec {
                resource: Box::new(walk_resource_spec(&payload.resource, s)),
                schema: payload.schema.clone(),
            }),
            flag: Box::new(s.c_expression(flag)),
            snapshot: *snapshot,
        },
        CResourceTerm::MutexUse {
            mutex,
            snapshot,
            protected,
        } => CResourceTerm::MutexUse {
            protected: protected.as_ref().map(|p| {
                Box::new(CResourceTypeSpec {
                    resource: Box::new(walk_resource_spec(&p.resource, s)),
                    schema: p.schema.clone(),
                })
            }),
            mutex: Box::new(s.c_expression(mutex)),
            snapshot: *snapshot,
        },
        CResourceTerm::Iterated(spec) => CResourceTerm::Iterated(Box::new(
            spec.map_expressions(|expression| s.c_expression(expression)),
        )),
        CResourceTerm::Memory(segment) => CResourceTerm::Memory(CMemorySegment {
            base: s.c_expression(&segment.base),
            start: s.c_expression(&segment.start),
            end: s.c_expression(&segment.end),
            element_width: segment.element_width,
            guard: segment
                .guard
                .as_ref()
                .map(|guard| s.spec_proposition(guard)),
        }),
        CResourceTerm::Composite {
            name,
            arguments,
            argument_snapshots,
            parameter_types,
        } => CResourceTerm::Composite {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| s.c_expression(argument))
                .collect(),
            argument_snapshots: argument_snapshots.clone(),
            parameter_types: parameter_types.clone(),
        },
        CResourceTerm::Token {
            name,
            arguments,
            argument_snapshots,
            parameter_types,
        } => CResourceTerm::Token {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| s.c_expression(argument))
                .collect(),
            argument_snapshots: argument_snapshots.clone(),
            parameter_types: parameter_types.clone(),
        },
    }
}

fn walk_sequence<S: VariableSubstitution + ?Sized>(sequence: &SequenceTerm, s: &S) -> SequenceTerm {
    let node = match sequence.node.as_ref() {
        SequenceTermNode::Literal(values) => SequenceTermNode::Literal(
            values
                .iter()
                .map(|value| s.c_value(value))
                .collect::<Vec<_>>()
                .into(),
        ),
        SequenceTermNode::Concat(left, right) => {
            SequenceTermNode::Concat(walk_sequence(left, s), walk_sequence(right, s))
        }
    };
    SequenceTerm {
        element_type: sequence.element_type,
        node: std::sync::Arc::new(node),
    }
}

fn walk_c_memory_range<S: VariableSubstitution + ?Sized>(
    range: &CMemoryRange,
    s: &S,
) -> CMemoryRange {
    range.with_bounds(
        s.pointer(&range.base),
        s.bitvector(range.bound_terms().0),
        s.bitvector(range.bound_terms().1),
    )
}

#[cfg(test)]
mod resource_frame_substitution_tests {
    use super::*;

    #[test]
    fn initialized_memory_substitution_rewrites_its_cell_and_preserves_pointer_carriers() {
        let source = Variable(71_890);
        let destination = Pointer::symbolic(Variable(71_891));
        let original = Pointer::symbolic(source);
        let stored = CPointerValue::new(original.clone(), CType::Int32Pointer)
            .with_designation(PointerDesignation::Unresolved(source));
        let claim = Proposition::CMemoryInitialized {
            memory: CMemory::new().store(original.clone(), CValue::Pointer(stored.clone())),
            base: original,
            bytes: 8,
        };
        let Proposition::CMemoryInitialized {
            memory,
            base,
            bytes,
        } = substitute_pointer_variable_in_proposition(&claim, source, &destination)
        else {
            panic!("the initialization claim must retain its form")
        };
        assert_eq!(base, destination);
        assert_eq!(bytes, 8);
        assert_eq!(
            memory.known_value(&base),
            Some(CValue::Pointer(stored.with_pointer(base)))
        );

        let original = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(source), 1),
        };
        let claim = Proposition::CMemoryInitialized {
            memory: CMemory::new()
                .store(original.clone(), int32(Bitvector32Term::Variable(source))),
            base: original,
            bytes: 4,
        };
        let Proposition::CMemoryInitialized {
            memory,
            base,
            bytes,
        } = substitute_bitvector_variable_in_proposition(
            &claim,
            source,
            &Bitvector32Term::Constant(2),
        )
        else {
            panic!("the initialization claim must retain its form")
        };
        assert_eq!(base.offset.as_const(), Some(2));
        assert_eq!(bytes, 4);
        assert_eq!(
            memory.known_value(&base),
            Some(int32(Bitvector32Term::Constant(2)))
        );
    }

    #[test]
    fn guard_substitution_renames_abstract_authority_but_preserves_concrete_acquisition() {
        let variable = Variable(71_900);
        let address = Pointer::symbolic(variable);
        let replacement = Pointer::symbolic(Variable(71_901));
        let abstract_guard = CResource::MutexGuard(MutexIdentity {
            epoch: None,
            mutex: address.clone(),
        });
        let concrete_guard = CResource::MutexGuard(MutexIdentity {
            epoch: Some(123),
            mutex: address,
        });
        assert_eq!(
            substitute_pointer_variable_in_c_resource(&abstract_guard, variable, &replacement),
            CResource::MutexGuard(MutexIdentity {
                epoch: None,
                mutex: replacement.clone()
            })
        );
        assert_eq!(
            substitute_pointer_variable_in_c_resource(&concrete_guard, variable, &replacement),
            concrete_guard
        );
    }

    #[test]
    fn lifetime_substitution_renames_abstract_authority_but_preserves_concrete_initialization() {
        let variable = Variable(71_900);
        let address = Pointer::symbolic(variable);
        let replacement = Pointer::symbolic(Variable(71_901));
        let abstract_guard = CResource::MutexLive(MutexIdentity {
            epoch: None,
            mutex: address.clone(),
        });
        let concrete_guard = CResource::MutexLive(MutexIdentity {
            epoch: Some(123),
            mutex: address,
        });
        assert_eq!(
            substitute_pointer_variable_in_c_resource(&abstract_guard, variable, &replacement),
            CResource::MutexLive(MutexIdentity {
                epoch: None,
                mutex: replacement.clone()
            })
        );
        assert_eq!(
            substitute_pointer_variable_in_c_resource(&concrete_guard, variable, &replacement),
            concrete_guard
        );
    }

    #[test]
    fn use_substitution_preserves_exact_share_and_diagnostic_address() {
        let variable = Variable(71_900);
        let address = Pointer {
            block: PointerBlock::Symbolic(variable),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(Bitvector32Term::Variable(variable)),
                byte_width: 1,
            },
        };
        let live = CResourceFact::own(CResource::MutexLive(MutexIdentity {
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
            substitute_pointer_variable_in_c_resource(
                resource,
                variable,
                &Pointer::symbolic(Variable(71_901))
            ),
            *resource
        );
        assert_eq!(
            substitute_bitvector_variable_in_c_resource(
                resource,
                variable,
                &Bitvector32Term::Constant(4)
            ),
            *resource
        );
    }

    #[test]
    fn unrelated_binder_preserves_nested_offset_snapshot() {
        let base = CMemory::new();
        let metadata = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Add(
                Box::new(PointerOffsetTerm::Add(
                    Box::new(PointerOffsetTerm::Int32Scaled {
                        value: Box::new(Bitvector32Term::Variable(Variable(100_000))),
                        byte_width: 4,
                    }),
                    Box::new(PointerOffsetTerm::Constant(8)),
                )),
                Box::new(PointerOffsetTerm::Constant(4)),
            ),
        };
        let snapshot = crate::kernel::intern_c_memory(
            base.store(metadata, CValue::Int32(Bitvector32Term::Constant(7))),
        );
        let rewritten = substitute_bitvector_variable_in_shared_memory(
            &snapshot,
            Variable(2_000_000),
            &Bitvector32Term::Variable(Variable(3_200_000)),
        );
        assert_eq!(rewritten.arena_id(), snapshot.arena_id());
    }

    #[test]
    fn state_substitutions_preserve_the_exact_loan_ledger_root() {
        let ledger = crate::kernel::loans::LoanLedger::new();
        let participant = ledger.fresh_participant().expect("participant identity");
        let state = CState::new()
            .with_local("x", int32(Bitvector32Term::Variable(Variable(71_100))))
            .with_loan_ledger(Some(ledger))
            .with_loan_participant(Some(participant));
        let bitvector_substituted = substitute_bitvector_variable_in_c_state(
            &state,
            Variable(71_100),
            &Bitvector32Term::Constant(4),
        );
        let pointer_substituted = substitute_pointer_variable_in_c_state(
            &state,
            Variable(71_100),
            &Pointer::symbolic(Variable(71_101)),
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

    fn inherited_check(range: CMemoryRange) -> CLoopEffectCheck {
        CLoopEffectCheck {
            effect: CLoopEffect::Mutable(Vec::new()),
            span: CLoopEffectSpan::Whole,
            context: None,
            origin: CLoopEffectOrigin::InheritedResourceDerived,
            validated_ranges: Some(vec![range]),
        }
    }

    #[test]
    fn bitvector_substitution_rewrites_validated_inherited_ranges() {
        let from = Variable(71_001);
        let range = CMemoryRange::new(
            Pointer {
                block: PointerBlock::Concrete("substitution:range".into()),
                offset: PointerOffsetTerm::Int32Scaled {
                    value: Box::new(Bitvector32Term::Variable(from)),
                    byte_width: 4,
                },
            },
            Bitvector32Term::Variable(from),
            Bitvector32Term::Add(
                Box::new(Bitvector32Term::Variable(from)),
                Box::new(Bitvector32Term::Constant(1)),
            ),
        );
        let statement = CStatement::While {
            condition: c_int32_literal(0),
            invariant: Vec::new(),
            invariant_checks: Vec::new(),
            effect_checks: vec![inherited_check(range)],
            resource_specs: Vec::new(),
            ranking_measures: Vec::new(),
            structural_measure: None,
            body: Box::new(CStatement::Skip),
            do_while: false,
            backedge_target: None,
            natural_exit_target: None,
        };
        let substituted = substitute_bitvector_variable_in_c_statement(
            &statement,
            from,
            &Bitvector32Term::Constant(4),
        );
        let CStatement::While { effect_checks, .. } = substituted else {
            panic!("substitution changed the statement shape");
        };
        let actual = effect_checks[0]
            .validated_ranges()
            .expect("validated carrier must be retained");
        assert_eq!(actual[0].start(), &Bitvector32Term::Constant(4));
        assert_eq!(actual[0].end(), &Bitvector32Term::Constant(5));
        assert_eq!(actual[0].base.offset, PointerOffsetTerm::Constant(16));
    }

    #[test]
    fn pointer_substitution_rewrites_validated_ranges_and_derived_interface() {
        let from = Variable(71_002);
        let replacement = Pointer {
            block: PointerBlock::Concrete("substitution:replacement".into()),
            offset: PointerOffsetTerm::Constant(2),
        };
        let range = CMemoryRange::new(
            Pointer {
                block: PointerBlock::Symbolic(from),
                offset: PointerOffsetTerm::Constant(0),
            },
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        );
        let statement = CStatement::While {
            condition: c_int32_literal(0),
            invariant: Vec::new(),
            invariant_checks: Vec::new(),
            effect_checks: vec![inherited_check(range)],
            resource_specs: Vec::new(),
            ranking_measures: Vec::new(),
            structural_measure: None,
            body: Box::new(CStatement::Skip),
            do_while: false,
            backedge_target: None,
            natural_exit_target: None,
        };
        let substituted =
            substitute_pointer_variable_in_c_statement(&statement, from, &replacement);
        let CStatement::While { effect_checks, .. } = substituted else {
            panic!("substitution changed the statement shape");
        };
        assert_eq!(
            effect_checks[0].validated_ranges().unwrap()[0].base.offset,
            replacement.offset
        );

        let derived_segment = CMemorySegment::new(
            CExpression::Value(CValue::pointer(Pointer {
                block: PointerBlock::Symbolic(from),
                offset: PointerOffsetTerm::Constant(0),
            })),
            CExpression::Value(int32(0)),
            CExpression::Value(int32(1)),
        );
        let function = CFunction::new(CType::Void, "substitution", Vec::new(), statement)
            .with_contract(
                Vec::new(),
                Vec::new(),
                vec![derived_segment],
                Vec::new(),
                true,
            )
            .with_resource_summary(Vec::new(), Vec::new())
            .with_resource_derived_mutable_frame();
        let substituted = substitute_pointer_variable_in_c_function(&function, from, &replacement);
        assert!(substituted.resource_derived_mutable_frame());
        assert_eq!(
            substituted.contract_mutable()[0].base,
            CExpression::Value(CValue::pointer(replacement))
        );
    }
}

/// Resolves load variables in a proposition through
/// defining-equation propositions (`v == load(snapshot, ptr)`), restoring
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

pub fn resolve_minted_load_variables(
    proposition: &Proposition,
    facts: &(impl ExecutionFactSource + ?Sized),
) -> Proposition {
    let mut resolved = proposition.clone();
    for fact in facts.fact_iter() {
        if !fact.certified {
            continue;
        }
        let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) =
            &fact.proposition
        else {
            continue;
        };
        let (Bitvector32Term::Variable(variable), load @ Bitvector32Term::MemoryLoad(_, _, _)) =
            (left.as_ref(), right.as_ref())
        else {
            continue;
        };
        resolved = substitute_bitvector_variable_in_proposition(&resolved, *variable, load);
    }
    resolved
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
        Proposition::Equal(left, right) => Proposition::Equal(
            rewritten_term(left, from, to),
            rewritten_term(right, from, to),
        ),
        Proposition::ConditionIs(condition, value) => {
            let leaf = Proposition::ConditionIs(condition.clone(), *value);
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
        Proposition::ForAll { var, sort, body } if *var != from => {
            let (var, body) = capture_avoiding_algebraic_quantifier_body(*var, body, from, to);
            Proposition::ForAll {
                var,
                sort: sort.clone(),
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
pub(in crate::kernel) fn substitute_bitvector_variables_in_proposition(
    proposition: &Proposition,
    substitutions: &BTreeMap<Variable, Bitvector32Term>,
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
            &Bitvector32Term::Variable(*temporary),
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
    replacement: &Bitvector32Term,
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
    let renamed = substitute_bitvector_variable_in_proposition(
        body,
        binder,
        &Bitvector32Term::Variable(fresh),
    );
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
        Proposition::Equal(left, right) => {
            collect_term_bound_variables(left, variables);
            collect_term_bound_variables(right, variables);
        }
        Proposition::ConditionIs(condition, _) => {
            collect_condition_bound_variables(condition, variables);
        }
        Proposition::Predicate { arguments, .. } => {
            for argument in arguments {
                collect_term_bound_variables(argument, variables);
            }
        }
        Proposition::CExpressionEvaluates {
            state,
            expression,
            outcome,
        } => {
            collect_c_state_bound_variables(state, variables);
            collect_c_expression_bound_variables(expression, variables);
            collect_expression_outcome_bound_variables(outcome, variables);
        }
        Proposition::CConditionEvaluates {
            state, condition, ..
        } => {
            collect_c_state_bound_variables(state, variables);
            collect_c_expression_bound_variables(condition, variables);
        }
        Proposition::CStatementExecutes {
            state,
            statement,
            outcome,
        }
        | Proposition::CStatementVerifies {
            state,
            statement,
            outcome,
        } => {
            collect_c_state_bound_variables(state, variables);
            collect_c_statement_bound_variables(statement, variables);
            collect_statement_outcome_bound_variables(outcome, variables);
        }
        Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome,
        }
        | Proposition::CFunctionVerifies {
            state,
            function,
            arguments,
            outcome,
        } => {
            collect_c_state_bound_variables(state, variables);
            collect_c_function_bound_variables(function, variables);
            for argument in arguments {
                collect_c_expression_bound_variables(argument, variables);
            }
            collect_function_outcome_bound_variables(outcome, variables);
        }
        Proposition::CFunctionSatisfiesSpecification {
            function,
            specification,
        }
        | Proposition::CFunctionPartiallySatisfiesSpecification {
            function,
            specification,
        } => {
            collect_c_function_bound_variables(function, variables);
            collect_c_function_specification_bound_variables(specification, variables);
        }
        Proposition::CMemoryLoads {
            memory,
            pointer,
            outcome,
        } => {
            collect_memory_bound_variables(memory, variables);
            collect_pointer_bound_variables(pointer, variables);
            collect_expression_outcome_bound_variables(outcome, variables);
        }
        Proposition::CMemoryInitialized {
            memory,
            base: pointer,
            ..
        }
        | Proposition::CMemoryReadDefined {
            memory, pointer, ..
        }
        | Proposition::CMemoryCanStore {
            memory, pointer, ..
        } => {
            collect_memory_bound_variables(memory, variables);
            collect_pointer_bound_variables(pointer, variables);
        }
        Proposition::CMemoryLoadable {
            memory,
            base,
            bytes,
            wide: _,
        } => {
            collect_memory_bound_variables(memory, variables);
            collect_pointer_bound_variables(base, variables);
            collect_bitvector_bound_variables(bytes, variables);
        }
        Proposition::CResourceSeparate { left, right }
        | Proposition::CResourceContains {
            parent: left,
            child: right,
        } => {
            collect_resource_bound_variables(left, variables);
            collect_resource_bound_variables(right, variables);
        }
        Proposition::CResourceComposition(resources) => {
            for fact in resources.facts() {
                collect_resource_bound_variables(fact.resource(), variables);
            }
        }
        Proposition::CMemoryMutatesOnly {
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
        Proposition::CMemoryEffectSummary {
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
        Proposition::CHeapAllocationFreed {
            before,
            after,
            allocation_base,
            bytes,
        } => {
            collect_memory_bound_variables(before, variables);
            collect_memory_bound_variables(after, variables);
            collect_pointer_bound_variables(allocation_base, variables);
            collect_bitvector_bound_variables(bytes, variables);
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
        Term::CValue(value) => collect_c_value_bound_variables(value, variables),
        Term::Sequence(sequence) => collect_sequence_bound_variables(sequence, variables),
        Term::Algebraic(term) => collect_algebraic_bound_variables(term, variables),
        Term::CExpressionOutcome(outcome) => {
            collect_expression_outcome_bound_variables(outcome, variables)
        }
        Term::CStatementOutcome(outcome) => {
            collect_statement_outcome_bound_variables(outcome, variables)
        }
        Term::CFunctionOutcome(outcome) => {
            collect_function_outcome_bound_variables(outcome, variables)
        }
        Term::CState(state) => collect_c_state_bound_variables(state, variables),
        Term::CMemory(memory) => collect_memory_bound_variables(memory, variables),
    }
}

fn collect_sequence_bound_variables(sequence: &SequenceTerm, variables: &mut BTreeSet<Variable>) {
    match sequence.node.as_ref() {
        SequenceTermNode::Literal(values) => {
            for value in values.iter() {
                collect_c_value_bound_variables(value, variables);
            }
        }
        SequenceTermNode::Concat(left, right) => {
            collect_sequence_bound_variables(left, variables);
            collect_sequence_bound_variables(right, variables);
        }
    }
}

fn collect_c_value_bound_variables(value: &CValue, variables: &mut BTreeSet<Variable>) {
    match value {
        CValue::PointerInteger(value) => {
            collect_bitvector_bound_variables(value.bits(), variables);
            collect_c_value_bound_variables(&CValue::Pointer(value.origin().clone()), variables);
        }
        CValue::Int8(bits) => collect_bitvector_bound_variables(bits, variables),
        CValue::Bool(bits)
        | CValue::Int16(bits)
        | CValue::Int32(bits)
        | CValue::UInt8(bits)
        | CValue::UInt16(bits)
        | CValue::UInt32(bits)
        | CValue::Int64(bits)
        | CValue::UInt64(bits)
        | CValue::Int128(bits)
        | CValue::UInt128(bits)
        | CValue::Float32(bits)
        | CValue::Float64(bits) => collect_bitvector_bound_variables(bits, variables),
        CValue::Pointer(pointer) => {
            collect_pointer_bound_variables(pointer.pointer(), variables);
            if let Some(designation) = pointer.designation() {
                if let Some(identity) = designation.loaded_identity() {
                    collect_memory_bitvector_variables(identity.memory(), variables);
                }
                if let Some(variable) = designation.unresolved_variable() {
                    variables.insert(variable);
                }
                for term in designation.pointer_terms() {
                    collect_pointer_bound_variables(term, variables);
                }
                for term in designation.integer_terms() {
                    collect_integer_bound_variables(term.as_ref(), variables);
                    crate::kernel::prelude::collect_integer_capture_bitvector_variables(
                        term.as_ref(),
                        variables,
                    );
                }
            }
        }
        CValue::Void => {}
    }
}

fn collect_algebraic_value_bound_variables(
    value: &AlgebraicValue,
    variables: &mut BTreeSet<Variable>,
) {
    match value {
        AlgebraicValue::C(value) => collect_c_value_bound_variables(value, variables),
        AlgebraicValue::Integer(value) => collect_integer_bound_variables(value, variables),
        AlgebraicValue::Algebraic(value) => collect_algebraic_bound_variables(value, variables),
    }
}

fn collect_c_expression_bound_variables(
    expression: &CExpression,
    variables: &mut BTreeSet<Variable>,
) {
    match expression {
        CExpression::Value(value) => collect_c_value_bound_variables(value, variables),
        CExpression::Variable(_) | CExpression::FunctionAddress(_) => {}
        CExpression::Cast { expression, .. } => {
            collect_c_expression_bound_variables(expression, variables);
        }
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_c_expression_bound_variables(condition, variables);
            collect_c_expression_bound_variables(then_branch, variables);
            collect_c_expression_bound_variables(else_branch, variables);
        }
        CExpression::FloatNegate(expression)
        | CExpression::FloatClassification { expression, .. } => {
            collect_c_expression_bound_variables(expression, variables);
        }
        CExpression::MemberAddress { object: body, .. }
        | CExpression::AddressOf(body)
        | CExpression::CheckedObjectAddress(body)
        | CExpression::Not(body)
        | CExpression::Load(body)
        | CExpression::BitwiseNot(body) => collect_c_expression_bound_variables(body, variables),
        CExpression::PointerOffsetBytes { pointer, .. }
        | CExpression::PointerAligned { pointer, .. }
        | CExpression::TypedLoad { pointer, .. } => {
            collect_c_expression_bound_variables(pointer, variables)
        }
        crate::kernel::binary_c_expression!(left, right) => {
            collect_c_expression_bound_variables(left, variables);
            collect_c_expression_bound_variables(right, variables);
        }
    }
}

pub(in crate::kernel) fn collect_c_statement_bound_variables(
    statement: &CStatement,
    variables: &mut BTreeSet<Variable>,
) {
    match statement {
        CStatement::Skip
        | CStatement::EndAutomaticLifetimes { .. }
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Goto { .. }
        | CStatement::Declare {
            initializer: None, ..
        }
        | CStatement::DeclareAggregate { .. } => {}
        CStatement::ForStep { step, .. } | CStatement::Scope { body: step } => {
            collect_c_statement_bound_variables(step, variables);
        }
        CStatement::Declare {
            initializer: Some(expression),
            ..
        }
        | CStatement::Assign { expression, .. }
        | CStatement::Return(expression)
        | CStatement::Throw(expression)
        | CStatement::Assert {
            condition: expression,
            ..
        } => collect_c_expression_bound_variables(expression, variables),
        CStatement::CallAssign { arguments, .. } | CStatement::Call { arguments, .. } => {
            for argument in arguments {
                collect_c_expression_bound_variables(argument, variables);
            }
        }
        CStatement::HeapAllocate { bytes, .. } => {
            collect_c_expression_bound_variables(bytes, variables)
        }
        CStatement::HeapFree { pointer } => {
            collect_c_expression_bound_variables(pointer, variables)
        }
        CStatement::Seq(first, second) => {
            collect_c_statement_bound_variables(first, variables);
            collect_c_statement_bound_variables(second, variables);
        }
        CStatement::TryCatchInt32 {
            try_body, handler, ..
        } => {
            collect_c_statement_bound_variables(try_body, variables);
            collect_c_statement_bound_variables(handler, variables);
        }
        CStatement::Store { pointer, value } | CStatement::TypedStore { pointer, value, .. } => {
            collect_c_expression_bound_variables(pointer, variables);
            collect_c_expression_bound_variables(value, variables);
        }
        CStatement::CopyAggregate { target, source, .. }
        | CStatement::InitializeScalarArray { target, source, .. } => {
            collect_c_expression_bound_variables(target, variables);
            collect_c_expression_bound_variables(source, variables);
        }
        CStatement::Update {
            target, operand, ..
        } => {
            collect_c_expression_bound_variables(target, variables);
            collect_c_expression_bound_variables(operand, variables);
        }
        CStatement::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_c_expression_bound_variables(condition, variables);
            collect_c_statement_bound_variables(then_branch, variables);
            collect_c_statement_bound_variables(else_branch, variables);
        }
        CStatement::While {
            condition,
            invariant,
            invariant_checks,
            effect_checks,
            body,
            ..
        } => {
            collect_c_expression_bound_variables(condition, variables);
            for proposition in invariant {
                collect_proposition_bound_variables(proposition, variables);
            }
            for check in invariant_checks {
                collect_spec_proposition_bound_variables(check.proposition(), variables);
            }
            for check in effect_checks {
                collect_loop_effect_bound_variables(check.effect(), variables);
            }
            collect_c_statement_bound_variables(body, variables);
        }
        CStatement::Switch { expression, cases } => {
            collect_c_expression_bound_variables(expression, variables);
            for case in cases {
                collect_c_statement_bound_variables(&case.body, variables);
            }
        }
    }
}

fn collect_loop_effect_bound_variables(effect: &CLoopEffect, variables: &mut BTreeSet<Variable>) {
    if let CLoopEffect::Mutable(segments) = effect {
        for segment in segments {
            collect_c_memory_segment_bound_variables(segment, variables);
        }
    }
}

fn collect_c_memory_segment_bound_variables(
    segment: &CMemorySegment,
    variables: &mut BTreeSet<Variable>,
) {
    collect_c_expression_bound_variables(&segment.base, variables);
    collect_c_expression_bound_variables(&segment.start, variables);
    collect_c_expression_bound_variables(&segment.end, variables);
    if let Some(guard) = segment.guard() {
        collect_spec_proposition_bound_variables(guard, variables);
    }
}

pub(in crate::kernel) fn collect_c_state_bound_variables(
    state: &CState,
    variables: &mut BTreeSet<Variable>,
) {
    if let Some(destination) = &state.aggregate_destination {
        collect_pointer_bound_variables(&destination.pointer, variables);
    }
    for binding in state.locals.bindings.values() {
        if let CLocalBinding::Object { value, .. } = binding {
            collect_c_value_bound_variables(value, variables);
        }
    }
    collect_memory_bound_variables(&state.memory, variables);
    for fact in state.resources.facts() {
        collect_resource_bound_variables(fact.resource(), variables);
    }
}

pub(in crate::kernel) fn collect_statement_outcome_bound_variables(
    outcome: &CStatementOutcome,
    variables: &mut BTreeSet<Variable>,
) {
    match outcome {
        CStatementOutcome::Normal(state)
        | CStatementOutcome::Break(state)
        | CStatementOutcome::Continue(state)
        | CStatementOutcome::Jump { state, .. } => {
            collect_c_state_bound_variables(state, variables)
        }
        CStatementOutcome::Return { value, state } | CStatementOutcome::Throw { value, state } => {
            collect_c_value_bound_variables(value, variables);
            collect_c_state_bound_variables(state, variables);
        }
        CStatementOutcome::VerificationDiverges
        | CStatementOutcome::UndefinedBehavior(_)
        | CStatementOutcome::RuntimeError(_) => {}
    }
}

fn collect_function_outcome_bound_variables(
    outcome: &CFunctionOutcome,
    variables: &mut BTreeSet<Variable>,
) {
    match outcome {
        CFunctionOutcome::Return { value, state } | CFunctionOutcome::Throw { value, state } => {
            collect_c_value_bound_variables(value, variables);
            collect_c_state_bound_variables(state, variables);
        }
        CFunctionOutcome::VerificationDiverges
        | CFunctionOutcome::UndefinedBehavior(_)
        | CFunctionOutcome::RuntimeError(_) => {}
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

fn collect_c_resource_spec_bound_variables(
    resource: &CResourceSpec,
    variables: &mut BTreeSet<Variable>,
) {
    for place in resource.native_record_places() {
        collect_c_expression_bound_variables(&place.carrier, variables);
        if let Some(count) = &place.prefix_count {
            collect_c_expression_bound_variables(count, variables);
        }
    }
    for span in resource.native_span_requirements() {
        collect_c_expression_bound_variables(&span.carrier, variables);
        collect_c_expression_bound_variables(&span.count, variables);
    }
    match resource.term() {
        CResourceTerm::Instance { resource, .. } => {
            collect_c_resource_term_bound_variables(resource, variables)
        }
        CResourceTerm::PopulationAuthority { protected, .. } => {
            collect_c_resource_spec_bound_variables(&protected.resource, variables)
        }
        CResourceTerm::MutexGuard { mutex, .. } | CResourceTerm::MutexLive { mutex, .. } => {
            collect_c_expression_bound_variables(mutex, variables)
        }
        CResourceTerm::MutexUse {
            mutex, protected, ..
        } => {
            collect_c_expression_bound_variables(mutex, variables);
            if let Some(protected) = protected {
                collect_c_resource_spec_bound_variables(&protected.resource, variables);
            }
        }
        CResourceTerm::Publication { flag, payload, .. } => {
            collect_c_expression_bound_variables(flag, variables);
            collect_c_resource_spec_bound_variables(&payload.resource, variables);
        }
        CResourceTerm::Memory(segment) => {
            collect_c_memory_segment_bound_variables(segment, variables)
        }
        CResourceTerm::Composite { arguments, .. } | CResourceTerm::Token { arguments, .. } => {
            for argument in arguments {
                collect_c_expression_bound_variables(argument, variables);
            }
        }
        CResourceTerm::Iterated(spec) => {
            for expression in spec.expressions() {
                collect_c_expression_bound_variables(expression, variables);
            }
        }
    }
    if let CResourceQuantity::Count(quantity) = resource.quantity() {
        collect_c_expression_bound_variables(quantity, variables);
    }
}

fn collect_c_resource_term_bound_variables(
    resource: &CResourceTerm,
    variables: &mut BTreeSet<Variable>,
) {
    match resource {
        CResourceTerm::Instance { resource, .. } => {
            collect_c_resource_term_bound_variables(resource, variables)
        }
        CResourceTerm::PopulationAuthority { protected, .. } => {
            collect_c_resource_spec_bound_variables(&protected.resource, variables)
        }
        CResourceTerm::MutexGuard { mutex, .. } | CResourceTerm::MutexLive { mutex, .. } => {
            collect_c_expression_bound_variables(mutex, variables)
        }
        CResourceTerm::MutexUse {
            mutex, protected, ..
        } => {
            collect_c_expression_bound_variables(mutex, variables);
            if let Some(protected) = protected {
                collect_c_resource_spec_bound_variables(&protected.resource, variables);
            }
        }
        CResourceTerm::Publication { flag, payload, .. } => {
            collect_c_expression_bound_variables(flag, variables);
            collect_c_resource_spec_bound_variables(&payload.resource, variables);
        }
        CResourceTerm::Memory(segment) => {
            collect_c_memory_segment_bound_variables(segment, variables)
        }
        CResourceTerm::Composite { arguments, .. } | CResourceTerm::Token { arguments, .. } => {
            for argument in arguments {
                collect_c_expression_bound_variables(argument, variables);
            }
        }
        CResourceTerm::Iterated(spec) => {
            for expression in spec.expressions() {
                collect_c_expression_bound_variables(expression, variables);
            }
        }
    }
}

pub(in crate::kernel) fn collect_c_function_bound_variables(
    function: &CFunction,
    variables: &mut BTreeSet<Variable>,
) {
    collect_c_function_contract_interface_bound_variables(function.contract_interface(), variables);
    collect_c_statement_bound_variables(function.body(), variables);
}

/// Collects only bound variables in the body-independent contract interface.
/// This is the companion to the bitvector collector used for named callback
/// contracts; no template statement or storage is traversed.
pub(in crate::kernel) fn collect_c_function_contract_interface_bound_variables(
    interface: &CFunctionContractInterface,
    variables: &mut BTreeSet<Variable>,
) {
    for resource in interface
        .proof_parameters()
        .iter()
        .chain(interface.resource_requires())
        .chain(interface.resource_ensures())
        .chain(interface.resource_constructors())
    {
        collect_c_resource_spec_bound_variables(resource, variables);
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
        collect_c_memory_segment_bound_variables(segment, variables);
    }
}

fn collect_c_function_specification_bound_variables(
    specification: &CFunctionSpecification,
    variables: &mut BTreeSet<Variable>,
) {
    collect_c_state_bound_variables(specification.state(), variables);
    for argument in specification.arguments() {
        collect_c_expression_bound_variables(argument, variables);
    }
    for requirement in specification.requires() {
        collect_proposition_bound_variables(requirement, variables);
    }
    collect_function_outcome_bound_variables(specification.outcome(), variables);
}

fn collect_expression_outcome_bound_variables(
    outcome: &CExpressionOutcome,
    variables: &mut BTreeSet<Variable>,
) {
    if let CExpressionOutcome::Value(value) = outcome {
        collect_c_value_bound_variables(value, variables);
    }
}

fn collect_pointer_bound_variables(pointer: &Pointer, variables: &mut BTreeSet<Variable>) {
    match &pointer.block {
        PointerBlock::PureFunctionApplication(_) => {
            collect_proposition_capture_variables(
                &Proposition::ConditionIs(
                    ConditionTerm::PointerEqual(
                        Box::new(pointer.clone()),
                        Box::new(pointer.clone()),
                    ),
                    true,
                ),
                variables,
            );
        }
        PointerBlock::FunctionSymbolic(variable)
        | PointerBlock::Symbolic(variable)
        | PointerBlock::ExternalObject(variable) => {
            variables.insert(*variable);
        }
        PointerBlock::Concrete(_)
        | PointerBlock::StringLiteral { .. }
        | PointerBlock::Function(_)
        | PointerBlock::ExternalArgument
        | PointerBlock::LoadedPointer(_)
        | PointerBlock::Heap(_)
        | PointerBlock::Temporary(_) => {}
    }
    collect_pointer_offset_bound_variables(&pointer.offset, variables);
}

thread_local! {
    static SHARED_MEMORY_BOUND_VARIABLES: std::cell::RefCell<std::collections::HashMap<SharedCMemory, std::sync::Arc<BTreeSet<Variable>>>> = std::cell::RefCell::new(std::collections::HashMap::new());
}

pub(in crate::kernel) fn clear_shared_memory_bound_variables() {
    SHARED_MEMORY_BOUND_VARIABLES.with(|cache| cache.borrow_mut().clear());
}

fn collect_shared_memory_bound_variables(
    memory: &SharedCMemory,
    variables: &mut BTreeSet<Variable>,
) {
    if let Some(known) =
        SHARED_MEMORY_BOUND_VARIABLES.with(|cache| cache.borrow().get(memory).cloned())
    {
        variables.extend(known.iter().copied());
        return;
    }
    let mut dependencies = BTreeSet::new();
    collect_memory_bound_variables(memory.memory(), &mut dependencies);
    variables.extend(dependencies.iter().copied());
    SHARED_MEMORY_BOUND_VARIABLES.with(|cache| {
        cache
            .borrow_mut()
            .insert(memory.clone(), std::sync::Arc::new(dependencies));
    });
}

fn collect_memory_bound_variables(memory: &CMemory, variables: &mut BTreeSet<Variable>) {
    for row in memory.heap.native_record_inputs.values() {
        collect_c_value_bound_variables(&CValue::Pointer(row.origin.clone()), variables);
        if let CNativeInputKind::TypedSlice { count, .. }
        | CNativeInputKind::TypedPrefix { count, .. }
        | CNativeInputKind::RecordPrefix { count, .. }
        | CNativeInputKind::AllocatedScalar { bytes: count, .. } = &row.kind
        {
            collect_integer_bound_variables(count.as_ref(), variables);
            collect_integer_capture_bitvector_variables(count.as_ref(), variables);
        }
    }
    for (base, pending) in memory.heap.pending_reallocations.iter() {
        crate::instrumentation::record_deterministic_work(pending.copied_cells.len());
        collect_pointer_bound_variables(base, variables);
        collect_c_value_bound_variables(&CValue::Pointer(pending.old_pointer.clone()), variables);
        collect_bitvector_bound_variables(&pending.old_bytes, variables);
        if let Some(prefix) = &pending.zeroed_prefix {
            collect_bitvector_bound_variables(prefix, variables);
        }
        for (offset, value) in &pending.copied_cells {
            collect_pointer_offset_bound_variables(offset, variables);
            collect_c_value_bound_variables(value, variables);
        }
    }
    for pointer in memory
        .heap
        .uninitialized_objects
        .keys()
        .chain(memory.heap.initialized.as_map().keys())
        .chain(memory.heap.object_input_domains.keys())
        .chain(memory.heap.scalar_input_domains.keys())
    {
        collect_pointer_bound_variables(pointer, variables);
    }
    for contents in memory.blocks.values() {
        collect_bitvector_bound_variables(contents.size(), variables);
    }
    for (pointer, value) in memory.cells.concrete().iter() {
        collect_pointer_bound_variables(pointer, variables);
        collect_c_value_bound_variables(value, variables);
    }
    // Bound identities come from the represented value/source and address,
    // never from a slot's reserved load ID. Keep the bound collector separate
    // from free-variable collection and inspect each retained source once.
    for run in memory.cells.runs() {
        crate::instrumentation::record_deterministic_work(1);
        collect_pointer_bound_variables(run.base(), variables);
        match run.value_mode() {
            crate::kernel::primitives::RunValueMode::Constant(value) => {
                collect_c_value_bound_variables(value, variables)
            }
            crate::kernel::primitives::RunValueMode::Copy { source_base } => {
                collect_pointer_bound_variables(source_base, variables);
                collect_shared_memory_bound_variables(run.source(), variables);
            }
            crate::kernel::primitives::RunValueMode::Load
            | crate::kernel::primitives::RunValueMode::SymbolicStorage => {
                collect_shared_memory_bound_variables(run.source(), variables);
            }
        }
    }
}

#[cfg(test)]
mod compressed_bound_run_tests {
    use super::*;

    #[test]
    fn compressed_load_run_keeps_fold_binders_separate_from_free_value_variables() {
        let mut samples = Vec::new();
        for count in [8, 1024, 1_000_000] {
            let _session = crate::kernel::VerificationSession::enter();
            let free = Variable(9_381_021);
            let accumulator = Variable(9_381_022);
            let item = Variable(9_381_023);
            let source = CMemory::new().store(
                Pointer::symbolic(Variable(9_381_024)),
                CValue::UInt32(Bitvector32Term::RangeFold {
                    start: Box::new(Bitvector32Term::Constant(0)),
                    end: Box::new(Bitvector32Term::Constant(3)),
                    initial: Box::new(Bitvector32Term::Variable(free)),
                    accumulator,
                    item,
                    body: Box::new(Bitvector32Term::Variable(accumulator)),
                }),
            );
            let memory = CMemory::new().with_proof_entry_cells(
                Pointer::symbolic(Variable(9_381_025)),
                4,
                CType::UInt32,
                0,
                count,
                crate::kernel::intern_c_memory(source),
            );
            let (bound, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut variables = BTreeSet::new();
                collect_memory_bound_variables(&memory, &mut variables);
                variables
            });
            assert!(bound.contains(&accumulator));
            assert!(bound.contains(&item));
            assert!(!bound.contains(&free));
            samples.push(work);
        }
        assert!(
            samples.iter().all(|work| *work == samples[0]),
            "{samples:?}"
        );
    }
}

fn collect_resource_bound_variables(resource: &CResource, variables: &mut BTreeSet<Variable>) {
    match resource {
        CResource::PopulationAuthority(description) => {
            description
                .visit_values(|value| collect_algebraic_value_bound_variables(value, variables));
        }
        CResource::MutexUse(identity) => {
            if let Some(p) = &identity.protected {
                p.visit_values(|v| collect_algebraic_value_bound_variables(v, variables));
            }
            if identity.binding.is_none() {
                collect_pointer_bound_variables(&identity.mutex, variables);
            }
        }
        CResource::MutexGuard(identity) | CResource::MutexLive(identity) => {
            if identity.epoch.is_none() {
                let pointer = &identity.mutex;
                collect_pointer_bound_variables(pointer, variables);
            }
        }
        CResource::Publication(right) => {
            right
                .payload
                .visit_values(|v| collect_algebraic_value_bound_variables(v, variables));
            collect_pointer_bound_variables(&right.flag, variables);
            if let Some(value) = &right.observed {
                collect_c_value_bound_variables(value, variables);
            }
        }
        CResource::Instance(instance) => {
            for value in instance.arguments.iter().chain(instance.fields.iter()) {
                collect_algebraic_value_bound_variables(value, variables);
            }
            crate::kernel::ResourceReference::visit_captured_values(
                instance.resource_arguments(),
                |value| {
                    collect_algebraic_value_bound_variables(value, variables);
                },
            );
        }

        CResource::Memory(range) => {
            collect_pointer_bound_variables(&range.base, variables);
            collect_bitvector_bound_variables(range.bound_terms().0, variables);
            collect_bitvector_bound_variables(range.bound_terms().1, variables);
        }
        CResource::Iterated(iterated) => {
            for pointer in iterated.pointers() {
                collect_pointer_bound_variables(pointer, variables);
            }
            for term in iterated.terms() {
                collect_bitvector_bound_variables(term, variables);
            }
        }
        CResource::Composite { arguments, .. } | CResource::Token { arguments, .. } => {
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
fn collect_bitvector_bound_variables(term: &Bitvector32Term, variables: &mut BTreeSet<Variable>) {
    match term {
        Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_) => {}
        crate::kernel::binary_bitvector32_term!(left, right) => {
            collect_bitvector_bound_variables(left, variables);
            collect_bitvector_bound_variables(right, variables);
        }
        Bitvector32Term::BitwiseNot(value)
        | Bitvector32Term::Float32Negate(value)
        | Bitvector32Term::Float64Negate(value) => {
            collect_bitvector_bound_variables(value, variables);
        }
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_bound_variables(condition, variables);
            collect_bitvector_bound_variables(then_term, variables);
            collect_bitvector_bound_variables(else_term, variables);
        }
        Bitvector32Term::RangeFold {
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
        Bitvector32Term::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                collect_bitvector_bound_variables(argument, variables);
            }
        }
        Bitvector32Term::ClickFunctionApplication { arguments, .. } => {
            for argument in arguments {
                match argument {
                    PureFunctionArgument::Value(value) => {
                        collect_c_value_bound_variables(value, variables)
                    }
                    PureFunctionArgument::Algebraic(term) => {
                        collect_algebraic_bound_variables(term, variables)
                    }
                    PureFunctionArgument::Integer(_) => {}
                    PureFunctionArgument::ArrayRef {
                        memory, pointer, ..
                    } => {
                        collect_memory_bound_variables(memory, variables);
                        collect_c_value_bound_variables(pointer, variables);
                    }
                }
            }
        }
        Bitvector32Term::AlgebraicMatch { scrutinee, arms } => {
            collect_algebraic_bound_variables(scrutinee, variables);
            for arm in arms {
                for binding in &arm.bindings {
                    collect_algebraic_value_bound_variables(binding, variables);
                }
                collect_bitvector_bound_variables(&arm.body, variables);
            }
        }
        Bitvector32Term::MemoryLoad(memory, pointer, _) => {
            // Memory snapshots are immutable kernel values; their free
            // variable collector remains the source of truth for snapshot
            // contents, while the pointer can contain nested fold terms.
            collect_memory_bitvector_variables(memory, variables);
            collect_pointer_offset_bound_variables(&pointer.offset, variables);
        }
        Bitvector32Term::PointerAddress(pointer) => {
            collect_pointer_offset_bound_variables(&pointer.offset, variables);
        }
        Bitvector32Term::IntegerToMachine { value, .. } => {
            collect_integer_bound_variables(value, variables);
        }
        Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_)
        | Bitvector32Term::MachineIntegerConstant(_) => {}
        Bitvector32Term::Int64From32(value)
        | Bitvector32Term::MachineIntegerCast { value, .. }
        | Bitvector32Term::UInt64From32(value)
        | Bitvector32Term::UInt32From64(value)
        | Bitvector32Term::Int64FromUInt32(value)
        | Bitvector32Term::UInt64FromInt32(value)
        | Bitvector32Term::UInt64FromInt64(value)
        | Bitvector32Term::Int64BitwiseNot(value)
        | Bitvector32Term::UInt64BitwiseNot(value) => {
            collect_bitvector_bound_variables(value, variables)
        }
        crate::kernel::binary_wide_term!(left, right)
        | Bitvector32Term::Float32Binary { left, right, .. }
        | Bitvector32Term::Float64Binary { left, right, .. } => {
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
                    PureFunctionArgument::Value(value) => {
                        collect_c_value_bound_variables(value, variables)
                    }
                    PureFunctionArgument::Algebraic(term) => {
                        collect_algebraic_bound_variables(term, variables)
                    }
                    PureFunctionArgument::Integer(_) => {}
                    PureFunctionArgument::ArrayRef {
                        memory, pointer, ..
                    } => {
                        collect_memory_bound_variables(memory, variables);
                        collect_c_value_bound_variables(pointer, variables);
                    }
                }
            }
        }
    }
}

fn collect_condition_bound_variables(
    condition: &ConditionTerm,
    variables: &mut BTreeSet<Variable>,
) {
    match condition {
        ConditionTerm::AlgebraicEqual(left, right) => {
            left.for_each_bitvector_term(|term| collect_bitvector_bound_variables(term, variables));
            right
                .for_each_bitvector_term(|term| collect_bitvector_bound_variables(term, variables));
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
        ConditionTerm::PointerOffsetEqual(left, right) => {
            collect_pointer_offset_bound_variables(left, variables);
            collect_pointer_offset_bound_variables(right, variables);
        }
        ConditionTerm::PointerEqual(left, right) => {
            collect_pointer_offset_bound_variables(&left.offset, variables);
            collect_pointer_offset_bound_variables(&right.offset, variables);
        }
    }
}

fn collect_pointer_offset_bound_variables(
    offset: &PointerOffsetTerm,
    variables: &mut BTreeSet<Variable>,
) {
    match offset {
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {}
        PointerOffsetTerm::Add(left, right) => {
            collect_pointer_offset_bound_variables(left, variables);
            collect_pointer_offset_bound_variables(right, variables);
        }
        PointerOffsetTerm::Int32Scaled { value, .. }
        | PointerOffsetTerm::Int64Scaled { value, .. } => {
            collect_bitvector_bound_variables(value, variables);
        }
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_term(
    term: &Term,
    from: Variable,
    to: &Bitvector32Term,
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
        Term::CValue(value) => {
            Term::CValue(substitute_bitvector_variable_in_c_value(value, from, to))
        }
        Term::Sequence(sequence) => Term::Sequence(substitute_bitvector_variable_in_sequence(
            sequence, from, to,
        )),
        Term::Algebraic(term) => Term::Algebraic(AlgebraicTerm {
            algebraic_type: term.algebraic_type.clone(),
            node: match &term.node {
                AlgebraicTermNode::Variable(variable) => AlgebraicTermNode::Variable(*variable),
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
            },
        }),
        Term::CExpressionOutcome(outcome) => Term::CExpressionOutcome(
            substitute_bitvector_variable_in_c_expression_outcome(outcome, from, to),
        ),
        Term::CStatementOutcome(outcome) => Term::CStatementOutcome(Box::new(
            substitute_bitvector_variable_in_c_statement_outcome(outcome, from, to),
        )),
        Term::CFunctionOutcome(outcome) => Term::CFunctionOutcome(Box::new(
            substitute_bitvector_variable_in_c_function_outcome(outcome, from, to),
        )),
        Term::CMemory(memory) => {
            Term::CMemory(substitute_bitvector_variable_in_memory(memory, from, to))
        }
        Term::CState(state) => Term::CState(Box::new(substitute_bitvector_variable_in_c_state(
            state, from, to,
        ))),
    }
}

fn substitute_bitvector_variable_in_integer(
    term: &IntegerTerm,
    from: Variable,
    to: &Bitvector32Term,
) -> IntegerTerm {
    match substitute_bitvector_variable_in_integer_checked(term, from, to) {
        Ok(result) => result,
        Err(error) => panic!("integer substitution refused: {error:?}"),
    }
}

fn substitute_bitvector_variable_in_integer_checked(
    term: &IntegerTerm,
    from: Variable,
    to: &Bitvector32Term,
) -> Result<IntegerTerm, IntegerPureSubstitutionError> {
    substitute_bitvector_variable_in_integer_checked_with_mode(term, from, to, false)
}

fn substitute_bitvector_variable_in_integer_checked_with_registered_loads(
    term: &IntegerTerm,
    from: Variable,
    to: &Bitvector32Term,
) -> Result<IntegerTerm, IntegerPureSubstitutionError> {
    substitute_bitvector_variable_in_integer_checked_with_mode(term, from, to, true)
}

fn substitute_bitvector_variable_in_integer_checked_with_mode(
    term: &IntegerTerm,
    from: Variable,
    to: &Bitvector32Term,
    resolve_registered_loads: bool,
) -> Result<IntegerTerm, IntegerPureSubstitutionError> {
    let source = Bitvector32Term::Variable(from);
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
                    collect_bitvector_variables(start.value(), variables);
                    collect_bitvector_variables(end.value(), variables);
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

/// Checked singleton substitution for the pure proposition fragment. One
/// carrier-aware walker owns the entire traversal, including Integer leaves
/// and quantifier scopes. A refused or exhausted walk never returns a partial
/// proposition to either the planner or its certificate checker.
pub(crate) fn substitute_machine_constant_in_pure_proposition(
    proposition: &Proposition,
    from: Variable,
    value: i64,
) -> Result<Proposition, IntegerPureSubstitutionError> {
    use crate::kernel::proof::term_rewrite::{TermRewrite, TypedCReplacement};

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
        TypedCReplacement::Bitvector(signed_i64_bitvector_constant(value)),
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
    // one setup traversal without scanning their snapshots.
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
    // rewritten cell while retaining its original snapshot.
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
            validate_integer_pure_condition(condition, collector)
        }
        Proposition::CMemoryReadDefined { .. }
        | Proposition::CMemoryInitialized { .. }
        | Proposition::CMemoryLoadable { .. } => {
            // A symbolic array read contributes this obligation to the
            // existential body.  It is a supported C carrier as long as its
            // pointer and byte-count expressions are rewritten by the same
            // checked walker; the memory snapshot remains opaque.
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
        Proposition::ForAll { var, sort, body } => {
            if !matches!(
                sort,
                Sort::Integer
                    | Sort::CInt32
                    | Sort::CInt64
                    | Sort::CMachineInteger(_)
                    | Sort::CPointer(_)
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
                    | Sort::CInt32
                    | Sort::CInt64
                    | Sort::CMachineInteger(_)
                    | Sort::CPointer(_)
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
        &Proposition::ConditionIs(condition.clone(), true),
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
    C(crate::kernel::proof::term_rewrite::CSubstitutionScope),
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
                        rewritten.push(Proposition::ConditionIs(
                            substitute_integer_pure_condition_with_walker(condition, walker)?,
                            *value,
                        ));
                    }
                    Proposition::CMemoryReadDefined { .. }
                    | Proposition::CMemoryInitialized { .. }
                    | Proposition::CMemoryLoadable { .. } => {
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
                    Proposition::ForAll { var, sort, body } => {
                        queue_integer_quantifier_rewrite(
                            false, None, *var, sort, body, from, shadowed, walker, &mut tasks,
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
                            Some(name),
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
                    IntegerPropositionScope::C(scope) => {
                        walker.pop_c_substitution_scope(scope);
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
    name: Option<&String>,
    var: Variable,
    sort: &Sort,
    body: &'a Proposition,
    from: Variable,
    shadowed: bool,
    walker: &mut crate::kernel::proof::term_rewrite::TermRewrite<'_>,
    tasks: &mut Vec<IntegerPropositionRewriteTask<'a>>,
) -> Result<(), IntegerPureSubstitutionError> {
    let is_integer = *sort == Sort::Integer;
    let is_c = matches!(
        sort,
        Sort::CInt32 | Sort::CInt64 | Sort::CMachineInteger(_) | Sort::CPointer(_)
    );
    if !is_integer && !is_c {
        return Err(IntegerPureSubstitutionError::UnsupportedSort);
    }

    let renamed = if is_integer {
        !shadowed && var != from && walker.replacement_contains_integer_variable(var)
    } else {
        walker.replacement_contains_c_variable(var)
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
    } else {
        (
            IntegerPropositionScope::C(walker.push_c_substitution_scope(var, new_var)),
            shadowed,
        )
    };
    tasks.push(IntegerPropositionRewriteTask::FinishQuantifier {
        exists,
        name: name.cloned(),
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
        &Proposition::ConditionIs(condition.clone(), true),
        walker,
    )?
    else {
        unreachable!()
    };
    Ok(result)
}

fn rewrite_integer_memory_loadable_with_walker(
    proposition: &Proposition,
    walker: &mut crate::kernel::proof::term_rewrite::TermRewrite<'_>,
) -> Result<Proposition, IntegerPureSubstitutionError> {
    if let Proposition::CMemoryReadDefined {
        memory,
        pointer,
        value_type,
    } = proposition
    {
        integer_work(1)?;
        let Term::CValue(CValue::Pointer(pointer)) = walker.term(&Term::CValue(CValue::Pointer(
            CPointerValue::new(pointer.clone(), CType::VoidPointer),
        ))) else {
            unreachable!("pointer rewrite changed its carrier")
        };
        integer_substitution_refusal(walker.refusal())?;
        return Ok(Proposition::CMemoryReadDefined {
            memory: memory.clone(),
            pointer: pointer.pointer().clone(),
            value_type: *value_type,
        });
    }
    if let Proposition::CMemoryInitialized {
        memory,
        base: pointer,
        bytes,
    } = proposition
    {
        integer_work(1)?;
        let Term::CValue(CValue::Pointer(pointer)) = walker.term(&Term::CValue(CValue::Pointer(
            CPointerValue::new(pointer.clone(), CType::VoidPointer),
        ))) else {
            unreachable!("pointer rewrite changed its carrier")
        };
        integer_substitution_refusal(walker.refusal())?;
        return Ok(Proposition::CMemoryInitialized {
            memory: memory.clone(),
            base: pointer.pointer().clone(),
            bytes: *bytes,
        });
    }
    let Proposition::CMemoryLoadable {
        memory,
        base,
        bytes,
        wide,
    } = proposition
    else {
        unreachable!("memory-viewable helper called for another proposition carrier")
    };
    integer_work(1)?;
    let pointer = CValue::Pointer(CPointerValue::new(base.clone(), CType::VoidPointer));
    let Term::CValue(CValue::Pointer(pointer)) = walker.term(&Term::CValue(pointer)) else {
        unreachable!("pointer rewrite changed its carrier")
    };
    if walker.work_exhausted() {
        return Err(IntegerPureSubstitutionError::WorkLimitExceeded);
    }
    let bytes = walker.bits(bytes);
    integer_substitution_refusal(walker.refusal())?;
    Ok(Proposition::CMemoryLoadable {
        // Snapshots are immutable proof-state identities.  Keep the same
        // handle and rewrite only the selected address/width expressions.
        memory: memory.clone(),
        base: pointer.pointer().clone(),
        bytes,
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
            | Term::CValue(_)
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
            &Bitvector32Term::Variable(temporary_item),
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
        let Some(bits) = integer_item_bitvector(item_value, item_type) else {
            return Err(IntegerPureSubstitutionError::UnsupportedCarrier);
        };
        Ok(
            substitute_bitvector_variable_in_integer_checked_with_registered_loads(
                &with_accumulator,
                temporary_item,
                &bits,
            )?,
        )
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
fn integer_item_bitvector(
    value: &IntegerTerm,
    item_type: MachineIntegerType,
) -> Option<Bitvector32Term> {
    match (value, item_type) {
        (IntegerTerm::Machine(machine), _) if machine.ty() == item_type => {
            Some(machine.value().clone())
        }
        (IntegerTerm::Constant(value), MachineIntegerType::Int32) => value
            .to_i64()
            .filter(|value| (i64::from(i32::MIN)..=i64::from(i32::MAX)).contains(value))
            .map(|value| Bitvector32Term::Constant(value as i32 as u32)),
        (IntegerTerm::Constant(value), MachineIntegerType::UInt64) => {
            value.to_u64().map(Bitvector32Term::UInt64Constant)
        }
        _ => None,
    }
}

fn substitute_bitvector_variable_in_algebraic_term(
    term: &AlgebraicTerm,
    from: Variable,
    to: &Bitvector32Term,
) -> AlgebraicTerm {
    let Term::Algebraic(term) =
        substitute_bitvector_variable_in_term(&Term::Algebraic(term.clone()), from, to)
    else {
        unreachable!()
    };
    term
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_c_expression(
    expression: &CExpression,
    from: Variable,
    to: &Bitvector32Term,
) -> CExpression {
    match expression {
        CExpression::Value(value) => {
            CExpression::Value(substitute_bitvector_variable_in_c_value(value, from, to))
        }
        CExpression::Variable(name) => CExpression::Variable(name.clone()),
        CExpression::FunctionAddress(name) => CExpression::FunctionAddress(name.clone()),
        CExpression::Cast {
            expression,
            target_type,
            integer_mode,
            pointee_struct,
            pointee_volatile,
            pointee_constant,
            explicit_qualification,
        } => CExpression::Cast {
            expression: Box::new(substitute_bitvector_variable_in_c_expression(
                expression, from, to,
            )),
            target_type: *target_type,
            integer_mode: *integer_mode,
            pointee_struct: pointee_struct.clone(),
            pointee_volatile: *pointee_volatile,
            pointee_constant: *pointee_constant,
            explicit_qualification: *explicit_qualification,
        },
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => CExpression::Conditional {
            condition: Box::new(substitute_bitvector_variable_in_c_expression(
                condition, from, to,
            )),
            then_branch: Box::new(substitute_bitvector_variable_in_c_expression(
                then_branch,
                from,
                to,
            )),
            else_branch: Box::new(substitute_bitvector_variable_in_c_expression(
                else_branch,
                from,
                to,
            )),
        },
        CExpression::FloatClassification {
            expression,
            classification,
        } => CExpression::FloatClassification {
            expression: Box::new(substitute_bitvector_variable_in_c_expression(
                expression, from, to,
            )),
            classification: *classification,
        },
        CExpression::FloatNegate(expression) => CExpression::FloatNegate(Box::new(
            substitute_bitvector_variable_in_c_expression(expression, from, to),
        )),
        CExpression::ArrayRowAddress {
            array,
            index,
            shape,
            element_type,
        } => CExpression::ArrayRowAddress {
            array: Box::new(substitute_bitvector_variable_in_c_expression(
                array, from, to,
            )),
            index: Box::new(substitute_bitvector_variable_in_c_expression(
                index, from, to,
            )),
            shape: shape.clone(),
            element_type: *element_type,
        },
        CExpression::RecordPointerOffset {
            pointer,
            index,
            layout,
            subtract,
        } => CExpression::RecordPointerOffset {
            pointer: Box::new(substitute_bitvector_variable_in_c_expression(
                pointer, from, to,
            )),
            index: Box::new(substitute_bitvector_variable_in_c_expression(
                index, from, to,
            )),
            layout: layout.clone(),
            subtract: *subtract,
        },
        CExpression::MemberAddress { object, selection } => CExpression::MemberAddress {
            object: Box::new(substitute_bitvector_variable_in_c_expression(
                object, from, to,
            )),
            selection: selection.clone(),
        },
        CExpression::AddressOf(body) => CExpression::AddressOf(Box::new(
            substitute_bitvector_variable_in_c_expression(body, from, to),
        )),
        CExpression::CheckedObjectAddress(body) => CExpression::CheckedObjectAddress(Box::new(
            substitute_bitvector_variable_in_c_expression(body, from, to),
        )),
        CExpression::PointerOffsetBytes { pointer, bytes } => CExpression::PointerOffsetBytes {
            pointer: Box::new(substitute_bitvector_variable_in_c_expression(
                pointer, from, to,
            )),
            bytes: *bytes,
        },
        CExpression::PointerAligned { pointer, alignment } => CExpression::PointerAligned {
            pointer: Box::new(substitute_bitvector_variable_in_c_expression(
                pointer, from, to,
            )),
            alignment: *alignment,
        },
        CExpression::Not(body) => CExpression::Not(Box::new(
            substitute_bitvector_variable_in_c_expression(body, from, to),
        )),
        CExpression::Load(body) => CExpression::Load(Box::new(
            substitute_bitvector_variable_in_c_expression(body, from, to),
        )),
        CExpression::TypedLoad {
            pointer,
            value_type,
            volatile,
            pointee_constant,
            source,
        } => CExpression::TypedLoad {
            pointer: Box::new(substitute_bitvector_variable_in_c_expression(
                pointer, from, to,
            )),
            value_type: *value_type,
            volatile: *volatile,
            pointee_constant: *pointee_constant,
            source: source.clone(),
        },
        CExpression::LessThan(left, right) => CExpression::LessThan(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::LessEqual(left, right) => CExpression::LessEqual(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::GreaterThan(left, right) => CExpression::GreaterThan(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::GreaterEqual(left, right) => CExpression::GreaterEqual(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::Equal(left, right) => CExpression::Equal(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::NotEqual(left, right) => CExpression::NotEqual(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::And(left, right) => CExpression::And(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::Or(left, right) => CExpression::Or(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::Add(left, right) => CExpression::Add(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::Subtract(left, right) => CExpression::Subtract(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::Multiply(left, right) => CExpression::Multiply(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::Divide(left, right) => CExpression::Divide(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::Remainder(left, right) => CExpression::Remainder(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::ShiftLeft(left, right) => CExpression::ShiftLeft(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::ShiftRight(left, right) => CExpression::ShiftRight(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::BitwiseAnd(left, right) => CExpression::BitwiseAnd(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::BitwiseOr(left, right) => CExpression::BitwiseOr(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::BitwiseXor(left, right) => CExpression::BitwiseXor(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::BitwiseNot(expression) => CExpression::BitwiseNot(Box::new(
            substitute_bitvector_variable_in_c_expression(expression, from, to),
        )),
        CExpression::Index(left, right) => CExpression::Index(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_spec_expression(
    expression: &SpecExpression,
    from: Variable,
    to: &Bitvector32Term,
) -> SpecExpression {
    let source = Bitvector32Term::Variable(from);
    let mut rewrite =
        crate::kernel::proof::term_rewrite::TermRewrite::for_bits_checked(&source, to);
    rewrite
        .spec_expression(expression)
        .unwrap_or_else(|error| panic!("spec expression substitution refused: {error:?}"))
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_spec_proposition(
    proposition: &SpecProposition,
    from: Variable,
    to: &Bitvector32Term,
) -> SpecProposition {
    let source = Bitvector32Term::Variable(from);
    let mut rewrite =
        crate::kernel::proof::term_rewrite::TermRewrite::for_bits_checked(&source, to);
    rewrite
        .spec_proposition(proposition)
        .unwrap_or_else(|error| panic!("spec proposition substitution refused: {error:?}"))
}

fn substitute_bitvector_variable_in_spec_integer(
    expression: &SpecIntegerExpression,
    from: Variable,
    to: &Bitvector32Term,
) -> SpecIntegerExpression {
    let source = Bitvector32Term::Variable(from);
    let mut rewrite =
        crate::kernel::proof::term_rewrite::TermRewrite::for_bits_checked(&source, to);
    rewrite
        .spec_integer_expression(expression)
        .unwrap_or_else(|error| panic!("spec Integer substitution refused: {error:?}"))
}

#[cfg(test)]
mod spec_carrier_substitution_binder_tests {
    use super::*;

    fn int32_value(variable: Variable) -> SpecExpression {
        SpecExpression::Value(CValue::Int32(Bitvector32Term::Variable(variable)))
    }

    fn fold_body(item: Variable, source: Variable) -> SpecIntegerExpression {
        SpecIntegerExpression::Add(
            Box::new(SpecIntegerExpression::FromMachine(Box::new(int32_value(
                item,
            )))),
            Box::new(SpecIntegerExpression::Term(IntegerTerm::Machine(
                SharedMachineIntegerTerm::intern(
                    MachineIntegerType::Int32,
                    Bitvector32Term::Variable(source),
                ),
            ))),
        )
    }

    fn int32_fold(item: Variable, source: Variable) -> SpecExpression {
        SpecExpression::IntegerToMachine {
            value: Box::new(SpecIntegerExpression::RangeFold {
                index: SpecIntegerRangeFoldIndex::Int32 {
                    start: Box::new(int32_value(source)),
                    end: Box::new(SpecExpression::Value(CValue::Int32(
                        Bitvector32Term::Constant(8),
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
            &Bitvector32Term::Variable(item),
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
        assert_eq!(substituted_source.value(), &Bitvector32Term::Variable(item));
    }

    #[test]
    fn spec_integer_fold_does_not_substitute_through_its_own_item_binder() {
        let source = Variable(320);
        let rewritten = substitute_bitvector_variable_in_spec_expression(
            &int32_fold(source, source),
            source,
            &Bitvector32Term::Constant(5),
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
            SpecExpression::Value(CValue::Int32(Bitvector32Term::Constant(5)))
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
                Bitvector32Term::Variable(source),
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
                operator: CComparisonOperator::Equal,
                right: int32_value(binder),
            }),
        };
        let rewritten = substitute_bitvector_variable_in_spec_proposition(
            &proposition,
            source,
            &Bitvector32Term::Variable(binder),
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
                operator: CComparisonOperator::Equal,
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
                operator: CComparisonOperator::Equal,
                right: SpecExpression::Value(CValue::Int32(Bitvector32Term::Constant(8))),
            }),
        };
        let rewritten = substitute_bitvector_variable_in_spec_proposition(
            &proposition,
            source,
            &Bitvector32Term::Constant(5),
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
                        &Bitvector32Term::Constant(1),
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
    fn machine_backed_integer_substitution_scales_with_shared_dag() {
        for depth in [8, 16, 32, 64] {
            let source = SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int32,
                Bitvector32Term::Variable(Variable(7)),
            );
            let mut term = IntegerTerm::Machine(source);
            for _ in 0..depth {
                term = IntegerTerm::add(term.clone(), term.clone());
            }
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                substitute_bitvector_variable_in_integer(
                    &term,
                    Variable(7),
                    &Bitvector32Term::Constant(7),
                )
            });
            assert!(
                work <= (depth + 1) * 32,
                "unexpected shared DAG work at depth {depth}: {work}"
            );
        }
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_condition(
    condition: &ConditionTerm,
    from: Variable,
    to: &Bitvector32Term,
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
        ConditionTerm::Variable(variable) => ConditionTerm::Variable(*variable),
        ConditionTerm::Bitvector32SignedLessThan(left, right) => ConditionTerm::signed_less_than(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => ConditionTerm::signed_less_equal(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
            ConditionTerm::signed_greater_than(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
            ConditionTerm::signed_greater_equal(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector32Equal(left, right) => ConditionTerm::equal(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        ConditionTerm::Bitvector32SignedAddOverflows(left, right) => {
            ConditionTerm::signed_add_overflows(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector32SignedSubtractOverflows(left, right) => {
            ConditionTerm::signed_subtract_overflows(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right) => {
            ConditionTerm::signed_multiply_overflows(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector32SignedDivideOverflows(left, right) => {
            ConditionTerm::signed_divide_overflows(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right) => {
            ConditionTerm::signed_shift_left_overflows(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector64SignedLessThan(left, right) => {
            ConditionTerm::int64_signed_less_than(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector64SignedLessEqual(left, right) => {
            ConditionTerm::int64_signed_less_equal(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector64SignedGreaterThan(left, right) => {
            ConditionTerm::int64_signed_greater_than(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector64SignedGreaterEqual(left, right) => {
            ConditionTerm::int64_signed_greater_equal(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector64UnsignedLessThan(left, right) => ConditionTerm::uint64_less_than(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        ConditionTerm::Bitvector64UnsignedLessEqual(left, right) => {
            ConditionTerm::uint64_less_equal(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector64UnsignedGreaterThan(left, right) => {
            ConditionTerm::uint64_greater_than(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector64UnsignedGreaterEqual(left, right) => {
            ConditionTerm::uint64_greater_equal(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector64Equal(left, right) => ConditionTerm::Bitvector64Equal(
            Box::new(substitute_bitvector_variable(left, from, to)),
            Box::new(substitute_bitvector_variable(right, from, to)),
        ),
        ConditionTerm::Bitvector64SignedAddOverflows(left, right) => {
            ConditionTerm::int64_signed_add_overflows(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector64SignedSubtractOverflows(left, right) => {
            ConditionTerm::int64_signed_subtract_overflows(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector64SignedMultiplyOverflows(left, right) => {
            ConditionTerm::int64_signed_multiply_overflows(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector64SignedDivideOverflows(left, right) => {
            ConditionTerm::int64_signed_divide_overflows(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector64SignedShiftLeftOverflows(left, right) => {
            ConditionTerm::int64_signed_shift_left_overflows(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
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
        ConditionTerm::Float32(CFloatCondition::Comparison {
            operator,
            left,
            right,
        }) => ConditionTerm::float32_compare(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
            *operator,
        ),
        ConditionTerm::Float32(CFloatCondition::Classification {
            classification,
            value,
        }) => ConditionTerm::float32_classification(
            substitute_bitvector_variable(value, from, to),
            *classification,
        ),
        ConditionTerm::Float64(CFloatCondition::Comparison {
            operator,
            left,
            right,
        }) => ConditionTerm::float64_compare(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
            *operator,
        ),
        ConditionTerm::Float64(CFloatCondition::Classification {
            classification,
            value,
        }) => ConditionTerm::float64_classification(
            substitute_bitvector_variable(value, from, to),
            *classification,
        ),
        ConditionTerm::PointerOffsetEqual(left, right) => ConditionTerm::pointer_offset_equal(
            substitute_bitvector_variable_in_pointer_offset(left, from, to),
            substitute_bitvector_variable_in_pointer_offset(right, from, to),
        ),
        ConditionTerm::PointerEqual(left, right) => ConditionTerm::pointer_equal(
            substitute_bitvector_variable_in_pointer(left, from, to),
            substitute_bitvector_variable_in_pointer(right, from, to),
        ),
    }
}

fn substitute_through_load_variable(
    variable: Variable,
    from: Variable,
    to: &Bitvector32Term,
) -> Option<Bitvector32Term> {
    if !crate::kernel::is_load_variable(&variable) {
        return None;
    }
    let (memory, pointer) = crate::kernel::eval::registered_load_for_variable(&variable)?;
    let kind = crate::kernel::eval::registered_load_kind_for_variable(&variable)?;
    let substituted_pointer = Pointer {
        block: pointer.block.clone(),
        offset: substitute_bitvector_variable_in_pointer_offset(&pointer.offset, from, to),
    };
    // Deciding that this load variable is untouched means rewriting the
    // snapshot it was minted against, whose own cells hold further load
    // variables. Going through the interned-snapshot memo makes the common
    // "nothing changed" answer a lookup instead of a fresh rebuild of the
    // whole reachable snapshot DAG, and compares the result by arena identity
    // rather than by deep structural equality.
    let substituted_memory = substitute_bitvector_variable_in_shared_memory(&memory, from, to);
    if substituted_pointer == pointer && substituted_memory == memory {
        return None;
    }
    // A load variable's snapshot is the canonical projection of the snapshot
    // the load read, cut down to what that one address can observe. The
    // projection is recorded per `(projected, address)`, and the history walk
    // reaches the source through that record. A substituted address has none,
    // so a load renamed or instantiated here would be stranded at a snapshot
    // with no history, where the same read lowered directly for the new
    // address (an `intro`duced binder, say) crosses the steps back to the
    // source. Substitute from the source instead and let `canonical_term`
    // project it for the new address and record that projection, exactly as
    // a direct lowering does. Sound: two snapshots with one projection agree
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
    crate::kernel::eval::transport_load_access_width(
        &memory,
        &pointer,
        &substituted_memory,
        &substituted_pointer,
    );
    Some(crate::kernel::eval::canonical_term(
        &Bitvector32Term::MemoryLoad(substituted_memory, Box::new(substituted_pointer), kind),
    ))
}

pub(crate) fn substitute_bitvector_variable(
    term: &Bitvector32Term,
    from: Variable,
    to: &Bitvector32Term,
) -> Bitvector32Term {
    match term {
        Bitvector32Term::MachineIntegerCast {
            value,
            source,
            destination,
        } => Bitvector32Term::machine_integer_cast(
            *source,
            *destination,
            substitute_bitvector_variable(value, from, to),
        ),

        Bitvector32Term::MachineIntegerConstant(value) => {
            Bitvector32Term::MachineIntegerConstant(*value)
        }

        Bitvector32Term::Constant(value) => Bitvector32Term::Constant(*value),
        Bitvector32Term::Int64Constant(value) => Bitvector32Term::Int64Constant(*value),
        Bitvector32Term::UInt64Constant(value) => Bitvector32Term::UInt64Constant(*value),
        Bitvector32Term::Variable(variable) if *variable == from => to.clone(),
        Bitvector32Term::Variable(variable) => {
            // A load variable can represent a load whose address mentions
            // the substituted variable (a universal's body contains `p[k]`
            // with the bound `k` inside the address). Substitution reaches
            // through the variable into the load and takes the canonical
            // form of the result, so instantiating a universal yields the
            // same load variable as a direct read of that cell.
            substitute_through_load_variable(*variable, from, to)
                .unwrap_or(Bitvector32Term::Variable(*variable))
        }
        Bitvector32Term::Int64From32(value) => {
            Bitvector32Term::int64_from_32(substitute_bitvector_variable(value, from, to))
        }
        Bitvector32Term::UInt64From32(value) => {
            Bitvector32Term::uint64_from_32(substitute_bitvector_variable(value, from, to))
        }
        Bitvector32Term::UInt32From64(value) => {
            Bitvector32Term::uint32_from_64(substitute_bitvector_variable(value, from, to))
        }
        Bitvector32Term::Int64FromUInt32(value) => {
            Bitvector32Term::int64_from_uint32(substitute_bitvector_variable(value, from, to))
        }
        Bitvector32Term::UInt64FromInt32(value) => {
            Bitvector32Term::uint64_from_int32(substitute_bitvector_variable(value, from, to))
        }
        Bitvector32Term::UInt64FromInt64(value) => {
            Bitvector32Term::uint64_from_int64(substitute_bitvector_variable(value, from, to))
        }
        Bitvector32Term::Int64Add(left, right) => Bitvector32Term::int64_add(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::Int64Subtract(left, right) => Bitvector32Term::int64_subtract(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::Int64Multiply(left, right) => Bitvector32Term::int64_multiply(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::Int64Divide(left, right) => Bitvector32Term::int64_divide(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::Int64Remainder(left, right) => Bitvector32Term::int64_remainder(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::Int64ShiftLeft(left, right) => Bitvector32Term::int64_shift_left(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::Int64ArithmeticShiftRight(left, right) => {
            Bitvector32Term::int64_arithmetic_shift_right(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        Bitvector32Term::Int64BitwiseAnd(left, right) => Bitvector32Term::int64_bitwise_and(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::Int64BitwiseOr(left, right) => Bitvector32Term::int64_bitwise_or(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::Int64BitwiseXor(left, right) => Bitvector32Term::int64_bitwise_xor(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::Int64BitwiseNot(value) => {
            Bitvector32Term::int64_bitwise_not(substitute_bitvector_variable(value, from, to))
        }
        Bitvector32Term::UInt64Add(left, right) => Bitvector32Term::uint64_add(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::UInt64Subtract(left, right) => Bitvector32Term::uint64_subtract(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::UInt64Multiply(left, right) => Bitvector32Term::uint64_multiply(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::UInt64Divide(left, right) => Bitvector32Term::uint64_divide(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::UInt64Remainder(left, right) => Bitvector32Term::uint64_remainder(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::UInt64ShiftLeft(left, right) => Bitvector32Term::uint64_shift_left(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::UInt64LogicalShiftRight(left, right) => {
            Bitvector32Term::uint64_logical_shift_right(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        Bitvector32Term::UInt64BitwiseAnd(left, right) => Bitvector32Term::uint64_bitwise_and(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::UInt64BitwiseOr(left, right) => Bitvector32Term::uint64_bitwise_or(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::UInt64BitwiseXor(left, right) => Bitvector32Term::uint64_bitwise_xor(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::UInt64BitwiseNot(value) => {
            Bitvector32Term::uint64_bitwise_not(substitute_bitvector_variable(value, from, to))
        }
        Bitvector32Term::Float32Negate(value) => {
            Bitvector32Term::float32_negate(substitute_bitvector_variable(value, from, to))
        }
        Bitvector32Term::Float32Binary {
            operator,
            left,
            right,
        } => Bitvector32Term::float32_binary(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
            *operator,
        ),
        Bitvector32Term::Float64Negate(value) => {
            Bitvector32Term::float64_negate(substitute_bitvector_variable(value, from, to))
        }
        Bitvector32Term::Float64Binary {
            operator,
            left,
            right,
        } => Bitvector32Term::float64_binary(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
            *operator,
        ),
        Bitvector32Term::Add(left, right) => Bitvector32Term::add(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::Subtract(left, right) => Bitvector32Term::subtract(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::Multiply(left, right) => Bitvector32Term::multiply(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::Divide(left, right) => Bitvector32Term::divide(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::UnsignedDivide(left, right) => Bitvector32Term::unsigned_divide(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::Remainder(left, right) => Bitvector32Term::remainder(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::UnsignedRemainder(left, right) => Bitvector32Term::unsigned_remainder(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::ShiftLeft(left, right) => Bitvector32Term::shift_left(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
            Bitvector32Term::arithmetic_shift_right(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        Bitvector32Term::LogicalShiftRight(left, right) => Bitvector32Term::logical_shift_right(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::BitwiseAnd(left, right) => Bitvector32Term::bitwise_and(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::BitwiseOr(left, right) => Bitvector32Term::bitwise_or(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::BitwiseXor(left, right) => Bitvector32Term::bitwise_xor(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::BitwiseNot(value) => {
            Bitvector32Term::bitwise_not(substitute_bitvector_variable(value, from, to))
        }
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => Bitvector32Term::if_then_else(
            substitute_bitvector_variable_in_condition(condition, from, to),
            substitute_bitvector_variable(then_term, from, to),
            substitute_bitvector_variable(else_term, from, to),
        ),
        Bitvector32Term::RangeFold {
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
                    &Bitvector32Term::Variable(renamed),
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
                body =
                    substitute_bitvector_variable(&body, item, &Bitvector32Term::Variable(renamed));
                item = renamed;
            }
            if original_accumulator != from && original_item != from {
                body = substitute_bitvector_variable(&body, from, to);
            }
            Bitvector32Term::range_fold(
                substitute_bitvector_variable(start, from, to),
                substitute_bitvector_variable(end, from, to),
                substitute_bitvector_variable(initial, from, to),
                accumulator,
                item,
                body,
            )
        }
        Bitvector32Term::PureFunctionApplication { name, arguments } => {
            Bitvector32Term::PureFunctionApplication {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| substitute_bitvector_variable(argument, from, to))
                    .collect(),
            }
        }
        Bitvector32Term::ClickFunctionApplication { name, arguments } => {
            Bitvector32Term::ClickFunctionApplication {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| {
                        substitute_bitvector_variable_in_pure_function_argument(argument, from, to)
                    })
                    .collect(),
            }
        }
        Bitvector32Term::AlgebraicMatch { scrutinee, arms } => Bitvector32Term::AlgebraicMatch {
            scrutinee: Box::new(substitute_bitvector_variable_in_algebraic_term(
                scrutinee, from, to,
            )),
            arms: arms
                .iter()
                .map(|arm| AlgebraicBitvectorMatchArm {
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
        Bitvector32Term::MemoryLoad(memory, pointer, kind) => {
            let rewritten_memory = substitute_bitvector_variable_in_shared_memory(memory, from, to);
            let rewritten_pointer = substitute_bitvector_variable_in_pointer(pointer, from, to);
            crate::kernel::eval::transport_load_access_width(
                memory,
                pointer,
                &rewritten_memory,
                &rewritten_pointer,
            );
            Bitvector32Term::MemoryLoad(rewritten_memory, Box::new(rewritten_pointer), *kind)
        }
        Bitvector32Term::PointerAddress(pointer) => Bitvector32Term::pointer_address(
            substitute_bitvector_variable_in_pointer(pointer, from, to),
        ),
        Bitvector32Term::IntegerToMachine { value, destination } => {
            Bitvector32Term::IntegerToMachine {
                value: substitute_bitvector_variable_in_integer(value.as_ref(), from, to).into(),
                destination: *destination,
            }
        }
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_pointer_offset(
    offset: &PointerOffsetTerm,
    from: Variable,
    to: &Bitvector32Term,
) -> PointerOffsetTerm {
    substitute_bitvector_variable_in_pointer_offset_cow(offset, from, to).into_owned()
}

/// Keep an unchanged pointer spelling intact. Rebuilding every `Add` through
/// the normalizing constructor changes an otherwise untouched memory cell's
/// key, which in turn mints a different snapshot for a binder rename that did
/// not occur anywhere in that cell.
fn substitute_bitvector_variable_in_pointer_offset_cow<'a>(
    offset: &'a PointerOffsetTerm,
    from: Variable,
    to: &Bitvector32Term,
) -> std::borrow::Cow<'a, PointerOffsetTerm> {
    use std::borrow::Cow;
    match offset {
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => Cow::Borrowed(offset),
        PointerOffsetTerm::Add(left, right) => {
            let left = substitute_bitvector_variable_in_pointer_offset_cow(left, from, to);
            let right = substitute_bitvector_variable_in_pointer_offset_cow(right, from, to);
            if matches!((&left, &right), (Cow::Borrowed(_), Cow::Borrowed(_))) {
                Cow::Borrowed(offset)
            } else {
                Cow::Owned(PointerOffsetTerm::add(
                    left.into_owned(),
                    right.into_owned(),
                ))
            }
        }
        PointerOffsetTerm::Int32Scaled { value, byte_width } => {
            let rewritten = substitute_bitvector_variable(value, from, to);
            if rewritten == **value {
                Cow::Borrowed(offset)
            } else {
                Cow::Owned(PointerOffsetTerm::scale_int32(rewritten, *byte_width))
            }
        }
        PointerOffsetTerm::Int64Scaled {
            value,
            byte_width,
            unsigned,
        } => {
            let rewritten = substitute_bitvector_variable(value, from, to);
            if rewritten == **value {
                Cow::Borrowed(offset)
            } else {
                Cow::Owned(PointerOffsetTerm::scale_int64(
                    rewritten,
                    *byte_width,
                    *unsigned,
                ))
            }
        }
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_pointer(
    pointer: &Pointer,
    from: Variable,
    to: &Bitvector32Term,
) -> Pointer {
    if matches!(pointer.block, PointerBlock::PureFunctionApplication(_)) {
        let source = Bitvector32Term::Variable(from);
        let term = Term::CValue(CValue::pointer(pointer.clone()));
        let Term::CValue(CValue::Pointer(result)) =
            crate::kernel::proof::term_rewrite::TermRewrite::for_bits(&source, to).term(&term)
        else {
            unreachable!()
        };
        return result.into_pointer();
    }
    Pointer {
        block: pointer.block.clone(),
        offset: substitute_bitvector_variable_in_pointer_offset(&pointer.offset, from, to),
    }
}

/// One in-flight `(from, to)` substitution's already-rewritten snapshots.
///
/// A `MemoryLoad` term carries a whole snapshot, and a snapshot's cells can
/// hold further `MemoryLoad` terms, so the terms a proof builds form a DAG of
/// snapshots rather than a tree. Rewriting one variable used to walk that DAG
/// as a tree, re-deriving and re-interning every shared snapshot once per path
/// that reaches it: in `mdtests/rb_replace_node_with_children.md`, whose three
/// nested `unfold`s name a cell at each level, 96 variable substitutions cost
/// 965,776 snapshot rebuilds.
///
/// Snapshots are interned, so the rewrite of one is a pure function of its
/// arena id and the `(from, to)` pair. Keyed by that id, each distinct
/// snapshot is rebuilt exactly once per substitution and the walk becomes
/// linear in the DAG's nodes. The frame holds the borrowed replacement term's
/// address: the term is alive for as long as the frame, so an equal address is
/// the same object with the same contents, the argument
/// `PureFactContextIdScope` uses.
struct SubstitutedMemoryFrame {
    from: Variable,
    to: usize,
    substituted: std::collections::HashMap<(u32, u32), SharedCMemory>,
}

thread_local! {
    static SUBSTITUTED_MEMORIES: std::cell::RefCell<Vec<SubstitutedMemoryFrame>> =
        const { std::cell::RefCell::new(Vec::new()) };
    /// Interned snapshots a variable was found not to occur in. A quantified
    /// fact over `m[p + j]` names its binder only in the address, never in
    /// the snapshot, yet each instantiation used to rewrite the whole
    /// snapshot again: the arena pipeline's order decisions instantiate its
    /// frames once per candidate term. The answer depends only on the
    /// immutable snapshot and the variable, so it is kept across
    /// substitutions; the key names the arena, so a reset arena misses.
    static MEMORY_LACKS_VARIABLE: std::cell::RefCell<
        std::collections::HashSet<((u32, u32), Variable)>,
    > = std::cell::RefCell::new(std::collections::HashSet::new());
}

/// Entries kept before the absent-variable memo is cleared.
const MEMORY_LACKS_VARIABLE_LIMIT: usize = 1 << 20;

/// Opens (or joins) the snapshot memo for one `(from, to)` substitution.
struct SubstitutedMemoryScope {
    pushed: bool,
}

impl SubstitutedMemoryScope {
    fn enter(from: Variable, to: &Bitvector32Term) -> Self {
        let address = to as *const Bitvector32Term as usize;
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

/// Rewrites one variable inside an interned snapshot, reusing this
/// substitution's earlier answer for the same snapshot.
fn substitute_bitvector_variable_in_shared_memory(
    memory: &SharedCMemory,
    from: Variable,
    to: &Bitvector32Term,
) -> SharedCMemory {
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
    let substituted =
        crate::kernel::intern_c_memory(rewrite_memory_snapshot(memory.memory(), from, to));
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

/// Rewrites one variable throughout a memory snapshot.
///
/// This is the unit of work the snapshot DAG multiplies, so it is a named
/// profiler operation charged its snapshot's size: a rewrite that revisits one
/// shared snapshot once per reaching path shows up as `substitution: snapshot
/// rewrite` growing far faster than the proof, which is what `click profile`
/// could not point at before.
pub(in crate::kernel) fn substitute_bitvector_variable_in_memory(
    memory: &CMemory,
    from: Variable,
    to: &Bitvector32Term,
) -> CMemory {
    // A snapshot carried by value (a loadability or effect proposition) is
    // interned only to consult and fill the absent-variable memo; interning
    // an already-registered snapshot is a shallow lookup.
    let shared = crate::kernel::intern_c_memory(memory.clone());
    let identity = shared.arena_id();
    if memory_lacks_variable(identity, from) {
        return memory.clone();
    }
    let substituted = rewrite_memory_snapshot(memory, from, to);
    if crate::kernel::intern_c_memory(substituted.clone()) == shared {
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

fn rewrite_memory_snapshot(memory: &CMemory, from: Variable, to: &Bitvector32Term) -> CMemory {
    crate::instrumentation::measure_operation(
        "kernel",
        "substitution",
        "substitution: snapshot rewrite",
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
fn snapshot_size_substitution_preserves_declared_types_and_write_protection() {
    let from = Variable(84001);
    let mut memory =
        CMemory::new().with_declared_scalar_block("local:word".into(), 4, CType::UInt32);
    let mut read_only = CBlock::read_only(4);
    read_only.size = Bitvector32Term::Variable(from);
    std::sync::Arc::make_mut(&mut memory.blocks).insert("global:protected".into(), read_only);
    let rewritten = substitute_bitvector_variable_in_memory_contents(
        &memory,
        from,
        &Bitvector32Term::Constant(16),
    );
    assert_eq!(
        rewritten.blocks.get(&PointerBlock::from("local:word")),
        memory.blocks.get(&PointerBlock::from("local:word"))
    );
    let protected = rewritten
        .blocks
        .get(&PointerBlock::from("global:protected"))
        .unwrap();
    assert!(protected.read_only);
    assert_eq!(protected.size, Bitvector32Term::Constant(16));
}

fn substitute_bitvector_variable_in_memory_contents(
    memory: &CMemory,
    from: Variable,
    to: &Bitvector32Term,
) -> CMemory {
    crate::instrumentation::record_deterministic_work(
        memory.cells.representation_len() + memory.union_cells.len() + memory.blocks.len(),
    );
    let cells = std::sync::Arc::new(memory.cells.map_cells(
        |pointer, value| {
            (
                substitute_bitvector_variable_in_pointer(pointer, from, to),
                substitute_bitvector_variable_in_c_value(value, from, to),
            )
        },
        |run| run_slot_named_by_load_variable(run, from),
    ));
    let (native_record_inputs, native_record_input_origins) = memory.map_native_record_inputs(
        |pointer| {
            let CValue::Pointer(pointer) = substitute_bitvector_variable_in_c_value(
                &CValue::Pointer(pointer.clone()),
                from,
                to,
            ) else {
                unreachable!("pointer substitution preserves the carrier")
            };
            pointer
        },
        |count| substitute_bitvector_variable_in_integer(count.as_ref(), from, to).into(),
    );
    let mut result = CMemory {
        construction: None,
        blocks: std::sync::Arc::new(
            memory
                .blocks
                .iter()
                .map(|(block, contents)| {
                    // Substitution changes the extent term, not the storage
                    // declaration or its write protection. Rebuilding a bare
                    // block erased these properties, even for a constant size.
                    let mut rewritten = contents.clone();
                    rewritten.size = substitute_bitvector_variable(contents.size(), from, to);
                    (block.clone(), rewritten)
                })
                .collect(),
        ),
        cells,
        union_cells: std::sync::Arc::new(
            memory
                .union_cells
                .iter()
                .map(|((pointer, c_type), value)| {
                    (
                        (
                            substitute_bitvector_variable_in_pointer(pointer, from, to),
                            *c_type,
                        ),
                        substitute_bitvector_variable_in_c_value(value, from, to),
                    )
                })
                .collect(),
        ),
        // Carried unrewritten. The mark inside is an identity, not an
        // address or a value, and a rewritten snapshot that dropped it could
        // re-intern as a state that forgot nothing.
        forgotten: memory.forgotten.clone(),
        heap: std::sync::Arc::new(CHeapMemory {
            native_record_inputs,
            native_record_input_origins,
            live_allocations: memory
                .heap
                .live_allocations
                .iter()
                .map(|(base, bytes)| {
                    (
                        substitute_bitvector_variable_in_pointer(base, from, to),
                        substitute_bitvector_variable(bytes, from, to),
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
                        substitute_bitvector_variable(bytes, from, to),
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
                        substitute_bitvector_variable(bytes, from, to),
                    )
                })
                .collect(),
            object_input_domains: memory.map_object_input_domains(|base| {
                substitute_bitvector_variable_in_pointer(base, from, to)
            }),
            scalar_input_domains: memory.map_scalar_input_domains(|base| {
                substitute_bitvector_variable_in_pointer(base, from, to)
            }),
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
            initialized: memory.heap.initialized.map_pointers(|pointer| {
                substitute_bitvector_variable_in_pointer(pointer, from, to)
            }),
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
                    let CValue::Pointer(old_pointer) = substitute_bitvector_variable_in_c_value(
                        &CValue::Pointer(pending.old_pointer.clone()),
                        from,
                        to,
                    ) else {
                        unreachable!("pointer substitution preserves its carrier")
                    };
                    (
                        substitute_bitvector_variable_in_pointer(base, from, to),
                        CPendingReallocation {
                            old_pointer,
                            old_bytes: substitute_bitvector_variable(&pending.old_bytes, from, to),
                            zeroed_prefix: pending
                                .zeroed_prefix
                                .as_ref()
                                .map(|prefix| substitute_bitvector_variable(prefix, from, to)),
                            initialized_prefix: pending.initialized_prefix.clone(),
                            copied_cells: pending
                                .copied_cells
                                .iter()
                                .map(|(offset, value)| {
                                    (
                                        substitute_bitvector_variable_in_pointer_offset(
                                            offset, from, to,
                                        ),
                                        substitute_bitvector_variable_in_c_value(value, from, to),
                                    )
                                })
                                .collect(),
                        },
                    )
                })
                .collect(),
        }),
    };
    result.record_diagnostic_transform(
        "substitute scalar variable",
        vec![memory.clone()],
        vec![
            CValue::Int32(Bitvector32Term::Variable(from)),
            CValue::Int32(to.clone()),
        ],
    );
    result
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_c_value(
    value: &CValue,
    from: Variable,
    to: &Bitvector32Term,
) -> CValue {
    match value {
        CValue::PointerInteger(value) => {
            let CValue::Pointer(origin) = substitute_bitvector_variable_in_c_value(
                &CValue::Pointer(value.origin().clone()),
                from,
                to,
            ) else {
                unreachable!("pointer substitution preserves the full carrier")
            };
            CValue::PointerInteger(std::sync::Arc::new(value.with_parts(
                substitute_bitvector_variable(value.bits(), from, to),
                origin,
            )))
        }
        CValue::Void => CValue::Void,
        CValue::Bool(bits) => CValue::Bool(substitute_bitvector_variable(bits, from, to)),
        CValue::Int8(bits) => int8(substitute_bitvector_variable(bits, from, to)),
        CValue::Int16(bits) => int16(substitute_bitvector_variable(bits, from, to)),
        CValue::Int32(bits) => int32(substitute_bitvector_variable(bits, from, to)),
        CValue::UInt8(bits) => uint8(substitute_bitvector_variable(bits, from, to)),
        CValue::UInt16(bits) => uint16(substitute_bitvector_variable(bits, from, to)),
        CValue::UInt32(bits) => uint32(substitute_bitvector_variable(bits, from, to)),
        CValue::Int64(bits) => CValue::Int64(substitute_bitvector_variable(bits, from, to)),
        CValue::UInt64(bits) => CValue::UInt64(substitute_bitvector_variable(bits, from, to)),
        CValue::Int128(bits) => CValue::Int128(substitute_bitvector_variable(bits, from, to)),
        CValue::UInt128(bits) => CValue::UInt128(substitute_bitvector_variable(bits, from, to)),
        CValue::Float32(bits) => CValue::Float32(substitute_bitvector_variable(bits, from, to)),
        CValue::Float64(bits) => CValue::Float64(substitute_bitvector_variable(bits, from, to)),
        CValue::Pointer(pointer) => {
            CValue::Pointer(crate::kernel::eval::transport_pointer_load_pair(
                pointer,
                pointer
                    .clone()
                    .with_pointer(substitute_bitvector_variable_in_pointer(
                        pointer.pointer(),
                        from,
                        to,
                    ))
                    .map_designation(|designation| match designation {
                        PointerDesignation::Unresolved(variable) => {
                            PointerDesignation::Unresolved(*variable)
                        }
                        // Follow the same snapshot substitution and DAG memo
                        // used by a scalar MemoryLoad, then re-intern the pair.
                        PointerDesignation::Loaded(identity) => {
                            let address = substitute_bitvector_variable_in_pointer(
                                identity.address(),
                                from,
                                to,
                            );
                            let memory = if address == *identity.address() {
                                identity.memory().clone()
                            } else {
                                super::memory_resolution::canonical_load_projection_source(
                                    identity.memory(),
                                    identity.address(),
                                )
                                .unwrap_or_else(|| identity.memory().clone())
                            };
                            PointerDesignation::Loaded(PointerLoadIdentity::new(
                                substitute_bitvector_variable_in_shared_memory(&memory, from, to),
                                address,
                            ))
                        }
                        PointerDesignation::Object {
                            root,
                            path,
                            base,
                            element_type,
                            stride,
                            count,
                        } => PointerDesignation::Object {
                            root: substitute_bitvector_variable_in_pointer(root, from, to),
                            path: path
                                .iter()
                                .map(|selection| match selection {
                                    PointerDomainSelection::Member(name) => {
                                        PointerDomainSelection::Member(name.clone())
                                    }
                                    PointerDomainSelection::Element(index) => {
                                        PointerDomainSelection::Element(
                                            substitute_bitvector_variable_in_integer(
                                                index.as_ref(),
                                                from,
                                                to,
                                            )
                                            .into(),
                                        )
                                    }
                                })
                                .collect::<Vec<_>>()
                                .into(),
                            base: substitute_bitvector_variable_in_pointer(base, from, to),
                            element_type: *element_type,
                            stride: *stride,
                            count: substitute_bitvector_variable_in_integer(
                                count.as_ref(),
                                from,
                                to,
                            )
                            .into(),
                        },
                        PointerDesignation::InputSelected {
                            input,
                            origin,
                            path,
                            base,
                            element_type,
                            stride,
                            count,
                        } => {
                            let input = match input {
                                CNativeInputIdentity::Unresolved(variable) => {
                                    CNativeInputIdentity::Unresolved(*variable)
                                }
                                CNativeInputIdentity::Loaded(identity) => {
                                    let address = substitute_bitvector_variable_in_pointer(
                                        identity.address(),
                                        from,
                                        to,
                                    );
                                    let memory = if address == *identity.address() {
                                        identity.memory().clone()
                                    } else {
                                        super::memory_resolution::canonical_load_projection_source(
                                            identity.memory(),
                                            identity.address(),
                                        )
                                        .unwrap_or_else(|| identity.memory().clone())
                                    };
                                    CNativeInputIdentity::Loaded(PointerLoadIdentity::new(
                                        substitute_bitvector_variable_in_shared_memory(
                                            &memory, from, to,
                                        ),
                                        address,
                                    ))
                                }
                            };
                            PointerDesignation::InputSelected {
                                input,
                                origin: substitute_bitvector_variable_in_pointer(origin, from, to),
                                path: path
                                    .iter()
                                    .map(|part| match part {
                                        PointerDomainSelection::Member(name) => {
                                            PointerDomainSelection::Member(name.clone())
                                        }
                                        PointerDomainSelection::Element(index) => {
                                            PointerDomainSelection::Element(
                                                substitute_bitvector_variable_in_integer(
                                                    index.as_ref(),
                                                    from,
                                                    to,
                                                )
                                                .into(),
                                            )
                                        }
                                    })
                                    .collect::<Vec<_>>()
                                    .into(),
                                base: substitute_bitvector_variable_in_pointer(base, from, to),
                                element_type: *element_type,
                                stride: *stride,
                                count: substitute_bitvector_variable_in_integer(
                                    count.as_ref(),
                                    from,
                                    to,
                                )
                                .into(),
                            }
                        }
                    }),
            ))
        }
    }
}

fn pointer_capture_avoiding_quantifier_body(
    binder: Variable,
    sort: &Sort,
    body: &Proposition,
    from: Variable,
    replacement: &Pointer,
) -> (Proposition, Variable) {
    let mut replacement_variables = BTreeSet::new();
    collect_pointer_bound_variables(replacement, &mut replacement_variables);
    if !replacement_variables.contains(&binder) || !matches!(sort, Sort::CPointer(_)) {
        return (body.clone(), binder);
    }
    let mut reserved = crate::kernel::proposition_variables(body);
    reserved.insert(from);
    reserved.insert(binder);
    reserved.extend(replacement_variables);
    let fresh = KernelVariableGenerator::fresh_for(0, reserved).next();
    let pointer = match sort {
        Sort::CPointer(CType::FunctionPointer(_)) => Pointer::symbolic_function(fresh),
        Sort::CPointer(_) => Pointer::symbolic(fresh),
        _ => unreachable!("pointer capture avoidance only handles pointer binders"),
    };
    (
        substitute_pointer_variable_in_proposition(body, binder, &pointer),
        fresh,
    )
}

fn substitute_pointer_variable_in_term(term: &Term, from: Variable, to: &Pointer) -> Term {
    match term {
        Term::Condition(condition) => Term::Condition(substitute_pointer_variable_in_condition(
            condition, from, to,
        )),
        Term::Integer(_) => {
            crate::kernel::proof::term_rewrite::TermRewrite::for_pointer_variable(from, to)
                .term(term)
        }
        Term::Bitvector32(_) | Term::PointerOffset(_) => term.clone(),
        Term::CValue(value) => {
            Term::CValue(substitute_pointer_variable_in_c_value(value, from, to))
        }
        Term::Sequence(sequence) => {
            Term::Sequence(substitute_pointer_variable_in_sequence(sequence, from, to))
        }
        Term::Algebraic(term) => Term::Algebraic(AlgebraicTerm {
            algebraic_type: term.algebraic_type.clone(),
            node: substitute_pointer_variable_in_algebraic_term_node(term, from, to),
        }),
        Term::CExpressionOutcome(outcome) => Term::CExpressionOutcome(
            substitute_pointer_variable_in_c_expression_outcome(outcome, from, to),
        ),
        Term::CStatementOutcome(outcome) => Term::CStatementOutcome(Box::new(
            substitute_pointer_variable_in_c_statement_outcome(outcome, from, to),
        )),
        Term::CFunctionOutcome(outcome) => Term::CFunctionOutcome(Box::new(
            substitute_pointer_variable_in_c_function_outcome(outcome, from, to),
        )),
        Term::CMemory(memory) => {
            Term::CMemory(substitute_pointer_variable_in_memory(memory, from, to))
        }
        Term::CState(state) => Term::CState(Box::new(substitute_pointer_variable_in_c_state(
            state, from, to,
        ))),
    }
}

fn substitute_pointer_variable_in_algebraic_term_node(
    term: &AlgebraicTerm,
    from: Variable,
    to: &Pointer,
) -> AlgebraicTermNode {
    match &term.node {
        AlgebraicTermNode::Variable(variable) => AlgebraicTermNode::Variable(*variable),
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
    }
}

fn substitute_pointer_variable_in_algebraic_term(
    term: &AlgebraicTerm,
    from: Variable,
    to: &Pointer,
) -> AlgebraicTerm {
    AlgebraicTerm {
        algebraic_type: term.algebraic_type.clone(),
        node: substitute_pointer_variable_in_algebraic_term_node(term, from, to),
    }
}

fn substitute_pointer_variable_in_condition(
    condition: &ConditionTerm,
    from: Variable,
    to: &Pointer,
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
        ConditionTerm::PointerEqual(left, right) => ConditionTerm::pointer_equal(
            substitute_pointer_variable_in_pointer(left, from, to),
            substitute_pointer_variable_in_pointer(right, from, to),
        ),
        condition => condition.clone(),
    }
}

fn substitute_pointer_variable_in_c_value(value: &CValue, from: Variable, to: &Pointer) -> CValue {
    let Term::CValue(value) =
        crate::kernel::proof::term_rewrite::TermRewrite::for_pointer_variable(from, to)
            .term(&Term::CValue(value.clone()))
    else {
        unreachable!("C value rewriting preserves its carrier")
    };
    value
}

fn substitute_pointer_variable_in_pointer(
    pointer: &Pointer,
    from: Variable,
    to: &Pointer,
) -> Pointer {
    if matches!(&pointer.block, PointerBlock::PureFunctionApplication(_)) {
        let term = Term::CValue(CValue::pointer(pointer.clone()));
        let Term::CValue(CValue::Pointer(result)) =
            crate::kernel::proof::term_rewrite::TermRewrite::for_pointer_variable(from, to)
                .term(&term)
        else {
            unreachable!()
        };
        return result.into_pointer();
    }
    if matches!(pointer.block, PointerBlock::ExternalObject(variable) if variable == from) {
        let identity = to.object_identity();
        return Pointer {
            block: identity.block,
            offset: PointerOffsetTerm::add(identity.offset, pointer.offset.clone()),
        };
    }
    let replaces_block = matches!(
        (&pointer.block, &to.block),
        (PointerBlock::Symbolic(variable), _) | (PointerBlock::FunctionSymbolic(variable), _)
            if *variable == from
    );
    let offset = pointer.offset.clone();
    if replaces_block {
        Pointer {
            block: to.block.clone(),
            offset: PointerOffsetTerm::add(to.offset.clone(), offset),
        }
    } else {
        pointer.clone()
    }
}

fn substitute_pointer_variable_in_c_expression(
    expression: &CExpression,
    from: Variable,
    to: &Pointer,
) -> CExpression {
    match expression {
        CExpression::Value(value) => {
            CExpression::Value(substitute_pointer_variable_in_c_value(value, from, to))
        }
        CExpression::Variable(_) | CExpression::FunctionAddress(_) => expression.clone(),
        CExpression::Cast {
            expression,
            target_type,
            integer_mode,
            pointee_struct,
            pointee_volatile,
            pointee_constant,
            explicit_qualification,
        } => CExpression::Cast {
            expression: Box::new(substitute_pointer_variable_in_c_expression(
                expression, from, to,
            )),
            target_type: *target_type,
            integer_mode: *integer_mode,
            pointee_struct: pointee_struct.clone(),
            pointee_volatile: *pointee_volatile,
            pointee_constant: *pointee_constant,
            explicit_qualification: *explicit_qualification,
        },
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => CExpression::Conditional {
            condition: Box::new(substitute_pointer_variable_in_c_expression(
                condition, from, to,
            )),
            then_branch: Box::new(substitute_pointer_variable_in_c_expression(
                then_branch,
                from,
                to,
            )),
            else_branch: Box::new(substitute_pointer_variable_in_c_expression(
                else_branch,
                from,
                to,
            )),
        },
        CExpression::FloatClassification {
            expression,
            classification,
        } => CExpression::FloatClassification {
            expression: Box::new(substitute_pointer_variable_in_c_expression(
                expression, from, to,
            )),
            classification: *classification,
        },
        CExpression::FloatNegate(expression) => CExpression::FloatNegate(Box::new(
            substitute_pointer_variable_in_c_expression(expression, from, to),
        )),
        CExpression::ArrayRowAddress {
            array,
            index,
            shape,
            element_type,
        } => CExpression::ArrayRowAddress {
            array: Box::new(substitute_pointer_variable_in_c_expression(array, from, to)),
            index: Box::new(substitute_pointer_variable_in_c_expression(index, from, to)),
            shape: shape.clone(),
            element_type: *element_type,
        },
        CExpression::RecordPointerOffset {
            pointer,
            index,
            layout,
            subtract,
        } => CExpression::RecordPointerOffset {
            pointer: Box::new(substitute_pointer_variable_in_c_expression(
                pointer, from, to,
            )),
            index: Box::new(substitute_pointer_variable_in_c_expression(index, from, to)),
            layout: layout.clone(),
            subtract: *subtract,
        },
        CExpression::MemberAddress { object, selection } => CExpression::MemberAddress {
            object: Box::new(substitute_pointer_variable_in_c_expression(
                object, from, to,
            )),
            selection: selection.clone(),
        },
        CExpression::AddressOf(body) => CExpression::AddressOf(Box::new(
            substitute_pointer_variable_in_c_expression(body, from, to),
        )),
        CExpression::CheckedObjectAddress(body) => CExpression::CheckedObjectAddress(Box::new(
            substitute_pointer_variable_in_c_expression(body, from, to),
        )),
        CExpression::PointerOffsetBytes { pointer, bytes } => CExpression::PointerOffsetBytes {
            pointer: Box::new(substitute_pointer_variable_in_c_expression(
                pointer, from, to,
            )),
            bytes: *bytes,
        },
        CExpression::PointerAligned { pointer, alignment } => CExpression::PointerAligned {
            pointer: Box::new(substitute_pointer_variable_in_c_expression(
                pointer, from, to,
            )),
            alignment: *alignment,
        },
        CExpression::Load(body) => CExpression::Load(Box::new(
            substitute_pointer_variable_in_c_expression(body, from, to),
        )),
        CExpression::TypedLoad {
            pointer,
            value_type,
            volatile,
            pointee_constant,
            source,
        } => CExpression::TypedLoad {
            pointer: Box::new(substitute_pointer_variable_in_c_expression(
                pointer, from, to,
            )),
            value_type: *value_type,
            volatile: *volatile,
            pointee_constant: *pointee_constant,
            source: source.clone(),
        },
        CExpression::Not(body) | CExpression::BitwiseNot(body) => {
            let body = Box::new(substitute_pointer_variable_in_c_expression(body, from, to));
            match expression {
                CExpression::Not(_) => CExpression::Not(body),
                CExpression::BitwiseNot(_) => CExpression::BitwiseNot(body),
                _ => unreachable!("the combined unary expression arm is exhaustive"),
            }
        }
        crate::kernel::binary_c_operation!(left, right) | CExpression::Index(left, right) => {
            let left = Box::new(substitute_pointer_variable_in_c_expression(left, from, to));
            let right = Box::new(substitute_pointer_variable_in_c_expression(right, from, to));
            match expression {
                CExpression::LessThan(_, _) => CExpression::LessThan(left, right),
                CExpression::LessEqual(_, _) => CExpression::LessEqual(left, right),
                CExpression::GreaterThan(_, _) => CExpression::GreaterThan(left, right),
                CExpression::GreaterEqual(_, _) => CExpression::GreaterEqual(left, right),
                CExpression::Equal(_, _) => CExpression::Equal(left, right),
                CExpression::NotEqual(_, _) => CExpression::NotEqual(left, right),
                CExpression::And(_, _) => CExpression::And(left, right),
                CExpression::Or(_, _) => CExpression::Or(left, right),
                CExpression::Add(_, _) => CExpression::Add(left, right),
                CExpression::Subtract(_, _) => CExpression::Subtract(left, right),
                CExpression::Multiply(_, _) => CExpression::Multiply(left, right),
                CExpression::Divide(_, _) => CExpression::Divide(left, right),
                CExpression::Remainder(_, _) => CExpression::Remainder(left, right),
                CExpression::ShiftLeft(_, _) => CExpression::ShiftLeft(left, right),
                CExpression::ShiftRight(_, _) => CExpression::ShiftRight(left, right),
                CExpression::BitwiseAnd(_, _) => CExpression::BitwiseAnd(left, right),
                CExpression::BitwiseOr(_, _) => CExpression::BitwiseOr(left, right),
                CExpression::BitwiseXor(_, _) => CExpression::BitwiseXor(left, right),
                CExpression::Index(_, _) => CExpression::Index(left, right),
                _ => unreachable!("the combined binary expression arm is exhaustive"),
            }
        }
    }
}

pub(crate) fn substitute_pointer_variable_in_memory(
    memory: &CMemory,
    from: Variable,
    to: &Pointer,
) -> CMemory {
    let (native_record_inputs, native_record_input_origins) = memory.map_native_record_inputs(
        |pointer| {
            let CValue::Pointer(pointer) =
                substitute_pointer_variable_in_c_value(&CValue::Pointer(pointer.clone()), from, to)
            else {
                unreachable!("pointer substitution preserves the carrier")
            };
            pointer
        },
        |count| {
            let Term::Integer(count) =
                crate::kernel::proof::term_rewrite::TermRewrite::for_pointer_variable(from, to)
                    .term(&Term::Integer(count.as_ref().clone()))
            else {
                unreachable!("integer rewriting preserves its carrier")
            };
            count.into()
        },
    );
    let mut result = CMemory {
        construction: None,
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
                    substitute_pointer_variable_in_c_value(value, from, to),
                )
            },
            // A symbolic storage run's pointer slots each point into the
            // block their own load variable names, so substituting one of
            // those variables changes that slot alone.
            |run| {
                (*run.value_mode() == crate::kernel::primitives::RunValueMode::SymbolicStorage
                    && run.element_type().is_pointer())
                .then(|| run_slot_named_by_load_variable(run, from))
                .flatten()
            },
        )),
        union_cells: std::sync::Arc::new(
            memory
                .union_cells
                .iter()
                .map(|((pointer, c_type), value)| {
                    (
                        (
                            substitute_pointer_variable_in_pointer(pointer, from, to),
                            *c_type,
                        ),
                        substitute_pointer_variable_in_c_value(value, from, to),
                    )
                })
                .collect(),
        ),
        forgotten: std::sync::Arc::new(CForgottenKnowledge {
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
        heap: std::sync::Arc::new(CHeapMemory {
            native_record_inputs,
            native_record_input_origins,
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
            object_input_domains: memory.map_object_input_domains(|base| {
                substitute_pointer_variable_in_pointer(base, from, to)
            }),
            scalar_input_domains: memory.map_scalar_input_domains(|base| {
                substitute_pointer_variable_in_pointer(base, from, to)
            }),
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
            initialized: memory
                .heap
                .initialized
                .map_pointers(|pointer| substitute_pointer_variable_in_pointer(pointer, from, to)),
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
                    let CValue::Pointer(old_pointer) = substitute_pointer_variable_in_c_value(
                        &CValue::Pointer(pending.old_pointer.clone()),
                        from,
                        to,
                    ) else {
                        unreachable!("pointer substitution preserves its carrier")
                    };
                    (
                        substitute_pointer_variable_in_pointer(base, from, to),
                        CPendingReallocation {
                            old_pointer,
                            old_bytes: pending.old_bytes.clone(),
                            zeroed_prefix: pending.zeroed_prefix.clone(),
                            initialized_prefix: pending.initialized_prefix.clone(),
                            copied_cells: pending
                                .copied_cells
                                .iter()
                                .map(|(offset, value)| {
                                    (
                                        offset.clone(),
                                        substitute_pointer_variable_in_c_value(value, from, to),
                                    )
                                })
                                .collect(),
                        },
                    )
                })
                .collect(),
        }),
    };
    result.record_diagnostic_transform(
        "substitute pointer variable",
        vec![memory.clone()],
        vec![
            CValue::pointer(Pointer::symbolic(from)),
            CValue::pointer(to.clone()),
        ],
    );
    result
}

fn substitute_pointer_variable_in_block(
    block: &PointerBlock,
    from: Variable,
    to: &Pointer,
) -> PointerBlock {
    match block {
        PointerBlock::PureFunctionApplication(_) => {
            substitute_pointer_variable_in_pointer(
                &Pointer {
                    block: block.clone(),
                    offset: PointerOffsetTerm::Constant(0),
                },
                from,
                to,
            )
            .block
        }
        PointerBlock::ExternalObject(variable) if *variable == from => to.object_identity().block,
        PointerBlock::Symbolic(variable) | PointerBlock::FunctionSymbolic(variable)
            if *variable == from =>
        {
            to.block.clone()
        }
        block => block.clone(),
    }
}

fn substitute_pointer_variable_in_spec_memory(
    memory: &SpecMemory,
    from: Variable,
    to: &Pointer,
) -> SpecMemory {
    match memory {
        SpecMemory::Current => SpecMemory::Current,
        SpecMemory::FunctionEntry => SpecMemory::FunctionEntry,
        SpecMemory::LoopEntry => SpecMemory::LoopEntry,
        SpecMemory::Fixed(memory) => {
            SpecMemory::Fixed(substitute_pointer_variable_in_memory(memory, from, to))
        }
    }
}

fn substitute_pointer_variable_in_spec_algebraic_expression(
    expression: &SpecAlgebraicExpression,
    from: Variable,
    to: &Pointer,
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
        SpecAlgebraicExpressionNode::Constructor { variant, fields } => {
            SpecAlgebraicExpressionNode::Constructor {
                variant: variant.clone(),
                fields: fields
                    .iter()
                    .map(|field| match field {
                        SpecAlgebraicValue::C(field) => SpecAlgebraicValue::C(
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
    };
    SpecAlgebraicExpression {
        algebraic_type: expression.algebraic_type.clone(),
        node,
    }
}

fn substitute_pointer_variable_in_spec_expression(
    expression: &SpecExpression,
    from: Variable,
    to: &Pointer,
) -> SpecExpression {
    match expression {
        SpecExpression::ResourceField { .. } => expression.clone(),
        SpecExpression::IntegerToMachine { value, destination } => {
            SpecExpression::IntegerToMachine {
                value: Box::new(substitute_pointer_variable_in_spec_integer(value, from, to)),
                destination: *destination,
            }
        }
        SpecExpression::Value(value) => {
            SpecExpression::Value(substitute_pointer_variable_in_c_value(value, from, to))
        }
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
        SpecExpression::CExpression(expression) => SpecExpression::CExpression(
            substitute_pointer_variable_in_c_expression(expression, from, to),
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
                SpecExpression::ShiftRight(_, _) => SpecExpression::ShiftRight(left, right),
                SpecExpression::BitwiseAnd(_, _) => SpecExpression::BitwiseAnd(left, right),
                SpecExpression::BitwiseOr(_, _) => SpecExpression::BitwiseOr(left, right),
                SpecExpression::BitwiseXor(_, _) => SpecExpression::BitwiseXor(left, right),
                _ => unreachable!("the combined spec binary arm is exhaustive"),
            }
        }
        SpecExpression::BitwiseNot(expression) => SpecExpression::BitwiseNot(Box::new(
            substitute_pointer_variable_in_spec_expression(expression, from, to),
        )),
        SpecExpression::Cast(expression, target_type) => SpecExpression::Cast(
            Box::new(substitute_pointer_variable_in_spec_expression(
                expression, from, to,
            )),
            *target_type,
        ),
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
        } => SpecExpression::PureFunctionApplication {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| {
                    substitute_pointer_variable_in_spec_function_argument(argument, from, to)
                })
                .collect(),
            result_type: *result_type,
        },
        SpecExpression::LoopEntrySnapshot(expression) => {
            SpecExpression::LoopEntrySnapshot(Box::new(
                substitute_pointer_variable_in_spec_expression(expression, from, to),
            ))
        }
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
            memory,
            pointer,
            value_type,
        } => SpecExpression::MemoryLoad {
            memory: substitute_pointer_variable_in_spec_memory(memory, from, to),
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
    to: &Pointer,
) -> SpecPureFunctionArgument {
    match argument {
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
            memory,
            pointer,
            element_type,
        } => SpecPureFunctionArgument::ArrayRef {
            memory: substitute_pointer_variable_in_spec_memory(memory, from, to),
            pointer: substitute_pointer_variable_in_spec_expression(pointer, from, to),
            element_type: *element_type,
        },
    }
}

fn substitute_pointer_variable_in_spec_integer(
    expression: &SpecIntegerExpression,
    from: Variable,
    to: &Pointer,
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
    to: &Pointer,
) -> SpecProposition {
    match proposition {
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
            c_type,
            body,
        } => SpecProposition::ForAllPointer {
            name: name.clone(),
            variable: *variable,
            c_type: *c_type,
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
            c_type,
            body,
        } => SpecProposition::ExistsPointer {
            name: name.clone(),
            variable: *variable,
            c_type: *c_type,
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
                    SpecPredicateArgument::ArrayRef { memory, pointer } => {
                        SpecPredicateArgument::ArrayRef {
                            memory: substitute_pointer_variable_in_spec_memory(memory, from, to),
                            pointer: substitute_pointer_variable_in_spec_expression(
                                pointer, from, to,
                            ),
                        }
                    }
                })
                .collect(),
        },
        SpecProposition::ResourceSeparate { left, right } => SpecProposition::ResourceSeparate {
            left: substitute_pointer_variable_in_spec_resource(left, from, to),
            right: substitute_pointer_variable_in_spec_resource(right, from, to),
        },
        SpecProposition::ResourceContains { parent, child } => SpecProposition::ResourceContains {
            parent: substitute_pointer_variable_in_spec_resource(parent, from, to),
            child: substitute_pointer_variable_in_spec_resource(child, from, to),
        },
        SpecProposition::MemoryInitialized {
            memory,
            base,
            bytes,
        } => SpecProposition::MemoryInitialized {
            memory: substitute_pointer_variable_in_spec_memory(memory, from, to),
            base: substitute_pointer_variable_in_spec_expression(base, from, to),
            bytes: *bytes,
        },
        SpecProposition::MemoryLoadable {
            memory,
            base,
            start,
            end,
            element_width,
        } => SpecProposition::MemoryLoadable {
            memory: substitute_pointer_variable_in_spec_memory(memory, from, to),
            base: substitute_pointer_variable_in_spec_expression(base, from, to),
            start: substitute_pointer_variable_in_spec_expression(start, from, to),
            end: substitute_pointer_variable_in_spec_expression(end, from, to),
            element_width: *element_width,
        },
        SpecProposition::Defined(expression) => SpecProposition::Defined(
            substitute_pointer_variable_in_spec_expression(expression, from, to),
        ),
    }
}

fn substitute_pointer_variable_in_spec_sequence(
    sequence: &SpecSequenceExpression,
    from: Variable,
    to: &Pointer,
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
    to: &Pointer,
) -> SpecResource {
    match resource {
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
        let value = CValue::typed_pointer(Pointer::symbolic(Variable(918)), CType::Int32Pointer)
            .with_pointer_pointee_constant(true)
            .with_pointer_pointee_volatile(true);
        assert_eq!(
            substitute_bitvector_variable_in_c_value(
                &value,
                Variable(919),
                &Bitvector32Term::Constant(0)
            ),
            value
        );
        assert_eq!(
            substitute_pointer_variable_in_c_value(&value, Variable(919), &Pointer::null()),
            value
        );
        let replaced =
            substitute_pointer_variable_in_c_value(&value, Variable(918), &Pointer::null());
        assert!(matches!(replaced, CValue::Pointer(pointer)
            if pointer.is_null() && pointer.pointee_constant() && pointer.pointee_volatile()));

        let value = CValue::typed_pointer(
            Pointer {
                block: "qualified-substitution".into(),
                offset: PointerOffsetTerm::Int32Scaled {
                    value: Box::new(Bitvector32Term::Variable(Variable(919))),
                    byte_width: 4,
                },
            },
            CType::Int32Pointer,
        )
        .with_pointer_pointee_constant(true)
        .with_pointer_pointee_volatile(true);
        let replaced = substitute_bitvector_variable_in_c_value(
            &value,
            Variable(919),
            &Bitvector32Term::Constant(1),
        );
        assert!(matches!(replaced, CValue::Pointer(pointer)
            if pointer.offset.as_const() == Some(4)
                && pointer.pointee_constant() && pointer.pointee_volatile()));
    }

    #[test]
    fn pointee_const_return_survives_both_substitutions() {
        let function = CFunction::new(
            CType::UInt8Pointer,
            "text",
            Vec::new(),
            c_return(c_int32_literal(0)),
        )
        .with_return_pointee_constant(true);
        assert!(
            substitute_bitvector_variable_in_c_function(
                &function,
                Variable(914),
                &Bitvector32Term::Constant(0),
            )
            .return_pointee_is_constant()
        );
        assert!(
            substitute_pointer_variable_in_c_function(
                &function,
                Variable(914),
                &Pointer::symbolic(Variable(915)),
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
                Bitvector32Term::Variable(Variable(701)),
            ),
        ));
        let term = Bitvector32Term::IntegerToMachine {
            value: payload.clone(),
            destination: crate::kernel::MachineIntegerType::UInt32,
        };
        let replaced = substitute_bitvector_variable(
            &term,
            Variable(701),
            &Bitvector32Term::Variable(Variable(702)),
        );
        let Bitvector32Term::IntegerToMachine { value, destination } = replaced else {
            panic!("substitution changed the carrier shape")
        };
        assert_eq!(destination, crate::kernel::MachineIntegerType::UInt32);
        assert!(matches!(value.as_ref(), IntegerTerm::Machine(machine)
            if machine.ty() == crate::kernel::MachineIntegerType::Int32
                && machine.value() == &Bitvector32Term::Variable(Variable(702))));
    }

    #[test]
    fn integer_to_machine_substitution_reuses_unchanged_shared_payload() {
        let payload = crate::kernel::SharedIntegerTerm::from(IntegerTerm::Variable(Variable(703)));
        let term = Bitvector32Term::IntegerToMachine {
            value: payload.clone(),
            destination: crate::kernel::MachineIntegerType::Int32,
        };
        let replaced =
            substitute_bitvector_variable(&term, Variable(704), &Bitvector32Term::Constant(0));
        let Bitvector32Term::IntegerToMachine { value, .. } = replaced else {
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
        let source = Pointer {
            block: PointerBlock::Symbolic(binder),
            offset: PointerOffsetTerm::Constant(8),
        };
        let replacement = Pointer {
            block: PointerBlock::Symbolic(Variable(611)),
            offset: PointerOffsetTerm::Constant(4),
        };
        let expected = Pointer {
            block: replacement.block.clone(),
            offset: PointerOffsetTerm::Constant(12),
        };
        let bits = Bitvector32Term::PointerAddress(Box::new(source));
        let term =
            IntegerTerm::from_machine(crate::kernel::MachineIntegerType::UInt64, bits.clone())
                .unwrap();
        let proposition = Proposition::ConditionIs(
            ConditionTerm::integer_equal(term, IntegerTerm::constant_i64(0)),
            true,
        );
        let rewritten =
            substitute_pointer_variable_in_proposition(&proposition, binder, &replacement);
        let Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, _), true) = rewritten else {
            panic!("unexpected proposition")
        };
        let IntegerTerm::Machine(observation) = left.as_ref() else {
            panic!("missing observation")
        };
        assert_eq!(
            observation.value(),
            &Bitvector32Term::PointerAddress(Box::new(expected.clone()))
        );

        let spec = SpecProposition::IntegerComparison {
            left: SpecIntegerExpression::FromMachine(Box::new(SpecExpression::Value(
                CValue::UInt64(bits),
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
            SpecExpression::Value(CValue::UInt64(Bitvector32Term::PointerAddress(Box::new(
                expected
            ))))
        );
    }
}

#[cfg(test)]
mod integer_function_traversal_tests {
    use super::*;

    #[test]
    fn integer_applications_rewrite_c_and_nested_integer_arguments() {
        let from = Variable(817);
        let machine = Bitvector32Term::Variable(from);
        let make = |machine: Bitvector32Term| {
            IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
                "observed".into(),
                vec![
                    PureFunctionArgument::Value(CValue::Int32(machine.clone())),
                    PureFunctionArgument::Integer(
                        IntegerTerm::from_machine(MachineIntegerType::Int32, machine)
                            .unwrap()
                            .into(),
                    ),
                ],
            ))
        };
        let original = make(machine);
        let expected = make(Bitvector32Term::Variable(Variable(818)));
        assert_eq!(
            substitute_bitvector_variable_in_integer(
                &original,
                from,
                &Bitvector32Term::Variable(Variable(818))
            ),
            expected
        );
        assert_eq!(
            crate::kernel::proof::term_rewrite::TermRewrite::for_bits(
                &Bitvector32Term::Variable(from),
                &Bitvector32Term::Variable(Variable(818))
            )
            .term(&Term::Integer(original)),
            Term::Integer(expected)
        );
    }

    #[test]
    fn shared_integer_application_substitution_scales_with_dag_size() {
        let from = Variable(831);
        let mut samples = Vec::new();
        for depth in [8, 16, 32, 64] {
            let mut term: SharedIntegerTerm = IntegerTerm::from_machine(
                MachineIntegerType::Int32,
                Bitvector32Term::Variable(from),
            )
            .unwrap()
            .into();
            for _ in 0..depth {
                term = IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
                    "pair".into(),
                    vec![
                        PureFunctionArgument::Integer(term.clone()),
                        PureFunctionArgument::Integer(term),
                    ],
                ))
                .into();
            }
            let (changed, work) = crate::instrumentation::measure_deterministic_work(|| {
                substitute_bitvector_variable_in_integer(
                    &term,
                    from,
                    &Bitvector32Term::Variable(Variable(832)),
                )
            });
            assert_ne!(&changed, term.as_ref());
            assert!(work > 0);
            samples.push(work);
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1] <= pair[0] * 3,
                "application substitution expanded the DAG: {samples:?}"
            );
        }
    }

    #[test]
    fn public_integer_substitution_keeps_array_ref_snapshots_opaque() {
        let source = Variable(840);
        let pointer = CValue::Pointer(CPointerValue::new(
            Pointer {
                block: PointerBlock::Symbolic(Variable(841)),
                offset: PointerOffsetTerm::Constant(0),
            },
            CType::VoidPointer,
        ));
        let make_memory = |count: u64| {
            let mut memory = CMemory::new().with_block("array", 8);
            for index in 0..count {
                memory = memory.with_block(PointerBlock::Heap(index + 1), 8);
            }
            memory
        };
        let make = |memory: CMemory| {
            Proposition::Equal(
                Term::Integer(IntegerTerm::PureFunctionApplication(
                    SharedPureApplication::intern(
                        "observe_array".into(),
                        vec![
                            PureFunctionArgument::Integer(IntegerTerm::var(source).into()),
                            PureFunctionArgument::ArrayRef {
                                memory,
                                pointer: pointer.clone(),
                                element_type: CType::UInt8,
                            },
                        ],
                    ),
                )),
                Term::Integer(IntegerTerm::constant_i64(0)),
            )
        };
        let snapshot = |proposition: Proposition| {
            let Proposition::Equal(Term::Integer(value), _) = proposition else {
                panic!("expected Integer equality")
            };
            let IntegerTerm::PureFunctionApplication(application) = value else {
                panic!("expected pure Integer application")
            };
            let [
                PureFunctionArgument::Integer(integer),
                PureFunctionArgument::ArrayRef { memory, .. },
            ] = application.arguments()
            else {
                panic!("expected Integer and ArrayRef arguments")
            };
            assert!(matches!(integer.as_ref(), IntegerTerm::Constant(_)));
            memory.clone()
        };
        // Construct the selected term before measuring its substitution. Pin
        // a constant ceiling across snapshot sizes rather than exact equality
        // between two totals: fixed interning/bookkeeping costs can differ,
        // but traversing even the 256-block snapshot would exceed this bound.
        for count in [0, 16, 256, 4096] {
            let memory = make_memory(count);
            let input = make(memory.clone());
            let replacement = IntegerTerm::constant_i64(7);
            let (changed, work) = crate::instrumentation::measure_deterministic_work(|| {
                substitute_integer_variable_in_pure_proposition(&input, source, &replacement)
                    .expect("snapshot substitution should be supported")
            });
            assert!(std::sync::Arc::ptr_eq(
                &snapshot(changed).blocks,
                &memory.blocks
            ));
            assert!(work > 0 && work <= 128, "{count} unrelated blocks: {work}");
        }
    }
}

#[cfg(test)]
mod integer_match_substitution_scope_tests {
    use super::*;

    fn symbolic_match(body: IntegerTerm, binding: Variable) -> IntegerTerm {
        symbolic_match_with_binding(
            body,
            AlgebraicValue::C(CValue::Int32(Bitvector32Term::Variable(binding))),
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
                    variant: "Left".into(),
                    bindings: vec![AlgebraicValue::C(CValue::Int32(Bitvector32Term::Variable(
                        binding,
                    )))],
                    body: body.clone().into(),
                },
                AlgebraicIntegerMatchArm {
                    variant: "Right".into(),
                    bindings: vec![AlgebraicValue::C(CValue::Int32(Bitvector32Term::Variable(
                        binding,
                    )))],
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
                PureFunctionArgument::Value(CValue::Int32(Bitvector32Term::Variable(y))),
                PureFunctionArgument::Value(CValue::Int32(Bitvector32Term::Variable(x))),
                PureFunctionArgument::Value(CValue::Int32(Bitvector32Term::Variable(Variable(
                    9003,
                )))),
            ],
        ));
        let rewritten = substitute_bitvector_variable_in_integer(
            &symbolic_match(body, y),
            x,
            &Bitvector32Term::Variable(y),
        );
        let IntegerTerm::AlgebraicMatch { arms, .. } = rewritten else {
            panic!("expected algebraic match")
        };
        let AlgebraicValue::C(CValue::Int32(Bitvector32Term::Variable(fresh))) =
            arms[0].bindings[0]
        else {
            panic!("expected C binder")
        };
        assert_ne!(fresh, y);
        let IntegerTerm::PureFunctionApplication(application) = arms[0].body.as_ref() else {
            panic!("expected application body")
        };
        let [
            PureFunctionArgument::Value(CValue::Int32(Bitvector32Term::Variable(first))),
            PureFunctionArgument::Value(CValue::Int32(Bitvector32Term::Variable(second))),
            PureFunctionArgument::Value(CValue::Int32(Bitvector32Term::Variable(free))),
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
            vec![PureFunctionArgument::Value(CValue::Int32(
                Bitvector32Term::Variable(y),
            ))],
        ));
        let rewritten = substitute_bitvector_variable_in_integer(
            &symbolic_match(body, y),
            y,
            &Bitvector32Term::Variable(z),
        );
        let IntegerTerm::AlgebraicMatch { arms, .. } = rewritten else {
            panic!("expected algebraic match")
        };
        assert_eq!(
            arms[0].bindings[0],
            AlgebraicValue::C(CValue::Int32(Bitvector32Term::Variable(y),))
        );
        let IntegerTerm::PureFunctionApplication(application) = arms[0].body.as_ref() else {
            panic!("expected application body")
        };
        assert_eq!(
            application.arguments(),
            &[PureFunctionArgument::Value(CValue::Int32(
                Bitvector32Term::Variable(y),
            ))]
        );
    }

    #[test]
    fn substitution_freshens_each_integral_match_carrier() {
        let source = Variable(9040);
        let replacement = Variable(9041);
        let carriers = [
            CValue::Bool(Bitvector32Term::Variable(replacement)),
            CValue::Int8(Bitvector32Term::Variable(replacement)),
            CValue::Int16(Bitvector32Term::Variable(replacement)),
            CValue::Int32(Bitvector32Term::Variable(replacement)),
            CValue::UInt8(Bitvector32Term::Variable(replacement)),
            CValue::UInt16(Bitvector32Term::Variable(replacement)),
            CValue::UInt32(Bitvector32Term::Variable(replacement)),
            CValue::Int64(Bitvector32Term::Variable(replacement)),
            CValue::UInt64(Bitvector32Term::Variable(replacement)),
        ];
        for carrier in carriers {
            let body = IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
                "observe".into(),
                vec![PureFunctionArgument::Value(CValue::Int32(
                    Bitvector32Term::Variable(source),
                ))],
            ));
            let rewritten = substitute_bitvector_variable_in_integer(
                &symbolic_match_with_binding(body, AlgebraicValue::C(carrier.clone())),
                source,
                &Bitvector32Term::Variable(replacement),
            );
            let IntegerTerm::AlgebraicMatch { arms, .. } = rewritten else {
                panic!("expected algebraic match")
            };
            assert_ne!(arms[0].bindings[0], AlgebraicValue::C(carrier));
        }
    }

    #[test]
    fn match_substitution_shared_function_dag_scales_linearly() {
        let mut work = Vec::new();
        for depth in [8usize, 16, 32, 64] {
            let mut body = IntegerTerm::from_machine(
                MachineIntegerType::Int32,
                Bitvector32Term::Variable(Variable(9050)),
            )
            .unwrap();
            for _ in 0..depth {
                body = IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
                    "pair".into(),
                    vec![
                        PureFunctionArgument::Integer(body.clone().into()),
                        PureFunctionArgument::Integer(body.into()),
                    ],
                ));
            }
            let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
                substitute_bitvector_variable_in_integer(
                    &symbolic_match(body, Variable(9051)),
                    Variable(9050),
                    &Bitvector32Term::Variable(Variable(9052)),
                )
            });
            work.push(measured);
        }
        for pair in work.windows(2) {
            assert!(pair[1] <= pair[0] * 3, "function DAG expanded: {work:?}");
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

    #[test]
    fn match_substitution_shared_bodies_scale_linearly() {
        let mut work = Vec::new();
        for depth in [8usize, 16, 32, 64] {
            let mut body = IntegerTerm::from_machine(
                MachineIntegerType::Int32,
                Bitvector32Term::Variable(Variable(9020)),
            )
            .unwrap();
            for _ in 0..depth {
                body = shared_symbolic_match(body, Variable(9021));
            }
            let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
                substitute_bitvector_variable_in_integer(
                    &symbolic_match(body, Variable(9021)),
                    Variable(9020),
                    &Bitvector32Term::Variable(Variable(9022)),
                )
            });
            work.push(measured);
        }
        for pair in work.windows(2) {
            assert!(
                pair[1] <= pair[0] * 3,
                "match substitution expanded: {work:?}"
            );
        }
    }
}

#[cfg(test)]
mod integer_mixed_quantifier_tests {
    use super::*;

    fn application(integer: IntegerTerm, machine: Bitvector32Term) -> IntegerTerm {
        IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
            "opaque".into(),
            vec![
                PureFunctionArgument::Integer(integer.into()),
                PureFunctionArgument::Value(CValue::Int32(machine)),
            ],
        ))
    }

    #[test]
    fn integer_substitution_descends_function_and_reverse_conversion_arguments() {
        let from = Variable(87);
        let converted = Bitvector32Term::IntegerToMachine {
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
                    Bitvector32Term::IntegerToMachine {
                        value: IntegerTerm::constant_i64(9).into(),
                        destination: MachineIntegerType::Int32,
                    }
                )),
                Term::Integer(IntegerTerm::constant_i64(9)),
            )
        );
    }

    #[test]
    fn integer_atom_capture_avoidance_preserves_c_variable_carrier() {
        let from = Variable(88);
        let bound = Variable(89);
        let source = Proposition::ForAll {
            var: bound,
            sort: Sort::Integer,
            body: Box::new(Proposition::Equal(
                Term::Integer(application(
                    IntegerTerm::var(from),
                    Bitvector32Term::Variable(bound),
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
                    Bitvector32Term::Variable(bound)
                )),
                Term::Integer(IntegerTerm::var(fresh)),
            )
        );
    }

    #[test]
    fn integer_function_quantifier_substitution_preserves_shared_dags() {
        let from = Variable(90);
        let mut work = Vec::new();
        for depth in [8, 16, 32, 64] {
            let mut value = IntegerTerm::var(from);
            for _ in 0..depth {
                let child: SharedIntegerTerm = value.into();
                value = IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
                    "pair".into(),
                    vec![
                        PureFunctionArgument::Integer(child.clone()),
                        PureFunctionArgument::Integer(child),
                    ],
                ));
            }
            let source = Proposition::Equal(
                Term::Integer(value),
                Term::Integer(IntegerTerm::constant_i64(0)),
            );
            let (result, measured) = crate::instrumentation::measure_deterministic_work(|| {
                substitute_integer_variable_in_pure_proposition(
                    &source,
                    from,
                    &IntegerTerm::constant_i64(2),
                )
                .unwrap()
            });
            let Proposition::Equal(Term::Integer(mut value), _) = result else {
                panic!("equality lost")
            };
            for _ in 0..depth {
                let IntegerTerm::PureFunctionApplication(application) = value else {
                    panic!("application lost")
                };
                let [
                    PureFunctionArgument::Integer(left),
                    PureFunctionArgument::Integer(right),
                ] = application.arguments()
                else {
                    panic!("arguments lost")
                };
                assert_eq!(left.id(), right.id());
                value = left.as_ref().clone();
            }
            assert_eq!(value, IntegerTerm::constant_i64(2));
            work.push(measured);
        }
        for pair in work.windows(2) {
            assert!(pair[1] <= pair[0] * 3, "{work:?}");
        }
    }

    #[test]
    fn integer_witness_replacement_reserves_registered_pointer_integer() {
        let memory = crate::kernel::intern_c_memory(
            crate::kernel::CMemory::new().with_block("integer-witness-capture", 64),
        );
        let source = Variable(9_100);
        // This ID is intentionally shared by the replacement's registered
        // pointer and the nested Integer binder. The pointer occurrence is
        // free in the replacement even though the load itself is opaque.
        let free_index = Variable(9_101);
        let load = crate::kernel::eval::load_variable_for_exact_cell(
            &memory,
            &Pointer {
                block: PointerBlock::Concrete("integer-witness-capture".into()),
                offset: PointerOffsetTerm::Int32Scaled {
                    value: Box::new(Bitvector32Term::IntegerToMachine {
                        value: IntegerTerm::var(free_index).into(),
                        destination: MachineIntegerType::Int32,
                    }),
                    byte_width: 4,
                },
            },
            crate::kernel::LoadKind::Bits32,
            4,
        );
        let replacement = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            Bitvector32Term::Variable(load),
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
        let Bitvector32Term::Variable(rewritten_load) = machine.value() else {
            panic!("registered load was expanded into the memory snapshot")
        };
        let (rewritten_memory, rewritten_pointer) =
            crate::kernel::eval::registered_load_for_variable(rewritten_load)
                .expect("replacement load must retain its defining pointer");
        assert_eq!(rewritten_memory, memory);
        assert!(matches!(
            rewritten_pointer.offset,
            PointerOffsetTerm::Int32Scaled { value, .. }
                if matches!(value.as_ref(), Bitvector32Term::IntegerToMachine { value, .. }
                    if matches!(value.as_ref(), IntegerTerm::Variable(variable)
                if *variable == free_index))
        ));
    }

    fn c_int_equality(left: Variable, right: Variable) -> Proposition {
        Proposition::Equal(
            Term::Bitvector32(Bitvector32Term::Variable(left)),
            Term::Bitvector32(Bitvector32Term::Variable(right)),
        )
    }

    #[test]
    fn integer_substitution_freshens_nested_c_binder_by_carrier() {
        let source = Variable(9_200);
        let c_binder = Variable(9_201);
        let replacement = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            Bitvector32Term::Variable(c_binder),
        ));
        let proposition = Proposition::ForAll {
            var: c_binder,
            sort: Sort::CInt32,
            body: Box::new(Proposition::And(
                Box::new(Proposition::Equal(
                    Term::Integer(IntegerTerm::var(source)),
                    Term::Integer(IntegerTerm::constant_i64(0)),
                )),
                Box::new(c_int_equality(c_binder, c_binder)),
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
        assert!(matches!(
            *integer_goal,
            Proposition::Equal(
                Term::Integer(IntegerTerm::Machine(_)),
                Term::Integer(IntegerTerm::Constant(_))
            )
        ));
        assert_eq!(*c_goal, c_int_equality(fresh, fresh));
    }

    #[test]
    fn integer_source_is_not_shadowed_by_same_id_c_binder() {
        let source = Variable(9_210);
        let proposition = Proposition::ForAll {
            var: source,
            sort: Sort::CInt32,
            body: Box::new(Proposition::And(
                Box::new(Proposition::Equal(
                    Term::Integer(IntegerTerm::var(source)),
                    Term::Integer(IntegerTerm::constant_i64(0)),
                )),
                Box::new(c_int_equality(source, source)),
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
        assert_eq!(*c_goal, c_int_equality(source, source));
    }

    #[test]
    fn integer_substitution_preserves_nested_c_integer_pointer_scopes() {
        let source = Variable(9_220);
        let outer_c = Variable(9_221);
        let inner_integer = outer_c;
        let inner_pointer = Variable(9_222);
        let replacement = IntegerTerm::from_machine(
            MachineIntegerType::UInt64,
            Bitvector32Term::PointerAddress(Box::new(Pointer::symbolic(inner_pointer))),
        )
        .expect("pointer observations are Integer-valued");
        let pointer_value = |variable| {
            Term::CValue(CValue::Pointer(CPointerValue::new(
                Pointer::symbolic(variable),
                CType::Int32Pointer,
            )))
        };
        let proposition = Proposition::ForAll {
            var: outer_c,
            sort: Sort::CInt32,
            body: Box::new(Proposition::Exists {
                name: "inner".into(),
                var: inner_integer,
                sort: Sort::Integer,
                body: Box::new(Proposition::ForAll {
                    var: inner_pointer,
                    sort: Sort::CPointer(CType::Int32Pointer),
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
        assert!(matches!(
            *integer_goal,
            Proposition::Equal(Term::Integer(IntegerTerm::Machine(_)), Term::Integer(_))
        ));
        assert_eq!(
            *pointer_goal,
            Proposition::Equal(pointer_value(outer_c), pointer_value(pointer_after))
        );
    }

    #[test]
    fn integer_substitution_rejects_non_term_nested_sort() {
        let proposition = Proposition::ForAll {
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

    #[test]
    fn integer_substitution_nested_carrier_scopes_scale_with_shared_body() {
        let source = Variable(9_240);
        let mut work = Vec::new();
        for depth in [8, 16, 32, 64] {
            let mut body = Proposition::Equal(
                Term::Integer(IntegerTerm::var(source)),
                Term::Integer(IntegerTerm::constant_i64(0)),
            );
            for index in (0..depth).rev() {
                let variable = Variable(9_300 + (index / 2) as u64);
                body = if index % 2 == 0 {
                    Proposition::ForAll {
                        var: variable,
                        sort: Sort::CInt32,
                        body: Box::new(body),
                    }
                } else {
                    Proposition::Exists {
                        name: format!("integer{index}"),
                        var: variable,
                        sort: Sort::Integer,
                        body: Box::new(body),
                    }
                };
            }
            let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
                substitute_integer_variable_in_pure_proposition(
                    &body,
                    source,
                    &IntegerTerm::constant_i64(3),
                )
                .expect("nested carrier scopes should remain bounded")
            });
            work.push(measured);
        }
        for pair in work.windows(2) {
            assert!(
                pair[1] <= pair[0] * 3,
                "nested scope rewrite expanded: {work:?}"
            );
        }
    }
}

#[cfg(test)]
mod integer_range_fold_substitution_tests {
    use super::*;

    fn int32_index(start: Bitvector32Term, end: Bitvector32Term) -> IntegerRangeFoldIndex {
        IntegerRangeFoldIndex::Int32 {
            start: SharedIntegerRangeEndpoint::intern(start),
            end: SharedIntegerRangeEndpoint::intern(end),
        }
    }

    fn c_item(value: Variable) -> IntegerTerm {
        IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            Bitvector32Term::Variable(value),
        ))
    }

    fn c_item_value(value: Bitvector32Term) -> IntegerTerm {
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
                IntegerTerm::add(c_item(source), c_item(item)),
                c_item(free_y_plus_one),
            ),
            c_item(free_zero),
        );
        let fold = IntegerTerm::range_fold(
            int32_index(Bitvector32Term::Constant(0), Bitvector32Term::Constant(1)),
            IntegerTerm::var(accumulator),
            accumulator,
            item,
            body,
        );

        let replaced = substitute_bitvector_variable_in_integer(
            &fold,
            source,
            &Bitvector32Term::Variable(item),
        );
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
            if machine.value() == &Bitvector32Term::Variable(free_zero))
        );
        let IntegerTerm::Add(prefix, free_item) = left.as_ref() else {
            panic!("missing free y+1 term")
        };
        assert!(matches!(free_item.as_ref(), IntegerTerm::Machine(machine)
            if machine.value() == &Bitvector32Term::Variable(free_y_plus_one)));
        let IntegerTerm::Add(replaced_source, bound_item) = prefix.as_ref() else {
            panic!("missing source and item terms")
        };
        assert!(
            matches!(replaced_source.as_ref(), IntegerTerm::Machine(machine)
            if machine.value() == &Bitvector32Term::Variable(item))
        );
        assert!(matches!(bound_item.as_ref(), IntegerTerm::Machine(machine)
            if machine.value() == &Bitvector32Term::Variable(fresh_item)));
    }

    #[test]
    fn int32_fold_substitution_keeps_bound_item_but_rewrites_endpoints_and_initial() {
        let source = Variable(70_010);
        let accumulator = Variable(70_011);
        let body = c_item(source);
        let fold = IntegerTerm::range_fold(
            int32_index(
                Bitvector32Term::Variable(source),
                Bitvector32Term::Variable(source),
            ),
            c_item(source),
            accumulator,
            source,
            body,
        );

        let replaced =
            substitute_bitvector_variable_in_integer(&fold, source, &Bitvector32Term::Constant(9));
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
        assert_eq!(start.value(), &Bitvector32Term::Constant(9));
        assert_eq!(end.value(), &Bitvector32Term::Constant(9));
        // The initial value was `to_integer(source)`, so substituting a literal
        // decides that observation: it is the mathematical 9, the same Integer
        // an evaluation of `to_integer(9)` produces. The body's observation is
        // of the bound item and stays an observation.
        assert_eq!(initial.as_ref(), &IntegerTerm::constant_i64(9));
        assert!(matches!(body.as_ref(), IntegerTerm::Machine(machine)
            if machine.value() == &Bitvector32Term::Variable(source)));
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
            &Bitvector32Term::Constant(9),
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
        let body = c_item(item);
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
        let body = c_item(item);
        let malformed = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::UInt32,
            Bitvector32Term::Variable(Variable(70_054)),
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
    fn int32_fold_substitution_rewrites_registered_load_address_only() {
        let item = Variable(70_056);
        let memory = crate::kernel::intern_c_memory(CMemory::new().with_block("array", 16));
        let pointer = Pointer {
            block: PointerBlock::Concrete("array".into()),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(Bitvector32Term::Variable(item)),
                byte_width: 4,
            },
        };
        let load_variable = crate::kernel::eval::load_variable_for_cell(
            &memory,
            &pointer,
            crate::kernel::LoadKind::Bits32,
        );
        let (source_snapshot, _) =
            crate::kernel::eval::registered_load_for_variable(&load_variable)
                .expect("the source load must be registered");
        let body = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            Bitvector32Term::Variable(load_variable),
        ));
        let result = instantiate_integer_range_fold_step(
            &body,
            Variable(70_057),
            &IntegerTerm::constant_i64(0),
            item,
            &c_item_value(Bitvector32Term::Constant(0)),
            Some(MachineIntegerType::Int32),
        )
        .expect("the checked fold step should preserve the registered load");
        let IntegerTerm::Machine(machine) = result else {
            panic!("the machine load carrier was lost");
        };
        let Bitvector32Term::Variable(rewritten_load) = machine.value() else {
            panic!("the registered load was not reminted");
        };
        assert_ne!(*rewritten_load, load_variable);
        let (snapshot, pointer) = crate::kernel::eval::registered_load_for_variable(rewritten_load)
            .expect("the rewritten load must remain registered");
        assert_eq!(snapshot, source_snapshot);
        assert_eq!(pointer.offset, PointerOffsetTerm::Constant(0));
    }

    #[test]
    fn int32_fold_substitution_canonicalizes_nonzero_load_base() {
        let item = Variable(70_058);
        let memory = crate::kernel::intern_c_memory(CMemory::new().with_block("array", 16));
        let pointer = Pointer {
            block: PointerBlock::Concrete("array".into()),
            offset: PointerOffsetTerm::Add(
                Box::new(PointerOffsetTerm::Constant(4)),
                Box::new(PointerOffsetTerm::Int32Scaled {
                    value: Box::new(Bitvector32Term::Variable(item)),
                    byte_width: 4,
                }),
            ),
        };
        let load_variable = crate::kernel::eval::load_variable_for_cell(
            &memory,
            &pointer,
            crate::kernel::LoadKind::Bits32,
        );
        let (source_snapshot, _) =
            crate::kernel::eval::registered_load_for_variable(&load_variable)
                .expect("the source load must be registered");
        let body = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            Bitvector32Term::Variable(load_variable),
        ));
        let result = instantiate_integer_range_fold_step(
            &body,
            Variable(70_059),
            &IntegerTerm::constant_i64(0),
            item,
            &c_item_value(Bitvector32Term::Constant(0)),
            Some(MachineIntegerType::Int32),
        )
        .expect("the checked fold step should preserve the registered load");
        let IntegerTerm::Machine(machine) = result else {
            panic!("the machine load carrier was lost");
        };
        let Bitvector32Term::Variable(rewritten_load) = machine.value() else {
            panic!("the registered load was not reminted");
        };
        assert_ne!(*rewritten_load, load_variable);
        let (snapshot, pointer) = crate::kernel::eval::registered_load_for_variable(rewritten_load)
            .expect("the rewritten load must remain registered");
        assert_eq!(snapshot, source_snapshot);
        assert_eq!(pointer.offset, PointerOffsetTerm::Constant(4));
    }

    #[test]
    fn checked_machine_fold_substitution_rejects_work_exhaustion() {
        use crate::instrumentation::{self, TacticEvent, TacticWorkLimits, VerificationEvent};

        let source = Variable(70_060);
        let mut payload = Bitvector32Term::Variable(source);
        for _ in 0..64 {
            payload =
                Bitvector32Term::Add(Box::new(payload), Box::new(Bitvector32Term::Constant(1)));
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
                        &Bitvector32Term::Constant(7),
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

    fn reference_resource() -> CResource {
        let schema =
            ResourceFieldSchema::new(vec![("value".into(), ResourceFieldType::C(CType::Int32))])
                .unwrap();
        let leaf = ResourceInstance::new(
            Variable(200),
            "cell".into(),
            vec![
                AlgebraicValue::C(CValue::Int32(Bitvector32Term::Variable(Variable(100)))),
                AlgebraicValue::C(CValue::pointer(Pointer::symbolic(Variable(101)))),
            ]
            .into(),
            schema.clone(),
            vec![AlgebraicValue::C(CValue::Int32(Bitvector32Term::Variable(
                Variable(102),
            )))]
            .into(),
        )
        .unwrap();
        let middle = ResourceInstance::new(
            Variable(201),
            "middle".into(),
            vec![].into(),
            schema.clone(),
            vec![AlgebraicValue::C(int32(0))].into(),
        )
        .unwrap()
        .with_resource_arguments(vec![ResourceReference::from_instance(&leaf)]);
        CResource::Instance(
            ResourceInstance::new(
                Variable(202),
                "wrapper".into(),
                vec![].into(),
                schema,
                vec![AlgebraicValue::C(int32(0))].into(),
            )
            .unwrap()
            .with_resource_arguments(vec![ResourceReference::from_instance(&middle)]),
        )
    }

    #[test]
    fn substitutions_reach_nested_reference_values_without_changing_occurrences() {
        let source = reference_resource();
        let replaced = substitute_bitvector_variable_in_c_resource(
            &source,
            Variable(100),
            &Bitvector32Term::Constant(7),
        );
        let pointer = Pointer::symbolic(Variable(103));
        let replaced =
            substitute_pointer_variable_in_c_resource(&replaced, Variable(101), &pointer);
        let CResource::Instance(instance) = replaced else {
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
                AlgebraicValue::C(int32(7)),
                AlgebraicValue::C(CValue::pointer(pointer))
            ]
        );
        let mut variables = BTreeSet::new();
        collect_resource_bound_variables(&CResource::Instance(instance), &mut variables);
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
        crate::kernel::reasoning::collect_c_resource_bitvector_variables(
            &resource,
            &mut bitvectors,
        );
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

    fn observed(variable: Variable) -> IntegerTerm {
        IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            Bitvector32Term::Variable(variable),
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
        for sort in [Sort::CInt32, Sort::Integer] {
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
                            var: variable,
                            sort: sort.clone(),
                            body: Box::new(body),
                        }
                    }
                };
                let expected = if sort == Sort::CInt32 {
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
        let (complete, work) = instrumentation::measure_deterministic_work(|| {
            substitute_machine_constant_in_pure_proposition(&source, variable, 7)
        });
        assert!(complete.is_ok());
        for limit in [0, 4, 64, work - 1] {
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
                        assert!(instrumentation::exceeded_verification_limit_context().is_some());
                        instrumentation::emit(VerificationEvent::TacticFailed(tactic));
                        result
                    })
                },
            );
            assert_eq!(result, Err(IntegerPureSubstitutionError::WorkLimitExceeded));
        }
    }

    #[test]
    fn checked_singleton_substitution_scales_with_shared_integer_dags() {
        let variable = Variable(70_102);
        let samples = [8, 16, 32, 64].map(|depth| {
            let mut value = observed(variable);
            for _ in 0..depth {
                value = IntegerTerm::add(value.clone(), value.clone());
            }
            let source =
                Proposition::Equal(Term::Integer(value), Term::Integer(observed(variable)));
            let (result, work) = instrumentation::measure_deterministic_work(|| {
                substitute_machine_constant_in_pure_proposition(&source, variable, 7)
            });
            assert!(result.is_ok());
            assert!(
                work <= 128 * (depth + 1),
                "depth {depth}: {work} work units"
            );
            work
        });
        assert!(samples[3] <= samples[0] * 10, "{samples:?}");
    }

    #[test]
    fn checked_singleton_substitution_refuses_unsupported_carriers() {
        let source = Proposition::Predicate {
            name: "opaque".into(),
            arguments: vec![Term::CMemory(CMemory::new())],
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
                Term::Bitvector32(Bitvector32Term::Variable(variable)),
                Term::Integer(IntegerTerm::var(variable)),
            ],
        };
        assert_eq!(
            substitute_machine_constant_in_pure_proposition(&source, variable, 7),
            Ok(Proposition::Predicate {
                name: "opaque".into(),
                arguments: vec![
                    Term::Integer(IntegerTerm::constant_i64(7)),
                    Term::Bitvector32(Bitvector32Term::Constant(7)),
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
                var: Variable(80_000 + index),
                sort: Sort::CInt32,
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
}

#[cfg(test)]
mod pointer_integer_structural_tests {
    use super::*;

    #[test]
    fn pointer_integer_substitution_preserves_exact_origin_and_its_dependencies() {
        let numeric = Variable(983_201);
        let identity = Variable(983_202);
        let block = Variable(983_203);
        let pointer = CPointerValue::new(
            Pointer {
                block: PointerBlock::Symbolic(block),
                offset: PointerOffsetTerm::Int32Scaled {
                    value: Bitvector32Term::Variable(numeric).into(),
                    byte_width: 4,
                },
            },
            CType::Int32Pointer,
        )
        .with_designation(PointerDesignation::Unresolved(identity));
        let carrier = CPointerIntegerValue::from_pointer(pointer.clone(), CType::UInt64)
            .unwrap()
            .with_parts(Bitvector32Term::Variable(numeric), pointer);
        let value = CValue::PointerInteger(std::sync::Arc::new(carrier));
        let mut variables = BTreeSet::new();
        collect_c_value_bitvector_variables(&value, &mut variables);
        assert_eq!(variables, BTreeSet::from([numeric, identity, block]));

        let rewritten = substitute_bitvector_variable_in_c_value(
            &value,
            numeric,
            &Bitvector32Term::Constant(3),
        );
        let CValue::PointerInteger(rewritten) = rewritten else {
            panic!("structural substitution retains the integer carrier")
        };
        assert_eq!(rewritten.c_type(), CType::UInt64);
        assert_eq!(rewritten.bits(), &Bitvector32Term::Constant(3));
        assert_eq!(
            rewritten.origin().designation(),
            Some(&PointerDesignation::Unresolved(identity))
        );
        assert_eq!(
            rewritten.origin().pointer().block,
            PointerBlock::Symbolic(block)
        );
        assert_eq!(rewritten.origin().pointer().offset.as_const(), Some(12));
        let mut variables = BTreeSet::new();
        collect_c_value_bitvector_variables(&CValue::PointerInteger(rewritten), &mut variables);
        assert_eq!(variables, BTreeSet::from([identity, block]));
    }
}
