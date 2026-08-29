use super::*;

impl CParameter {
    pub fn new(name: impl Into<String>, c_type: CType) -> Self {
        Self {
            name: name.into(),
            c_type,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn c_type(&self) -> CType {
        self.c_type
    }
}

impl CFunction {
    pub fn new(
        return_type: CType,
        name: impl Into<String>,
        parameters: Vec<CParameter>,
        body: CStatement,
    ) -> Self {
        Self {
            return_type,
            name: name.into(),
            parameters,
            source_body: body.clone(),
            body,
            resource_requires: Vec::new(),
            resource_ensures: Vec::new(),
            contract_requires: Vec::new(),
            contract_ensures: Vec::new(),
            contract_mutable: Vec::new(),
            contract_claims: Vec::new(),
            opaque_contract_supported: true,
            composite_resource_definitions: Vec::new(),
            predicate_unfoldings: Vec::new(),
        }
    }

    pub fn with_source_body(mut self, source_body: CStatement) -> Self {
        self.source_body = source_body;
        self
    }

    pub fn with_resource_summary(
        mut self,
        requires: Vec<CResourceSpec>,
        ensures: Vec<CResourceSpec>,
    ) -> Self {
        self.resource_requires = requires;
        self.resource_ensures = ensures;
        self
    }

    pub fn with_contract(
        mut self,
        requires: Vec<SpecProposition>,
        ensures: Vec<SpecProposition>,
        mutable: Vec<CMemorySegment>,
        claims: Vec<CFunctionContractClaim>,
        opaque_supported: bool,
    ) -> Self {
        self.contract_requires = requires;
        self.contract_ensures = ensures;
        self.contract_mutable = mutable;
        self.contract_claims = claims;
        self.opaque_contract_supported = opaque_supported;
        self
    }

    pub fn with_composite_resource_definitions(
        mut self,
        definitions: Vec<CCompositeResourceDefinition>,
    ) -> Self {
        self.composite_resource_definitions = definitions;
        self
    }

    pub fn with_predicate_unfoldings(mut self, unfoldings: Vec<CPredicateUnfolding>) -> Self {
        self.predicate_unfoldings = unfoldings;
        self
    }

    pub fn return_type(&self) -> CType {
        self.return_type
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn parameters(&self) -> &[CParameter] {
        &self.parameters
    }

    pub fn body(&self) -> &CStatement {
        &self.body
    }

    pub fn source_body(&self) -> &CStatement {
        &self.source_body
    }

    pub fn resource_requires(&self) -> &[CResourceSpec] {
        &self.resource_requires
    }

    pub fn resource_ensures(&self) -> &[CResourceSpec] {
        &self.resource_ensures
    }

    pub fn contract_requires(&self) -> &[SpecProposition] {
        &self.contract_requires
    }

    pub fn contract_ensures(&self) -> &[SpecProposition] {
        &self.contract_ensures
    }

    pub fn contract_mutable(&self) -> &[CMemorySegment] {
        &self.contract_mutable
    }

    pub fn contract_claims(&self) -> &[CFunctionContractClaim] {
        &self.contract_claims
    }

    pub fn opaque_contract_supported(&self) -> bool {
        self.opaque_contract_supported
    }

    pub fn composite_resource_definitions(&self) -> &[CCompositeResourceDefinition] {
        &self.composite_resource_definitions
    }

    pub fn predicate_unfoldings(&self) -> &[CPredicateUnfolding] {
        &self.predicate_unfoldings
    }
}

impl CPredicateUnfolding {
    pub fn new(predicate: SpecProposition, body: SpecProposition) -> Self {
        Self { predicate, body }
    }

    pub fn predicate(&self) -> &SpecProposition {
        &self.predicate
    }

    pub fn body(&self) -> &SpecProposition {
        &self.body
    }
}

impl CCompositeResourceDefinition {
    pub fn new(
        name: impl Into<String>,
        parameters: Vec<CParameter>,
        condition: Option<SpecProposition>,
        recursive: bool,
        contains: Vec<CResourceSpec>,
        facts: Vec<SpecProposition>,
    ) -> Self {
        Self {
            name: name.into(),
            parameters,
            condition,
            recursive,
            counted_population: false,
            contains,
            facts,
        }
    }

    pub fn counted_population(
        name: impl Into<String>,
        parameters: Vec<CParameter>,
        condition: Option<SpecProposition>,
        contains: Vec<CResourceSpec>,
        facts: Vec<SpecProposition>,
    ) -> Self {
        Self {
            name: name.into(),
            parameters,
            condition,
            recursive: false,
            counted_population: true,
            contains,
            facts,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn parameters(&self) -> &[CParameter] {
        &self.parameters
    }

    pub fn condition(&self) -> Option<&SpecProposition> {
        self.condition.as_ref()
    }

    pub fn is_recursive(&self) -> bool {
        self.recursive
    }

    pub fn is_counted_population(&self) -> bool {
        self.counted_population
    }

    pub fn needs_outcome_resource_transfer(&self) -> bool {
        self.recursive || self.counted_population
    }

    pub fn contains(&self) -> &[CResourceSpec] {
        &self.contains
    }

    pub fn facts(&self) -> &[SpecProposition] {
        &self.facts
    }
}

impl CFunctionContractClaim {
    pub fn body_safety() -> Self {
        Self {
            key: CFunctionContractClaimKey::BodySafety,
            target: CFunctionContractClaimTarget::BodySafety,
        }
    }

    pub fn effect(index: usize) -> Self {
        Self {
            key: CFunctionContractClaimKey::Effect(index),
            target: CFunctionContractClaimTarget::Effect,
        }
    }

    pub fn ensure_proposition(source_index: usize, contract_index: usize) -> Self {
        Self {
            key: CFunctionContractClaimKey::Ensure(source_index),
            target: CFunctionContractClaimTarget::EnsureProposition(contract_index),
        }
    }

    pub fn ensure_resource(source_index: usize, resource_index: usize) -> Self {
        Self {
            key: CFunctionContractClaimKey::Ensure(source_index),
            target: CFunctionContractClaimTarget::EnsureResource(resource_index),
        }
    }

    pub fn key(&self) -> &CFunctionContractClaimKey {
        &self.key
    }

    pub fn target(&self) -> &CFunctionContractClaimTarget {
        &self.target
    }
}

impl CLoopInvariantCheck {
    pub fn new(
        proposition: SpecProposition,
        entry_context: Option<String>,
        preservation_context: Option<String>,
    ) -> Self {
        Self {
            proposition,
            entry_context,
            preservation_context,
        }
    }

    pub fn proposition(&self) -> &SpecProposition {
        &self.proposition
    }

    pub fn entry_context(&self) -> Option<&str> {
        self.entry_context.as_deref()
    }

    pub fn preservation_context(&self) -> Option<&str> {
        self.preservation_context.as_deref()
    }
}

impl CLoopEffectCheck {
    pub fn new(effect: CLoopEffect, context: Option<String>) -> Self {
        Self {
            effect,
            span: CLoopEffectSpan::Step,
            context,
        }
    }

    pub fn new_with_span(
        effect: CLoopEffect,
        span: CLoopEffectSpan,
        context: Option<String>,
    ) -> Self {
        Self {
            effect,
            span,
            context,
        }
    }

    pub fn effect(&self) -> &CLoopEffect {
        &self.effect
    }

    pub fn span(&self) -> CLoopEffectSpan {
        self.span
    }

    pub fn context(&self) -> Option<&str> {
        self.context.as_deref()
    }
}

impl CMemorySegment {
    pub fn new(base: CExpression, start: CExpression, end: CExpression) -> Self {
        Self {
            base,
            start,
            end,
            guard: None,
        }
    }

    pub fn with_guard(mut self, guard: SpecProposition) -> Self {
        self.guard = Some(guard);
        self
    }

    pub fn guard(&self) -> Option<&SpecProposition> {
        self.guard.as_ref()
    }
}

impl CMemoryRange {
    pub fn new(base: Pointer, start: Bitvector32Term, end: Bitvector32Term) -> Self {
        Self { base, start, end }
    }

    pub fn base(&self) -> &Pointer {
        &self.base
    }

    pub fn start(&self) -> &Bitvector32Term {
        &self.start
    }

    pub fn end(&self) -> &Bitvector32Term {
        &self.end
    }
}

impl CFunctionSpecification {
    pub fn new(
        state: CState,
        arguments: Vec<CExpression>,
        requires: Vec<Proposition>,
        outcome: CFunctionOutcome,
    ) -> Self {
        Self {
            state,
            arguments,
            requires,
            outcome,
        }
    }

    pub fn state(&self) -> &CState {
        &self.state
    }

    pub fn arguments(&self) -> &[CExpression] {
        &self.arguments
    }

    pub fn requires(&self) -> &[Proposition] {
        &self.requires
    }

    pub fn outcome(&self) -> &CFunctionOutcome {
        &self.outcome
    }
}

impl CExecutionEnvironment {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_function(mut self, function: CFunction) -> Self {
        std::sync::Arc::make_mut(&mut self.functions).insert(function.name().to_string(), function);
        self.variable_index = CExecutionEnvironmentVariableIndex::default();
        self
    }

    pub fn get_function(&self, name: &str) -> Option<&CFunction> {
        self.functions.get(name)
    }

    pub fn with_verified_function_rule(mut self, rule: CVerifiedFunctionRule) -> Self {
        std::sync::Arc::make_mut(&mut self.verified_function_rules)
            .insert(rule.function.name().to_string(), rule);
        self.variable_index = CExecutionEnvironmentVariableIndex::default();
        self
    }

    pub fn with_verified_function_termination_rules(
        mut self,
        rules: impl IntoIterator<Item = CVerifiedFunctionTerminationRule>,
    ) -> Self {
        for rule in rules {
            std::sync::Arc::make_mut(&mut self.verified_function_termination_rules)
                .insert(rule.function.name().to_string(), rule);
        }
        self.variable_index = CExecutionEnvironmentVariableIndex::default();
        self
    }

    pub fn has_verified_function_termination(&self, name: &str) -> bool {
        self.verified_function_termination_rules.contains_key(name)
    }

    pub fn without_verified_function_rule(mut self, name: &str) -> Self {
        std::sync::Arc::make_mut(&mut self.verified_function_rules).remove(name);
        self.variable_index = CExecutionEnvironmentVariableIndex::default();
        self
    }

    pub(in crate::kernel) fn get_verified_function_rule(
        &self,
        name: &str,
    ) -> Option<&CVerifiedFunctionRule> {
        self.verified_function_rules.get(name)
    }

    pub(crate) fn verified_function_rules(&self) -> Vec<CVerifiedFunctionRule> {
        self.verified_function_rules.values().cloned().collect()
    }

    pub fn with_verified_loop_rules(
        mut self,
        rules: impl IntoIterator<Item = CVerifiedLoopRule>,
    ) -> Self {
        std::sync::Arc::make_mut(&mut self.verified_loop_rules).extend(rules);
        self.variable_index = CExecutionEnvironmentVariableIndex::default();
        self
    }

    #[cfg(test)]
    pub(crate) fn shares_project_storage_with(&self, other: &Self) -> bool {
        std::sync::Arc::ptr_eq(&self.functions, &other.functions)
            && std::sync::Arc::ptr_eq(
                &self.verified_function_rules,
                &other.verified_function_rules,
            )
            && std::sync::Arc::ptr_eq(
                &self.verified_function_termination_rules,
                &other.verified_function_termination_rules,
            )
    }

    #[cfg(test)]
    pub(crate) fn shares_all_storage_with(&self, other: &Self) -> bool {
        self.shares_project_storage_with(other)
            && std::sync::Arc::ptr_eq(&self.verified_loop_rules, &other.verified_loop_rules)
            && self
                .variable_index
                .shares_storage_with(&other.variable_index)
    }

    pub(in crate::kernel) fn applicable_verified_loop_rule(
        &self,
        state: &CState,
        statement: &CStatement,
        assumptions: &PureFactContext,
    ) -> Option<&CVerifiedLoopRule> {
        self.verified_loop_rules.iter().find(|rule| {
            let statement_matches = rule.loop_statement == *statement;
            let assumptions_match = rule
                .required_assumptions
                .pure_facts()
                .iter()
                .all(|required| {
                    assumptions.pure_facts().contains(required)
                        || assumptions.proves(required)
                        || match required {
                            Proposition::CMemoryLoadable {
                                memory,
                                base,
                                bytes,
                            } => {
                                memory_snapshots_proven_equal_at_pointer(
                                    memory,
                                    state.memory(),
                                    base,
                                    assumptions,
                                ) && (bytes.as_const().is_some_and(|bytes| {
                                    resource_context_has_read(
                                        state.resources(),
                                        base,
                                        bytes,
                                        assumptions,
                                    )
                                }) || resource_context_has_symbolic_int32_range_read(
                                    state.resources(),
                                    base,
                                    bytes,
                                ))
                            }
                            _ => false,
                        }
                });
            let state_matches = rule.symbolic_entry_state.locals == state.locals
                && rule.symbolic_entry_state.memory == state.memory
                && crate::kernel::api::contract_certification::resource_contexts_definitionally_equal_with_definitions(
                    &rule.composite_resource_definitions,
                    rule.symbolic_entry_state.memory(),
                    rule.symbolic_entry_state.resources(),
                    state.memory(),
                    state.resources(),
                    assumptions,
                );
            state_matches && statement_matches && assumptions_match
        })
    }
}

impl CVerifiedLoopRule {
    pub fn with_composite_resource_definitions(
        mut self,
        definitions: impl IntoIterator<Item = CCompositeResourceDefinition>,
    ) -> Self {
        self.composite_resource_definitions.extend(definitions);
        self
    }
}

impl CTerminationError {
    pub fn message(&self) -> &str {
        &self.message
    }
}

impl std::fmt::Display for CTerminationError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.message.fmt(formatter)
    }
}

impl std::error::Error for CTerminationError {}
