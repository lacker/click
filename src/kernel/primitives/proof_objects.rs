use super::*;

impl Theorem {
    pub(in crate::kernel) fn new(proposition: Proposition) -> Self {
        Self {
            proposition: std::sync::Arc::new(proposition),
        }
    }

    pub fn proposition(&self) -> &Proposition {
        self.proposition.as_ref()
    }
}

impl PropositionDerivation {
    pub fn conclusion(&self) -> &Proposition {
        &self.conclusion
    }

    /// Return the checked child derivations when this proof concludes a
    /// conjunction. Certificate lowering can preserve this structure instead
    /// of rediscovering it from a flattened premise set.
    pub fn conjunction_parts(&self) -> Option<(&Self, &Self)> {
        match &self.rule {
            PropositionDerivationRule::And { left, right } => Some((left, right)),
            _ => None,
        }
    }

    /// Return the checked selected disjunct and whether it is the left one.
    pub fn disjunction_choice(&self) -> Option<(bool, &Self)> {
        match &self.rule {
            PropositionDerivationRule::OrLeft(proof) => Some((true, proof)),
            PropositionDerivationRule::OrRight(proof) => Some((false, proof)),
            _ => None,
        }
    }

    /// Return the checked proof of a false antecedent when this derivation
    /// concludes an implication by contradiction.
    pub fn false_antecedent_proof(&self) -> Option<&Self> {
        match &self.rule {
            PropositionDerivationRule::ImpliesFalseAntecedent(proof) => Some(proof),
            _ => None,
        }
    }

    /// Return the exact ordered edges selected by an atomic signed-order
    /// decision. `None` means this derivation used another rule; an empty
    /// path is never recorded.
    pub fn signed_order_path(&self) -> Option<&[SignedOrderDerivationStep]> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence: AtomicPropositionDerivationEvidence::SignedOrderPath(path),
                ..
            } => Some(path),
            _ => None,
        }
    }

    /// Return the exact oriented ground-int32 equality edges selected by an
    /// atomic equality decision.
    pub fn bitvector_equality_path(&self) -> Option<&[BitvectorEqualityDerivationStep]> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence: AtomicPropositionDerivationEvidence::BitvectorEqualityPath(path),
                ..
            } => Some(path),
            _ => None,
        }
    }

    /// Return the exact strict-order premise selected when the atomic prover
    /// used the int32 increment-upper-bound rule.
    pub fn int32_increment_upper_bound_step(&self) -> Option<&SignedOrderDerivationStep> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence: AtomicPropositionDerivationEvidence::Int32IncrementUpperBound(step),
                ..
            } => Some(step),
            _ => None,
        }
    }

    /// Return the exact strict upper-bound premise selected when the atomic
    /// prover established that an int32 increment is strictly increasing.
    pub fn int32_increment_strictly_increases_step(&self) -> Option<&SignedOrderDerivationStep> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence: AtomicPropositionDerivationEvidence::Int32IncrementStrictlyIncreases(step),
                ..
            } => Some(step),
            _ => None,
        }
    }

    /// Return the exact `value < INT32_MAX` premise selected when the atomic
    /// prover established that `value + 1` is defined.
    pub fn int32_increment_below_max_is_defined_step(&self) -> Option<&SignedOrderDerivationStep> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence: AtomicPropositionDerivationEvidence::Int32IncrementBelowMaxIsDefined(step),
                ..
            } => Some(step),
            _ => None,
        }
    }

    /// Return the exact non-strict lower edge and strict upper edge selected
    /// when the atomic prover established a lower bound on `value + 1`.
    pub fn int32_increment_lower_bound_steps(
        &self,
    ) -> Option<(&SignedOrderDerivationStep, &SignedOrderDerivationStep)> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence: AtomicPropositionDerivationEvidence::Int32IncrementLowerBound(bounds),
                ..
            } => Some((&bounds.lower_bound, &bounds.upper_bound)),
            _ => None,
        }
    }

    /// Return the exact non-strict lower edge and strict upper edge selected
    /// when the atomic prover established a greater-equal lower bound on
    /// `value + 1`.
    pub fn int32_increment_greater_equal_lower_bound_steps(
        &self,
    ) -> Option<(&SignedOrderDerivationStep, &SignedOrderDerivationStep)> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence:
                    AtomicPropositionDerivationEvidence::Int32IncrementGreaterEqualLowerBound(bounds),
                ..
            } => Some((&bounds.lower_bound, &bounds.upper_bound)),
            _ => None,
        }
    }

    /// Return the exact non-strict lower edge and strict upper edge selected
    /// when the atomic prover established a strict lower bound on `value + 1`.
    pub fn int32_increment_strict_greater_lower_bound_steps(
        &self,
    ) -> Option<(&SignedOrderDerivationStep, &SignedOrderDerivationStep)> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence:
                    AtomicPropositionDerivationEvidence::Int32IncrementStrictGreaterLowerBound(bounds),
                ..
            } => Some((&bounds.lower_bound, &bounds.upper_bound)),
            _ => None,
        }
    }

    /// Return the exact non-strict order edge and strict upper edge selected
    /// when the atomic prover established that increment preserves order.
    pub fn int32_increment_preserves_order_steps(
        &self,
    ) -> Option<(&SignedOrderDerivationStep, &SignedOrderDerivationStep)> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence: AtomicPropositionDerivationEvidence::Int32IncrementPreservesOrder(bounds),
                ..
            } => Some((&bounds.lower_bound, &bounds.upper_bound)),
            _ => None,
        }
    }

    /// Return the exact `1 <= value` premise selected when the atomic prover
    /// established `0 <= value`.
    pub fn int32_positive_is_nonnegative_step(&self) -> Option<&SignedOrderDerivationStep> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence: AtomicPropositionDerivationEvidence::Int32PositiveIsNonnegative(step),
                ..
            } => Some(step),
            _ => None,
        }
    }

    /// Return the exact strict positivity premise selected when the atomic
    /// prover established that a predecessor is nonnegative.
    pub fn int32_positive_predecessor_is_nonnegative_step(
        &self,
    ) -> Option<&SignedOrderDerivationStep> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence:
                    AtomicPropositionDerivationEvidence::Int32PositivePredecessorIsNonnegative(step),
                ..
            } => Some(step),
            _ => None,
        }
    }

    /// Return the exact strict positivity premise selected when the atomic
    /// prover established that a predecessor strictly decreases its input.
    pub fn int32_positive_predecessor_strictly_decreases_step(
        &self,
    ) -> Option<&SignedOrderDerivationStep> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence:
                    AtomicPropositionDerivationEvidence::Int32PositivePredecessorStrictlyDecreases(step),
                ..
            } => Some(step),
            _ => None,
        }
    }

    /// Return the exact nonnegative and upper-bound edges selected when the
    /// atomic prover established an upper bound on a predecessor.
    pub fn int32_nonnegative_predecessor_upper_bound_steps(
        &self,
    ) -> Option<(&SignedOrderDerivationStep, &SignedOrderDerivationStep)> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence:
                    AtomicPropositionDerivationEvidence::Int32NonnegativePredecessorUpperBound(bounds),
                ..
            } => Some((&bounds.nonnegative, &bounds.upper_bound)),
            _ => None,
        }
    }

    /// Return the exact `1 <= value` edge selected when the atomic prover
    /// first derived positivity and then established a nonnegative
    /// predecessor.
    pub fn int32_one_le_predecessor_is_nonnegative_step(
        &self,
    ) -> Option<&SignedOrderDerivationStep> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence:
                    AtomicPropositionDerivationEvidence::Int32OneLePredecessorIsNonnegative(step),
                ..
            } => Some(step),
            _ => None,
        }
    }

    /// Return the exact `1 <= value` edge selected when the atomic prover
    /// first derived positivity and then established predecessor decrease.
    pub fn int32_one_le_predecessor_strictly_decreases_step(
        &self,
    ) -> Option<&SignedOrderDerivationStep> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence:
                    AtomicPropositionDerivationEvidence::Int32OneLePredecessorStrictlyDecreases(step),
                ..
            } => Some(step),
            _ => None,
        }
    }

    /// Return the exact `left <= right` and `not (left < right)` premises
    /// selected when the atomic prover established int32 equality.
    pub fn int32_le_and_not_lt_implies_equality_premises(
        &self,
    ) -> Option<(&Proposition, &Proposition)> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence:
                    AtomicPropositionDerivationEvidence::Int32LeAndNotLtImpliesEquality(evidence),
                ..
            } => Some((&evidence.less_equal, &evidence.not_less_than)),
            _ => None,
        }
    }

    /// Return the exact `left >= right` and `not (left > right)` premises
    /// selected when the atomic prover established int32 equality.
    pub fn int32_ge_and_not_gt_implies_equality_premises(
        &self,
    ) -> Option<(&Proposition, &Proposition)> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence:
                    AtomicPropositionDerivationEvidence::Int32GeAndNotGtImpliesEquality(evidence),
                ..
            } => Some((&evidence.greater_equal, &evidence.not_greater_than)),
            _ => None,
        }
    }

    pub fn context_premises(&self) -> Vec<Proposition> {
        let mut premises = BTreeSet::new();
        self.collect_context_premises(&mut premises);
        premises.into_iter().collect()
    }

    fn collect_context_premises(&self, premises: &mut BTreeSet<Proposition>) {
        fn collect_local_assumptions(
            proposition: &Proposition,
            assumptions: &mut BTreeSet<Proposition>,
        ) {
            if let Proposition::And(left, right) = proposition {
                collect_local_assumptions(left, assumptions);
                collect_local_assumptions(right, assumptions);
            } else {
                assumptions.insert(proposition.clone());
            }
        }

        match &self.rule {
            PropositionDerivationRule::ContextFree => {}
            PropositionDerivationRule::ContextualAtomic {
                premises: required, ..
            }
            | PropositionDerivationRule::Explosion { premises: required } => {
                premises.extend(required.pure_facts());
            }
            PropositionDerivationRule::And { left, right } => {
                left.collect_context_premises(premises);
                right.collect_context_premises(premises);
            }
            PropositionDerivationRule::OrLeft(proof)
            | PropositionDerivationRule::OrRight(proof)
            | PropositionDerivationRule::DoubleNegation(proof)
            | PropositionDerivationRule::ImpliesFalseAntecedent(proof)
            | PropositionDerivationRule::ForAllBody(proof) => {
                proof.collect_context_premises(premises);
            }
            PropositionDerivationRule::Implies { antecedent, body } => {
                let mut body_premises = BTreeSet::new();
                body.collect_context_premises(&mut body_premises);
                let mut local_assumptions = BTreeSet::new();
                collect_local_assumptions(antecedent, &mut local_assumptions);
                for local in local_assumptions {
                    body_premises.remove(&local);
                }
                premises.extend(body_premises);
            }
            PropositionDerivationRule::FiniteForAll { instances } => {
                for instance in instances {
                    instance.collect_context_premises(premises);
                }
            }
            PropositionDerivationRule::FiniteContextSplit {
                premises: range_premises,
                instances,
                ..
            } => {
                premises.extend(range_premises.pure_facts());
                for instance in instances {
                    instance.collect_context_premises(premises);
                }
            }
            PropositionDerivationRule::UpperBoundSplit {
                bound,
                variable,
                pivot,
                below,
                at,
            } => {
                premises.insert(Proposition::ConditionIs(bound.clone(), true));
                let variable = Bitvector32Term::Variable(*variable);
                for (proof, local) in [
                    (
                        below,
                        ConditionTerm::signed_less_than(variable.clone(), pivot.clone()),
                    ),
                    (at, ConditionTerm::equal(variable, pivot.clone())),
                ] {
                    let mut case_premises = BTreeSet::new();
                    proof.collect_context_premises(&mut case_premises);
                    case_premises.remove(&Proposition::ConditionIs(local, true));
                    premises.extend(case_premises);
                }
            }
            PropositionDerivationRule::DisjunctionCases { disjunction, cases } => {
                premises.insert(disjunction.clone());
                let mut case_propositions = Vec::new();
                collect_or_cases(disjunction, &mut case_propositions);
                for (case, local) in cases.iter().zip(case_propositions) {
                    let mut case_premises = BTreeSet::new();
                    case.collect_context_premises(&mut case_premises);
                    let mut local_assumptions = BTreeSet::new();
                    collect_local_assumptions(&local, &mut local_assumptions);
                    for local in local_assumptions {
                        case_premises.remove(&local);
                    }
                    premises.extend(case_premises);
                }
            }
        }
    }
}

impl SignedOrderDerivationStep {
    pub fn lower(&self) -> &Bitvector32Term {
        &self.lower
    }

    pub fn upper(&self) -> &Bitvector32Term {
        &self.upper
    }

    pub fn is_strict(&self) -> bool {
        self.strict
    }

    /// Return the exact context proposition from which this normalized edge
    /// was collected. This matters for polarity-normalized edges such as
    /// `not (x <= y)`, whose path shape is `y < x` but whose replay premise
    /// is not literally that positive comparison.
    pub fn premise(&self) -> &Proposition {
        &self.premise
    }
}

impl BitvectorEqualityDerivationStep {
    pub fn source(&self) -> &Bitvector32Term {
        &self.source
    }

    pub fn target(&self) -> &Bitvector32Term {
        &self.target
    }

    pub fn premise(&self) -> &Proposition {
        &self.premise
    }
}

#[cfg(test)]
impl PureFactContext {
    pub(crate) fn shares_persistent_storage_with(&self, other: &Self) -> bool {
        self.condition_facts
            .shares_root_with(&other.condition_facts)
            && self
                .signed_order_bounds
                .shares_root_with(&other.signed_order_bounds)
            && std::sync::Arc::ptr_eq(
                &self.memory_load_condition_facts,
                &other.memory_load_condition_facts,
            )
            && std::sync::Arc::ptr_eq(
                &self.bitvector_equality_facts,
                &other.bitvector_equality_facts,
            )
            && std::sync::Arc::ptr_eq(&self.prop_facts, &other.prop_facts)
            && std::sync::Arc::ptr_eq(&self.resource_compositions, &other.resource_compositions)
            && std::sync::Arc::ptr_eq(&self.memory_loadable_facts, &other.memory_loadable_facts)
            && std::sync::Arc::ptr_eq(
                &self.memory_loadable_shape_facts,
                &other.memory_loadable_shape_facts,
            )
            && std::sync::Arc::ptr_eq(
                &self.memory_separation_facts,
                &other.memory_separation_facts,
            )
            && std::sync::Arc::ptr_eq(
                &self.composition_separation_facts,
                &other.composition_separation_facts,
            )
    }
}

impl Default for ExecutionBudget {
    fn default() -> Self {
        Self {
            expression_steps: 10_000,
            statement_steps: 10_000,
            function_calls: 1_000,
            loop_unrolls: 256,
            paths: 10_000,
            next_opaque_call: 0,
            next_verification_variable: 1_000_000,
        }
    }
}

impl ExecutionBudget {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_expression_steps(mut self, expression_steps: usize) -> Self {
        self.expression_steps = expression_steps;
        self
    }

    pub fn with_statement_steps(mut self, statement_steps: usize) -> Self {
        self.statement_steps = statement_steps;
        self
    }

    pub fn with_function_calls(mut self, function_calls: usize) -> Self {
        self.function_calls = function_calls;
        self
    }

    pub fn with_loop_unrolls(mut self, loop_unrolls: usize) -> Self {
        self.loop_unrolls = loop_unrolls;
        self
    }

    pub fn with_paths(mut self, paths: usize) -> Self {
        self.paths = paths;
        self
    }

    pub(crate) fn with_next_opaque_call(mut self, next_opaque_call: u64) -> Self {
        self.next_opaque_call = next_opaque_call;
        self
    }

    pub(crate) fn next_opaque_call(&self) -> u64 {
        self.next_opaque_call
    }

    pub(crate) fn with_next_verification_variable(
        mut self,
        next_verification_variable: u64,
    ) -> Self {
        self.next_verification_variable = 1_000_000 + next_verification_variable;
        self
    }

    pub(crate) fn next_verification_variable(&self) -> u64 {
        self.next_verification_variable - 1_000_000
    }

    pub(in crate::kernel) fn consume_expression_step(&mut self) -> ExecutionResult<()> {
        consume_budget(&mut self.expression_steps, ExecutionLimit::ExpressionSteps)
    }

    pub(in crate::kernel) fn consume_statement_step(&mut self) -> ExecutionResult<()> {
        consume_budget(&mut self.statement_steps, ExecutionLimit::StatementSteps)
    }

    pub(in crate::kernel) fn consume_function_call(&mut self) -> ExecutionResult<()> {
        consume_budget(&mut self.function_calls, ExecutionLimit::FunctionCalls)
    }

    pub(in crate::kernel) fn consume_loop_unroll(&mut self) -> ExecutionResult<()> {
        consume_budget(&mut self.loop_unrolls, ExecutionLimit::LoopUnrolls)
    }

    pub(in crate::kernel) fn consume_paths(&mut self, paths: usize) -> ExecutionResult<()> {
        if crate::instrumentation::deadline_exceeded() {
            return Err(ExecutionLimit::Deadline);
        }
        if self.paths < paths {
            return Err(ExecutionLimit::Paths);
        }
        self.paths -= paths;
        Ok(())
    }
}

pub(in crate::kernel) type ExecutionResult<T> = Result<T, ExecutionLimit>;

pub(in crate::kernel) fn consume_budget(
    remaining: &mut usize,
    limit: ExecutionLimit,
) -> ExecutionResult<()> {
    if crate::instrumentation::deadline_exceeded() {
        return Err(ExecutionLimit::Deadline);
    }
    if *remaining == 0 {
        return Err(limit);
    }
    *remaining -= 1;
    Ok(())
}
