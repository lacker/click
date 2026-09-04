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

    /// Whether an atomic leaf retained a concrete theory rule rather than
    /// the compatibility-era opaque success marker.
    pub fn has_typed_atomic_evidence(&self) -> bool {
        matches!(
            &self.rule,
            PropositionDerivationRule::ContextualAtomic { evidence, .. }
                if !matches!(evidence, AtomicPropositionDerivationEvidence::Legacy)
        )
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

    /// Return the exact equality paths selected to rewrite variables in a
    /// larger atomic proposition before context-free normalization.
    pub fn bitvector_equality_rewrite_paths(
        &self,
    ) -> Option<&[Vec<BitvectorEqualityDerivationStep>]> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence: AtomicPropositionDerivationEvidence::BitvectorEqualityRewritePaths(paths),
                ..
            } => Some(paths),
            _ => None,
        }
    }

    /// Return the exact universal specialization selected by the atomic
    /// prover: the quantified fact, concrete argument, and guard premises.
    pub fn forall_int32_instantiation(
        &self,
    ) -> Option<(&Proposition, &Bitvector32Term, &[Proposition])> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence: AtomicPropositionDerivationEvidence::ForallInt32Instantiation(evidence),
                ..
            } => Some((
                &evidence.quantified,
                &evidence.argument,
                &evidence.guard_premises,
            )),
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

    /// Return the exact non-strict constant upper bound selected when the
    /// atomic prover established a larger constant bound on an increment.
    pub fn int32_increment_constant_upper_bound_step(&self) -> Option<&SignedOrderDerivationStep> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence:
                    AtomicPropositionDerivationEvidence::Int32IncrementConstantUpperBound(step),
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

    /// Return the exact maximum bound selected for `defined(1 + value)`.
    pub fn int32_one_plus_below_max_is_defined_step(&self) -> Option<&SignedOrderDerivationStep> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence: AtomicPropositionDerivationEvidence::Int32OnePlusBelowMaxIsDefined(step),
                ..
            } => Some(step),
            _ => None,
        }
    }

    /// Return the exact maximum bound selected for `value < 1 + value`.
    pub fn int32_one_plus_strictly_increases_step(&self) -> Option<&SignedOrderDerivationStep> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence: AtomicPropositionDerivationEvidence::Int32OnePlusStrictlyIncreases(step),
                ..
            } => Some(step),
            _ => None,
        }
    }

    /// Return the exact nonnegative-amount and remaining-headroom premises
    /// selected when the atomic prover established symbolic addition
    /// definedness through the named int32 theorem.
    pub fn int32_nonnegative_add_within_max_steps(
        &self,
    ) -> Option<(&SignedOrderDerivationStep, &SignedOrderDerivationStep)> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence:
                    AtomicPropositionDerivationEvidence::Int32NonnegativeAddWithinMaxIsDefined(evidence),
                ..
            } => Some((&evidence.amount_nonnegative, &evidence.within_headroom)),
            _ => None,
        }
    }

    /// Return the exact nonnegative-amount and amount-within-value premises
    /// selected when the atomic prover established symbolic subtraction
    /// definedness through the named int32 theorem.
    pub fn int32_nonnegative_subtract_within_value_steps(
        &self,
    ) -> Option<(&SignedOrderDerivationStep, &SignedOrderDerivationStep)> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence:
                    AtomicPropositionDerivationEvidence::Int32NonnegativeSubtractWithinValueIsDefined(
                        evidence,
                    ),
                ..
            } => Some((&evidence.amount_nonnegative, &evidence.within_value)),
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

    /// Return the exact strict lower edge and strict upper edge selected when
    /// the atomic prover established a strict lower bound on `value + 1` by
    /// first weakening the lower edge to non-strict order.
    pub fn int32_increment_strict_greater_from_strict_lower_steps(
        &self,
    ) -> Option<(&SignedOrderDerivationStep, &SignedOrderDerivationStep)> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence:
                    AtomicPropositionDerivationEvidence::Int32IncrementStrictGreaterFromStrictLower(
                        bounds,
                    ),
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

    /// Return the exact `0 < value` premise selected when the atomic prover
    /// established `0 <= value`.
    pub fn int32_strictly_positive_is_nonnegative_step(
        &self,
    ) -> Option<&SignedOrderDerivationStep> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence:
                    AtomicPropositionDerivationEvidence::Int32StrictlyPositiveIsNonnegative(step),
                ..
            } => Some(step),
            _ => None,
        }
    }

    /// Return the exact `lower + 1 <= value` premise selected when the atomic
    /// prover established `lower < value`.
    pub fn int32_successor_le_implies_lt_step(&self) -> Option<&SignedOrderDerivationStep> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence: AtomicPropositionDerivationEvidence::Int32SuccessorLeImpliesLt(step),
                ..
            } => Some(step),
            _ => None,
        }
    }

    /// Return the exact stronger constant lower bound selected when the
    /// atomic prover established a weaker constant lower bound.
    pub fn int32_constant_lower_bound_weakening_step(&self) -> Option<&SignedOrderDerivationStep> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence:
                    AtomicPropositionDerivationEvidence::Int32ConstantLowerBoundWeakening(step),
                ..
            } => Some(step),
            _ => None,
        }
    }

    /// Return the exact `not (value < lower + 1)` premise selected when the
    /// atomic prover established `value >= lower`.
    pub fn int32_negated_strict_successor_bound_step(&self) -> Option<&SignedOrderDerivationStep> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence:
                    AtomicPropositionDerivationEvidence::Int32NegatedStrictSuccessorBound(step),
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
                    AtomicPropositionDerivationEvidence::Int32OneLePredecessorIsNonnegative(
                        Int32OneLeEvidence::Direct(step),
                    ),
                ..
            } => Some(step),
            _ => None,
        }
    }

    pub fn int32_equal_one_predecessor_is_nonnegative_path(
        &self,
    ) -> Option<&[BitvectorEqualityDerivationStep]> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence:
                    AtomicPropositionDerivationEvidence::Int32OneLePredecessorIsNonnegative(
                        Int32OneLeEvidence::EqualOne(path),
                    ),
                ..
            } => Some(path),
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
                    AtomicPropositionDerivationEvidence::Int32OneLePredecessorStrictlyDecreases(
                        Int32OneLeEvidence::Direct(step),
                    ),
                ..
            } => Some(step),
            _ => None,
        }
    }

    pub fn int32_equal_one_predecessor_strictly_decreases_path(
        &self,
    ) -> Option<&[BitvectorEqualityDerivationStep]> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence:
                    AtomicPropositionDerivationEvidence::Int32OneLePredecessorStrictlyDecreases(
                        Int32OneLeEvidence::EqualOne(path),
                    ),
                ..
            } => Some(path),
            _ => None,
        }
    }

    pub fn int32_equal_one_predecessor_is_zero_path(
        &self,
    ) -> Option<&[BitvectorEqualityDerivationStep]> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence: AtomicPropositionDerivationEvidence::Int32EqualOnePredecessorIsZero(path),
                ..
            } => Some(path),
            _ => None,
        }
    }

    /// Return the exact `left <= right` and `left != right` premises selected
    /// when the atomic prover established `left < right`.
    pub fn int32_le_and_neq_implies_strict_premises(&self) -> Option<(&Proposition, &Proposition)> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence: AtomicPropositionDerivationEvidence::Int32LeAndNeqImpliesStrict(evidence),
                ..
            } => Some((&evidence.less_equal, &evidence.not_equal)),
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
            PropositionDerivationRule::ExistsFromFact { source, body } => {
                premises.insert(source.clone());
                let mut body_premises = BTreeSet::new();
                body.collect_context_premises(&mut body_premises);
                if let Proposition::Exists {
                    var: source_var,
                    sort,
                    body: source_body,
                    ..
                } = source
                {
                    if let Some(renamed) =
                        crate::kernel::api::substitute_quantified_body_capture_free(
                            source_body,
                            *source_var,
                            match &self.conclusion {
                                Proposition::Exists { var, .. } => *var,
                                _ => *source_var,
                            },
                            sort,
                        )
                    {
                        let mut conjuncts = BTreeSet::new();
                        collect_local_assumptions(&renamed, &mut conjuncts);
                        for conjunct in conjuncts {
                            body_premises.remove(&conjunct);
                        }
                    }
                }
                premises.extend(body_premises);
            }
            PropositionDerivationRule::ExistsFromWitness { body, .. } => {
                body.collect_context_premises(premises);
            }
            PropositionDerivationRule::ForAllLoadableRange { source } => {
                premises.insert(source.clone());
            }
            PropositionDerivationRule::ExistsLoadableRange { source, .. } => {
                premises.insert(source.clone());
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
    /// `not (x <= y)`, whose path shape is `y < x` but whose check premise
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
            next_kernel_variable: 1_000_000,
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

    /// Adds the evaluator work inherent in one selected C expression.
    ///
    /// The ordinary fixed allowance remains available for work repeated by
    /// dynamic execution, such as short-circuit path amplification. Explicit
    /// budgets supplied to `*_with_budget` APIs are intentionally not adjusted.
    pub(crate) fn for_c_expression(expression: &CExpression) -> Self {
        Self::default().with_c_source_cost(c_expression_source_cost(expression))
    }

    /// Adds the evaluator work inherent in one selected C statement tree.
    pub(crate) fn for_c_statement(statement: &CStatement) -> Self {
        Self::default().with_c_source_cost(c_statement_source_cost(statement))
    }

    /// Adds the structural work of the independent verification evaluator.
    /// Ordinary leaf statements cross both its verification dispatcher and
    /// the shared statement evaluator, so their baseline contains two visits.
    pub(crate) fn for_c_statement_verification(statement: &CStatement) -> Self {
        Self::default().with_c_source_cost(c_statement_verification_source_cost(statement))
    }

    /// Adds the evaluator work inherent in one selected whole-function
    /// judgment, including evaluation of its caller-side arguments.
    pub(crate) fn for_c_function(function: &CFunction, arguments: &[CExpression]) -> Self {
        let mut cost = c_statement_source_cost(function.body());
        for argument in arguments {
            cost.add_expression(c_expression_source_cost(argument).expression_steps);
        }
        Self::default().with_c_source_cost(cost)
    }

    pub(crate) fn for_c_function_verification(
        function: &CFunction,
        arguments: &[CExpression],
    ) -> Self {
        let mut cost = c_statement_verification_source_cost(function.body());
        for argument in arguments {
            cost.add_expression(c_expression_source_cost(argument).expression_steps);
        }
        Self::default().with_c_source_cost(cost)
    }

    fn with_c_source_cost(mut self, cost: CSourceCost) -> Self {
        self.expression_steps = self.expression_steps.saturating_add(cost.expression_steps);
        self.statement_steps = self.statement_steps.saturating_add(cost.statement_steps);
        self
    }

    pub(crate) fn with_next_opaque_call(mut self, next_opaque_call: u64) -> Self {
        self.next_opaque_call = next_opaque_call;
        self
    }

    pub(crate) fn next_opaque_call(&self) -> u64 {
        self.next_opaque_call
    }

    pub(crate) fn with_next_kernel_variable(mut self, next_kernel_variable: u64) -> Self {
        self.next_kernel_variable = 1_000_000 + next_kernel_variable;
        self
    }

    pub(crate) fn next_kernel_variable(&self) -> u64 {
        self.next_kernel_variable - 1_000_000
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

    /// Enforces the maximum number of paths returned by one evaluator result.
    ///
    /// Returning one continuation is ordinary straight-line execution, not
    /// path growth. Charging that singleton at every expression and statement
    /// wrapper made a fixed path-explosion guard behave like a hidden source
    /// length limit. Propagating the same paths through another wrapper does
    /// not spend the capacity again.
    pub(in crate::kernel) fn check_path_width(&self, produced_paths: usize) -> ExecutionResult<()> {
        if crate::instrumentation::deadline_exceeded() {
            return Err(ExecutionLimit::Deadline);
        }
        if self.paths < produced_paths {
            return Err(ExecutionLimit::Paths);
        }
        Ok(())
    }
}

/// Static evaluator visits attributable to the selected C syntax itself.
///
/// This is deliberately separate from `ExecutionBudget`: syntax contributes
/// baseline capacity once, while repeated execution of that syntax continues
/// to consume the fixed dynamic reserve and the independent call, loop, and
/// path limits.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct CSourceCost {
    expression_steps: usize,
    statement_steps: usize,
}

impl CSourceCost {
    fn expression(expression_steps: usize) -> Self {
        Self {
            expression_steps,
            statement_steps: 0,
        }
    }

    fn add_expression(&mut self, steps: usize) {
        self.expression_steps = self.expression_steps.saturating_add(steps);
    }
}

/// Expression visits made by one non-amplified rvalue evaluation.
fn c_expression_source_cost(expression: &CExpression) -> CSourceCost {
    CSourceCost::expression(c_expression_steps_for_mode(expression, false))
}

fn c_expression_source_steps(expression: &CExpression) -> usize {
    c_expression_source_cost(expression).expression_steps
}

fn c_expression_steps_for_mode(expression: &CExpression, lvalue: bool) -> usize {
    let mut steps = 0usize;
    let mut pending = vec![(expression, lvalue)];
    while let Some((expression, lvalue)) = pending.pop() {
        steps = steps.saturating_add(1);
        if lvalue {
            match expression {
                CExpression::Load(pointer) | CExpression::TypedLoad { pointer, .. } => {
                    pending.push((pointer, false));
                }
                CExpression::Index(base, index) => {
                    pending.push((base, false));
                    pending.push((index, false));
                }
                // Variables are complete lvalues. Invalid lvalue forms fail
                // immediately after their one visit.
                _ => {}
            }
            continue;
        }
        match expression {
            CExpression::Value(_) | CExpression::FunctionAddress(_) => {}
            CExpression::Cast { expression, .. } => pending.push((expression, false)),
            CExpression::Conditional {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push((condition, false));
                pending.push((then_branch, false));
                pending.push((else_branch, false));
            }
            CExpression::FloatClassification { expression, .. } => {
                pending.push((expression, false))
            }
            // Scalar variables add an lvalue visit. Arrays skip it, so this is
            // a safe structural allowance without consulting an execution
            // state during budget construction.
            CExpression::Variable(_) => pending.push((expression, true)),
            CExpression::AddressOf(target) => pending.push((target, true)),
            CExpression::PointerOffsetBytes { pointer, .. }
            | CExpression::Not(pointer)
            | CExpression::BitwiseNot(pointer) => pending.push((pointer, false)),
            CExpression::LessThan(left, right)
            | CExpression::LessEqual(left, right)
            | CExpression::GreaterThan(left, right)
            | CExpression::GreaterEqual(left, right)
            | CExpression::Equal(left, right)
            | CExpression::NotEqual(left, right)
            | CExpression::And(left, right)
            | CExpression::Or(left, right)
            | CExpression::Add(left, right)
            | CExpression::Subtract(left, right)
            | CExpression::Multiply(left, right)
            | CExpression::Divide(left, right)
            | CExpression::Remainder(left, right)
            | CExpression::ShiftLeft(left, right)
            | CExpression::ShiftRight(left, right)
            | CExpression::BitwiseAnd(left, right)
            | CExpression::BitwiseOr(left, right)
            | CExpression::BitwiseXor(left, right) => {
                pending.push((left, false));
                pending.push((right, false));
            }
            CExpression::Load(_) | CExpression::TypedLoad { .. } | CExpression::Index(_, _) => {
                pending.push((expression, true))
            }
        }
    }
    steps
}

fn c_statement_source_cost(statement: &CStatement) -> CSourceCost {
    let mut cost = CSourceCost::default();
    let mut pending = vec![statement];
    while let Some(statement) = pending.pop() {
        if !matches!(statement, CStatement::Seq(_, _)) {
            cost.statement_steps = cost.statement_steps.saturating_add(1);
        }
        match statement {
            CStatement::Skip
            | CStatement::Break
            | CStatement::Continue
            | CStatement::Declare { .. }
            | CStatement::DeclareAggregate { .. } => {}
            CStatement::ContinueWithStep { step } => pending.push(step),
            CStatement::Assign { expression, .. } => {
                cost.add_expression(1); // assignment target lvalue
                cost.add_expression(c_expression_source_steps(expression));
            }
            CStatement::CallAssign { arguments, .. } | CStatement::Call { arguments, .. } => {
                for argument in arguments {
                    cost.add_expression(c_expression_source_steps(argument));
                }
            }
            CStatement::HeapAllocate { bytes, .. } => {
                cost.add_expression(c_expression_source_steps(bytes));
                // Successful allocation assigns a synthesized pointer value
                // to a local: one lvalue and one value-expression visit.
                cost.add_expression(2);
            }
            CStatement::HeapFree { pointer } => {
                cost.add_expression(c_expression_source_steps(pointer));
            }
            CStatement::Assert { condition, .. } => {
                cost.add_expression(c_expression_source_steps(condition));
            }
            CStatement::Seq(first, second) => {
                pending.push(first);
                pending.push(second);
            }
            CStatement::Return(expression) => {
                cost.add_expression(c_expression_source_steps(expression));
            }
            CStatement::Store { pointer, value }
            | CStatement::TypedStore { pointer, value, .. } => {
                // The store target is evaluated as a synthesized load lvalue.
                cost.add_expression(1usize.saturating_add(c_expression_source_steps(pointer)));
                cost.add_expression(c_expression_source_steps(value));
            }
            CStatement::Update {
                target, operand, ..
            } => {
                cost.add_expression(c_expression_steps_for_mode(target, true));
                cost.add_expression(1); // read the current lvalue value
                cost.add_expression(c_expression_source_steps(operand));
                cost.add_expression(1); // apply the update operator
            }
            CStatement::If {
                condition,
                then_branch,
                else_branch,
            } => {
                cost.add_expression(c_expression_source_steps(condition));
                pending.push(then_branch);
                pending.push(else_branch);
            }
            CStatement::While {
                condition, body, ..
            } => {
                cost.add_expression(c_expression_source_steps(condition));
                pending.push(body);
            }
            CStatement::Switch { expression, cases } => {
                cost.add_expression(c_expression_source_steps(expression));
                for case in cases {
                    pending.push(&case.body);
                }
            }
        }
    }
    cost
}

fn c_statement_verification_source_cost(statement: &CStatement) -> CSourceCost {
    let mut cost = c_statement_source_cost(statement);
    cost.statement_steps = c_statement_verification_source_steps(statement);
    cost
}

fn c_statement_verification_source_steps(statement: &CStatement) -> usize {
    let mut steps = 0usize;
    let mut pending = vec![statement];
    while let Some(statement) = pending.pop() {
        match statement {
            CStatement::Seq(first, second) => {
                pending.push(first);
                pending.push(second);
            }
            CStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                steps = steps.saturating_add(1);
                pending.push(then_branch);
                pending.push(else_branch);
            }
            CStatement::While {
                invariant_checks,
                effect_checks,
                body,
                ..
            } if !invariant_checks.is_empty() || !effect_checks.is_empty() => {
                steps = steps.saturating_add(1);
                pending.push(body);
            }
            CStatement::Switch { cases, .. } => {
                steps = steps.saturating_add(1);
                for case in cases {
                    pending.push(&case.body);
                }
            }
            // The verification dispatcher charges once, then delegates an
            // ordinary leaf to the shared evaluator, which charges again.
            _ => steps = steps.saturating_add(2),
        }
    }
    steps
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
