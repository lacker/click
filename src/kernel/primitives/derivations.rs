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

    /// Return the exact equality paths used to establish that two registered
    /// load variables address one cell in one memory epoch.
    pub fn load_address_congruence_paths(&self) -> Option<Vec<&[BitvectorEqualityDerivationStep]>> {
        let PropositionDerivationRule::ContextualAtomic {
            evidence: AtomicPropositionDerivationEvidence::LoadAddressCongruence(evidence),
            ..
        } = &self.rule
        else {
            return None;
        };
        Some(evidence.offset.equality_paths())
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

    /// Return the exact facts an atomic pointer-word equality decision
    /// retained.
    pub fn pointer_word_premises(&self) -> Option<&[Proposition]> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence: AtomicPropositionDerivationEvidence::PointerWord(evidence),
                ..
            } => Some(&evidence.premises),
            _ => None,
        }
    }

    /// Return the base-alignment premise an atomic pointer-alignment
    /// decision retained; the inner `None` marks an intrinsic heap base.
    pub fn pointer_alignment_premise(&self) -> Option<Option<&Proposition>> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence: AtomicPropositionDerivationEvidence::PointerAlignment(evidence),
                ..
            } => Some(evidence.premise.as_ref()),
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

    /// The exact constructor equality cited by a checked injectivity step.
    /// Certificate lowering uses this only to select the existing `extract`
    /// syntax; proof checking recomputes the field equality independently.
    pub(crate) fn algebraic_constructor_injectivity_source(&self) -> Option<(&Proposition, usize)> {
        match &self.rule {
            PropositionDerivationRule::AlgebraicConstructorInjectivity {
                source,
                field_index,
            } => Some((source, *field_index)),
            _ => None,
        }
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
                premises.extend(required.named().iter().cloned());
            }
            PropositionDerivationRule::And { left, right } => {
                left.collect_context_premises(premises);
                right.collect_context_premises(premises);
            }
            PropositionDerivationRule::AlgebraicConstructorCongruence { fields } => {
                for field in fields {
                    field.collect_context_premises(premises);
                }
            }
            PropositionDerivationRule::AlgebraicConstructorInjectivity { source, .. } => {
                premises.insert(source.clone());
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
                    && let Some(renamed) =
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
            PropositionDerivationRule::SingletonSubstitution { equality, body, .. } => {
                equality.collect_context_premises(premises);
                body.collect_context_premises(premises);
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

impl PointerOffsetCongruenceEvidence {
    fn equality_paths(&self) -> Vec<&[BitvectorEqualityDerivationStep]> {
        match self {
            Self::Exact | Self::ExactPremise(_) => Vec::new(),
            Self::Add { first, second, .. } => {
                let mut paths = first.equality_paths();
                paths.extend(second.equality_paths());
                paths
            }
            Self::Int32Scaled { path, .. }
            | Self::Int64Scaled { path, .. }
            | Self::ElementIndex { path, .. } => vec![path],
            Self::Int32ScaledDerived { .. } | Self::ElementIndexDerived { .. } => Vec::new(),
        }
    }

    pub(in crate::kernel) fn checks(
        &self,
        left: &PointerOffsetTerm,
        right: &PointerOffsetTerm,
        assumptions: &PureFactContext,
    ) -> bool {
        match self {
            Self::Exact => left == right,
            Self::ExactPremise(premise) => {
                let Proposition::ConditionIs(
                    ConditionTerm::PointerOffsetEqual(premise_left, premise_right),
                    true,
                ) = premise.as_ref()
                else {
                    return false;
                };
                assumptions.contains_assumed_exact(premise)
                    && ((premise_left.as_ref() == left && premise_right.as_ref() == right)
                        || (premise_left.as_ref() == right && premise_right.as_ref() == left))
            }
            Self::Add {
                first,
                second,
                swapped,
            } => {
                let (
                    PointerOffsetTerm::Add(left_a, left_b),
                    PointerOffsetTerm::Add(right_a, right_b),
                ) = (left, right)
                else {
                    return false;
                };
                let (right_first, right_second) = if *swapped {
                    (right_b.as_ref(), right_a.as_ref())
                } else {
                    (right_a.as_ref(), right_b.as_ref())
                };
                first.checks(left_a, right_first, assumptions)
                    && second.checks(left_b, right_second, assumptions)
            }
            Self::Int32Scaled { byte_width, path } => {
                let (
                    PointerOffsetTerm::Int32Scaled {
                        value: left,
                        byte_width: left_width,
                    },
                    PointerOffsetTerm::Int32Scaled {
                        value: right,
                        byte_width: right_width,
                    },
                ) = (left, right)
                else {
                    return false;
                };
                left_width == byte_width
                    && right_width == byte_width
                    && assumptions.checks_exact_bitvector_equality_path(path, left, right)
            }
            Self::Int32ScaledDerived {
                byte_width,
                equality,
            } => {
                let (
                    PointerOffsetTerm::Int32Scaled {
                        value: left,
                        byte_width: left_width,
                    },
                    PointerOffsetTerm::Int32Scaled {
                        value: right,
                        byte_width: right_width,
                    },
                ) = (left, right)
                else {
                    return false;
                };
                left_width == byte_width
                    && right_width == byte_width
                    && equality.checks(left, right, assumptions)
            }
            Self::Int64Scaled {
                byte_width,
                unsigned,
                path,
            } => {
                let (
                    PointerOffsetTerm::Int64Scaled {
                        value: left,
                        byte_width: left_width,
                        unsigned: left_unsigned,
                    },
                    PointerOffsetTerm::Int64Scaled {
                        value: right,
                        byte_width: right_width,
                        unsigned: right_unsigned,
                    },
                ) = (left, right)
                else {
                    return false;
                };
                left_width == byte_width
                    && right_width == byte_width
                    && left_unsigned == unsigned
                    && right_unsigned == unsigned
                    && assumptions.checks_exact_bitvector_equality_path(path, left, right)
            }
            Self::ElementIndex { byte_width, path } => {
                if crate::kernel::reasoning::common_pointer_offset_element_width(left, right)
                    != Some(*byte_width)
                {
                    return false;
                }
                let (Some(left), Some(right)) = (
                    crate::kernel::reasoning::element_index_from_offset(left, *byte_width),
                    crate::kernel::reasoning::element_index_from_offset(right, *byte_width),
                ) else {
                    return false;
                };
                assumptions.checks_exact_bitvector_equality_path(path, &left, &right)
            }
            Self::ElementIndexDerived {
                byte_width,
                equality,
            } => {
                if crate::kernel::reasoning::common_pointer_offset_element_width(left, right)
                    != Some(*byte_width)
                {
                    return false;
                }
                let (Some(left), Some(right)) = (
                    crate::kernel::reasoning::element_index_from_offset(left, *byte_width),
                    crate::kernel::reasoning::element_index_from_offset(right, *byte_width),
                ) else {
                    return false;
                };
                equality.checks(&left, &right, assumptions)
            }
        }
    }
}

impl DirectBitvectorEqualityEvidence {
    pub(in crate::kernel) fn checks(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        assumptions: &PureFactContext,
    ) -> bool {
        match self {
            Self::AdditiveCancellation {
                left: reduced_left,
                right: reduced_right,
                equality,
            } => {
                crate::kernel::reasoning::bitvector_equality_after_additive_cancellation(
                    left, right,
                ) == Some((reduced_left.clone(), reduced_right.clone()))
                    && equality.checks(reduced_left, reduced_right, assumptions)
            }
            Self::EqualSignedConstants {
                value,
                left: left_evidence,
                right: right_evidence,
            } => {
                let checks =
                    |term: &Bitvector32Term, evidence: &SignedConstantEvidence| match evidence {
                        SignedConstantEvidence::Constant => {
                            signed_bitvector_constant(term) == Some(*value)
                        }
                        SignedConstantEvidence::SingletonBounds {
                            variable,
                            lower,
                            upper,
                        } => {
                            let bound =
                                |evidence: &IndexedSignedOrderBoundEvidence, lower_bound: bool| {
                                    let normalized = if evidence.forward {
                                        (
                                            evidence.endpoint.clone(),
                                            evidence.other.clone(),
                                            evidence.strict,
                                        )
                                    } else {
                                        (
                                            evidence.other.clone(),
                                            evidence.endpoint.clone(),
                                            evidence.strict,
                                        )
                                    };
                                    let source_matches = match evidence.source.as_ref() {
                                        Proposition::ConditionIs(condition, value) => {
                                            crate::kernel::reasoning::condition_as_order_fact(
                                                condition, *value,
                                            ) == Some(normalized)
                                                && assumptions
                                                    .contains_assumed_exact(&evidence.source)
                                        }
                                        _ => false,
                                    };
                                    let recorded =
                                        assumptions.signed_order_bound_entries(term).any(|entry| {
                                            entry
                                                == (
                                                    evidence.endpoint.clone(),
                                                    evidence.other.clone(),
                                                    evidence.strict,
                                                    evidence.forward,
                                                )
                                        });
                                    if !source_matches
                                        || !recorded
                                        || lower_bound == evidence.forward
                                    {
                                        return None;
                                    }
                                    let bound = signed_bitvector_constant(&evidence.other)?;
                                    if lower_bound {
                                        if evidence.strict {
                                            bound.checked_add(1)
                                        } else {
                                            Some(bound)
                                        }
                                    } else if evidence.strict {
                                        bound.checked_sub(1)
                                    } else {
                                        Some(bound)
                                    }
                                };
                            bitvector_variable(term) == Some(*variable)
                                && bound(lower, true) == Some(*value)
                                && bound(upper, false) == Some(*value)
                        }
                    };
                checks(left, left_evidence) && checks(right, right_evidence)
            }
            Self::LeAndNotLt(evidence) => {
                let less_equal = Proposition::ConditionIs(
                    ConditionTerm::signed_less_equal(left.clone(), right.clone()),
                    true,
                );
                let not_less_than = Proposition::ConditionIs(
                    ConditionTerm::signed_less_than(left.clone(), right.clone()),
                    false,
                );
                evidence.less_equal == less_equal
                    && evidence.not_less_than == not_less_than
                    && assumptions.contains_assumed_exact(&evidence.less_equal)
                    && assumptions.contains_assumed_exact(&evidence.not_less_than)
            }
            Self::GeAndNotGt(evidence) => {
                let greater_equal = Proposition::ConditionIs(
                    ConditionTerm::signed_greater_equal(left.clone(), right.clone()),
                    true,
                );
                let not_greater_than = Proposition::ConditionIs(
                    ConditionTerm::signed_greater_than(left.clone(), right.clone()),
                    false,
                );
                evidence.greater_equal == greater_equal
                    && evidence.not_greater_than == not_greater_than
                    && assumptions.contains_assumed_exact(&evidence.greater_equal)
                    && assumptions.contains_assumed_exact(&evidence.not_greater_than)
            }
        }
    }

    fn collect_context_premises(&self, premises: &mut BTreeSet<Proposition>) {
        let collect_signed = |evidence: &SignedConstantEvidence,
                              premises: &mut BTreeSet<Proposition>| {
            if let SignedConstantEvidence::SingletonBounds { lower, upper, .. } = evidence {
                premises.insert(lower.source.as_ref().clone());
                premises.insert(upper.source.as_ref().clone());
            }
        };
        match self {
            Self::AdditiveCancellation { equality, .. } => {
                equality.collect_context_premises(premises)
            }
            Self::EqualSignedConstants { left, right, .. } => {
                collect_signed(left, premises);
                collect_signed(right, premises);
            }
            Self::LeAndNotLt(evidence) => {
                premises.insert(evidence.less_equal.clone());
                premises.insert(evidence.not_less_than.clone());
            }
            Self::GeAndNotGt(evidence) => {
                premises.insert(evidence.greater_equal.clone());
                premises.insert(evidence.not_greater_than.clone());
            }
        }
    }
}

impl LoadAddressCongruenceEvidence {
    pub(in crate::kernel) fn checks(
        &self,
        proposition: &Proposition,
        assumptions: &PureFactContext,
    ) -> bool {
        let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) =
            proposition
        else {
            return false;
        };
        let (Bitvector32Term::Variable(left), Bitvector32Term::Variable(right)) =
            (left.as_ref(), right.as_ref())
        else {
            return false;
        };
        let (Some((left_memory, left_pointer)), Some((right_memory, right_pointer))) = (
            crate::kernel::eval::registered_load_for_variable(left),
            crate::kernel::eval::registered_load_for_variable(right),
        ) else {
            return false;
        };
        left_memory == right_memory
            && left_pointer == self.left_pointer
            && right_pointer == self.right_pointer
            && left_pointer.block == right_pointer.block
            && self
                .offset
                .checks(&left_pointer.offset, &right_pointer.offset, assumptions)
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
            && self
                .bitvector64_equality_facts
                .shares_root_with(&other.bitvector64_equality_facts)
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

/// A budget is either the start of an execution or a continuation of one;
/// there is no default. `Default` would let a mid-execution evaluation
/// restart the fresh-identity counter at the base of the range by writing
/// nothing at all, which is how one `Variable` comes to name two unrelated
/// things. Tests that build a budget over no live state say so through this
/// impl, which is exactly [`ExecutionBudget::for_new_execution`].
#[cfg(test)]
impl Default for ExecutionBudget {
    fn default() -> Self {
        Self::for_new_execution()
    }
}

impl ExecutionBudget {
    /// The first identity a symbolic execution may invent.
    pub(in crate::kernel) const KERNEL_VARIABLE_BASE: u64 = 1_000_000;

    /// The first identity a symbolic execution may not invent: the surface's
    /// quantifier variables start here, the spec fold binders at `3_000_000`,
    /// the algebraic binders at `4_000_000`, and the load variables at
    /// `1 << 40`. Those producers pick identities by a constant base and a
    /// hash rather than from this counter, so they cannot avoid an execution
    /// that has counted into their range; the execution refuses instead.
    pub(in crate::kernel) const KERNEL_VARIABLE_CEILING: u64 = 2_000_000;

    /// The first identity a lowered match arm's binder may use.
    ///
    /// A match binder is a *bound* variable of the term it is lowered into,
    /// so its identity has to be distinguishable from every *free* identity
    /// any state or term around it can carry. Reserving a range for it is
    /// what makes that distinction structural: nothing else mints an
    /// identity here, so an occurrence of one of these in an arm body is a
    /// bound occurrence of that arm's binder and nothing else.
    ///
    /// The range overlaps none of the reserved ones: the execution counter
    /// runs `1_000_000 .. 2_000_000`, the surface's quantifier variables
    /// start at `2_000_000`, the spec fold binders span
    /// `3_000_000 .. 1_003_000_000`, the surface's algebraic binders step by
    /// `65_536` from `4_000_000`, symbolic pointer blocks span
    /// `4_000_000_000 .. 8_000_000_000`, and the load variables span
    /// `1 << 40 .. 1 << 41`. The kernel test
    /// `the_match_binder_range_is_disjoint_from_every_other_producer` asserts
    /// that rather than leaving it to this comment.
    pub(in crate::kernel) const MATCH_BINDER_VARIABLE_BASE: u64 = 1 << 41;

    /// The first identity past the match-binder range. One lowering that
    /// needed more binders than this would start naming something else, so
    /// it refuses here exactly as the execution counter refuses at
    /// [`Self::KERNEL_VARIABLE_CEILING`].
    pub(in crate::kernel) const MATCH_BINDER_VARIABLE_CEILING: u64 = 1 << 42;

    /// Whether `variable` is a match-arm binder identity.
    ///
    /// A rewrite that eliminates a binder asks this before substituting: an
    /// identity outside the range is a free variable of some execution or
    /// producer, and substituting it would be a capture rather than a
    /// binder elimination.
    pub(in crate::kernel) fn is_match_binder_variable(variable: Variable) -> bool {
        (Self::MATCH_BINDER_VARIABLE_BASE..Self::MATCH_BINDER_VARIABLE_CEILING)
            .contains(&variable.0)
    }

    /// The first runtime error an evaluation under this budget dropped
    /// because every path of a sub-evaluation ended in one, for the message
    /// a caller writes when the evaluation produced no value path at all.
    pub fn dropped_runtime_error(&self) -> Option<&CRuntimeError> {
        self.dropped_runtime_error.as_ref()
    }

    /// The first constant element range this budget's lowering refused as a
    /// 32-bit byte extent, for the message a caller writes when the lowering
    /// produced no path at all.
    pub fn dropped_range_extent(&self) -> Option<&super::DroppedRangeExtent> {
        self.dropped_range_extent.as_ref()
    }

    /// Records such a refusal. Diagnostic only; it decides nothing.
    pub(in crate::kernel) fn record_dropped_range_extent(
        &mut self,
        element_count: i64,
        element_width: u32,
        byte_limit: u32,
    ) {
        self.dropped_range_extent
            .get_or_insert(super::DroppedRangeExtent {
                element_count,
                element_width,
                byte_limit,
            });
    }

    /// The fixed work allowances every budget starts from, beside the one
    /// field a caller must choose. Private, so "the other fields' defaults"
    /// stays a convenience and never becomes a way to leave the
    /// fresh-identity counter unspecified.
    fn with_kernel_variable_counter(next_kernel_variable: u64) -> Self {
        Self {
            expression_steps: 10_000,
            statement_steps: 10_000,
            function_calls: 1_000,
            loop_unrolls: 256,
            paths: 10_000,
            next_opaque_call: 0,
            next_kernel_variable,
            next_match_binder_variable: Self::MATCH_BINDER_VARIABLE_BASE,
            refuses_execution_identities: false,
            dropped_runtime_error: None,
            dropped_range_extent: None,
        }
    }

    /// A budget for an execution that has issued nothing yet: the
    /// fresh-identity counter starts at [`Self::KERNEL_VARIABLE_BASE`].
    ///
    /// Legitimate only where no live state carries identities some execution
    /// issued -- a brand-new symbolic execution, or a check of a closed
    /// theorem whose state the caller did not execute into. Anything
    /// evaluated against a live execution state uses
    /// [`Self::continuing_from`] instead: restarting the counter beside live
    /// state is how a loop-havocked local and a re-bound model field, or a
    /// join-abstracted pointer and a later heap block, became one `Variable`.
    pub(crate) fn for_new_execution() -> Self {
        Self::with_kernel_variable_counter(Self::KERNEL_VARIABLE_BASE)
    }

    /// A budget that continues an execution which has already reached `mark`,
    /// the execution-relative offset [`Self::next_kernel_variable`] reports
    /// and `ExecutionProofCore::kernel_variable_mark` holds.
    ///
    /// Everything this budget invents counts up from there, so it cannot name
    /// anything the execution has already handed out. Where the evaluation's
    /// result flows back into the live state, the caller reads the reached
    /// mark back with [`Self::next_kernel_variable`] and installs it with
    /// `ExecutionProofCore::advance_kernel_variable_mark`.
    pub(crate) fn continuing_from(mark: u64) -> Self {
        Self::with_kernel_variable_counter(Self::KERNEL_VARIABLE_BASE + mark)
    }

    /// Evaluates against a live execution state; may mint match binders,
    /// refuses execution identities.
    ///
    /// The evaluation belongs to a state some live execution owns, and it is
    /// reached from a site the execution's mark has not been threaded to.
    /// **It cannot allocate an execution identity at all.**
    ///
    /// It used to restart the counter at [`Self::KERNEL_VARIABLE_BASE`] and
    /// was named `restarting_beside_live_state` for saying so, which made the
    /// hazard greppable but left it live: the one site that did allocate
    /// handed match binders the identities a loop havoc had already given to
    /// a local, and the binder-elimination rewrite substituted the local
    /// along with the binder. Match binders now come from
    /// [`Self::MATCH_BINDER_VARIABLE_BASE`], a range no execution can reach,
    /// so nothing these sites invent needs the execution counter — and asking
    /// for one is a defect in the caller rather than a silent collision. The
    /// request refuses with
    /// [`ExecutionLimit::ExecutionIdentityBesideLiveState`], so the counter
    /// this constructor still starts at the base is never read.
    ///
    /// The users are the proof-side evaluation families reached from the
    /// surface's `have`, `fold`, `unfold` and theorem-application drivers,
    /// which do not carry the execution's mark. A site that genuinely has to
    /// invent an execution identity must be given that mark and use
    /// [`Self::continuing_from`]; `docs/internals/kernel.md` records why.
    pub(crate) fn beside_live_state() -> Self {
        let mut budget = Self::for_new_execution();
        budget.refuses_execution_identities = true;
        budget
    }

    /// [`Self::for_new_execution`] under its historical name, for tests that
    /// build a budget over a state they constructed themselves.
    #[cfg(test)]
    pub(crate) fn new() -> Self {
        Self::for_new_execution()
    }

    /// The work allowance of one selected C expression over a new execution,
    /// for tests. Production callers open the budget explicitly and add the
    /// cost with [`Self::with_c_expression_cost`].
    #[cfg(test)]
    pub(crate) fn for_c_expression(expression: &CExpression) -> Self {
        Self::for_new_execution().with_c_expression_cost(expression)
    }

    /// [`Self::continuing_from`] as a builder step, for tests that set the
    /// counter on a budget they already built.
    #[cfg(test)]
    pub(crate) fn with_next_kernel_variable(mut self, next_kernel_variable: u64) -> Self {
        self.next_kernel_variable = Self::KERNEL_VARIABLE_BASE + next_kernel_variable;
        self
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
    ///
    /// This is a work allowance, not a counter: it is added to a budget the
    /// caller has already opened with [`Self::for_new_execution`] or
    /// [`Self::continuing_from`], so the choice between the two stays at the
    /// call site rather than hiding inside a constructor.
    pub(crate) fn with_c_expression_cost(self, expression: &CExpression) -> Self {
        self.with_c_source_cost(c_expression_source_cost(expression))
    }

    /// Adds the evaluator work inherent in one selected C statement tree.
    pub(crate) fn with_c_statement_cost(self, statement: &CStatement) -> Self {
        self.with_c_source_cost(c_statement_source_cost(statement))
    }

    /// Adds the structural work of the independent verification evaluator.
    /// Ordinary leaf statements cross both its verification dispatcher and
    /// the shared statement evaluator, so their baseline contains two visits.
    pub(crate) fn with_c_statement_verification_cost(self, statement: &CStatement) -> Self {
        self.with_c_source_cost(c_statement_verification_source_cost(statement))
    }

    /// Adds the evaluator work inherent in one selected whole-function
    /// judgment, including evaluation of its caller-side arguments.
    pub(crate) fn with_c_function_cost(
        self,
        function: &CFunction,
        arguments: &[CExpression],
    ) -> Self {
        let mut cost = c_statement_source_cost(function.body());
        for argument in arguments {
            cost.add_expression(c_expression_source_cost(argument).expression_steps);
        }
        self.with_c_source_cost(cost)
    }

    pub(crate) fn with_c_function_verification_cost(
        self,
        function: &CFunction,
        arguments: &[CExpression],
    ) -> Self {
        let mut cost = c_statement_verification_source_cost(function.body());
        for argument in arguments {
            cost.add_expression(c_expression_source_cost(argument).expression_steps);
        }
        self.with_c_source_cost(cost)
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

    /// The mark this budget's evaluation has reached, execution-relative: the
    /// value a caller installs with
    /// `ExecutionProofCore::advance_kernel_variable_mark` when the
    /// evaluation's result flows back into the live state.
    pub(crate) fn next_kernel_variable(&self) -> u64 {
        self.next_kernel_variable - Self::KERNEL_VARIABLE_BASE
    }

    /// One identity from this execution's single kernel-variable counter.
    ///
    /// Every kernel allocation made under this budget comes through here --
    /// a loop head's havoc of modified locals, a re-bound binder's model
    /// fields, an opaque call result, a heap allocation, a branch join's
    /// abstraction -- so two of them cannot hand the same identity to two
    /// different things.
    ///
    /// The counter starts at [`ExecutionBudget::KERNEL_VARIABLE_BASE`] and
    /// refuses at [`ExecutionBudget::KERNEL_VARIABLE_CEILING`], which is the
    /// lowest identity some other producer reserves by a constant. Without
    /// that check a long enough execution would walk into the surface's
    /// quantifier variables, then the spec fold binders, then the algebraic
    /// binders, silently: each of those ranges is chosen to be disjoint from
    /// this one and nothing else enforces it. The check is one comparison.
    ///
    /// A budget built by [`Self::beside_live_state`] cannot issue one at all:
    /// its counter would start over identities the live state already holds,
    /// and nothing it evaluates needs an execution identity.
    pub(in crate::kernel) fn allocate_kernel_variable(&mut self) -> ExecutionResult<Variable> {
        if self.refuses_execution_identities {
            return Err(ExecutionLimit::ExecutionIdentityBesideLiveState);
        }
        if self.next_kernel_variable >= Self::KERNEL_VARIABLE_CEILING {
            return Err(ExecutionLimit::KernelVariables {
                ceiling: Self::KERNEL_VARIABLE_CEILING,
            });
        }
        let variable = Variable(self.next_kernel_variable);
        self.next_kernel_variable += 1;
        Ok(variable)
    }

    /// One binder identity for a match arm this lowering is building.
    ///
    /// The counter is this budget's own and counts through
    /// [`Self::MATCH_BINDER_VARIABLE_BASE`], so two binders of one lowering
    /// -- including a nested match's, whose arms are lowered while the
    /// enclosing arm is being built -- are always distinct, and no binder can
    /// equal a free identity of any execution, quantifier, fold, load or
    /// pointer producer.
    ///
    /// Two separately lowered terms do reuse these identities, because each
    /// budget starts its binder counter at the base. That is safe exactly
    /// because they are bound: substituting one term under the other's binder
    /// goes through `TermRewrite`, which alpha-renames a binder that would
    /// capture a free variable of the replacement and stops substituting
    /// under a binder that shadows the variable being replaced. Alpha-
    /// equivalent terms are interchangeable; a free identity shared with
    /// something live is not.
    pub(in crate::kernel) fn allocate_match_binder_variable(
        &mut self,
    ) -> ExecutionResult<Variable> {
        if self.next_match_binder_variable >= Self::MATCH_BINDER_VARIABLE_CEILING {
            return Err(ExecutionLimit::MatchBinderVariables {
                ceiling: Self::MATCH_BINDER_VARIABLE_CEILING,
            });
        }
        let variable = Variable(self.next_match_binder_variable);
        self.next_match_binder_variable += 1;
        Ok(variable)
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
        if crate::kernel::assumptions::reasoning_interrupted() {
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
            CExpression::FloatNegate(expression)
            | CExpression::FloatClassification { expression, .. } => {
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
            | CStatement::Goto { .. }
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
            CStatement::TryCatchInt32 {
                try_body, handler, ..
            } => {
                pending.push(try_body);
                pending.push(handler);
            }
            CStatement::Return(expression) | CStatement::Throw(expression) => {
                cost.add_expression(c_expression_source_steps(expression));
            }
            CStatement::Store { pointer, value }
            | CStatement::TypedStore { pointer, value, .. } => {
                // The store target is evaluated as a synthesized load lvalue.
                cost.add_expression(1usize.saturating_add(c_expression_source_steps(pointer)));
                cost.add_expression(c_expression_source_steps(value));
            }
            CStatement::CopyAggregate { target, source, .. } => {
                cost.add_expression(c_expression_source_steps(target));
                cost.add_expression(c_expression_source_steps(source));
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
    if crate::kernel::assumptions::reasoning_interrupted() {
        return Err(ExecutionLimit::Deadline);
    }
    if *remaining == 0 {
        return Err(limit);
    }
    *remaining -= 1;
    Ok(())
}
