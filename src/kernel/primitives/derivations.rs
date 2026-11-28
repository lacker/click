use super::*;
use crate::kernel::{CompareRelation, MachineIntegerType};

impl Theorem {
    pub(in crate::kernel) fn new(proposition: Proposition) -> Self {
        Self {
            proposition: std::sync::Arc::new(proposition),
            deferred_premises: None,
        }
    }

    /// Issue an execution theorem with its ambient context as shared
    /// evidence. The caller has established the path under that exact context.
    pub(in crate::kernel) fn with_ambient_premises(
        proposition: Proposition,
        assumptions: &PureFactContext,
    ) -> Self {
        Self {
            proposition: std::sync::Arc::new(proposition),
            deferred_premises: Some(std::sync::Arc::new(DeferredTheoremPremises {
                propositions: assumptions.prop_facts.clone(),
                conditions: assumptions.condition_facts.clone(),
                standalone: OnceLock::new(),
            })),
        }
    }

    pub fn proposition(&self) -> &Proposition {
        match &self.deferred_premises {
            None => &self.proposition,
            Some(retained) => retained.standalone.get_or_init(|| {
                crate::kernel::reasoning::path_facts::wrap_ambient_proof_facts(
                    self.proposition.as_ref().clone(),
                    &retained.propositions,
                    &retained.conditions,
                )
            }),
        }
    }

    /// Inspect the execution judgment, with its proof premises discharged by
    /// the caller's existing evidence checks. This returns syntax only.
    pub(crate) fn execution_conclusion(&self) -> &Proposition {
        let mut conclusion = self.proposition.as_ref();
        while let Proposition::Implies(_, body) = conclusion {
            conclusion = body;
        }
        conclusion
    }
}

impl std::fmt::Debug for Theorem {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("Theorem")
            .field("proposition", &self.proposition())
            .finish()
    }
}

impl PartialEq for Theorem {
    fn eq(&self, other: &Self) -> bool {
        // Both pieces are immutable and created together. Cloning a theorem
        // retains its proof, including the exact ambient premises.
        std::sync::Arc::ptr_eq(&self.proposition, &other.proposition)
            || self.proposition() == other.proposition()
    }
}

impl Eq for Theorem {}

impl std::hash::Hash for Theorem {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.proposition().hash(state);
    }
}

impl Ord for Theorem {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if std::sync::Arc::ptr_eq(&self.proposition, &other.proposition) {
            return std::cmp::Ordering::Equal;
        }
        self.proposition().cmp(other.proposition())
    }
}

impl PartialOrd for Theorem {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PropositionDerivation {
    /// Whether this equality retained exact constants and singleton bounds.
    /// Surface transcription uses only the retained context premises to emit
    /// an ordinary explicit arithmetic proof.
    pub fn is_int32_pinned_constant_equality(&self) -> bool {
        matches!(
            &self.rule,
            PropositionDerivationRule::ContextualAtomic {
                evidence: AtomicPropositionDerivationEvidence::Int32PinnedConstantEquality(_),
                ..
            }
        )
    }

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

    /// Return the checked selected disjunct and whether it is the left one.
    pub fn disjunction_choice(&self) -> Option<(bool, &Self)> {
        match &self.rule {
            PropositionDerivationRule::OrLeft(proof) => Some((true, proof)),
            PropositionDerivationRule::OrRight(proof) => Some((false, proof)),
            _ => None,
        }
    }

    /// Return the exact ordered edges selected by an atomic signed-order
    /// decision. `None` means this derivation used another rule; an empty
    /// path is never recorded.
    pub fn signed_order_path(&self) -> Option<&[OrderDerivationStep]> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence: AtomicPropositionDerivationEvidence::SignedOrderPath(path),
                ..
            } => Some(path),
            _ => None,
        }
    }

    /// Return the format and the exact ordered edges selected by an atomic
    /// 64-bit or `uint32` order decision.
    pub fn wide_order_path(&self) -> Option<(MachineIntegerType, &[OrderDerivationStep])> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence: AtomicPropositionDerivationEvidence::WideOrderPath { format, path },
                ..
            } => Some((*format, path)),
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
    /// load variables address one cell in one memory version.
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
    ) -> Option<(&Proposition, &OldMachineTerm, &[Proposition])> {
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
    pub fn int32_increment_below_max_is_defined_premise(&self) -> Option<&Proposition> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence: AtomicPropositionDerivationEvidence::Int32IncrementBelowMaxIsDefined(step),
                ..
            } => Some(step),
            _ => None,
        }
    }

    /// Return the exact maximum bound selected for `defined(1 + value)`.
    pub fn int32_one_plus_below_max_is_defined_premise(&self) -> Option<&Proposition> {
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
    pub fn int32_nonnegative_add_within_max_premises(
        &self,
    ) -> Option<(&Proposition, &Proposition)> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence:
                    AtomicPropositionDerivationEvidence::Int32NonnegativeAddWithinMaxIsDefined(evidence),
                ..
            } => Some((&evidence[0], &evidence[1])),
            _ => None,
        }
    }

    /// Return the exact nonnegative-amount and amount-within-value premises
    /// selected when the atomic prover established symbolic subtraction
    /// definedness through the named int32 theorem.
    pub fn int32_nonnegative_subtract_within_value_premises(
        &self,
    ) -> Option<(&Proposition, &Proposition)> {
        match &self.rule {
            PropositionDerivationRule::ContextualAtomic {
                evidence:
                    AtomicPropositionDerivationEvidence::Int32NonnegativeSubtractWithinValueIsDefined(
                        evidence,
                    ),
                ..
            } => Some((&evidence[0], &evidence[1])),
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

    /// Return the exact `0 < value` premise selected when the atomic prover
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

    /// The premises an equality or signed-order path names, when this
    /// derivation recorded one: the facts its typed closer cites, in path
    /// order without repeats.
    pub fn recorded_path_premises(&self) -> Option<Vec<Proposition>> {
        let mut premises = Vec::new();
        let mut seen = BTreeSet::new();
        let mut push = |premise: &Proposition| {
            if seen.insert(premise.clone()) {
                premises.push(premise.clone());
            }
        };
        if let Some(path) = self.bitvector_equality_path() {
            path.iter().for_each(|step| push(step.premise()));
        } else {
            let path = self.signed_order_path()?;
            path.iter().for_each(|step| push(step.premise()));
        }
        Some(premises)
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
                premises.insert(source.as_ref().clone());
            }
            PropositionDerivationRule::OrLeft(proof)
            | PropositionDerivationRule::OrRight(proof)
            | PropositionDerivationRule::DoubleNegation(proof)
            | PropositionDerivationRule::ImpliesFalseAntecedent(proof)
            | PropositionDerivationRule::ForAllBody { proof, .. } => {
                proof.collect_context_premises(premises);
            }
            PropositionDerivationRule::ExistsFromFact {
                source,
                witness,
                body,
            } => {
                premises.insert(source.as_ref().clone());
                let mut body_premises = BTreeSet::new();
                body.collect_context_premises(&mut body_premises);
                if let Proposition::Exists {
                    var: source_var,
                    sort,
                    body: source_body,
                    ..
                } = source.as_ref()
                    && let Some(renamed) = crate::kernel::quantifiers::rename_quantified_variable(
                        source_body,
                        **source_var,
                        *witness,
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
                premises.insert(source.as_ref().clone());
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
            PropositionDerivationRule::RefutedDisjunction { disjunction } => {
                premises.insert(disjunction.as_ref().clone());
                let mut cases = Vec::new();
                collect_or_cases(disjunction, &mut cases);
                for case in cases {
                    premises.insert(Proposition::Not(Box::new(case)));
                }
            }
            PropositionDerivationRule::DisjunctionCases { disjunction, cases } => {
                premises.insert(disjunction.as_ref().clone());
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

impl AtomicPropositionDerivationEvidence {
    /// Exact sources already retained by these equality producers. Other
    /// evidence families keep their selected context until they expose a
    /// complete dependency list too; partial dependencies are never sufficient.
    pub(in crate::kernel) fn equality_premises(&self) -> Option<BTreeSet<Proposition>> {
        let mut premises = BTreeSet::new();
        match self {
            Self::BitvectorEqualityPath(path) => {
                for step in path {
                    crate::instrumentation::record_deterministic_work(1);
                    premises.insert(step.premise.clone());
                }
            }
            Self::LoadAddressCongruence(evidence) => {
                evidence.offset.collect_equality_premises(&mut premises)?;
            }
            Self::Int32PinnedConstantEquality(evidence) => {
                evidence.collect_context_premises(&mut premises);
            }
            Self::Int32LeAndNotLtImpliesEquality(evidence) => {
                premises.insert(evidence.less_equal.clone());
                premises.insert(evidence.not_less_than.clone());
            }
            Self::Int32GeAndNotGtImpliesEquality(evidence) => {
                premises.insert(evidence.greater_equal.clone());
                premises.insert(evidence.not_greater_than.clone());
            }
            _ => return None,
        }
        Some(premises)
    }
}

impl PointerOffsetCongruenceEvidence {
    fn collect_equality_premises(&self, premises: &mut BTreeSet<Proposition>) -> Option<()> {
        crate::instrumentation::record_deterministic_work(1);
        match self {
            Self::Exact => {}
            // This rule currently asks the context for constants without
            // retaining their sources. Keep its original selected context.
            Self::WideScaledConstant { .. } => return None,
            Self::ExactPremise(premise) => {
                premises.insert(premise.as_ref().clone());
            }
            Self::Add { first, second, .. } => {
                first.collect_equality_premises(premises)?;
                second.collect_equality_premises(premises)?;
            }
            Self::Int32Scaled { path, .. }
            | Self::Int64Scaled { path, .. }
            | Self::ElementIndex { path, .. } => {
                for step in path {
                    crate::instrumentation::record_deterministic_work(1);
                    premises.insert(step.premise.clone());
                }
            }
            Self::Int32ScaledDerived { equality, .. }
            | Self::ElementIndexDerived { equality, .. } => {
                equality.collect_context_premises(premises);
            }
        }
        Some(())
    }

    fn equality_paths(&self) -> Vec<&[BitvectorEqualityDerivationStep]> {
        match self {
            Self::Exact | Self::ExactPremise(_) | Self::WideScaledConstant { .. } => Vec::new(),
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
        left: &AddressOffset,
        right: &AddressOffset,
        assumptions: &PureFactContext,
    ) -> bool {
        match self {
            Self::Exact => left == right,
            Self::WideScaledConstant { value } => {
                crate::kernel::assumptions::exact_wide_scaled_offset_constant(left, assumptions)
                    == Some(*value)
                    && crate::kernel::assumptions::exact_wide_scaled_offset_constant(
                        right,
                        assumptions,
                    ) == Some(*value)
            }
            Self::ExactPremise(premise) => {
                let Proposition::ConditionIs(condition, true) = premise.as_ref() else {
                    return false;
                };
                let Some((premise_left, premise_right)) =
                    condition.old_form().pointer_offset_sides()
                else {
                    return false;
                };
                assumptions.contains_assumed_exact(premise)
                    && ((premise_left == left && premise_right == right)
                        || (premise_left == right && premise_right == left))
            }
            Self::Add {
                first,
                second,
                swapped,
            } => {
                let (OffsetView::Add(left_a, left_b), OffsetView::Add(right_a, right_b)) =
                    (left.view(), right.view())
                else {
                    return false;
                };
                let (right_first, right_second) = if *swapped {
                    (right_b, right_a)
                } else {
                    (right_a, right_b)
                };
                first.checks(left_a, right_first, assumptions)
                    && second.checks(left_b, right_second, assumptions)
            }
            Self::Int32Scaled { byte_width, path } => {
                let (
                    OffsetView::Int32Scaled {
                        index: left,
                        byte_width: left_width,
                    },
                    OffsetView::Int32Scaled {
                        index: right,
                        byte_width: right_width,
                    },
                ) = (left.view(), right.view())
                else {
                    return false;
                };
                left_width == *byte_width
                    && right_width == *byte_width
                    && assumptions.checks_exact_bitvector_equality_path_views(
                        path,
                        left.operand_view(),
                        right.operand_view(),
                    )
            }
            Self::Int32ScaledDerived {
                byte_width,
                equality,
            } => {
                let (
                    OffsetView::Int32Scaled {
                        index: left,
                        byte_width: left_width,
                    },
                    OffsetView::Int32Scaled {
                        index: right,
                        byte_width: right_width,
                    },
                ) = (left.view(), right.view())
                else {
                    return false;
                };
                left_width == *byte_width
                    && right_width == *byte_width
                    && equality.checks_views(left.operand_view(), right.operand_view(), assumptions)
            }
            Self::Int64Scaled {
                byte_width,
                unsigned,
                path,
            } => {
                let (
                    OffsetView::Int64Scaled {
                        index: left,
                        byte_width: left_width,
                        unsigned: left_unsigned,
                    },
                    OffsetView::Int64Scaled {
                        index: right,
                        byte_width: right_width,
                        unsigned: right_unsigned,
                    },
                ) = (left.view(), right.view())
                else {
                    return false;
                };
                left_width == *byte_width
                    && right_width == *byte_width
                    && left_unsigned == *unsigned
                    && right_unsigned == *unsigned
                    && assumptions.checks_exact_bitvector_equality_path_views(
                        path,
                        left.operand_view(),
                        right.operand_view(),
                    )
            }
            Self::ElementIndex { byte_width, path } => {
                if crate::kernel::reasoning::common_pointer_offset_element_width(left, right)
                    != Some(*byte_width)
                {
                    return false;
                }
                let (Some(left), Some(right)) = (
                    crate::kernel::reasoning::shared_element_index_from_offset(left, *byte_width),
                    crate::kernel::reasoning::shared_element_index_from_offset(right, *byte_width),
                ) else {
                    return false;
                };
                assumptions.checks_exact_bitvector_equality_path_views(
                    path,
                    left.operand_view(),
                    right.operand_view(),
                )
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
                    crate::kernel::reasoning::shared_element_index_from_offset(left, *byte_width),
                    crate::kernel::reasoning::shared_element_index_from_offset(right, *byte_width),
                ) else {
                    return false;
                };
                equality.checks_views(left.operand_view(), right.operand_view(), assumptions)
            }
        }
    }
}

impl SignedConstantEvidence {
    pub(in crate::kernel) fn exact_equality_value_view(
        term: crate::kernel::MachineOperandView<'_>,
        source: &Proposition,
    ) -> Option<i64> {
        use crate::kernel::machine_integer::{Relation, comparison::comparison_view};
        let Proposition::ConditionIs(condition, value) = source else {
            return None;
        };
        let view = comparison_view(condition.old_form(), *value)?;
        if !matches!(
            view.format,
            MachineIntegerType::Int32 | MachineIntegerType::UInt32
        ) || view.relation != Relation::Equal
        {
            return None;
        }
        use crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey;
        let key = ScalarOperandKey::new(term);
        let [left, right] = view
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        let other = if ScalarOperandKey::new(left) == key {
            right
        } else if ScalarOperandKey::new(right) == key {
            left
        } else {
            return None;
        };
        other.word32_constant().map(|bits| i64::from(bits as i32))
    }
}

impl DirectBitvectorEqualityEvidence {
    pub(in crate::kernel) fn checks(
        &self,
        left: &OldMachineTerm,
        right: &OldMachineTerm,
        assumptions: &PureFactContext,
    ) -> bool {
        self.checks_views(
            crate::kernel::MachineOperandView::Old(left),
            crate::kernel::MachineOperandView::Old(right),
            assumptions,
        )
    }

    pub(in crate::kernel) fn checks_views(
        &self,
        left: crate::kernel::MachineOperandView<'_>,
        right: crate::kernel::MachineOperandView<'_>,
        assumptions: &PureFactContext,
    ) -> bool {
        match self {
            Self::AdditiveCancellation {
                left: reduced_left,
                right: reduced_right,
                equality,
            } => {
                crate::kernel::reasoning::shared_bitvector_equality_cancellation(left, right)
                    == Some((reduced_left.clone(), reduced_right.clone()))
                    && equality.checks_views(
                        reduced_left.operand_view(),
                        reduced_right.operand_view(),
                        assumptions,
                    )
            }
            Self::EqualSignedConstants {
                value,
                left: left_evidence,
                right: right_evidence,
            } => {
                let checks = |term: crate::kernel::MachineOperandView<'_>,
                              evidence: &SignedConstantEvidence| {
                    match evidence {
                        SignedConstantEvidence::Constant => {
                            term.word32_constant().map(|n| i64::from(n as i32)) == Some(*value)
                        }
                        SignedConstantEvidence::ExactEquality(source) => {
                            assumptions.contains_assumed_exact(source)
                                && SignedConstantEvidence::exact_equality_value_view(term, source)
                                    == Some(*value)
                        }
                        SignedConstantEvidence::SingletonBounds {
                            variable,
                            lower,
                            upper,
                        } => {
                            let bound =
                                |evidence: &IndexedSignedOrderBoundEvidence, lower_bound: bool| {
                                    use crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey as Key;
                                    let Proposition::ConditionIs(condition, truth) =
                                        evidence.source.as_ref()
                                    else {
                                        return None;
                                    };
                                    let view = crate::kernel::assumptions::order_view_at_format(
                                        condition.old_form(),
                                        *truth,
                                        MachineIntegerType::Int32,
                                    )?;
                                    let strict = view.relation
                                        == crate::kernel::machine_integer::Relation::Less;
                                    let [left, right] = view
                                        .operands
                                        .each_ref()
                                        .map(|operand| operand.operand_view());
                                    let (endpoint, other) = if evidence.forward {
                                        (left, right)
                                    } else {
                                        (right, left)
                                    };
                                    if !assumptions.contains_assumed_exact(&evidence.source)
                                        || Key::new(endpoint) != Key::new(term)
                                        || lower_bound == evidence.forward
                                    {
                                        return None;
                                    }
                                    let bound = if let Some(source) = &evidence.other_equality {
                                        if !assumptions.contains_assumed_exact(source) {
                                            return None;
                                        }
                                        SignedConstantEvidence::exact_equality_value_view(
                                            other, source,
                                        )?
                                    } else {
                                        other
                                            .word32_constant()
                                            .map(|bits| i64::from(bits as i32))?
                                    };
                                    if lower_bound {
                                        if strict {
                                            bound.checked_add(1)
                                        } else {
                                            Some(bound)
                                        }
                                    } else if strict {
                                        bound.checked_sub(1)
                                    } else {
                                        Some(bound)
                                    }
                                };
                            term.variable() == Some(variable)
                                && bound(lower, true) == Some(*value)
                                && bound(upper, false) == Some(*value)
                        }
                    }
                };
                checks(left, left_evidence) && checks(right, right_evidence)
            }
            Self::LeAndNotLt(evidence) => {
                let less_equal = Proposition::condition_is(
                    crate::kernel::machine_integer::comparison::condition_for_operand_views(
                        MachineIntegerType::Int32,
                        CompareRelation::LessEqual,
                        [left, right],
                    ),
                    true,
                );
                let not_less_than = Proposition::condition_is(
                    crate::kernel::machine_integer::comparison::condition_for_operand_views(
                        MachineIntegerType::Int32,
                        CompareRelation::LessThan,
                        [left, right],
                    ),
                    false,
                );
                evidence.less_equal == less_equal
                    && evidence.not_less_than == not_less_than
                    && assumptions.contains_assumed_exact(&evidence.less_equal)
                    && assumptions.contains_assumed_exact(&evidence.not_less_than)
            }
            Self::GeAndNotGt(evidence) => {
                let greater_equal = Proposition::condition_is(
                    crate::kernel::machine_integer::comparison::condition_for_operand_views(
                        MachineIntegerType::Int32,
                        CompareRelation::GreaterEqual,
                        [left, right],
                    ),
                    true,
                );
                let not_greater_than = Proposition::condition_is(
                    crate::kernel::machine_integer::comparison::condition_for_operand_views(
                        MachineIntegerType::Int32,
                        CompareRelation::GreaterThan,
                        [left, right],
                    ),
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
            match evidence {
                SignedConstantEvidence::Constant => {}
                SignedConstantEvidence::ExactEquality(source) => {
                    premises.insert(source.as_ref().clone());
                }
                SignedConstantEvidence::SingletonBounds { lower, upper, .. } => {
                    for bound in [lower, upper] {
                        premises.insert(bound.source.as_ref().clone());
                        if let Some(source) = &bound.other_equality {
                            premises.insert(source.as_ref().clone());
                        }
                    }
                }
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
        let Some((
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left,
                right,
            },
            true,
        )) = proposition.old_condition()
        else {
            return false;
        };
        let (Some(left), Some(right)) = (
            crate::kernel::eval::scalar_read_observation(crate::kernel::MachineOperandView::Old(
                left,
            )),
            crate::kernel::eval::scalar_read_observation(crate::kernel::MachineOperandView::Old(
                right,
            )),
        ) else {
            return false;
        };
        let (left_pointer, right_pointer) = (&left.pointer, &right.pointer);
        left.point == right.point
            && left.kind == right.kind
            && *left_pointer == self.left_pointer
            && *right_pointer == self.right_pointer
            && left_pointer.base == right_pointer.base
            && self
                .offset
                .checks(&left_pointer.offset, &right_pointer.offset, assumptions)
    }
}

impl OrderDerivationStep {
    /// The exact proposition supporting this oriented edge.
    pub fn premise(&self) -> &Proposition {
        &self.premise
    }
}

impl SignedOrderDerivationStep {
    pub(in crate::kernel) fn from_views(
        lower: MachineOperandView<'_>,
        upper: MachineOperandView<'_>,
        strict: bool,
        premise: Proposition,
    ) -> Self {
        use super::super::assumptions::checked_scalar_facts::ScalarOperandKey as Key;
        let retain = |operand| match operand {
            MachineOperandView::Old(term) => Key::Written(term.clone()),
            MachineOperandView::Shared(_) => Key::for_format(MachineIntegerType::Int32, operand),
        };
        Self {
            lower: retain(lower),
            upper: retain(upper),
            strict,
            premise,
        }
    }

    pub(in crate::kernel) fn lower_view(&self) -> MachineOperandView<'_> {
        self.lower.operand_view()
    }

    pub(in crate::kernel) fn upper_view(&self) -> MachineOperandView<'_> {
        self.upper.operand_view()
    }

    fn endpoint_matches(
        endpoint: &super::super::assumptions::checked_scalar_facts::ScalarOperandKey,
        value: MachineOperandView<'_>,
    ) -> bool {
        use super::super::assumptions::checked_scalar_facts::ScalarOperandKey as Key;
        if let (Key::Written(left), MachineOperandView::Old(right)) = (endpoint, value) {
            left == right
        } else {
            Key::for_format(MachineIntegerType::Int32, endpoint.operand_view())
                == Key::for_format(MachineIntegerType::Int32, value)
        }
    }

    pub(in crate::kernel) fn lower_matches_view(&self, value: MachineOperandView<'_>) -> bool {
        Self::endpoint_matches(&self.lower, value)
    }

    pub(in crate::kernel) fn upper_matches_view(&self, value: MachineOperandView<'_>) -> bool {
        Self::endpoint_matches(&self.upper, value)
    }

    pub(in crate::kernel) fn lower_is(&self, value: &OldMachineTerm) -> bool {
        self.lower_matches_view(MachineOperandView::Old(value))
    }

    pub(in crate::kernel) fn upper_is(&self, value: &OldMachineTerm) -> bool {
        self.upper_matches_view(MachineOperandView::Old(value))
    }

    /// Explicit compatibility output; checker consumers use `lower_view`.
    pub fn lower(&self) -> &OldMachineTerm {
        match &self.lower {
            super::super::assumptions::checked_scalar_facts::ScalarOperandKey::Shared(term) => {
                term.value()
            }
            super::super::assumptions::checked_scalar_facts::ScalarOperandKey::Written(term) => {
                term
            }
        }
    }

    pub fn upper(&self) -> &OldMachineTerm {
        match &self.upper {
            super::super::assumptions::checked_scalar_facts::ScalarOperandKey::Shared(term) => {
                term.value()
            }
            super::super::assumptions::checked_scalar_facts::ScalarOperandKey::Written(term) => {
                term
            }
        }
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
    pub(crate) fn source_view(&self) -> MachineOperandView<'_> {
        self.source.operand_view()
    }
    pub(crate) fn target_view(&self) -> MachineOperandView<'_> {
        self.target.operand_view()
    }

    /// Explicit compatibility output for surface certificate construction.
    pub fn source(&self) -> &OldMachineTerm {
        self.source.value()
    }

    pub fn target(&self) -> &OldMachineTerm {
        self.target.value()
    }

    pub fn premise(&self) -> &Proposition {
        &self.premise
    }
}

impl PureFactContext {
    pub(crate) fn shares_persistent_storage_with(&self, other: &Self) -> bool {
        self.condition_facts
            .shares_root_with(&other.condition_facts)
            && self
                .signed_order_bounds
                .shares_root_with(&other.signed_order_bounds)
            && self
                .int64_signed_order_bounds
                .shares_root_with(&other.int64_signed_order_bounds)
            && self
                .memory_load_condition_facts
                .shares_root_with(&other.memory_load_condition_facts)
            && self
                .equality_graph
                .admitted
                .scalar_evidence_inputs
                .shares_root_with(&other.equality_graph.admitted.scalar_evidence_inputs)
            && self
                .equality_graph
                .admitted
                .bitvector64_equality_facts
                .shares_root_with(&other.equality_graph.admitted.bitvector64_equality_facts)
            && self
                .equality_graph
                .admitted
                .wide_constant_sources
                .shares_root_with(&other.equality_graph.admitted.wide_constant_sources)
            && self.prop_facts.ptr_eq(&other.prop_facts)
            && self
                .resource_compositions
                .shares_root_with(&other.resource_compositions)
            && self
                .memory_loadable_facts
                .shares_root_with(&other.memory_loadable_facts)
            && self
                .memory_loadable_shape_facts
                .shares_root_with(&other.memory_loadable_shape_facts)
            && self
                .memory_separation_facts
                .shares_root_with(&other.memory_separation_facts)
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

    /// The first identity a symbolic execution may not invent. Load variables
    /// are in a separate higher band beginning at `1 << 40`. Those producers use bounded counters or a name hash in
    /// their own ranges, so they cannot avoid an execution
    /// that has counted into their range; the execution refuses instead.
    pub(in crate::kernel) const KERNEL_VARIABLE_CEILING: u64 = 2_000_000;

    /// How many match-arm binders one lowering may allocate. A lowering that
    /// needs more refuses here, as the execution counter refuses at
    /// [`Self::KERNEL_VARIABLE_CEILING`].
    pub(in crate::kernel) const MATCH_BINDER_LIMIT: u64 = 1 << 40;

    /// Whether `variable` is a match-arm binder.
    ///
    /// A rewrite that eliminates a binder asks this before substituting: any
    /// other variable is a free variable of some execution or producer, and
    /// substituting it would be a capture rather than a binder elimination.
    pub(in crate::kernel) fn is_match_binder_variable(variable: Variable) -> bool {
        variable.is_match_binder()
    }

    /// How many witnesses one proof state may introduce. `intro()` on
    /// `forall v. body` replaces `v` by a *free* variable that stands for an
    /// arbitrary value, so it must name nothing the surrounding state names:
    /// program variables, the store, the memory state and resources as well
    /// as the facts. Witnesses have their own origin, which no other producer
    /// mints, so that is structural; a proof that needs more than this many
    /// refuses rather than reusing one.
    pub(in crate::kernel) const UNIVERSAL_WITNESS_LIMIT: u64 = 1 << 40;

    /// Whether `variable` is a universal-introduction or choice witness.
    #[cfg(test)]
    pub(in crate::kernel) fn is_universal_witness_variable(variable: Variable) -> bool {
        variable.is_witness()
    }

    /// The first runtime error an evaluation under this budget dropped
    /// because every path of a sub-evaluation ended in one, for the message
    /// a caller writes when the evaluation produced no value path at all.
    pub fn dropped_runtime_error(&self) -> Option<&RuntimeError> {
        self.dropped_runtime_error.as_ref()
    }

    /// The first undefined behavior an evaluation under this budget dropped
    /// because every path of a sub-evaluation ended in it, for the message a
    /// caller writes when the evaluation produced no value path at all.
    pub fn dropped_undefined_behavior(&self) -> Option<&UndefinedBehavior> {
        self.dropped_undefined_behavior.as_ref()
    }

    /// The first constant element range this budget's lowering refused as a
    /// 32-bit byte span, for the message a caller writes when the lowering
    /// produced no path at all.
    pub fn dropped_range_span(&self) -> Option<&super::DroppedRangeSpan> {
        self.dropped_range_span.as_ref()
    }

    /// Whether a stated memory range was dropped because this context
    /// refutes one of its span guards, and whether that guard ordered the
    /// range's endpoints (`true`) or bounded its byte count (`false`).
    pub fn dropped_refuted_range_span(&self) -> Option<bool> {
        self.dropped_refuted_range_span
    }

    /// Records such a refusal. Diagnostic only; it decides nothing.
    pub(in crate::kernel) fn record_dropped_refuted_range_span(&mut self, reversed: bool) {
        self.dropped_refuted_range_span.get_or_insert(reversed);
    }

    pub(in crate::kernel) fn record_dropped_range_span(
        &mut self,
        element_count: i64,
        element_width: u32,
        byte_limit: u32,
    ) {
        self.dropped_range_span
            .get_or_insert(super::DroppedRangeSpan {
                element_count,
                element_width,
                byte_limit,
            });
    }

    /// The first range fold this budget's lowering dropped because its body
    /// did not lower to one symbolic iteration, for the message a caller
    /// writes when the lowering produced no path at all.
    pub fn dropped_fold_body(&self) -> Option<&super::DroppedFoldBody> {
        self.dropped_fold_body.as_ref()
    }

    /// Records such a refusal. Diagnostic only; it decides nothing.
    pub(in crate::kernel) fn record_dropped_fold_body(
        &mut self,
        body_paths: usize,
        unavailable_body_fact: Option<Proposition>,
        item: Variable,
    ) {
        self.dropped_fold_body
            .get_or_insert(super::DroppedFoldBody {
                body_paths,
                unavailable_body_fact,
                item,
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
            inline_call_name: None,
            paths: 10_000,
            next_opaque_call: 0,
            next_kernel_variable,
            next_match_binder_variable: 0,
            refuses_execution_identities: false,
            dropped_runtime_error: None,
            dropped_undefined_behavior: None,
            dropped_range_span: None,
            dropped_refuted_range_span: None,
            dropped_fold_body: None,
            dropped_symbolic_pointer_conditional: false,
            dropped_comparison: None,
            program_byte_order: None,
        }
    }

    /// Installs the byte order of the environment a C statement executes
    /// under, for the byte view of integer cells its loads and stores use.
    pub(in crate::kernel) fn install_program_byte_order(&mut self, byte_order: ByteOrder) {
        self.program_byte_order = Some(byte_order);
    }

    /// The byte order installed by the executing statement, if any.
    pub(in crate::kernel) fn program_byte_order(&self) -> Option<ByteOrder> {
        self.program_byte_order
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
    /// along with the binder. Match binders now have their own origin
    /// ([`Variable::match_binder`]), which no execution can mint, so nothing
    /// these sites invent needs the execution counter — and asking for one is
    /// a defect in the caller rather than a silent collision. The
    /// request refuses with
    /// [`ExecutionLimit::ExecutionIdentityBesideLiveState`], so the counter
    /// this constructor still starts at zero is never read.
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
    /// cost with [`Self::with_program_expression_cost`].
    #[cfg(test)]
    pub(crate) fn for_program_expression(expression: &ProgramExpression) -> Self {
        Self::for_new_execution().with_program_expression_cost(expression)
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
    pub(crate) fn with_program_expression_cost(self, expression: &ProgramExpression) -> Self {
        self.with_program_source_cost(program_expression_source_cost(expression))
    }

    /// Adds the evaluator work inherent in one selected C statement tree.
    #[cfg(test)]
    pub(crate) fn with_execution_statement_cost(self, statement: &ProgramStatement) -> Self {
        self.with_program_source_cost(execution_statement_source_cost(statement))
    }

    /// Adds the evaluator work inherent in one selected whole-function
    /// judgment, including evaluation of its caller-side arguments.
    pub(crate) fn with_program_function_cost(
        self,
        function: &ProgramFunction,
        arguments: &[ProgramExpression],
    ) -> Self {
        let mut cost = execution_statement_source_cost(function.body());
        for argument in arguments {
            cost.add_expression(program_expression_source_cost(argument).expression_steps);
        }
        self.with_program_source_cost(cost)
    }

    fn with_program_source_cost(mut self, cost: ProgramSourceCost) -> Self {
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
    /// quantifier variables and then the other reserved ranges, silently:
    /// each producer has its own bounded range, disjoint from
    /// this one and nothing else enforces it. The check is one comparison.
    ///
    /// A budget built by [`Self::beside_live_state`] cannot issue one at all:
    /// its counter would start over identities the live state already holds,
    /// and nothing it evaluates needs an execution identity.
    /// Moves the counter past `variable`, so nothing it hands out from now
    /// on is `variable` or below it. Identities it skips are never handed
    /// out; the counter only advances.
    /// Continue from at least `mark` ([`Self::next_kernel_variable`]): every
    /// identity below it was issued by an earlier part of this execution.
    pub(in crate::kernel) fn continue_past_mark(&mut self, mark: u64) {
        self.next_kernel_variable = self
            .next_kernel_variable
            .max(Self::KERNEL_VARIABLE_BASE + mark);
    }

    pub(in crate::kernel) fn skip_kernel_variables_through(&mut self, variable: Variable) {
        self.next_kernel_variable = self.next_kernel_variable.max(variable.0 + 1);
    }

    /// Whether this budget evaluates beside a live state, where it may not
    /// invent an execution identity ([`Self::beside_live_state`]).
    pub(in crate::kernel) fn refuses_execution_identities(&self) -> bool {
        self.refuses_execution_identities
    }

    /// A fresh identity for a resource instance this execution creates.
    ///
    /// An instance identity is its own sort: it is distinct from every other
    /// instance identity, and is never compared with a value. It takes the
    /// execution counter's next number, which no other instance this
    /// execution created holds, and which is above every identity the
    /// surface gives a binder (those count up from zero). Value freshness
    /// therefore never has to reserve instance identities, nor instance
    /// freshness values.
    pub(in crate::kernel) fn allocate_instance_identity(&mut self) -> ExecutionResult<InstanceId> {
        self.allocate_kernel_variable()
            .map(InstanceId::from_variable)
    }

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
    /// The counter is this budget's own, so two binders of one lowering --
    /// including a nested match's, whose arms are lowered while the enclosing
    /// arm is being built -- are always distinct, and the binder origin means
    /// no binder can equal a free identity of any execution, quantifier,
    /// fold, load or pointer producer.
    ///
    /// Two separately lowered terms do reuse these identities, because each
    /// budget starts its binder counter at zero. That is safe exactly
    /// because they are bound: substituting one term under the other's binder
    /// goes through `TermRewrite`, which alpha-renames a binder that would
    /// capture a free variable of the replacement and stops substituting
    /// under a binder that shadows the variable being replaced. Alpha-
    /// equivalent terms are interchangeable; a free identity shared with
    /// something live is not.
    pub(in crate::kernel) fn allocate_match_binder_variable(
        &mut self,
    ) -> ExecutionResult<Variable> {
        if self.next_match_binder_variable >= Self::MATCH_BINDER_LIMIT {
            return Err(ExecutionLimit::MatchBinderVariables {
                ceiling: Self::MATCH_BINDER_LIMIT,
            });
        }
        let variable = Variable::match_binder(self.next_match_binder_variable);
        self.next_match_binder_variable += 1;
        Ok(variable)
    }

    /// Runs `lower` with this budget's match binders counted from zero
    /// again, then resumes the count.
    ///
    /// A lowering run this way is a separately lowered term in the sense of
    /// [`Self::allocate_match_binder_variable`]: its binders may reuse
    /// identities another term holds, which is safe because they are bound.
    /// One clause lowered twice this way is then one term, so a clause read
    /// in two contracts compares exactly rather than up to binder numbering.
    pub(in crate::kernel) fn with_match_binders_from_base<T>(
        &mut self,
        lower: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let resumed = std::mem::replace(&mut self.next_match_binder_variable, 0);
        let lowered = lower(self);
        self.next_match_binder_variable = resumed;
        lowered
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
struct ProgramSourceCost {
    expression_steps: usize,
    statement_steps: usize,
}

impl ProgramSourceCost {
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
fn program_expression_source_cost(expression: &ProgramExpression) -> ProgramSourceCost {
    ProgramSourceCost::expression(program_expression_steps_for_mode(expression, false))
}

fn program_expression_source_steps(expression: &ProgramExpression) -> usize {
    program_expression_source_cost(expression).expression_steps
}

fn program_expression_steps_for_mode(expression: &ProgramExpression, lvalue: bool) -> usize {
    let mut steps = 0usize;
    let mut pending = vec![(expression, lvalue)];
    while let Some((expression, lvalue)) = pending.pop() {
        steps = steps.saturating_add(1);
        if lvalue {
            match expression {
                ProgramExpression::Load(pointer) | ProgramExpression::TypedLoad { pointer, .. } => {
                    pending.push((pointer, false));
                }
                ProgramExpression::Index(base, index) => {
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
            ProgramExpression::StringLiteral(_)
            | ProgramExpression::Value(_)
            | ProgramExpression::FunctionAddress(_)
            | ProgramExpression::StepResult { .. } => {}
            ProgramExpression::Cast { expression, .. } => pending.push((expression, false)),
            ProgramExpression::Ternary {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push((condition, false));
                pending.push((then_branch, false));
                pending.push((else_branch, false));
            }
            ProgramExpression::Negate(expression)
            | ProgramExpression::FloatNegate(expression)
            | ProgramExpression::FloatClassification { expression, .. }
            | ProgramExpression::EnumField {
                value: expression, ..
            }
            | ProgramExpression::EnumIs {
                value: expression, ..
            }
            | ProgramExpression::SliceLength(expression)
            | ProgramExpression::SliceData(expression) => pending.push((expression, false)),
            ProgramExpression::EnumConstruct { fields, .. } => {
                pending.extend(fields.iter().map(|field| (field, false)))
            }
            // Scalar variables add an lvalue visit. Arrays skip it, so this is
            // a safe structural allowance without consulting an execution
            // state during budget construction.
            ProgramExpression::Variable(_) => pending.push((expression, true)),
            ProgramExpression::AddressOf(target)
            | ProgramExpression::CheckedObjectAddress(target) => pending.push((target, true)),
            ProgramExpression::PointerOffsetBytes { pointer, .. }
            | ProgramExpression::Subobject { pointer, .. }
            | ProgramExpression::Not(pointer)
            | ProgramExpression::BitwiseNot(pointer) => pending.push((pointer, false)),
            crate::kernel::binary_c_operation!(left, right)
            | ProgramExpression::SliceFromRawParts {
                data: left,
                count: right,
            } => {
                pending.push((left, false));
                pending.push((right, false));
            }
            ProgramExpression::Load(_)
            | ProgramExpression::TypedLoad { .. }
            | ProgramExpression::Index(_, _) => pending.push((expression, true)),
        }
    }
    steps
}

fn execution_statement_source_cost(statement: &ProgramStatement) -> ProgramSourceCost {
    let mut cost = ProgramSourceCost::default();
    let mut pending = vec![statement];
    while let Some(statement) = pending.pop() {
        if !matches!(statement, ProgramStatement::Seq(_)) {
            cost.statement_steps = cost.statement_steps.saturating_add(1);
        }
        match statement {
            ProgramStatement::ThrowOpaque(_)
            | ProgramStatement::BuiltinConstantP { .. }
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
                if let Some(expression) = initializer {
                    cost.add_expression(1); // assignment target lvalue
                    cost.add_expression(program_expression_source_steps(expression));
                }
                for expression in zero_fill.iter().flat_map(ZeroFill::expressions) {
                    cost.add_expression(program_expression_source_steps(expression));
                }
            }
            ProgramStatement::Assign { expression, .. } => {
                cost.add_expression(1); // assignment target lvalue
                cost.add_expression(program_expression_source_steps(expression));
            }
            ProgramStatement::CreateClosure {
                captures: arguments,
                ..
            }
            | ProgramStatement::CallConstruct { arguments, .. }
            | ProgramStatement::Call { arguments, .. }
            | ProgramStatement::CallResult { arguments, .. } => {
                for argument in arguments {
                    cost.add_expression(program_expression_source_steps(argument));
                }
            }
            ProgramStatement::HeapAllocate { bytes, .. } => {
                cost.add_expression(program_expression_source_steps(bytes));
                // Successful allocation assigns a synthesized pointer value
                // to a local: one lvalue and one value-expression visit.
                cost.add_expression(2);
            }
            ProgramStatement::HeapFree { pointer } => {
                cost.add_expression(program_expression_source_steps(pointer));
            }
            ProgramStatement::Assert { condition, .. }
            | ProgramStatement::LoopTest { condition, .. }
            | ProgramStatement::StepValue {
                expression: condition,
                ..
            } => {
                cost.add_expression(program_expression_source_steps(condition));
            }
            ProgramStatement::Seq(statements) => {
                for statement in statements.iter() {
                    pending.push(statement);
                }
            }
            ProgramStatement::TryCatchInt32 {
                try_body, handler, ..
            }
            | ProgramStatement::UnwindCleanup {
                body: try_body,
                cleanup: handler,
            } => {
                pending.push(try_body);
                pending.push(handler);
            }
            ProgramStatement::Return(expression) | ProgramStatement::Throw(expression) => {
                cost.add_expression(program_expression_source_steps(expression));
            }
            ProgramStatement::Store { pointer, value }
            | ProgramStatement::TypedStore { pointer, value, .. } => {
                // The store target is evaluated as a synthesized load lvalue.
                cost.add_expression(
                    1usize.saturating_add(program_expression_source_steps(pointer)),
                );
                cost.add_expression(program_expression_source_steps(value));
            }
            ProgramStatement::CopyAggregate { target, source, .. }
            | ProgramStatement::InitializeScalarArray { target, source, .. } => {
                cost.add_expression(program_expression_source_steps(target));
                cost.add_expression(program_expression_source_steps(source));
            }
            ProgramStatement::Update {
                target, operand, ..
            } => {
                cost.add_expression(program_expression_steps_for_mode(target, true));
                cost.add_expression(1); // read the current lvalue value
                cost.add_expression(program_expression_source_steps(operand));
                cost.add_expression(1); // apply the update operator
            }
            ProgramStatement::If {
                condition,
                then_branch,
                else_branch,
            } => {
                cost.add_expression(program_expression_source_steps(condition));
                pending.push(then_branch);
                pending.push(else_branch);
            }
            ProgramStatement::Loop {
                test: loop_test,
                update,
                body,
                ..
            } => {
                let condition = loop_test.source_condition();
                let test = loop_test.source_region();
                if let Some(condition) = condition {
                    cost.add_expression(program_expression_source_steps(condition));
                }
                pending.push(body);
                if let Some(test) = test {
                    pending.push(&test.statement);
                }
                if let Some(update) = update {
                    pending.push(update);
                }
            }
            ProgramStatement::Switch { expression, cases } => {
                cost.add_expression(program_expression_source_steps(expression));
                for case in cases {
                    pending.push(&case.body);
                }
            }
        }
    }
    cost
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
