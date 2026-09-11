//! The logical proposition search, as Surface Click planning.
//!
//! This is the prover that used to live in
//! `src/kernel/assumptions/proposition_reasoning.rs`. It is a recursive
//! backtracking search over a goal's logical structure: exact facts,
//! algebraic constructor rules and the condition decision procedure at the
//! leaves, then `And`, `Or` arm choice, `Not`, `Implies` under an assumed
//! antecedent, `ForAll` by finite instantiation or binder dropping, case
//! splits over disjunction facts, universal instantiation over quantified
//! facts, and singleton substitution.
//!
//! It plans; it does not issue authority. It advances state only through
//! checked kernel operations ([`PureFactContext::assume_proposition`],
//! [`PureFactContext::restricted_to_facts`],
//! [`PureFactContext::with_only_proposition_facts`],
//! [`PureFactContext::without_exact_fact`]) and public exact queries, and
//! everything it finds is returned as a [`PropositionDerivation`] whose
//! checker is local, deterministic, and still in the kernel. The atomic
//! theory checkers the leaves call (`decide`, `proves_memory_loadable`,
//! `proves_memory_access`, `proves_memory_disjoint`,
//! `proves_resource_separate`, `proves_resource_contains`, and the
//! canonicalization equality walks) stay in the kernel and are unchanged;
//! see `issues/simplify-kernel.md`.
//!
//! Nothing under `src/kernel/` may call into this module. A kernel
//! operation that needs to know whether a proposition holds uses an exact
//! route or emits the proposition as an obligation.

use crate::kernel::planning_api::*;
use crate::kernel::*;
use std::collections::BTreeSet;

/// The logical search over a kernel fact context, as Surface planning.
///
/// Import this trait to plan with a [`PureFactContext`]; the kernel itself
/// never does.
pub(crate) trait PropositionSearch {
    fn proves(&self, proposition: &Proposition) -> bool;

    fn derive_proposition(&self, proposition: &Proposition) -> Option<PropositionDerivation>;

    fn derive_simp_proposition(&self, proposition: &Proposition) -> Option<PropositionDerivation>;

    fn derive_simp_proposition_without_exact_goal(
        &self,
        proposition: &Proposition,
    ) -> Option<PropositionDerivation>;

    fn derive_atomic_proposition(&self, proposition: &Proposition)
    -> Option<PropositionDerivation>;

    fn derive_simp_atomic_proposition(
        &self,
        proposition: &Proposition,
    ) -> Option<PropositionDerivation>;

    fn derive_atomic_proposition_using(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivation>;

    fn atomic_derivation_premises(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> Option<(PureFactContext, u64, AtomicPropositionDerivationEvidence)>;

    fn derive_proposition_using(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivation>;

    fn derive_structural_rule(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivationRule>;

    fn derive_and_rule(
        &self,
        left: &Proposition,
        right: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivationRule>;

    fn derive_or_rule(
        &self,
        left: &Proposition,
        right: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivationRule>;

    fn derive_double_negation_rule(
        &self,
        inner: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivationRule>;

    fn derive_implies_rule(
        &self,
        left: &Proposition,
        right: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivationRule>;

    fn derive_forall_rule(
        &self,
        proposition: &Proposition,
        var: Variable,
        body: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivationRule>;

    fn derive_atomic_rule(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivationRule>;

    fn derive_by_algebraic_constructor_rules(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivationRule>;

    fn derive_finite_forall(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivationRule>;

    fn derive_exists_from_fact(
        &self,
        var: Variable,
        sort: &Sort,
        body: &Proposition,
    ) -> Option<PropositionDerivationRule>;

    fn derive_exists_from_witness(
        &self,
        var: Variable,
        sort: &Sort,
        body: &Proposition,
    ) -> Option<PropositionDerivationRule>;

    fn derive_forall_loadable_range(
        &self,
        proposition: &Proposition,
    ) -> Option<PropositionDerivationRule>;

    fn derive_exists_loadable_range(
        &self,
        var: Variable,
        sort: &Sort,
        body: &Proposition,
    ) -> Option<PropositionDerivationRule>;

    fn derive_by_singleton_substitution(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivationRule>;

    fn derive_by_disjunction_cases(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivationRule>;

    fn proves_finite_forall(&self, proposition: &Proposition) -> bool;

    fn proves_finite_forall_instantiations(
        &self,
        body: &Proposition,
        variables: &[Variable],
        ranges: &[FiniteForAllRange],
        values: &mut Vec<i64>,
    ) -> bool;

    fn proves_by_singleton_substitution(&self, proposition: &Proposition) -> bool;

    fn proves_not(&self, proposition: &Proposition) -> bool;
}

impl PropositionSearch for PureFactContext {
    fn proves(&self, proposition: &Proposition) -> bool {
        if reasoning_interrupted() {
            return false;
        }
        // One id resolution up front so every decision this proof attempt
        // makes shares it instead of rehashing the fact set per decision.
        let _id_scope = PureFactContextIdScope::enter(self);
        if solve_builtin_prop(proposition) {
            return true;
        }

        if self.contains_proposition_fact(proposition) {
            return true;
        }

        if let Some(rule) = self.derive_by_algebraic_constructor_rules(proposition, false) {
            let proof = proposition_derivation(proposition, rule);
            if proof.check(self) {
                record_implicit_reasoning_provenance(self, proposition);
                return true;
            }
        }

        let direct = match proposition {
            Proposition::ConditionIs(condition, value) => {
                self.decide(condition) == Some(*value)
                    // The memory DAG answers first where it can: a bounded
                    // walk over named derivation edges, ahead of the deep
                    // canonicalization below.
                    || *value
                        && matches!(
                            condition,
                            ConditionTerm::Bitvector32Equal(left, right)
                                if atomic_loads_equal_along_memory_derivations(
                                    left, right, self,
                                )
                        )
                    // Two terms for one value that differ only
                    // representationally (memory snapshots embedded in loads,
                    // including under folds and conditionals) are equal by
                    // deep canonicalization; both calls use complete,
                    // input-linear worklists.
                    || *value
                        && matches!(
                            condition,
                            ConditionTerm::Bitvector32Equal(left, right)
                                if canonicalize_atomic_loads(left)
                                        == canonicalize_atomic_loads(right)
                        )
                    || self.proves_condition_from_facts(condition, *value)
            }
            Proposition::And(left, right) => self.proves(left) && self.proves(right),
            Proposition::Or(left, right) => self.proves(left) || self.proves(right),
            Proposition::Not(body) => self.proves_not(body),
            Proposition::Implies(left, right) => {
                self.proves_not(left)
                    || self
                        .clone()
                        .assume_proposition(left.as_ref().clone())
                        .proves(right)
            }
            Proposition::ForAll {
                var,
                sort: Sort::CInt32,
                body,
                ..
            } => {
                self.proves_finite_forall(proposition)
                    || self.without_free_bitvector_variable(*var).proves(body)
            }
            Proposition::CMemoryLoadable {
                memory,
                base,
                bytes,
            } => self.proves_memory_loadable(memory, base, bytes),
            Proposition::CMemoryCanStore {
                memory,
                pointer,
                byte_width,
            } => self.proves_memory_access(memory, pointer, *byte_width),
            Proposition::CMemoryDisjoint {
                left_base,
                left_start,
                left_end,
                right_base,
                right_start,
                right_end,
            } => {
                self.contains_proposition_fact(proposition)
                    || self.proves_memory_disjoint(
                        left_base,
                        left_start,
                        left_end,
                        right_base,
                        right_start,
                        right_end,
                    )
                    || self.proves_memory_disjoint_from_resource_separate(
                        left_base,
                        left_start,
                        left_end,
                        right_base,
                        right_start,
                        right_end,
                    )
            }
            Proposition::CResourceSeparate { left, right } => {
                self.contains_proposition_fact(proposition)
                    || self.proves_resource_separate(left, right)
            }
            Proposition::CResourceContains { parent, child } => {
                self.contains_proposition_fact(proposition)
                    || self.proves_resource_contains(parent, child)
            }
            _ => self.contains_proposition_fact(proposition),
        };
        let proved = direct
            || crate::instrumentation::measure_operation(
                "kernel",
                "general proposition proof",
                "proposition proof: context inconsistency",
                || self.is_inconsistent(),
            )
            || crate::instrumentation::measure_operation(
                "kernel",
                "general proposition proof",
                "proposition proof: singleton substitution",
                || self.proves_by_singleton_substitution(proposition),
            );
        if proved {
            record_implicit_reasoning_provenance(self, proposition);
        }
        proved
    }

    /// Search for an explicit proof tree for a contextual consequence.
    ///
    /// This is the proof-producing counterpart to [`Self::proves`]. Atomic
    /// leaves retain the complete context used to check them; minimizing that
    /// context would require repeated solver calls and is not part of proof
    /// correctness.
    fn derive_proposition(&self, proposition: &Proposition) -> Option<PropositionDerivation> {
        self.derive_proposition_using(proposition, false)
    }

    fn derive_simp_proposition(&self, proposition: &Proposition) -> Option<PropositionDerivation> {
        self.derive_proposition_using(proposition, true)
    }

    /// Searches for a simplifier derivation without using the goal's own
    /// exact ambient fact as a premise. This is a read-only weakening used
    /// when an enclosing checked `have` needs independently checkable
    /// evidence rather than the circular `assumption()` candidate.
    ///
    /// The returned derivation still checks against the original stronger
    /// context. Removing one exact entry touches only persistent indexes
    /// keyed by that proposition; it never rebuilds or scans the fact set.
    fn derive_simp_proposition_without_exact_goal(
        &self,
        proposition: &Proposition,
    ) -> Option<PropositionDerivation> {
        self.without_exact_fact(proposition)
            .derive_simp_proposition(proposition)
    }

    /// Check one atomic theory consequence against this exact premise set.
    ///
    /// Unlike [`Self::derive_proposition`], this does not introduce logical
    /// structure or attempt finite case splits.
    fn derive_atomic_proposition(
        &self,
        proposition: &Proposition,
    ) -> Option<PropositionDerivation> {
        self.derive_atomic_proposition_using(proposition, false)
    }

    /// The simplifier's atomic theory check, without structural proof search.
    fn derive_simp_atomic_proposition(
        &self,
        proposition: &Proposition,
    ) -> Option<PropositionDerivation> {
        self.derive_atomic_proposition_using(proposition, true)
    }

    fn derive_atomic_proposition_using(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivation> {
        if simp_reasoning_interrupted() {
            return None;
        }
        self.atomic_derivation_premises(proposition, for_simp).map(
            |(premises, premises_id, evidence)| {
                proposition_derivation(
                    proposition,
                    PropositionDerivationRule::ContextualAtomic {
                        premises: RetainedPremises::from_context(&premises),
                        premises_id,
                        for_simp,
                        evidence,
                    },
                )
            },
        )
    }

    /// Select the range fact that justified a memory-access consequence.
    ///
    /// General solving may inspect several loadability ranges while planning.
    /// A derivation must retain the successful choice so check does not repeat
    /// that candidate search. Other fact kinds remain available because
    /// pointer/snapshot equality can depend on explicit frame facts.
    fn atomic_derivation_premises(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> Option<(PureFactContext, u64, AtomicPropositionDerivationEvidence)> {
        if self.proves_exact(proposition) {
            let exact = PureFactContext::new().assume_proposition(proposition.clone());
            let (evidence, premises_id) =
                exact.proves_atomic_for_derivation_with_id(proposition, for_simp);
            if let Some(evidence) = evidence {
                return Some((exact, premises_id, evidence));
            }
        }
        let condition_goal = match proposition {
            Proposition::ConditionIs(_, _) => true,
            Proposition::Not(body) => matches!(body.as_ref(), Proposition::ConditionIs(_, _)),
            _ => false,
        };
        if let Some(selected) = self.select_forall_int32_instantiation_evidence(proposition) {
            let mut candidate = PureFactContext::new().assume_proposition(selected.quantified);
            for premise in selected.guard_premises {
                candidate = candidate.assume_proposition(premise);
            }
            let (evidence, premises_id) =
                candidate.proves_atomic_for_derivation_with_id(proposition, for_simp);
            if matches!(
                evidence,
                Some(AtomicPropositionDerivationEvidence::ForallInt32Instantiation(_))
            ) {
                return evidence.map(|evidence| (candidate, premises_id, evidence));
            }
        }
        if atomic_premise_minimization_disabled() {
            let (evidence, premises_id) =
                self.proves_atomic_for_derivation_with_id(proposition, for_simp);
            return evidence.map(|evidence| (self.clone(), premises_id, evidence));
        }
        if condition_goal {
            // Keep the connected condition component. Order/equality
            // reasoning can only cross a fact that shares a symbolic term
            // with the component already reachable from the goal. Growing
            // that component once selects a conservative proof graph without
            // rerunning the prover once per ambient premise.
            let mut connected_variables = BTreeSet::new();
            collect_proposition_bitvector_variables(proposition, &mut connected_variables);
            let mut selected: Vec<(ConditionTerm, bool)> = Vec::new();
            let mut changed = true;
            while changed {
                changed = false;
                for (condition, value) in self.condition_fact_pairs() {
                    if selected.iter().any(|(chosen, _)| chosen == condition) {
                        continue;
                    }
                    let mut variables = BTreeSet::new();
                    collect_condition_bitvector_variables(condition, &mut variables);
                    let exact_goal_fact = matches!(
                        proposition,
                        Proposition::ConditionIs(goal, expected)
                            if goal == condition && *expected == value
                    );
                    if exact_goal_fact
                        || (!variables.is_empty() && !variables.is_disjoint(&connected_variables))
                    {
                        connected_variables.extend(variables);
                        selected.push((condition.clone(), value));
                        changed = true;
                    }
                }
            }
            let candidate = self.restricted_to_facts(&selected, &[]);
            let (evidence, premises_id) =
                candidate.proves_atomic_for_derivation_with_id(proposition, for_simp);
            if let Some(evidence) = evidence {
                return Some((candidate, premises_id, evidence));
            }
        }

        let candidate_family = |fact: &Proposition| match proposition {
            Proposition::CMemoryLoadable { .. } | Proposition::CMemoryCanStore { .. } => {
                matches!(fact, Proposition::CMemoryLoadable { .. })
            }
            Proposition::CResourceSeparate { .. } => matches!(
                fact,
                Proposition::CResourceSeparate { .. } | Proposition::CMemoryDisjoint { .. }
            ),
            Proposition::CMemoryDisjoint { .. } => matches!(
                fact,
                Proposition::CMemoryDisjoint { .. } | Proposition::CResourceSeparate { .. }
            ),
            _ => false,
        };
        let candidates = self
            .proposition_facts()
            .filter(|fact| candidate_family(fact))
            .cloned()
            .collect::<Vec<_>>();
        if let Proposition::CMemoryLoadable {
            memory,
            base,
            bytes,
        } = proposition
            && let Some(premises) = self.adjacent_loadable_region_facts(memory, base, bytes)
        {
            let candidate = self.with_only_proposition_facts(&premises);
            let (evidence, premises_id) =
                candidate.proves_atomic_for_derivation_with_id(proposition, for_simp);
            if let Some(evidence) = evidence {
                return Some((candidate, premises_id, evidence));
            }
        }
        if candidates.len() > 1 {
            for selected in &candidates {
                if simp_reasoning_interrupted() {
                    return None;
                }
                let candidate = self.with_only_proposition_facts(std::slice::from_ref(selected));
                let (evidence, premises_id) =
                    candidate.proves_atomic_for_derivation_with_id(proposition, for_simp);
                if let Some(evidence) = evidence {
                    return Some((candidate, premises_id, evidence));
                }
            }
            if matches!(proposition, Proposition::CMemoryLoadable { .. }) {
                for first in 0..candidates.len() {
                    for second in first + 1..candidates.len() {
                        if simp_reasoning_interrupted() {
                            return None;
                        }
                        let candidate = self.with_only_proposition_facts(&[
                            candidates[first].clone(),
                            candidates[second].clone(),
                        ]);
                        let (evidence, premises_id) =
                            candidate.proves_atomic_for_derivation_with_id(proposition, for_simp);
                        if let Some(evidence) = evidence {
                            return Some((candidate, premises_id, evidence));
                        }
                    }
                }
            }
        }
        let (evidence, premises_id) =
            self.proves_atomic_for_derivation_with_id(proposition, for_simp);
        evidence.map(|evidence| (self.clone(), premises_id, evidence))
    }

    fn derive_proposition_using(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivation> {
        let _id_scope = PureFactContextIdScope::enter(self);
        if simp_reasoning_interrupted() {
            return None;
        }
        if solve_builtin_prop(proposition) {
            return Some(proposition_derivation(
                proposition,
                PropositionDerivationRule::ContextFree,
            ));
        }
        if let Some(rule) = self.derive_by_algebraic_constructor_rules(proposition, for_simp) {
            return Some(proposition_derivation(proposition, rule));
        }
        let direct = self.derive_structural_rule(proposition, for_simp);
        if let Some(rule) = direct {
            return Some(proposition_derivation(proposition, rule));
        }
        if self.is_inconsistent() {
            return Some(proposition_derivation(
                proposition,
                PropositionDerivationRule::Explosion {
                    premises: RetainedPremises::from_context(self),
                },
            ));
        }
        if let Some(rule) = self.derive_by_singleton_substitution(proposition, for_simp) {
            return Some(proposition_derivation(proposition, rule));
        }
        self.derive_by_disjunction_cases(proposition, for_simp)
            .map(|rule| proposition_derivation(proposition, rule))
    }

    #[inline(never)]
    fn derive_structural_rule(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivationRule> {
        match proposition {
            Proposition::And(left, right) => self.derive_and_rule(left, right, for_simp),
            Proposition::Or(left, right) => self.derive_or_rule(left, right, for_simp),
            Proposition::Not(body) => match body.as_ref() {
                Proposition::Not(inner) => self.derive_double_negation_rule(inner, for_simp),
                _ => self.derive_atomic_rule(proposition, for_simp),
            },
            Proposition::Implies(left, right) => self.derive_implies_rule(left, right, for_simp),
            Proposition::ForAll { var, body, .. } => {
                self.derive_forall_rule(proposition, *var, body, for_simp)
            }
            Proposition::Exists {
                var, sort, body, ..
            } => self
                .derive_exists_from_witness(*var, sort, body)
                .or_else(|| self.derive_exists_from_fact(*var, sort, body))
                .or_else(|| self.derive_exists_loadable_range(*var, sort, body)),
            _ => self.derive_atomic_rule(proposition, for_simp),
        }
    }

    #[inline(never)]
    fn derive_and_rule(
        &self,
        left: &Proposition,
        right: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivationRule> {
        self.derive_proposition_using(left, for_simp)
            .zip(self.derive_proposition_using(right, for_simp))
            .map(|(left, right)| PropositionDerivationRule::And {
                left: Box::new(left),
                right: Box::new(right),
            })
    }

    #[inline(never)]
    fn derive_or_rule(
        &self,
        left: &Proposition,
        right: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivationRule> {
        self.derive_proposition_using(left, for_simp)
            .map(|proof| PropositionDerivationRule::OrLeft(Box::new(proof)))
            .or_else(|| {
                self.derive_proposition_using(right, for_simp)
                    .map(|proof| PropositionDerivationRule::OrRight(Box::new(proof)))
            })
    }

    #[inline(never)]
    fn derive_double_negation_rule(
        &self,
        inner: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivationRule> {
        self.derive_proposition_using(inner, for_simp)
            .map(|proof| PropositionDerivationRule::DoubleNegation(Box::new(proof)))
    }

    #[inline(never)]
    fn derive_implies_rule(
        &self,
        left: &Proposition,
        right: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivationRule> {
        let antecedent = left.clone();
        let negated_antecedent = Proposition::Not(Box::new(antecedent.clone()));
        if self.proves_exact(&negated_antecedent) {
            self.derive_proposition_using(&negated_antecedent, for_simp)
                .map(|proof| PropositionDerivationRule::ImpliesFalseAntecedent(Box::new(proof)))
        } else {
            self.clone()
                .assume_proposition(antecedent.clone())
                .derive_proposition_using(right, for_simp)
                .map(|body| PropositionDerivationRule::Implies {
                    antecedent,
                    body: Box::new(body),
                })
                .or_else(|| {
                    self.derive_proposition_using(&negated_antecedent, for_simp)
                        .map(|proof| {
                            PropositionDerivationRule::ImpliesFalseAntecedent(Box::new(proof))
                        })
                })
        }
    }

    #[inline(never)]
    fn derive_forall_rule(
        &self,
        proposition: &Proposition,
        var: Variable,
        body: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivationRule> {
        let body_derivation = self
            .without_free_bitvector_variable(var)
            .derive_proposition_using(body, for_simp)
            .map(|proof| PropositionDerivationRule::ForAllBody(Box::new(proof)));
        body_derivation
            .or_else(|| self.derive_forall_loadable_range(proposition))
            .or_else(|| self.derive_finite_forall(proposition, for_simp))
            .or_else(|| self.derive_atomic_rule(proposition, for_simp))
    }

    #[inline(never)]
    fn derive_atomic_rule(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivationRule> {
        self.atomic_derivation_premises(proposition, for_simp).map(
            |(premises, premises_id, evidence)| PropositionDerivationRule::ContextualAtomic {
                premises: RetainedPremises::from_context(&premises),
                premises_id,
                for_simp,
                evidence,
            },
        )
    }

    fn derive_by_algebraic_constructor_rules(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivationRule> {
        if let Some(fields) = algebraic_constructor_field_equalities(proposition)
            && !fields.is_empty()
        {
            let fields = fields
                .iter()
                .map(|field| self.derive_proposition_using(field, for_simp))
                .collect::<Option<Vec<_>>>()?;
            return Some(PropositionDerivationRule::AlgebraicConstructorCongruence { fields });
        }
        self.algebraic_constructor_field_sources(proposition)
            .next()
            .map(|(source, field_index)| {
                PropositionDerivationRule::AlgebraicConstructorInjectivity {
                    source: source.clone(),
                    field_index: *field_index,
                }
            })
    }

    fn derive_finite_forall(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivationRule> {
        let instances = self.finite_forall_instantiations(proposition);
        if instances.is_empty() {
            return None;
        }
        instances
            .iter()
            .map(|instance| self.derive_proposition_using(instance, for_simp))
            .collect::<Option<Vec<_>>>()
            .map(|instances| PropositionDerivationRule::FiniteForAll { instances })
    }

    /// Select one exact existential fact, rename its witness binder to the
    /// goal binder, and derive the goal body from the witness body's
    /// conjuncts. The selected fact is retained by the resulting rule; the
    /// witness conjuncts are local assumptions of its child proof.
    fn derive_exists_from_fact(
        &self,
        var: Variable,
        sort: &Sort,
        body: &Proposition,
    ) -> Option<PropositionDerivationRule> {
        let candidates = self
            .proposition_facts()
            .filter_map(|source| {
                let Proposition::Exists {
                    var: source_var,
                    sort: source_sort,
                    body: source_body,
                    ..
                } = source
                else {
                    return None;
                };
                if source_sort != sort {
                    return None;
                }
                let renamed = crate::kernel::api::substitute_quantified_body_capture_free(
                    source_body,
                    *source_var,
                    var,
                    sort,
                )?;
                Some((source.clone(), renamed))
            })
            .collect::<Vec<_>>();
        for (source, renamed_source_body) in candidates {
            let mut witness_assumptions = self.clone();
            let mut conjuncts = Vec::new();
            collect_proposition_conjuncts(&renamed_source_body, &mut conjuncts);
            for conjunct in conjuncts {
                witness_assumptions = witness_assumptions.assume_proposition(conjunct);
            }
            let derivation = witness_assumptions.derive_proposition_using(body, false);
            if let Some(derivation) = derivation {
                return Some(PropositionDerivationRule::ExistsFromFact {
                    source,
                    body: Box::new(derivation),
                });
            }
        }
        None
    }

    fn derive_exists_from_witness(
        &self,
        var: Variable,
        sort: &Sort,
        body: &Proposition,
    ) -> Option<PropositionDerivationRule> {
        if sort != &Sort::CInt32 {
            return None;
        }
        let mut variables = BTreeSet::new();
        for fact in self.memory_loadable_fact_propositions() {
            {
                collect_proposition_bitvector_variables(fact, &mut variables);
            }
        }
        variables.remove(&var);
        for variable in variables {
            let witness = Bitvector32Term::Variable(variable);
            let instantiated = substitute_bitvector_variable_in_proposition(body, var, &witness);
            let derivation = self.derive_proposition_using(&instantiated, false);
            if let Some(derivation) = derivation {
                return Some(PropositionDerivationRule::ExistsFromWitness {
                    witness,
                    body: Box::new(derivation),
                });
            }
        }
        None
    }

    /// Select one exact wider loadability fact that covers every one-byte
    /// cell described by an int32 universal's guarded range. The range
    /// arithmetic is delegated to the existing bounded loadability checker;
    /// this rule only adds the universal introduction and records the source
    /// range used by it.
    fn derive_forall_loadable_range(
        &self,
        proposition: &Proposition,
    ) -> Option<PropositionDerivationRule> {
        let (premises, conclusion) = forall_loadable_range_parts(proposition)?;
        let Proposition::CMemoryLoadable { base, bytes, .. } = conclusion else {
            return None;
        };
        if bytes.as_const() != Some(1) {
            return None;
        }
        for source in self.memory_loadable_candidates_for_base(base) {
            let mut candidate = PureFactContext::new().assume_proposition(source.clone());
            for premise in &premises {
                candidate = candidate.assume_proposition(premise.clone());
            }
            let covered = crate::kernel::api::loadable_covered_by_fact(&candidate, conclusion);
            if covered {
                return Some(PropositionDerivationRule::ForAllLoadableRange {
                    source: source.clone(),
                });
            }
        }
        None
    }

    fn derive_exists_loadable_range(
        &self,
        var: Variable,
        sort: &Sort,
        body: &Proposition,
    ) -> Option<PropositionDerivationRule> {
        if sort != &Sort::CInt32 {
            return None;
        }
        let witness = Bitvector32Term::Constant(0);
        let instantiated = substitute_bitvector_variable_in_proposition(body, var, &witness);
        if !matches!(instantiated, Proposition::CMemoryLoadable { .. }) {
            return None;
        }
        for source in self.memory_loadable_candidates_for_base(match &instantiated {
            Proposition::CMemoryLoadable { base, .. } => base,
            _ => unreachable!(),
        }) {
            let candidate = self.with_only_proposition_facts(std::slice::from_ref(source));
            if crate::kernel::api::loadable_covered_by_fact(&candidate, &instantiated) {
                return Some(PropositionDerivationRule::ExistsLoadableRange {
                    source: source.clone(),
                    witness,
                });
            }
        }
        None
    }

    fn derive_by_singleton_substitution(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivationRule> {
        let mut variables = BTreeSet::new();
        collect_proposition_bitvector_variables(proposition, &mut variables);
        let (variable, value, equality) = variables
            .into_iter()
            .filter_map(|variable| {
                self.singleton_constant_equality_evidence(variable)
                    .map(|(value, evidence)| (variable, value, evidence))
            })
            .next()?;
        let instantiated = substitute_bitvector_variable_in_proposition(
            proposition,
            variable,
            &signed_i64_bitvector_constant(value),
        );
        if instantiated == *proposition {
            return None;
        }
        let body = self.derive_proposition_using(&instantiated, for_simp)?;
        Some(PropositionDerivationRule::SingletonSubstitution {
            variable,
            value,
            equality,
            body: Box::new(body),
        })
    }

    fn derive_by_disjunction_cases(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivationRule> {
        for disjunction in self.disjunction_fact_propositions() {
            let mut cases = Vec::new();
            collect_or_cases(disjunction, &mut cases);
            if cases.len() < 2 {
                continue;
            }
            let base = self.without_exact_fact(disjunction);
            let Some(proofs) = cases
                .iter()
                .map(|case| {
                    base.clone()
                        .assume_proposition(case.clone())
                        .derive_proposition_using(proposition, for_simp)
                })
                .collect::<Option<Vec<_>>>()
            else {
                continue;
            };
            return Some(PropositionDerivationRule::DisjunctionCases {
                disjunction: disjunction.clone(),
                cases: proofs,
            });
        }
        None
    }

    fn proves_finite_forall(&self, proposition: &Proposition) -> bool {
        let mut variables = Vec::new();
        let body = collect_forall_chain(proposition, &mut variables);
        if variables.is_empty() {
            return false;
        }
        let Some(ranges) = finite_forall_ranges(&variables, body) else {
            return false;
        };
        let Some(instantiation_count) = ranges.iter().try_fold(1usize, |count, range| {
            let width = usize::try_from(range.upper - range.lower + 1).ok()?;
            count.checked_mul(width)
        }) else {
            return false;
        };
        crate::instrumentation::record_deterministic_work(instantiation_count);

        let mut values = Vec::with_capacity(variables.len());
        self.proves_finite_forall_instantiations(body, &variables, &ranges, &mut values)
    }

    fn proves_finite_forall_instantiations(
        &self,
        body: &Proposition,
        variables: &[Variable],
        ranges: &[FiniteForAllRange],
        values: &mut Vec<i64>,
    ) -> bool {
        if values.len() == variables.len() {
            let mut instantiated = body.clone();
            for (variable, value) in variables.iter().zip(values.iter()) {
                instantiated = substitute_bitvector_variable_in_proposition(
                    &instantiated,
                    *variable,
                    &signed_i64_bitvector_constant(*value),
                );
            }
            return self.proves(&instantiated);
        }

        let range = &ranges[values.len()];
        for value in range.lower..=range.upper {
            values.push(value);
            if !self.proves_finite_forall_instantiations(body, variables, ranges, values) {
                values.pop();
                return false;
            }
            values.pop();
        }
        true
    }

    fn proves_by_singleton_substitution(&self, proposition: &Proposition) -> bool {
        let mut variables = BTreeSet::new();
        collect_proposition_bitvector_variables(proposition, &mut variables);
        let Some((variable, value)) = variables
            .into_iter()
            .filter_map(|variable| {
                self.singleton_constant_equality_evidence(variable)
                    .map(|(value, _)| (variable, value))
            })
            .next()
        else {
            return false;
        };
        let instantiated = substitute_bitvector_variable_in_proposition(
            proposition,
            variable,
            &signed_i64_bitvector_constant(value),
        );
        if instantiated == *proposition {
            return false;
        }
        self.proves(&instantiated)
    }

    fn proves_not(&self, proposition: &Proposition) -> bool {
        match proposition {
            Proposition::ConditionIs(condition, value) => self.decide(condition) == Some(!*value),
            Proposition::Not(body) => self.proves(body),
            _ => self.contains_proposition_fact(&Proposition::Not(Box::new(proposition.clone()))),
        }
    }
}
