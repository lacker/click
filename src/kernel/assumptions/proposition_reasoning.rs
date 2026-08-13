use super::*;
use std::collections::HashSet;

thread_local! {
    static CONTEXT_INCONSISTENCY_POSITIVE_MEMO: RefCell<HashSet<(u64, bool)>> = RefCell::new(HashSet::new());
    static CONTEXT_INCONSISTENCY_NEGATIVE_MEMO: RefCell<HashSet<(u64, u64, bool)>> = RefCell::new(HashSet::new());
}

const CONTEXT_INCONSISTENCY_MEMO_LIMIT: usize = 200_000;

#[cfg(test)]
thread_local! {
    static CONTEXT_INCONSISTENCY_FULL_SCANS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

fn canonical_contradiction_condition(condition: &ConditionTerm) -> ConditionTerm {
    fn ordered<T: Ord + Clone>(left: &T, right: &T) -> (T, T) {
        if left <= right {
            (left.clone(), right.clone())
        } else {
            (right.clone(), left.clone())
        }
    }

    match condition {
        ConditionTerm::Bitvector32Equal(left, right) => {
            let (left, right) = ordered(left.as_ref(), right.as_ref());
            ConditionTerm::equal(left, right)
        }
        ConditionTerm::PointerOffsetEqual(left, right) => {
            let (left, right) = ordered(left.as_ref(), right.as_ref());
            ConditionTerm::pointer_offset_equal(left, right)
        }
        ConditionTerm::PointerEqual(left, right) => {
            let (left, right) = ordered(left.as_ref(), right.as_ref());
            ConditionTerm::pointer_equal(left, right)
        }
        ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
            ConditionTerm::signed_less_than(right.as_ref().clone(), left.as_ref().clone())
        }
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
            ConditionTerm::signed_less_equal(right.as_ref().clone(), left.as_ref().clone())
        }
        _ => condition.clone(),
    }
}

/// Cheap necessary condition for the assumption-sensitive equalities checked
/// by [`Assumptions::bitvector_terms_proven_equal`]. Exact equality and
/// explicit equality-graph paths are handled separately by its caller.
///
/// The remaining theory rules can only relate two conditionals, two folds, an
/// additive spelling (including a split fold), or a memory load that resolves
/// to another spelling. Keeping ordinary variables and constants out of those
/// recursive theories is important when contradiction checking considers
/// order endpoints.
fn bitvector_terms_may_be_theory_equal(left: &Bitvector32Term, right: &Bitvector32Term) -> bool {
    matches!(
        left,
        Bitvector32Term::MemoryLoad(_, _) | Bitvector32Term::Add(_, _)
    ) || matches!(
        right,
        Bitvector32Term::MemoryLoad(_, _) | Bitvector32Term::Add(_, _)
    ) || matches!(
        (left, right),
        (Bitvector32Term::If { .. }, Bitvector32Term::If { .. })
    ) || matches!(
        (left, right),
        (
            Bitvector32Term::RangeFold { .. },
            Bitvector32Term::RangeFold { .. }
        )
    )
}

/// The finite instantiation table of a constant-bounded universal goal, in
/// deterministic range order. `None` when the binder chain has no
/// guard-derived constant range or the table would exceed the finite
/// instantiation limit. This mirrors the ranges the kernel's `FiniteForAll`
/// derivation enumerates, so a surface certificate that spells each in-range
/// instance can be checked with work proportional to this table.
pub(crate) fn finite_forall_goal_instances(
    proposition: &Proposition,
) -> Option<Vec<(Vec<i64>, Proposition)>> {
    fn collect(
        body: &Proposition,
        variables: &[Variable],
        ranges: &[FiniteForAllRange],
        values: &mut Vec<i64>,
        instances: &mut Vec<(Vec<i64>, Proposition)>,
    ) {
        if values.len() == variables.len() {
            let mut instantiated = body.clone();
            for (variable, value) in variables.iter().zip(values.iter()) {
                instantiated = substitute_bitvector_variable_in_proposition(
                    &instantiated,
                    *variable,
                    &signed_i64_bitvector_constant(*value),
                );
            }
            instances.push((values.clone(), instantiated));
            return;
        }
        let range = &ranges[values.len()];
        for value in range.lower..=range.upper {
            values.push(value);
            collect(body, variables, ranges, values, instances);
            values.pop();
        }
    }

    let mut variables = Vec::new();
    let body = collect_forall_chain(proposition, &mut variables);
    if variables.is_empty() {
        return None;
    }
    let ranges = finite_forall_ranges(&variables, body)?;
    let instance_count = ranges.iter().try_fold(1usize, |count, range| {
        usize::try_from(range.upper - range.lower + 1)
            .ok()
            .and_then(|width| count.checked_mul(width))
    })?;
    if instance_count > FINITE_FORALL_INSTANTIATION_LIMIT {
        return None;
    }
    let mut instances = Vec::with_capacity(instance_count);
    collect(body, &variables, &ranges, &mut Vec::new(), &mut instances);
    Some(instances)
}

impl Assumptions {
    #[cfg(test)]
    pub(crate) fn reset_context_inconsistency_full_scans() {
        CONTEXT_INCONSISTENCY_FULL_SCANS.with(|scans| scans.set(0));
    }

    #[cfg(test)]
    pub(crate) fn context_inconsistency_full_scans() -> usize {
        CONTEXT_INCONSISTENCY_FULL_SCANS.with(std::cell::Cell::get)
    }

    pub fn proves(&self, proposition: &Proposition) -> bool {
        if crate::instrumentation::deadline_exceeded() {
            return false;
        }
        // One id resolution up front so every decision this proof attempt
        // makes shares it instead of rehashing the fact set per decision.
        let _id_scope = AssumptionsIdScope::enter(self);
        if solve_builtin_prop(proposition) {
            return true;
        }

        if self.prop_facts.contains(proposition) {
            return true;
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
                                if crate::kernel::api::atomic_loads_equal_along_memory_derivations(
                                    left, right, self,
                                )
                        )
                    // Two spellings of one value that differ only
                    // representationally (snapshot spellings inside loads,
                    // including under folds and conditionals) are equal by
                    // deep canonicalization; both calls are memoized.
                    || *value
                        && matches!(
                            condition,
                            ConditionTerm::Bitvector32Equal(left, right)
                                if !crate::kernel::api::bitvector_term_deeper_than(left, 64)
                                    && !crate::kernel::api::bitvector_term_deeper_than(right, 64)
                                    && crate::kernel::api::canonicalize_atomic_loads(left)
                                        == crate::kernel::api::canonicalize_atomic_loads(right)
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
                self.prop_facts.contains(proposition)
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
                self.prop_facts.contains(proposition) || self.proves_resource_separate(left, right)
            }
            Proposition::CResourceContains { parent, child } => {
                self.prop_facts.contains(proposition)
                    || self.proves_resource_contains(parent, child)
            }
            _ => self.prop_facts.contains(proposition),
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
                "proposition proof: finite context split",
                || self.proves_by_finite_context_split(proposition),
            )
            || crate::instrumentation::measure_operation(
                "kernel",
                "general proposition proof",
                "proposition proof: disjunction cases",
                || self.proves_by_disjunction_cases(proposition),
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
    pub fn derive_proposition(&self, proposition: &Proposition) -> Option<PropositionDerivation> {
        self.derive_proposition_using(proposition, false)
    }

    /// Build a replayable derivation while retaining its complete atomic
    /// premise sets. Internal deterministic checks that immediately replay and
    /// discard the derivation do not benefit from the deletion-based premise
    /// minimization used for emitted certificates.
    pub(in crate::kernel) fn derive_proposition_without_premise_minimization(
        &self,
        proposition: &Proposition,
    ) -> Option<PropositionDerivation> {
        let _guard = AtomicPremiseMinimizationGuard::disable();
        self.derive_proposition_using(proposition, false)
    }

    pub fn derive_simp_proposition(
        &self,
        proposition: &Proposition,
    ) -> Option<PropositionDerivation> {
        let _fuel = SimpReasoningFuelGuard::enter();
        self.derive_proposition_using(proposition, true)
    }

    /// Check one atomic theory consequence against this exact premise set.
    ///
    /// Unlike [`Self::derive_proposition`], this does not introduce logical
    /// structure or attempt finite case splits.
    pub fn derive_atomic_proposition(
        &self,
        proposition: &Proposition,
    ) -> Option<PropositionDerivation> {
        self.derive_atomic_proposition_using(proposition, false)
    }

    /// The simplifier's atomic theory check, without structural proof search.
    pub fn derive_simp_atomic_proposition(
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
        if !consume_simp_reasoning_fuel() {
            return None;
        }
        self.atomic_derivation_premises(proposition, for_simp)
            .map(|(premises, premises_id)| {
                proposition_derivation(
                    proposition,
                    PropositionDerivationRule::ContextualAtomic {
                        premises,
                        premises_id,
                        for_simp,
                    },
                )
            })
    }

    /// Select the range fact that justified a memory-access consequence.
    ///
    /// General solving may inspect several loadability ranges while planning.
    /// A derivation must retain the successful choice so replay does not repeat
    /// that candidate search. Other fact kinds remain available because
    /// pointer/snapshot equality can depend on explicit frame facts.
    fn atomic_derivation_premises(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> Option<(Assumptions, u64)> {
        if self.proves_exact(proposition) {
            let exact = Assumptions::new().assume_proposition(proposition.clone());
            let (proved, premises_id) =
                exact.proves_atomic_for_derivation_with_id(proposition, for_simp);
            if proved {
                return Some((exact, premises_id));
            }
        }
        let condition_goal = match proposition {
            Proposition::ConditionIs(_, _) => true,
            Proposition::Not(body) => matches!(body.as_ref(), Proposition::ConditionIs(_, _)),
            _ => false,
        };
        if atomic_premise_minimization_disabled() {
            let (proved, premises_id) =
                self.proves_atomic_for_derivation_with_id(proposition, for_simp);
            return proved.then(|| (self.clone(), premises_id));
        }
        if condition_goal {
            // Keep the connected condition component. Order/equality
            // reasoning can only cross a fact that shares a symbolic term
            // with the component already reachable from the goal. Growing
            // that component once selects a conservative proof graph without
            // rerunning the prover once per ambient premise.
            let mut candidate = self.clone();
            candidate.clear_proposition_facts();
            let mut connected_variables = BTreeSet::new();
            collect_proposition_bitvector_variables(proposition, &mut connected_variables);
            let mut selected = BTreeMap::new();
            let mut changed = true;
            while changed {
                changed = false;
                for (condition, value) in self.condition_facts.iter() {
                    if selected.contains_key(condition) {
                        continue;
                    }
                    let mut variables = BTreeSet::new();
                    collect_condition_bitvector_variables(condition, &mut variables);
                    let exact_goal_fact = matches!(
                        proposition,
                        Proposition::ConditionIs(goal, expected)
                            if goal == condition && expected == value
                    );
                    if exact_goal_fact
                        || (!variables.is_empty() && !variables.is_disjoint(&connected_variables))
                    {
                        connected_variables.extend(variables);
                        selected.insert(condition.clone(), *value);
                        changed = true;
                    }
                }
            }
            candidate.condition_facts = std::sync::Arc::new(selected);
            candidate.rebuild_signed_order_bounds();
            candidate.rebuild_memory_load_condition_facts();
            candidate.recompute_content_fingerprint();
            let (proved, premises_id) =
                candidate.proves_atomic_for_derivation_with_id(proposition, for_simp);
            if proved {
                return Some((candidate, premises_id));
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
            .prop_facts
            .iter()
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
            let mut candidate = self.clone();
            candidate.clear_proposition_facts();
            for premise in premises {
                candidate.insert_proposition_fact(premise);
            }
            let (proved, premises_id) =
                candidate.proves_atomic_for_derivation_with_id(proposition, for_simp);
            if proved {
                return Some((candidate, premises_id));
            }
        }
        if candidates.len() > 1 {
            for selected in &candidates {
                if !consume_simp_reasoning_fuel() {
                    return None;
                }
                let mut candidate = self.clone();
                candidate.clear_proposition_facts();
                candidate.insert_proposition_fact(selected.clone());
                let (proved, premises_id) =
                    candidate.proves_atomic_for_derivation_with_id(proposition, for_simp);
                if proved {
                    return Some((candidate, premises_id));
                }
            }
            if matches!(proposition, Proposition::CMemoryLoadable { .. }) {
                for first in 0..candidates.len() {
                    for second in first + 1..candidates.len() {
                        if !consume_simp_reasoning_fuel() {
                            return None;
                        }
                        let mut candidate = self.clone();
                        candidate.clear_proposition_facts();
                        candidate.insert_proposition_fact(candidates[first].clone());
                        candidate.insert_proposition_fact(candidates[second].clone());
                        let (proved, premises_id) =
                            candidate.proves_atomic_for_derivation_with_id(proposition, for_simp);
                        if proved {
                            return Some((candidate, premises_id));
                        }
                    }
                }
            }
        }
        let (proved, premises_id) =
            self.proves_atomic_for_derivation_with_id(proposition, for_simp);
        proved.then(|| (self.clone(), premises_id))
    }

    fn derive_proposition_using(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivation> {
        let _id_scope = AssumptionsIdScope::enter(self);
        if !consume_simp_reasoning_fuel() {
            return None;
        }
        if solve_builtin_prop(proposition) {
            return Some(proposition_derivation(
                proposition,
                PropositionDerivationRule::ContextFree,
            ));
        }
        let direct = match proposition {
            Proposition::And(left, right) => self
                .derive_proposition_using(left, for_simp)
                .zip(self.derive_proposition_using(right, for_simp))
                .map(|(left, right)| PropositionDerivationRule::And {
                    left: Box::new(left),
                    right: Box::new(right),
                }),
            Proposition::Or(left, right) => self
                .derive_proposition_using(left, for_simp)
                .map(|proof| PropositionDerivationRule::OrLeft(Box::new(proof)))
                .or_else(|| {
                    self.derive_proposition_using(right, for_simp)
                        .map(|proof| PropositionDerivationRule::OrRight(Box::new(proof)))
                }),
            Proposition::Not(body) => match body.as_ref() {
                Proposition::Not(inner) => self
                    .derive_proposition_using(inner, for_simp)
                    .map(|proof| PropositionDerivationRule::DoubleNegation(Box::new(proof))),
                _ => self.atomic_derivation_premises(proposition, for_simp).map(
                    |(premises, premises_id)| PropositionDerivationRule::ContextualAtomic {
                        premises,
                        premises_id,
                        for_simp,
                    },
                ),
            },
            Proposition::Implies(left, right) => {
                let antecedent = left.as_ref().clone();
                let negated_antecedent = Proposition::Not(Box::new(antecedent.clone()));
                if self.proves_exact(&negated_antecedent) {
                    self.derive_proposition_using(&negated_antecedent, for_simp)
                        .map(|proof| {
                            PropositionDerivationRule::ImpliesFalseAntecedent(Box::new(proof))
                        })
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
                                    PropositionDerivationRule::ImpliesFalseAntecedent(Box::new(
                                        proof,
                                    ))
                                })
                        })
                }
            }
            Proposition::ForAll { var, body, .. } => {
                let body_derivation = self
                    .without_free_bitvector_variable(*var)
                    .derive_proposition_using(body, for_simp)
                    .map(|proof| PropositionDerivationRule::ForAllBody(Box::new(proof)));
                body_derivation
                    .or_else(|| self.derive_finite_forall(proposition, for_simp))
                    .or_else(|| {
                        self.atomic_derivation_premises(proposition, for_simp).map(
                            |(premises, premises_id)| PropositionDerivationRule::ContextualAtomic {
                                premises,
                                premises_id,
                                for_simp,
                            },
                        )
                    })
            }
            _ => self.atomic_derivation_premises(proposition, for_simp).map(
                |(premises, premises_id)| PropositionDerivationRule::ContextualAtomic {
                    premises,
                    premises_id,
                    for_simp,
                },
            ),
        };
        if let Some(rule) = direct {
            return Some(proposition_derivation(proposition, rule));
        }
        if self.is_inconsistent() {
            return Some(proposition_derivation(
                proposition,
                PropositionDerivationRule::Explosion {
                    premises: self.clone(),
                },
            ));
        }
        if let Some(rule) = self.derive_by_finite_context_split(proposition, for_simp) {
            return Some(proposition_derivation(proposition, rule));
        }
        if let Some(rule) = self.derive_by_upper_bound_split(proposition, for_simp) {
            return Some(proposition_derivation(proposition, rule));
        }
        self.derive_by_disjunction_cases(proposition, for_simp)
            .map(|rule| proposition_derivation(proposition, rule))
    }

    fn proves_atomic_without_search(&self, proposition: &Proposition) -> bool {
        match proposition {
            Proposition::ConditionIs(condition, value) => {
                self.decide(condition) == Some(*value)
                    // The memory DAG answers first where it can; see the
                    // matching arm in `proves`.
                    || *value
                        && matches!(
                            condition,
                            ConditionTerm::Bitvector32Equal(left, right)
                                if crate::kernel::api::atomic_loads_equal_along_memory_derivations(
                                    left, right, self,
                                )
                        )
                    // Two spellings of one value that differ only
                    // representationally (snapshot spellings inside loads,
                    // including under folds and conditionals) are equal by
                    // deep canonicalization; both calls are memoized.
                    || *value
                        && matches!(
                            condition,
                            ConditionTerm::Bitvector32Equal(left, right)
                                if !crate::kernel::api::bitvector_term_deeper_than(left, 64)
                                    && !crate::kernel::api::bitvector_term_deeper_than(right, 64)
                                    && crate::kernel::api::canonicalize_atomic_loads(left)
                                        == crate::kernel::api::canonicalize_atomic_loads(right)
                        )
                    // Equalities over loads resolve through materialized
                    // cells and snapshot matching; the bounded resolution
                    // prover carries its own fuel but can re-enter this
                    // prover, so guard against reentrancy.
                    || *value
                        && matches!(
                            condition,
                            ConditionTerm::Bitvector32Equal(left, right)
                                if (bitvector_term_contains_load(left)
                                    || bitvector_term_contains_load(right))
                                    && atomic_load_equality_resolves(self, left, right)
                        )
                    || self.proves_condition_from_facts(condition, *value)
            }
            Proposition::Not(body) => match body.as_ref() {
                Proposition::ConditionIs(condition, value) => {
                    self.decide(condition) == Some(!*value)
                }
                _ => self.prop_facts.contains(proposition),
            },
            Proposition::CMemoryLoadable {
                memory,
                base,
                bytes,
            } => {
                self.proves_memory_loadable(memory, base, bytes)
                    // Loadability survives writes: an assumed loadable fact
                    // for the same range transports across any chain of
                    // recorded effects connecting the snapshots.
                    || self.prop_facts.iter().any(|fact| {
                        let Proposition::CMemoryLoadable {
                            memory: fact_memory,
                            base: fact_base,
                            bytes: fact_bytes,
                        } = fact
                        else {
                            return false;
                        };
                        {
                            let base_match =
                                crate::kernel::api::canonicalize_pointer_loads(fact_base, 0)
                                    == crate::kernel::api::canonicalize_pointer_loads(base, 0)
                                    || crate::kernel::reasoning::pointers_proven_equal_for_memory_resolution(
                                        fact_base, base, self,
                                    );
                            let bytes_match = crate::kernel::api::canonicalize_atomic_loads(fact_bytes)
                                == crate::kernel::api::canonicalize_atomic_loads(bytes)
                                || crate::kernel::reasoning::bitvector_terms_proven_equal_for_memory_resolution(
                                    fact_bytes, bytes, self,
                                );
                            base_match
                                && bytes_match
                                && crate::kernel::api::c_memories_connected_by_effects(
                                    fact_memory,
                                    memory,
                                    self,
                                )
                        }
                    })
                    // A goal subrange of a wider assumed loadable span is
                    // loadable when the bounds arithmetic certifies coverage.
                    || crate::kernel::api::loadable_covered_by_fact(self, proposition)
                    // Symbolic byte counts often fold to a constant width,
                    // unlocking the element-index coverage rules.
                    || {
                        let simplified = self.simplify_bitvector_under_assumptions(bytes);
                        simplified != *bytes
                            && self.proves_memory_loadable(memory, base, &simplified)
                    }
            }
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
                self.prop_facts.contains(proposition)
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
                self.prop_facts.contains(proposition) || self.proves_resource_separate(left, right)
            }
            Proposition::CResourceContains { parent, child } => {
                self.prop_facts.contains(proposition)
                    || self.proves_resource_contains(parent, child)
            }
            Proposition::And(_, _) | Proposition::Or(_, _) | Proposition::Implies(_, _) => false,
            Proposition::ForAll { var, sort, body } => {
                self.prop_facts.contains(proposition)
                    || self.prop_facts.iter().any(|fact| {
                        let Proposition::ForAll {
                            var: fact_var,
                            sort: fact_sort,
                            body: fact_body,
                        } = fact
                        else {
                            return false;
                        };
                        if fact_sort != sort {
                            return false;
                        }
                        let renamed = substitute_bitvector_variable_in_proposition(
                            fact_body,
                            *fact_var,
                            &Bitvector32Term::Variable(*var),
                        );
                        renamed == **body
                            || crate::kernel::api::propositions_alpha_equivalent(&renamed, body)
                            || self.propositions_equal_modulo_proven_terms(&renamed, body, 0)
                    })
            }
            Proposition::Exists {
                var, sort, body, ..
            } => {
                self.prop_facts.contains(proposition)
                    || self.proves_exists_from_facts(*var, sort, body)
            }
            _ => self.prop_facts.contains(proposition),
        }
    }

    /// Structural proposition equality where differing bitvector subterms
    /// are accepted when this context proves them equal; an assumed
    /// universal over a loop counter then matches the goal spelled with the
    /// counter's proven final value.
    fn propositions_equal_modulo_proven_terms(
        &self,
        left: &Proposition,
        right: &Proposition,
        depth: usize,
    ) -> bool {
        if depth > 16 {
            return false;
        }
        if left == right {
            return true;
        }
        match (left, right) {
            (Proposition::And(al, ar), Proposition::And(bl, br))
            | (Proposition::Or(al, ar), Proposition::Or(bl, br))
            | (Proposition::Implies(al, ar), Proposition::Implies(bl, br)) => {
                self.propositions_equal_modulo_proven_terms(al, bl, depth + 1)
                    && self.propositions_equal_modulo_proven_terms(ar, br, depth + 1)
            }
            (Proposition::Not(a), Proposition::Not(b)) => {
                self.propositions_equal_modulo_proven_terms(a, b, depth + 1)
            }
            (
                Proposition::ConditionIs(left_condition, left_value),
                Proposition::ConditionIs(right_condition, right_value),
            ) if left_value == right_value => {
                self.conditions_equal_modulo_proven_terms(left_condition, right_condition)
            }
            _ => false,
        }
    }

    fn conditions_equal_modulo_proven_terms(
        &self,
        left: &ConditionTerm,
        right: &ConditionTerm,
    ) -> bool {
        if left == right {
            return true;
        }
        let operands = match (left, right) {
            (
                ConditionTerm::Bitvector32SignedLessThan(a, b),
                ConditionTerm::Bitvector32SignedLessThan(c, d),
            )
            | (
                ConditionTerm::Bitvector32SignedLessEqual(a, b),
                ConditionTerm::Bitvector32SignedLessEqual(c, d),
            )
            | (
                ConditionTerm::Bitvector32SignedGreaterThan(a, b),
                ConditionTerm::Bitvector32SignedGreaterThan(c, d),
            )
            | (
                ConditionTerm::Bitvector32SignedGreaterEqual(a, b),
                ConditionTerm::Bitvector32SignedGreaterEqual(c, d),
            )
            | (ConditionTerm::Bitvector32Equal(a, b), ConditionTerm::Bitvector32Equal(c, d)) => {
                Some((a, b, c, d))
            }
            _ => None,
        };
        let Some((a, b, c, d)) = operands else {
            return false;
        };
        let le_holds = |x: &Bitvector32Term, y: &Bitvector32Term| {
            let condition = ConditionTerm::signed_less_equal(x.clone(), y.clone());
            self.decide(&condition) == Some(true)
                || self.proves_condition_from_facts(&condition, true)
        };
        let terms_equal = |x: &Bitvector32Term, y: &Bitvector32Term| {
            x == y
                || self.decide(&ConditionTerm::equal(x.clone(), y.clone())) == Some(true)
                || self.proves_condition_from_facts(
                    &ConditionTerm::equal(x.clone(), y.clone()),
                    true,
                )
                // Antisymmetry: mutual non-strict bounds prove equality.
                || (le_holds(x, y) && le_holds(y, x))
        };
        terms_equal(a, c) && terms_equal(b, d)
    }

    /// Proves an existential goal without search: an assumed existential over
    /// the same sort proves it up to bound-variable renaming, and an equality
    /// conjunct pinning the bound variable supplies a one-point witness whose
    /// instantiated conjuncts must each prove atomically.
    fn proves_exists_from_facts(&self, var: Variable, sort: &Sort, body: &Proposition) -> bool {
        fn conjuncts_of(proposition: &Proposition, into: &mut Vec<Proposition>) {
            match proposition {
                Proposition::And(left, right) => {
                    conjuncts_of(left, into);
                    conjuncts_of(right, into);
                }
                other => into.push(other.clone()),
            }
        }
        let alpha = self.prop_facts.iter().any(|fact| {
            let Proposition::Exists {
                var: fact_var,
                sort: fact_sort,
                body: fact_body,
                ..
            } = fact
            else {
                return false;
            };
            fact_sort == sort
                && crate::kernel::api::propositions_alpha_equivalent(
                    &substitute_bitvector_variable_in_proposition(
                        fact_body,
                        *fact_var,
                        &Bitvector32Term::Variable(var),
                    ),
                    body,
                )
        });
        if alpha {
            return true;
        }
        if !matches!(sort, Sort::CInt32 | Sort::Bitvector32) {
            return false;
        }
        let mut conjuncts = Vec::new();
        conjuncts_of(body, &mut conjuncts);
        let bound = Bitvector32Term::Variable(var);
        let mut witnesses = Vec::new();
        for conjunct in &conjuncts {
            let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) =
                conjunct
            else {
                continue;
            };
            for (side, other) in [(left, right), (right, left)] {
                let mentions_var =
                    substitute_bitvector_variable(other, var, &Bitvector32Term::Constant(0))
                        != **other;
                if **side == bound && !mentions_var {
                    witnesses.push((**other).clone());
                }
            }
        }
        witnesses.iter().any(|witness| {
            conjuncts.iter().all(|conjunct| {
                let instantiated =
                    substitute_bitvector_variable_in_proposition(conjunct, var, witness);
                self.proves_atomic_without_search(&instantiated)
            })
        })
    }

    fn proves_atomic_for_derivation(&self, proposition: &Proposition, for_simp: bool) -> bool {
        self.proves_atomic_for_derivation_with_id(proposition, for_simp)
            .0
    }

    fn proves_atomic_for_derivation_with_id(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> (bool, u64) {
        let id_scope = AssumptionsIdScope::enter(self);
        let premises_id = id_scope.id;
        if !decide_memo_disabled()
            && let Some(result) = ATOMIC_DERIVATION_MEMO.with(|memo| {
                memo.borrow()
                    .get(&(premises_id, for_simp))
                    .and_then(|entries| entries.get(proposition))
                    .copied()
            })
        {
            return (result, premises_id);
        }
        let truncations_before = SEARCH_TRUNCATIONS.with(Cell::get);
        let result = if for_simp {
            match proposition {
                Proposition::ConditionIs(condition, value) => {
                    self.decide_condition_for_simp(condition) == Some(*value)
                }
                Proposition::Not(body) => match body.as_ref() {
                    Proposition::ConditionIs(condition, value) => {
                        self.decide_condition_for_simp(condition) == Some(!*value)
                    }
                    _ => self.prop_facts.contains(proposition),
                },
                _ => self.proves_atomic_without_search(proposition),
            }
        } else {
            self.proves_atomic_without_search(proposition)
        };
        if !decide_memo_disabled()
            && (result || SEARCH_TRUNCATIONS.with(Cell::get) == truncations_before)
        {
            ATOMIC_DERIVATION_MEMO.with(|memo| {
                let mut memo = memo.borrow_mut();
                if memo.len() >= ASSUMPTIONS_MEMO_ID_LIMIT {
                    memo.clear();
                }
                let entries = memo.entry((premises_id, for_simp)).or_default();
                if entries.len() >= DECIDE_MEMO_LIMIT {
                    entries.clear();
                }
                entries.insert(proposition.clone(), result);
            });
        }
        (result, premises_id)
    }

    pub(super) fn replays_atomic_derivation(
        &self,
        proposition: &Proposition,
        for_simp: bool,
        premises_id: u64,
    ) -> bool {
        if !decide_memo_disabled()
            && let Some(result) = ATOMIC_DERIVATION_MEMO.with(|memo| {
                memo.borrow()
                    .get(&(premises_id, for_simp))
                    .and_then(|entries| entries.get(proposition))
                    .copied()
            })
        {
            return result;
        }
        self.proves_atomic_for_derivation(proposition, for_simp)
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

    fn derive_by_finite_context_split(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivationRule> {
        let mut variables = BTreeSet::new();
        collect_proposition_bitvector_variables(proposition, &mut variables);
        let mut candidates = variables
            .into_iter()
            .filter_map(|variable| {
                self.finite_context_range(variable)
                    .map(|range| (variable, range))
            })
            .filter(|(_, range)| range.lower <= range.upper)
            .collect::<Vec<_>>();
        candidates.sort_by_key(|(_, range)| range.upper - range.lower);

        let (variable, range) = candidates.into_iter().next()?;
        let width = usize::try_from(range.upper - range.lower + 1).ok()?;
        if width > FINITE_CONTEXT_SPLIT_LIMIT {
            return None;
        }
        let propositions = (range.lower..=range.upper)
            .map(|value| {
                substitute_bitvector_variable_in_proposition(
                    proposition,
                    variable,
                    &signed_i64_bitvector_constant(value),
                )
            })
            .collect::<Vec<_>>();
        if propositions.iter().all(|instance| instance == proposition) {
            return None;
        }
        let instances = propositions
            .iter()
            .map(|instance| self.derive_proposition_using(instance, for_simp))
            .collect::<Option<Vec<_>>>()?;
        Some(PropositionDerivationRule::FiniteContextSplit {
            variable,
            lower: range.lower,
            upper: range.upper,
            premises: self.clone(),
            instances,
        })
    }

    /// Case analysis on an assumed upper bound over a goal variable.
    ///
    /// A loop back edge asks the closer to re-prove `forall k < b + 1, P(k)`
    /// from an invariant that says `forall k < b, P(k)`. The gap is one index:
    /// `k` is either below `b` — where the invariant applies directly — or
    /// equal to `b`, where the body's own effect discharges it. Neither half
    /// needs a new theory; the split does.
    ///
    /// It is stated as a *goal-side* split rather than as a rule that extends
    /// a quantified fact's bound, which is what makes it cheap here: the
    /// earlier attempt on `claude/forall-extension-wip` had to re-prove the
    /// final index against a fact spelled at another snapshot and drowned in
    /// spelling drift, while each half of this split is derived in the
    /// ordinary way against whatever facts are actually present.
    ///
    /// Sound at both bound shapes, including the wrapping edge: `k <= b`
    /// obviously splits, and `k < b + 1` either splits the same way or — when
    /// `b` is `INT_MAX` and `b + 1` wraps — is unsatisfiable, so the split's
    /// disjunction follows vacuously.
    fn derive_by_upper_bound_split(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivationRule> {
        // Each half re-enters the whole search with one more fact, and the
        // bound that licensed the split survives into both halves, so this
        // recurses without a guard. One split is all the corpus needs — two
        // nested loops still close at this limit — and raising it to 2 cost
        // `bubble_sort3_two_pass_sorted` 20 s for nothing.
        const UPPER_BOUND_SPLIT_DEPTH_LIMIT: usize = 1;
        thread_local! {
            static UPPER_BOUND_SPLIT_DEPTH: Cell<usize> = const { Cell::new(0) };
        }
        if UPPER_BOUND_SPLIT_DEPTH.with(Cell::get) >= UPPER_BOUND_SPLIT_DEPTH_LIMIT {
            return None;
        }
        // Splitting a connective duplicates the work its own rule already
        // does on the way down; by the time the split can help, the guards
        // have been assumed and only the leaf is left.
        if matches!(
            proposition,
            Proposition::And(_, _)
                | Proposition::Or(_, _)
                | Proposition::Implies(_, _)
                | Proposition::ForAll { .. }
                | Proposition::Exists { .. }
        ) {
            return None;
        }
        let mut goal_variables = BTreeSet::new();
        collect_proposition_bitvector_variables(proposition, &mut goal_variables);
        if goal_variables.is_empty() {
            return None;
        }
        let candidates = self
            .condition_facts
            .iter()
            .filter(|(_, value)| **value)
            .filter_map(|(condition, _)| {
                let (variable, pivot) = upper_bound_split_candidate(condition)?;
                if !goal_variables.contains(&variable) {
                    return None;
                }
                let mut pivot_variables = BTreeSet::new();
                collect_bitvector_variables(pivot, &mut pivot_variables);
                if pivot_variables.contains(&variable) {
                    return None;
                }
                // Nothing to split once the context already knows which side
                // of the pivot the variable is on — and this is what stops the
                // halves, which each learn exactly that, from re-splitting.
                if self
                    .decide(&ConditionTerm::signed_less_than(
                        Bitvector32Term::Variable(variable),
                        pivot.clone(),
                    ))
                    .is_some()
                {
                    return None;
                }
                Some((condition.clone(), variable, pivot.clone()))
            })
            .collect::<Vec<_>>();
        for (bound, variable, pivot) in candidates {
            let term = Bitvector32Term::Variable(variable);
            UPPER_BOUND_SPLIT_DEPTH.with(|depth| depth.set(depth.get() + 1));
            let halves = [
                ConditionTerm::signed_less_than(term.clone(), pivot.clone()),
                ConditionTerm::equal(term.clone(), pivot.clone()),
            ]
            .into_iter()
            .map(|case| {
                self.clone()
                    .assume_condition(case, true)
                    .derive_proposition_using(proposition, for_simp)
            })
            .collect::<Option<Vec<_>>>();
            UPPER_BOUND_SPLIT_DEPTH.with(|depth| depth.set(depth.get() - 1));
            let Some(halves) = halves else {
                continue;
            };
            let [below, at]: [PropositionDerivation; 2] = halves
                .try_into()
                .expect("the split derives exactly two halves");
            return Some(PropositionDerivationRule::UpperBoundSplit {
                bound,
                variable,
                pivot,
                below: Box::new(below),
                at: Box::new(at),
            });
        }
        None
    }

    fn derive_by_disjunction_cases(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivationRule> {
        if !matches!(proposition, Proposition::Or(_, _)) {
            return None;
        }
        for disjunction in self.prop_facts.iter() {
            let mut cases = Vec::new();
            collect_or_cases(disjunction, &mut cases);
            if cases.len() < 2 || cases.len() > DISJUNCTION_CASE_LIMIT {
                continue;
            }
            let mut base = self.clone();
            base.remove_proposition_fact(disjunction);
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

    pub(in crate::kernel) fn proves_by_disjunction_cases(&self, proposition: &Proposition) -> bool {
        if !matches!(proposition, Proposition::Or(_, _)) {
            return false;
        }

        for disjunction in self.prop_facts.iter() {
            let mut cases = Vec::new();
            collect_or_cases(disjunction, &mut cases);
            if cases.len() < 2 || cases.len() > DISJUNCTION_CASE_LIMIT {
                continue;
            }

            let mut base = self.clone();
            base.remove_proposition_fact(disjunction);
            if cases.iter().all(|case| {
                base.clone()
                    .assume_proposition(case.clone())
                    .proves(proposition)
            }) {
                return true;
            }
        }
        false
    }

    pub(in crate::kernel) fn proves_finite_forall(&self, proposition: &Proposition) -> bool {
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
        if instantiation_count > FINITE_FORALL_INSTANTIATION_LIMIT {
            return false;
        }

        let mut values = Vec::with_capacity(variables.len());
        self.proves_finite_forall_instantiations(body, &variables, &ranges, &mut values)
    }

    pub(in crate::kernel) fn proves_finite_forall_instantiations(
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

    pub(in crate::kernel) fn proves_by_finite_context_split(
        &self,
        proposition: &Proposition,
    ) -> bool {
        let mut variables = BTreeSet::new();
        collect_proposition_bitvector_variables(proposition, &mut variables);
        let mut candidates = variables
            .into_iter()
            .filter_map(|variable| {
                self.finite_context_range(variable)
                    .map(|range| (variable, range))
            })
            .filter(|(_, range)| range.lower <= range.upper)
            .collect::<Vec<_>>();
        candidates.sort_by_key(|(_, range)| range.upper - range.lower);

        let Some((variable, range)) = candidates.into_iter().next() else {
            return false;
        };
        let Ok(width) = usize::try_from(range.upper - range.lower + 1) else {
            return false;
        };
        if width > FINITE_CONTEXT_SPLIT_LIMIT {
            return false;
        }

        let instances = (range.lower..=range.upper)
            .map(|value| {
                substitute_bitvector_variable_in_proposition(
                    proposition,
                    variable,
                    &signed_i64_bitvector_constant(value),
                )
            })
            .collect::<Vec<_>>();
        if instances
            .iter()
            .all(|instantiated| instantiated == proposition)
        {
            return false;
        }

        instances
            .iter()
            .all(|instantiated| self.proves(instantiated))
    }

    pub(in crate::kernel) fn finite_context_range(
        &self,
        variable: Variable,
    ) -> Option<FiniteForAllRange> {
        let mut range = IntegerRangeFacts::default();
        for (condition, value) in self.condition_facts.iter() {
            let Some((left, right, strict)) = condition_as_order_fact(condition, *value) else {
                continue;
            };
            match (bitvector_variable(&left), signed_bitvector_constant(&right)) {
                (Some(fact_variable), Some(bound)) if fact_variable == variable => {
                    let upper = if strict { bound.checked_sub(1)? } else { bound };
                    range.upper = Some(range.upper.map_or(upper, |current| current.min(upper)));
                }
                _ => {}
            }
            match (signed_bitvector_constant(&left), bitvector_variable(&right)) {
                (Some(bound), Some(fact_variable)) if fact_variable == variable => {
                    let lower = if strict { bound.checked_add(1)? } else { bound };
                    range.lower = Some(range.lower.map_or(lower, |current| current.max(lower)));
                }
                _ => {}
            }
        }

        let (Some(lower), Some(upper)) = (range.lower, range.upper) else {
            return None;
        };
        Some(FiniteForAllRange { lower, upper })
    }

    pub(in crate::kernel) fn proves_condition_from_facts(
        &self,
        condition: &ConditionTerm,
        value: bool,
    ) -> bool {
        self.condition_facts
            .iter()
            .any(|(fact_condition, fact_value)| {
                fact_value == &value && self.condition_matches(fact_condition, condition)
            })
            || self
                .prop_facts
                .iter()
                .any(|proposition| self.proposition_proves_condition(proposition, condition, value))
            || self.proves_condition_from_derived_order_facts(condition, value)
    }

    pub(in crate::kernel) fn proves_condition_from_derived_order_facts(
        &self,
        condition: &ConditionTerm,
        value: bool,
    ) -> bool {
        let Some((left, right, strict)) = condition_as_order_fact(condition, value) else {
            return false;
        };
        let mut order_facts = self.condition_order_facts().as_ref().clone();
        self.collect_derived_order_facts(&mut order_facts);
        self.collect_quantified_order_facts_for_condition(condition, &mut order_facts);
        self.has_order_path_in_facts(&left, &right, strict, &order_facts)
    }

    pub(super) fn collect_quantified_order_facts_for_condition(
        &self,
        condition: &ConditionTerm,
        order_facts: &mut Vec<(Bitvector32Term, Bitvector32Term, bool)>,
    ) {
        for proposition in self.prop_facts.iter() {
            for instance in self.forall_instantiations_for_condition(proposition, condition) {
                self.collect_derived_order_facts_from_proposition(&instance, order_facts);
            }
        }
    }

    pub(in crate::kernel) fn proposition_proves_condition(
        &self,
        proposition: &Proposition,
        condition: &ConditionTerm,
        value: bool,
    ) -> bool {
        match proposition {
            Proposition::ConditionIs(fact_condition, fact_value) => {
                fact_value == &value && self.condition_matches(fact_condition, condition)
            }
            Proposition::And(left, right) => {
                self.proposition_proves_condition(left, condition, value)
                    || self.proposition_proves_condition(right, condition, value)
            }
            Proposition::Implies(left, right) => {
                // Most accumulated call facts conclude something unrelated
                // to this target.  Inspect the conclusion first; conjunction
                // is commutative, and this avoids a global antecedent proof
                // for every irrelevant implication in a long call chain.
                self.proposition_proves_condition(right, condition, value) && {
                    #[cfg(test)]
                    CONDITION_IMPLICATION_ANTECEDENT_CHECKS
                        .with(|checks| checks.set(checks.get() + 1));
                    self.proves_without_prop_facts(left)
                }
            }
            Proposition::ForAll { body, .. } => {
                self.proposition_proves_condition(body, condition, value)
                    || self
                        .forall_instantiations_for_condition(proposition, condition)
                        .iter()
                        .any(|body| self.proposition_proves_condition(body, condition, value))
                    || self
                        .finite_forall_instantiations(proposition)
                        .iter()
                        .any(|body| self.proposition_proves_condition(body, condition, value))
            }
            _ => false,
        }
    }

    pub(in crate::kernel) fn finite_forall_instantiations(
        &self,
        proposition: &Proposition,
    ) -> Vec<Proposition> {
        let mut variables = Vec::new();
        let body = collect_forall_chain(proposition, &mut variables);
        if variables.is_empty() {
            return Vec::new();
        }
        let Some(ranges) = finite_forall_ranges(&variables, body) else {
            return Vec::new();
        };
        let Some(instantiation_count) = ranges.iter().try_fold(1usize, |count, range| {
            let width = usize::try_from(range.upper - range.lower + 1).ok()?;
            count.checked_mul(width)
        }) else {
            return Vec::new();
        };
        if instantiation_count > FINITE_FORALL_INSTANTIATION_LIMIT {
            return Vec::new();
        }

        let mut values = Vec::with_capacity(variables.len());
        let mut instantiations = Vec::with_capacity(instantiation_count);
        self.collect_finite_forall_condition_instantiations(
            body,
            &variables,
            &ranges,
            &mut values,
            &mut instantiations,
        );
        instantiations
    }

    pub(in crate::kernel) fn collect_finite_forall_condition_instantiations(
        &self,
        body: &Proposition,
        variables: &[Variable],
        ranges: &[FiniteForAllRange],
        values: &mut Vec<i64>,
        instantiations: &mut Vec<Proposition>,
    ) {
        if values.len() == variables.len() {
            let mut instantiated = body.clone();
            for (variable, value) in variables.iter().zip(values.iter()) {
                instantiated = substitute_bitvector_variable_in_proposition(
                    &instantiated,
                    *variable,
                    &signed_i64_bitvector_constant(*value),
                );
            }
            instantiations.push(instantiated);
            return;
        }

        let range = &ranges[values.len()];
        for value in range.lower..=range.upper {
            values.push(value);
            self.collect_finite_forall_condition_instantiations(
                body,
                variables,
                ranges,
                values,
                instantiations,
            );
            values.pop();
        }
    }

    pub(in crate::kernel) fn forall_instantiations_for_condition(
        &self,
        proposition: &Proposition,
        condition: &ConditionTerm,
    ) -> Vec<Proposition> {
        let Proposition::ForAll { var, body, .. } = proposition else {
            return Vec::new();
        };
        Self::guided_forall_condition_candidates(*var, body, condition)
            .into_iter()
            .map(|candidate| substitute_bitvector_variable_in_proposition(body, *var, &candidate))
            .collect()
    }

    /// Guided instantiation candidates for one universal int32 body against a
    /// target condition: bound-variable subterm matches inside the body's
    /// conclusion plus the variables of the target condition itself.
    pub(in crate::kernel) fn guided_forall_condition_candidates(
        var: Variable,
        body: &Proposition,
        condition: &ConditionTerm,
    ) -> BTreeSet<Bitvector32Term> {
        fn collect_offset_candidates(
            pattern: &PointerOffsetTerm,
            target: &PointerOffsetTerm,
            bound: Variable,
            candidates: &mut BTreeSet<Bitvector32Term>,
        ) {
            if crate::kernel::reasoning::substitute_bitvector_variable_in_pointer_offset(
                pattern,
                bound,
                &Bitvector32Term::Constant(0),
            ) == *target
            {
                candidates.insert(Bitvector32Term::Constant(0));
            }
            match (pattern, target) {
                (
                    PointerOffsetTerm::Add(left_a, left_b),
                    PointerOffsetTerm::Add(right_a, right_b),
                ) => {
                    collect_offset_candidates(left_a, right_a, bound, candidates);
                    collect_offset_candidates(left_b, right_b, bound, candidates);
                }
                (
                    PointerOffsetTerm::Int32Scaled {
                        value: left,
                        byte_width: left_width,
                    },
                    PointerOffsetTerm::Int32Scaled {
                        value: right,
                        byte_width: right_width,
                    },
                ) if left_width == right_width => {
                    collect_term_candidates(left, right, bound, candidates);
                }
                (
                    PointerOffsetTerm::Int32Scaled {
                        value: left,
                        byte_width,
                    },
                    PointerOffsetTerm::Constant(bytes),
                ) if *byte_width != 0 && bytes % byte_width == 0 => {
                    let elements = bytes / byte_width;
                    collect_term_candidates(
                        left,
                        &Bitvector32Term::Constant((elements as i32) as u32),
                        bound,
                        candidates,
                    );
                }
                _ => {}
            }
        }
        fn collect_pointer_candidates(
            pattern: &Pointer,
            target: &Pointer,
            bound: Variable,
            candidates: &mut BTreeSet<Bitvector32Term>,
        ) {
            if pattern.block == target.block {
                collect_offset_candidates(&pattern.offset, &target.offset, bound, candidates);
            }
        }
        fn collect_term_candidates(
            pattern: &Bitvector32Term,
            target: &Bitvector32Term,
            bound: Variable,
            candidates: &mut BTreeSet<Bitvector32Term>,
        ) {
            if matches!(pattern, Bitvector32Term::Variable(variable) if *variable == bound) {
                candidates.insert(target.clone());
                return;
            }
            if std::mem::discriminant(pattern) != std::mem::discriminant(target) {
                return;
            }
            fn binary(term: &Bitvector32Term) -> Option<(&Bitvector32Term, &Bitvector32Term)> {
                match term {
                    Bitvector32Term::Add(left, right)
                    | Bitvector32Term::Subtract(left, right)
                    | Bitvector32Term::Multiply(left, right)
                    | Bitvector32Term::Divide(left, right)
                    | Bitvector32Term::Remainder(left, right)
                    | Bitvector32Term::ShiftLeft(left, right)
                    | Bitvector32Term::ArithmeticShiftRight(left, right)
                    | Bitvector32Term::BitwiseAnd(left, right)
                    | Bitvector32Term::BitwiseOr(left, right)
                    | Bitvector32Term::BitwiseXor(left, right) => {
                        Some((left.as_ref(), right.as_ref()))
                    }
                    _ => None,
                }
            }
            match (pattern, target) {
                (Bitvector32Term::BitwiseNot(left), Bitvector32Term::BitwiseNot(right)) => {
                    collect_term_candidates(left, right, bound, candidates);
                }
                (
                    Bitvector32Term::MemoryLoad(_, left_pointer),
                    Bitvector32Term::MemoryLoad(_, right_pointer),
                ) => collect_pointer_candidates(left_pointer, right_pointer, bound, candidates),
                (left, right) => {
                    if let (Some((left_a, left_b)), Some((right_a, right_b))) =
                        (binary(left), binary(right))
                    {
                        collect_term_candidates(left_a, right_a, bound, candidates);
                        collect_term_candidates(left_b, right_b, bound, candidates);
                    }
                }
            }
        }
        let mut candidates = BTreeSet::new();
        let mut variables = BTreeSet::new();
        collect_condition_bitvector_variables(condition, &mut variables);
        candidates.extend(variables.into_iter().map(Bitvector32Term::Variable));
        let conclusion = match body {
            Proposition::Implies(_, conclusion) => conclusion.as_ref(),
            conclusion => conclusion,
        };
        if let (
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(pattern_left, pattern_right),
                _,
            ),
            ConditionTerm::Bitvector32Equal(target_left, target_right),
        ) = (conclusion, condition)
        {
            collect_term_candidates(pattern_left, target_left, var, &mut candidates);
            collect_term_candidates(pattern_right, target_right, var, &mut candidates);
            collect_term_candidates(pattern_left, target_right, var, &mut candidates);
            collect_term_candidates(pattern_right, target_left, var, &mut candidates);
        }
        candidates
    }

    pub(in crate::kernel) fn condition_matches(
        &self,
        fact: &ConditionTerm,
        target: &ConditionTerm,
    ) -> bool {
        if fact == target {
            return true;
        }

        match (fact, target) {
            (
                ConditionTerm::Bitvector32Equal(fact_left, fact_right),
                ConditionTerm::Bitvector32Equal(target_left, target_right),
            ) => {
                let fact_left = fact_left.as_ref();
                let fact_right = fact_right.as_ref();
                let target_left = target_left.as_ref();
                let target_right = target_right.as_ref();
                fact_right == target_right
                    && self.bitvector_terms_equal_for_transport(fact_left, target_left)
                    || fact_right == target_left
                        && self.bitvector_terms_equal_for_transport(fact_left, target_right)
                    || fact_left == target_right
                        && self.bitvector_terms_equal_for_transport(fact_right, target_left)
                    || fact_left == target_left
                        && self.bitvector_terms_equal_for_transport(fact_right, target_right)
                    || self.bitvector_terms_equal_for_transport(fact_left, target_left)
                        && self.bitvector_terms_equal_for_transport(fact_right, target_right)
                    || self.bitvector_terms_equal_for_transport(fact_left, target_right)
                        && self.bitvector_terms_equal_for_transport(fact_right, target_left)
            }
            (
                ConditionTerm::PointerOffsetEqual(fact_left, fact_right),
                ConditionTerm::PointerOffsetEqual(target_left, target_right),
            ) => {
                let fact_left = fact_left.as_ref();
                let fact_right = fact_right.as_ref();
                let target_left = target_left.as_ref();
                let target_right = target_right.as_ref();
                fact_right == target_right
                    && self.pointer_offset_terms_equal_for_transport(fact_left, target_left)
                    || fact_right == target_left
                        && self.pointer_offset_terms_equal_for_transport(fact_left, target_right)
                    || fact_left == target_right
                        && self.pointer_offset_terms_equal_for_transport(fact_right, target_left)
                    || fact_left == target_left
                        && self.pointer_offset_terms_equal_for_transport(fact_right, target_right)
                    || self.pointer_offset_terms_snapshot_equivalent(fact_left, target_left)
                        && self.pointer_offset_terms_snapshot_equivalent(fact_right, target_right)
                    || self.pointer_offset_terms_snapshot_equivalent(fact_left, target_right)
                        && self.pointer_offset_terms_snapshot_equivalent(fact_right, target_left)
            }
            (
                ConditionTerm::Bitvector32SignedLessThan(fact_left, fact_right),
                ConditionTerm::Bitvector32SignedLessThan(target_left, target_right),
            )
            | (
                ConditionTerm::Bitvector32SignedLessEqual(fact_left, fact_right),
                ConditionTerm::Bitvector32SignedLessEqual(target_left, target_right),
            )
            | (
                ConditionTerm::Bitvector32SignedGreaterThan(fact_left, fact_right),
                ConditionTerm::Bitvector32SignedGreaterThan(target_left, target_right),
            )
            | (
                ConditionTerm::Bitvector32SignedGreaterEqual(fact_left, fact_right),
                ConditionTerm::Bitvector32SignedGreaterEqual(target_left, target_right),
            ) => {
                self.bitvector_terms_equal_for_transport(fact_left, target_left)
                    && self.bitvector_terms_equal_for_transport(fact_right, target_right)
            }
            (
                ConditionTerm::Bitvector32SignedLessThan(fact_left, fact_right),
                ConditionTerm::Bitvector32SignedGreaterThan(target_left, target_right),
            )
            | (
                ConditionTerm::Bitvector32SignedGreaterThan(fact_left, fact_right),
                ConditionTerm::Bitvector32SignedLessThan(target_left, target_right),
            )
            | (
                ConditionTerm::Bitvector32SignedLessEqual(fact_left, fact_right),
                ConditionTerm::Bitvector32SignedGreaterEqual(target_left, target_right),
            )
            | (
                ConditionTerm::Bitvector32SignedGreaterEqual(fact_left, fact_right),
                ConditionTerm::Bitvector32SignedLessEqual(target_left, target_right),
            ) => {
                self.bitvector_terms_equal_for_transport(fact_left, target_right)
                    && self.bitvector_terms_equal_for_transport(fact_right, target_left)
            }
            _ => false,
        }
    }

    pub(in crate::kernel) fn bitvector_terms_proven_equal(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        left == right
            || self.bitvector_if_terms_proven_equal(left, right)
            || self.bitvector_add_terms_proven_equal(left, right)
            || self.count_fold_split_terms_proven_equal(left, right)
            || self.range_fold_terms_alpha_equivalent(left, right)
            || self.memory_loads_proven_equal(left, right)
    }

    /// Fact-transport equality, memoized by fact-set content identity.
    ///
    /// Order-fact matching asks this for every candidate fact of every
    /// decision, and the same term pairs recur across those scans, so the
    /// search is worth caching. The discipline is [`Self::decide`]'s: a
    /// `true` is evidence found in the facts and is always cacheable, while a
    /// `false` computed under an ambient truncation (memory-resolution fuel,
    /// the memory-load depth guard) is path-dependent and is not. Memoized
    /// only under an enclosing id scope, so no call pays a fact-set hash.
    pub(in crate::kernel) fn bitvector_terms_equal_for_transport(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        if left == right {
            return true;
        }
        let memo_id = if decide_memo_disabled() {
            None
        } else {
            ambient_assumptions_memo_id(self)
        };
        let memo_key = memo_id.map(|memo_id| (memo_id, left.clone(), right.clone()));
        if let Some(memo_key) = &memo_key
            && let Some(hit) =
                TRANSPORT_EQUAL_MEMO.with(|memo| memo.borrow().get(memo_key).copied())
        {
            return hit;
        }
        let truncations_before = SEARCH_TRUNCATIONS.with(Cell::get);
        let result = self.bitvector_terms_equal_for_transport_uncached(left, right);
        if let Some(memo_key) = memo_key
            && (result || SEARCH_TRUNCATIONS.with(Cell::get) == truncations_before)
        {
            TRANSPORT_EQUAL_MEMO.with(|memo| {
                let mut memo = memo.borrow_mut();
                if memo.len() >= DECIDE_MEMO_LIMIT {
                    memo.clear();
                }
                memo.insert(memo_key, result);
            });
        }
        result
    }

    fn bitvector_terms_equal_for_transport_uncached(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        if self.bitvector_terms_equal_from_facts(left, right)
            || self.bitvector_terms_proven_equal(left, right)
        {
            return true;
        }

        match (left, right) {
            (Bitvector32Term::Add(left_a, left_b), Bitvector32Term::Add(right_a, right_b))
            | (
                Bitvector32Term::Subtract(left_a, left_b),
                Bitvector32Term::Subtract(right_a, right_b),
            )
            | (
                Bitvector32Term::Multiply(left_a, left_b),
                Bitvector32Term::Multiply(right_a, right_b),
            )
            | (
                Bitvector32Term::Divide(left_a, left_b),
                Bitvector32Term::Divide(right_a, right_b),
            )
            | (
                Bitvector32Term::Remainder(left_a, left_b),
                Bitvector32Term::Remainder(right_a, right_b),
            )
            | (
                Bitvector32Term::ShiftLeft(left_a, left_b),
                Bitvector32Term::ShiftLeft(right_a, right_b),
            )
            | (
                Bitvector32Term::ArithmeticShiftRight(left_a, left_b),
                Bitvector32Term::ArithmeticShiftRight(right_a, right_b),
            )
            | (
                Bitvector32Term::BitwiseAnd(left_a, left_b),
                Bitvector32Term::BitwiseAnd(right_a, right_b),
            )
            | (
                Bitvector32Term::BitwiseOr(left_a, left_b),
                Bitvector32Term::BitwiseOr(right_a, right_b),
            )
            | (
                Bitvector32Term::BitwiseXor(left_a, left_b),
                Bitvector32Term::BitwiseXor(right_a, right_b),
            ) => {
                self.bitvector_terms_equal_for_transport(left_a, right_a)
                    && self.bitvector_terms_equal_for_transport(left_b, right_b)
            }
            (Bitvector32Term::BitwiseNot(left), Bitvector32Term::BitwiseNot(right)) => {
                self.bitvector_terms_equal_for_transport(left, right)
            }
            _ => false,
        }
    }

    fn pointer_offset_terms_equal_for_transport(
        &self,
        left: &PointerOffsetTerm,
        right: &PointerOffsetTerm,
    ) -> bool {
        if left == right {
            return true;
        }

        match (left, right) {
            (
                PointerOffsetTerm::Int32Scaled {
                    value: left,
                    byte_width: left_width,
                },
                PointerOffsetTerm::Int32Scaled {
                    value: right,
                    byte_width: right_width,
                },
            ) => left_width == right_width && self.bitvector_terms_equal_for_transport(left, right),
            (PointerOffsetTerm::Add(left_a, left_b), PointerOffsetTerm::Add(right_a, right_b)) => {
                self.pointer_offset_terms_equal_for_transport(left_a, right_a)
                    && self.pointer_offset_terms_equal_for_transport(left_b, right_b)
                    || self.pointer_offset_terms_equal_for_transport(left_a, right_b)
                        && self.pointer_offset_terms_equal_for_transport(left_b, right_a)
            }
            _ => false,
        }
    }

    fn pointer_offset_terms_snapshot_equivalent(
        &self,
        left: &PointerOffsetTerm,
        right: &PointerOffsetTerm,
    ) -> bool {
        if left == right {
            return true;
        }
        match (left, right) {
            (
                PointerOffsetTerm::Int32Scaled {
                    value: left,
                    byte_width: left_width,
                },
                PointerOffsetTerm::Int32Scaled {
                    value: right,
                    byte_width: right_width,
                },
            ) => left_width == right_width && self.bitvector_terms_snapshot_equivalent(left, right),
            (PointerOffsetTerm::Add(left_a, left_b), PointerOffsetTerm::Add(right_a, right_b)) => {
                self.pointer_offset_terms_snapshot_equivalent(left_a, right_a)
                    && self.pointer_offset_terms_snapshot_equivalent(left_b, right_b)
                    || self.pointer_offset_terms_snapshot_equivalent(left_a, right_b)
                        && self.pointer_offset_terms_snapshot_equivalent(left_b, right_a)
            }
            _ => false,
        }
    }

    pub(in crate::kernel) fn has_pointer_offset_snapshot_fact(
        &self,
        left: &PointerOffsetTerm,
        right: &PointerOffsetTerm,
    ) -> bool {
        // Keep this deliberately structural and one-hop. Callers use it only
        // to move an already-certified address equality between framed memory
        // snapshots, never to synthesize a new alias relationship.
        self.condition_facts.iter().any(|(condition, value)| {
            if !*value {
                return false;
            }
            let ConditionTerm::PointerOffsetEqual(fact_left, fact_right) = condition else {
                return false;
            };
            self.pointer_offset_terms_snapshot_equivalent(fact_left, left)
                && self.pointer_offset_terms_snapshot_equivalent(fact_right, right)
                || self.pointer_offset_terms_snapshot_equivalent(fact_left, right)
                    && self.pointer_offset_terms_snapshot_equivalent(fact_right, left)
        })
    }

    pub(super) fn bitvector_terms_snapshot_equivalent(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        if left == right {
            return true;
        }
        match (left, right) {
            (Bitvector32Term::MemoryLoad(_, _), Bitvector32Term::MemoryLoad(_, _)) => {
                memory_load_terms_equal_for_fact_transport(left, right, self)
            }
            (Bitvector32Term::Add(left_a, left_b), Bitvector32Term::Add(right_a, right_b))
            | (
                Bitvector32Term::Subtract(left_a, left_b),
                Bitvector32Term::Subtract(right_a, right_b),
            )
            | (
                Bitvector32Term::Multiply(left_a, left_b),
                Bitvector32Term::Multiply(right_a, right_b),
            ) => {
                self.bitvector_terms_snapshot_equivalent(left_a, right_a)
                    && self.bitvector_terms_snapshot_equivalent(left_b, right_b)
            }
            _ => false,
        }
    }

    pub(in crate::kernel) fn bitvector_if_terms_proven_equal(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        let (
            Bitvector32Term::If {
                condition: left_condition,
                then_term: left_then,
                else_term: left_else,
            },
            Bitvector32Term::If {
                condition: right_condition,
                then_term: right_then,
                else_term: right_else,
            },
        ) = (left, right)
        else {
            return false;
        };

        (left_condition == right_condition
            || self.condition_matches(left_condition, right_condition)
            || self.condition_matches(right_condition, left_condition))
            && self.bitvector_terms_proven_equal(left_then, right_then)
            && self.bitvector_terms_proven_equal(left_else, right_else)
    }

    pub(in crate::kernel) fn bitvector_add_terms_proven_equal(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        if !matches!(left, Bitvector32Term::Add(_, _))
            && !matches!(right, Bitvector32Term::Add(_, _))
        {
            return false;
        }

        let mut left_terms = Vec::new();
        let mut left_constant = 0u32;
        collect_bitvector_add_terms(left, &mut left_terms, &mut left_constant);

        let mut right_terms = Vec::new();
        let mut right_constant = 0u32;
        collect_bitvector_add_terms(right, &mut right_terms, &mut right_constant);

        if left_constant != right_constant || left_terms.len() != right_terms.len() {
            return false;
        }

        for left_term in left_terms {
            let Some(index) = right_terms.iter().position(|right_term| {
                self.bitvector_addend_terms_proven_equal(&left_term, right_term)
            }) else {
                return false;
            };
            right_terms.remove(index);
        }

        right_terms.is_empty()
    }

    pub(in crate::kernel) fn bitvector_addend_terms_proven_equal(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        left == right
            || self.bitvector_if_terms_proven_equal(left, right)
            || self.range_fold_terms_alpha_equivalent(left, right)
            || self.bitvector_terms_equal_from_facts(left, right)
            || self.memory_loads_proven_equal(left, right)
    }

    pub(in crate::kernel) fn count_fold_split_terms_proven_equal(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        count_fold_split_matches(left, right, self) || count_fold_split_matches(right, left, self)
    }

    pub(in crate::kernel) fn range_fold_terms_alpha_equivalent(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
    ) -> bool {
        range_fold_terms_alpha_equivalent(left, right, self)
    }

    pub(in crate::kernel) fn proves_without_prop_facts(&self, proposition: &Proposition) -> bool {
        if solve_builtin_prop(proposition) {
            return true;
        }

        let directly_proven = match proposition {
            Proposition::ConditionIs(condition, value) => self.decide(condition) == Some(*value),
            Proposition::And(left, right) => {
                self.proves_without_prop_facts(left) && self.proves_without_prop_facts(right)
            }
            Proposition::Or(left, right) => {
                self.proves_without_prop_facts(left) || self.proves_without_prop_facts(right)
            }
            Proposition::Not(body) => match body.as_ref() {
                Proposition::ConditionIs(condition, value) => {
                    self.decide(condition) == Some(!*value)
                }
                _ => false,
            },
            _ => false,
        };
        if directly_proven {
            return true;
        }

        // Inconsistency proves every proposition, but checking it can scan
        // all order, equality, and separation facts.  Implication-backed call
        // contracts invoke this helper for each antecedent; try the direct
        // evidence first so an ordinary call chain does not repeatedly pay
        // for a global contradiction search.
        self.is_inconsistent()
    }

    pub(in crate::kernel) fn is_inconsistent(&self) -> bool {
        let Some(assumptions_id) = ambient_assumptions_memo_id(self) else {
            return self.is_inconsistent_unmemoized();
        };
        let bridging = crate::kernel::api::extended_dag_bridging_active();
        if CONTEXT_INCONSISTENCY_POSITIVE_MEMO
            .with(|memo| memo.borrow().contains(&(assumptions_id, bridging)))
        {
            return true;
        }
        let generation = crate::kernel::primitives::c_memory_derivation_generation();
        if CONTEXT_INCONSISTENCY_NEGATIVE_MEMO.with(|memo| {
            memo.borrow()
                .contains(&(generation, assumptions_id, bridging))
        }) {
            return false;
        }
        let truncations_before = search_truncations();
        let result = self.is_inconsistent_unmemoized();
        if result {
            CONTEXT_INCONSISTENCY_POSITIVE_MEMO.with(|memo| {
                let mut memo = memo.borrow_mut();
                if memo.len() >= CONTEXT_INCONSISTENCY_MEMO_LIMIT {
                    memo.clear();
                }
                memo.insert((assumptions_id, bridging));
            });
        } else if !crate::instrumentation::deadline_exceeded()
            && search_truncations() == truncations_before
        {
            CONTEXT_INCONSISTENCY_NEGATIVE_MEMO.with(|memo| {
                let mut memo = memo.borrow_mut();
                if memo.len() >= CONTEXT_INCONSISTENCY_MEMO_LIMIT {
                    memo.clear();
                }
                memo.insert((generation, assumptions_id, bridging));
            });
        }
        result
    }

    fn is_inconsistent_unmemoized(&self) -> bool {
        #[cfg(test)]
        CONTEXT_INCONSISTENCY_FULL_SCANS.with(|scans| scans.set(scans.get() + 1));
        let fact_scan_timing = crate::instrumentation::OperationTiming::new(
            "kernel",
            "context inconsistency",
            "context inconsistency: fact scan and exact indexes",
        );
        let mut order_facts = Vec::new();
        let mut equal_facts = Vec::new();
        let mut disequal_facts = Vec::new();
        let mut exact_equal_pairs = BTreeSet::new();
        let mut exact_disequal_pairs = BTreeSet::new();
        let mut exact_order_pairs = BTreeMap::<(Bitvector32Term, Bitvector32Term), bool>::new();
        let mut condition_polarities = BTreeMap::new();
        for (condition, value) in self.condition_facts.iter() {
            crate::instrumentation::record_deterministic_work(1);
            let key = canonical_contradiction_condition(condition);
            if condition_polarities
                .insert(key, *value)
                .is_some_and(|prior| prior != *value)
            {
                return true;
            }
            match (condition, value) {
                (ConditionTerm::Constant(actual), expected) if actual != expected => return true,
                (ConditionTerm::Bitvector32Equal(left, right), true) => {
                    equal_facts.push((left.as_ref().clone(), right.as_ref().clone()));
                    let pair = if left <= right {
                        (left.as_ref().clone(), right.as_ref().clone())
                    } else {
                        (right.as_ref().clone(), left.as_ref().clone())
                    };
                    exact_equal_pairs.insert(pair);
                }
                (ConditionTerm::Bitvector32Equal(left, right), false) => {
                    disequal_facts.push((left.as_ref().clone(), right.as_ref().clone()));
                    let pair = if left <= right {
                        (left.as_ref().clone(), right.as_ref().clone())
                    } else {
                        (right.as_ref().clone(), left.as_ref().clone())
                    };
                    exact_disequal_pairs.insert(pair);
                }
                _ => {
                    if let Some(order_fact) = condition_as_order_fact(condition, *value) {
                        let pair = (order_fact.0.clone(), order_fact.1.clone());
                        exact_order_pairs
                            .entry(pair)
                            .and_modify(|strict| *strict |= order_fact.2)
                            .or_insert(order_fact.2);
                        order_facts.push(order_fact);
                    }
                }
            }
        }
        drop(fact_scan_timing);

        let exact_timing = crate::instrumentation::OperationTiming::new(
            "kernel",
            "context inconsistency",
            "context inconsistency: exact conflicts",
        );
        if exact_equal_pairs
            .iter()
            .any(|pair| exact_disequal_pairs.contains(pair))
        {
            return true;
        }
        if exact_order_pairs.iter().any(|((left, right), strict)| {
            (left == right && *strict)
                || exact_order_pairs
                    .get(&(right.clone(), left.clone()))
                    .is_some_and(|reverse_strict| *strict || *reverse_strict)
                || (*strict
                    && exact_equal_pairs.contains(&if left <= right {
                        (left.clone(), right.clone())
                    } else {
                        (right.clone(), left.clone())
                    }))
        }) {
            return true;
        }
        drop(exact_timing);

        let derived_pair_timing = crate::instrumentation::OperationTiming::new(
            "kernel",
            "context inconsistency",
            "context inconsistency: derived pair conflicts",
        );
        let equality_conflict_timing = crate::instrumentation::OperationTiming::new(
            "kernel",
            "context inconsistency",
            "context inconsistency: derived equality conflicts",
        );
        for (equal_left, equal_right) in &equal_facts {
            crate::instrumentation::record_deterministic_work(1);
            if disequal_facts
                .iter()
                .any(|(disequal_left, disequal_right)| {
                    crate::instrumentation::record_deterministic_work(1);
                    (equal_left == disequal_left && equal_right == disequal_right)
                        || (equal_left == disequal_right && equal_right == disequal_left)
                })
            {
                return true;
            }
        }
        drop(equality_conflict_timing);

        let terms_equal = |left: &Bitvector32Term, right: &Bitvector32Term| {
            left == right
                || self.bitvector_terms_equal_from_facts(left, right)
                || bitvector_terms_may_be_theory_equal(left, right)
                    && self.bitvector_terms_proven_equal(left, right)
        };
        let order_conflict_timing = crate::instrumentation::OperationTiming::new(
            "kernel",
            "context inconsistency",
            "context inconsistency: derived order conflicts",
        );
        for (left, right, strict) in &order_facts {
            crate::instrumentation::record_deterministic_work(1);
            if *strict && terms_equal(left, right) {
                return true;
            }
            if equal_facts.iter().any(|(equal_left, equal_right)| {
                crate::instrumentation::record_deterministic_work(1);
                (terms_equal(left, equal_left) && terms_equal(right, equal_right))
                    || (terms_equal(left, equal_right) && terms_equal(right, equal_left))
            }) && *strict
            {
                return true;
            }
            if order_facts
                .iter()
                .any(|(other_left, other_right, other_strict)| {
                    crate::instrumentation::record_deterministic_work(1);
                    terms_equal(left, other_right)
                        && terms_equal(right, other_left)
                        && (*strict || *other_strict)
                })
            {
                return true;
            }
        }
        drop(order_conflict_timing);
        drop(derived_pair_timing);

        if crate::instrumentation::measure_operation(
            "kernel",
            "context inconsistency",
            "context inconsistency: finite range",
            || finite_integer_range_exhausted(&order_facts, &equal_facts, &disequal_facts),
        ) {
            return true;
        }

        if crate::instrumentation::measure_operation(
            "kernel",
            "context inconsistency",
            "context inconsistency: alias separation",
            || self.alias_guard_refuted_by_separation(),
        ) {
            return true;
        }

        false
    }

    /// True when an assumed "these two offsets are the same address" guard is
    /// refuted by recorded separation.
    ///
    /// Memory-load lowering splits on every cell it cannot resolve, emitting a
    /// `PointerOffsetEqual(..) = true` guard for the aliasing branch. The
    /// invariant closer lowers with `defer_non_exact_condition_reasoning`, so
    /// the split is taken even where separation facts plus the surrounding
    /// bounds do rule the alias out — the bound that puts the index inside the
    /// separated range is only assumed *inside* the quantified body, which the
    /// splitter never sees. The resulting path is vacuous, and its goal
    /// ("the owner field this element aliases equals the stored value") is
    /// unprovable by anything except that vacuity.
    ///
    /// A `PointerOffsetEqual` guard is only ever emitted between two pointers
    /// in one block (`pointer_equality_condition` drops to offsets exactly
    /// then), but the condition itself no longer names that block. Recovering
    /// it from separation facts is sound rather than a guess: a separation
    /// between two ranges constrains offsets only when the ranges share a base
    /// block, so requiring that and re-attaching the shared block to both
    /// offsets asks precisely "do these two offsets fall in disjoint intervals
    /// of one block", which is a statement about the offset terms alone.
    fn alias_guard_refuted_by_separation(&self) -> bool {
        // `pointer_in_range` re-enters condition reasoning, which can reach
        // `is_inconsistent` again; one level is all this rule ever needs.
        thread_local! {
            static ALIAS_GUARD_REFUTATION_ACTIVE: Cell<bool> = const { Cell::new(false) };
        }
        if ALIAS_GUARD_REFUTATION_ACTIVE.with(Cell::get) {
            return false;
        }
        let guards = self
            .condition_facts
            .iter()
            .filter_map(|(condition, value)| match (condition, value) {
                (ConditionTerm::PointerOffsetEqual(left, right), true) if left != right => {
                    Some((left.as_ref(), right.as_ref()))
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        if guards.is_empty() {
            return false;
        }
        let separated = self
            .prop_facts
            .iter()
            .filter_map(|fact| match fact {
                Proposition::CResourceSeparate {
                    left: CResource::Memory(left),
                    right: CResource::Memory(right),
                } => Some((left, right)),
                _ => None,
            })
            .filter(|(left, right)| left.base().block == right.base().block)
            .collect::<Vec<_>>();
        if separated.is_empty() {
            return false;
        }
        ALIAS_GUARD_REFUTATION_ACTIVE.with(|active| active.set(true));
        let refuted = guards.iter().any(|(left, right)| {
            separated.iter().any(|(first, second)| {
                let holds = |range: &CMemoryRange, offset: &PointerOffsetTerm| {
                    let pointer = Pointer {
                        block: range.base().block.clone(),
                        offset: offset.clone(),
                    };
                    // Keep this contradiction rule bounded. Calling the
                    // general `pointer_in_range` prover here recursively
                    // re-enters context-wide contradiction search once for
                    // every separation fact. Deeper range consequences may
                    // be proved directly, but are not a routing precondition.
                    self.pointer_in_range_by_shallow_fact_graph(
                        &pointer,
                        range.base(),
                        range.start(),
                        range.end(),
                    )
                };
                holds(first, left) && holds(second, right)
                    || holds(first, right) && holds(second, left)
            })
        });
        ALIAS_GUARD_REFUTATION_ACTIVE.with(|active| active.set(false));
        refuted
    }

    pub(in crate::kernel) fn proves_not(&self, proposition: &Proposition) -> bool {
        match proposition {
            Proposition::ConditionIs(condition, value) => self.decide(condition) == Some(!*value),
            Proposition::Not(body) => self.proves(body),
            _ => self
                .prop_facts
                .contains(&Proposition::Not(Box::new(proposition.clone()))),
        }
    }
}
