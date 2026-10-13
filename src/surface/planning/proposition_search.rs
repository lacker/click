//! The logical proposition search, as Surface Click planning.
//!
//! This is the prover that used to live in
//! `src/kernel/assumptions/proposition_reasoning.rs`. It is a recursive
//! backtracking search over a goal's logical structure: exact facts,
//! algebraic constructor rules and the condition decision procedure at the
//! leaves, then `And`, `Or` arm choice, `Not`, `Implies` under an assumed
//! antecedent, `ForAll` by finite instantiation or checked premise selection, case
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
//! `proves_memory_access`, `proves_resource_separate`,
//! `proves_resource_contains`, and the canonicalization equality walks)
//! stay in the kernel and are unchanged;
//! see the kernel authority boundary in `docs/internals/proof-objects.md`.
//!
//! Nothing under `src/kernel/` may call into this module. A kernel
//! operation that needs to know whether a proposition holds uses an exact
//! route or emits the proposition as an obligation.

use crate::kernel::planning_api::*;
use crate::kernel::*;
#[cfg(test)]
use std::collections::BTreeMap;
use std::collections::BTreeSet;

/// Nested disjunction case splits allowed inside one derivation.
const MAX_DISJUNCTION_SPLIT_DEPTH: usize = 2;

thread_local! {
    static DISJUNCTION_SPLIT_DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

struct DisjunctionSplitDepth;

impl DisjunctionSplitDepth {
    fn enter() -> Option<Self> {
        DISJUNCTION_SPLIT_DEPTH.with(|depth| {
            (depth.get() < MAX_DISJUNCTION_SPLIT_DEPTH).then(|| {
                depth.set(depth.get() + 1);
                DisjunctionSplitDepth
            })
        })
    }
}

impl Drop for DisjunctionSplitDepth {
    fn drop(&mut self) {
        DISJUNCTION_SPLIT_DEPTH.with(|depth| depth.set(depth.get().saturating_sub(1)));
    }
}

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
        exclude_exact_goal: bool,
    ) -> Option<(PureFactContext, u64, AtomicPropositionDerivationEvidence)>;

    fn derive_proposition_using(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> Option<Box<PropositionDerivation>>;

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
                    || self
                        .derive_forall_rule(proposition, *var, body, false)
                        .is_some_and(|rule| proposition_derivation(proposition, rule).check(self))
            }
            Proposition::CValidPlace { .. } => self.proves_atomic_without_search(proposition),
            Proposition::CMemoryInitialized {
                memory,
                base,
                bytes,
            } => self.proves_memory_initialized(memory, base, *bytes),
            Proposition::CMemoryReadDefined {
                memory,
                pointer,
                value_type,
            } => self.proves_memory_read_defined(memory, pointer, *value_type),
            Proposition::CMemoryLoadable {
                memory,
                base,
                bytes,
                wide: true,
            } => self.proves_native_memory_loadable(memory, base, bytes),
            Proposition::CMemoryLoadable {
                memory,
                base,
                bytes,
                wide: false,
            } => self.proves_memory_loadable(memory, base, bytes),
            Proposition::CMemoryCanStore {
                memory,
                pointer,
                byte_width,
            } => self.proves_memory_access(memory, pointer, *byte_width),
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
            .map(|derivation| *derivation)
    }

    fn derive_simp_proposition(&self, proposition: &Proposition) -> Option<PropositionDerivation> {
        self.derive_proposition_using(proposition, true)
            .map(|derivation| *derivation)
    }

    /// Selects an independent derivation without taking the goal's own exact
    /// ambient fact as a premise. Keep the ambient graph intact: dropping a
    /// fact from it would rebuild its equality closure just to avoid the
    /// circular `assumption()` candidate.
    fn derive_simp_proposition_without_exact_goal(
        &self,
        proposition: &Proposition,
    ) -> Option<PropositionDerivation> {
        if let Some(derivation) = self.derive_simp_proposition(proposition)
            && !derivation.context_premises().contains(proposition)
        {
            return Some(derivation);
        }
        self.atomic_derivation_premises(proposition, true, true)
            .map(|(premises, premises_id, evidence)| {
                proposition_derivation(
                    proposition,
                    PropositionDerivationRule::ContextualAtomic {
                        premises: RetainedPremises::from_context(&premises),
                        premises_id,
                        for_simp: true,
                        evidence,
                    },
                )
            })
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
        self.atomic_derivation_premises(proposition, for_simp, false)
            .map(|(premises, premises_id, evidence)| {
                proposition_derivation(
                    proposition,
                    PropositionDerivationRule::ContextualAtomic {
                        premises: RetainedPremises::from_context(&premises),
                        premises_id,
                        for_simp,
                        evidence,
                    },
                )
            })
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
        exclude_exact_goal: bool,
    ) -> Option<(PureFactContext, u64, AtomicPropositionDerivationEvidence)> {
        // A retained object declaration/input can settle validity without
        // any pure premise. Ask the checked atomic leaf before searching for
        // dependencies; the complete carrier and snapshot are in the goal.
        if matches!(proposition, Proposition::CValidPlace { .. }) {
            let direct = PureFactContext::new();
            let (evidence, premises_id) =
                direct.proves_atomic_for_derivation_with_id(proposition, for_simp);
            if let Some(evidence) = evidence {
                return Some((direct, premises_id, evidence));
            }
        }
        if !exclude_exact_goal && self.proves_exact(proposition) {
            let exact = PureFactContext::new().assume_proposition(proposition.clone());
            let (evidence, premises_id) =
                exact.proves_atomic_for_derivation_with_id(proposition, for_simp);
            if let Some(evidence) = evidence {
                return Some((exact, premises_id, evidence));
            }
        }
        // A constant-pinned equality needs at most two indexed premises, even
        // when the same variable occurs in every preceding branch guard.
        // Recheck that small selection before trying the connected component.
        if let Some(premises) = self.indexed_constant_equality_premises(proposition)
            && (!exclude_exact_goal || !premises.contains(proposition))
        {
            let candidate = premises
                .into_iter()
                .fold(PureFactContext::new(), |context, premise| {
                    context.assume_proposition(premise)
                });
            let (evidence, premises_id) =
                candidate.proves_atomic_for_derivation_with_id(proposition, for_simp);
            if let Some(evidence) = evidence {
                return Some((candidate, premises_id, evidence));
            }
        }
        if let Proposition::ConditionIs(condition, _) = proposition
            && let Some(selected) = self.widened_unsigned_sum_bound_premises(condition)
        {
            let candidate = selected
                .into_iter()
                .fold(PureFactContext::new(), |context, premise| {
                    context.assume_proposition(premise)
                });
            let (evidence, premises_id) =
                candidate.proves_atomic_for_derivation_with_id(proposition, for_simp);
            if matches!(
                evidence,
                Some(AtomicPropositionDerivationEvidence::WidenedUnsignedSumBound)
            ) {
                return evidence.map(|evidence| (candidate, premises_id, evidence));
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
        let mut condition_sources = Vec::new();
        if condition_goal {
            let (selected, _, _, _) =
                connected_atomic_premises(self, proposition, &[], false, true, exclude_exact_goal)?;
            let candidate = atomic_context_from_facts(self, &selected, &[]);
            let (evidence, premises_id) =
                candidate.proves_atomic_for_derivation_with_id(proposition, for_simp);
            if let Some(evidence) = evidence {
                return Some((candidate, premises_id, evidence));
            }
            condition_sources = selected
                .into_iter()
                .map(|(condition, value)| Proposition::ConditionIs(condition, value))
                .collect();
        }

        let candidate_family = |fact: &Proposition| match proposition {
            Proposition::CMemoryReadDefined { .. } => matches!(
                fact,
                Proposition::CMemoryReadDefined { .. } | Proposition::CMemoryLoadable { .. }
            ),
            Proposition::CMemoryInitialized { .. }
            | Proposition::CMemoryLoadable { .. }
            | Proposition::CMemoryCanStore { .. } => {
                matches!(fact, Proposition::CMemoryLoadable { .. })
            }
            Proposition::CResourceSeparate { .. } => {
                matches!(fact, Proposition::CResourceSeparate { .. })
            }
            _ => false,
        };
        // A loadability or store goal is decided from the loadability facts
        // of its own block and from nothing else in that family: that is
        // the only bucket the kernel's loadable prover reads. Selecting
        // from the same index keeps every answer while leaving facts about
        // other objects unvisited.
        let goal_base = match proposition {
            Proposition::CMemoryInitialized { base, .. }
            | Proposition::CMemoryLoadable { base, .. } => Some(base),
            Proposition::CMemoryCanStore { pointer, .. } => Some(pointer),
            _ => None,
        };
        let usable = |fact: &&Proposition| !exclude_exact_goal || *fact != proposition;
        // A read-defined goal is first asked of the evidence stated at its
        // own address and of its block's loadability facts; a separation of
        // two memory ranges of the facts its block pair and the non-memory
        // residue hold. Those are the buckets the kernel's provers consult
        // directly.
        let indexed = match proposition {
            _ if goal_base.is_some() => goal_base.map(|base| {
                self.memory_loadable_candidates_for_base(base)
                    .inspect(|_| record_candidate_visit())
                    .filter(usable)
                    .cloned()
                    .collect::<Vec<_>>()
            }),
            Proposition::CMemoryReadDefined {
                pointer,
                value_type,
                ..
            } => Some(
                self.memory_read_defined_candidates(pointer, *value_type)
                    .into_iter()
                    .chain(self.memory_loadable_candidates_for_base(pointer))
                    .inspect(|_| record_candidate_visit())
                    .filter(usable)
                    .cloned()
                    .collect(),
            ),
            Proposition::CResourceSeparate { left, right } => self
                .resource_separation_candidates(left, right)
                .map(|facts| {
                    facts
                        .into_iter()
                        .inspect(|_| record_candidate_visit())
                        .filter(usable)
                        .cloned()
                        .collect()
                }),
            _ => None,
        };
        // The rest of the family is a fallback, reached only when no indexed
        // source justified the goal: a read whose address is itself computed
        // from another read, or a separation entailed through containment in
        // a differently placed fact, can still be proved from one of them.
        // Loadability needs none: its prover reads the block bucket alone.
        let family_fallback = |tried: &[Proposition]| {
            if !matches!(
                proposition,
                Proposition::CMemoryReadDefined { .. } | Proposition::CResourceSeparate { .. }
            ) {
                return Vec::new();
            }
            let tried = tried.iter().collect::<BTreeSet<_>>();
            self.proposition_facts()
                .inspect(|_| record_candidate_visit())
                .filter(|fact| candidate_family(fact) && usable(fact) && !tried.contains(fact))
                .cloned()
                .collect::<Vec<_>>()
        };
        let candidates = indexed.unwrap_or_default();
        // Every trial is rebuilt only from explicitly selected dependencies.
        // The kernel must establish the goal again in that restricted context.
        let trial = |sources: &[Proposition]| {
            let direct = atomic_context_from_facts(self, &[], sources);
            let (evidence, premises_id) =
                direct.proves_atomic_for_derivation_with_id(proposition, for_simp);
            if let Some(evidence) = evidence {
                return Some((direct, premises_id, evidence));
            }
            let (conditions, propositions, _, _) = connected_atomic_premises(
                self,
                proposition,
                sources,
                false,
                false,
                exclude_exact_goal,
            )?;
            let candidate = atomic_context_from_facts(self, &conditions, &propositions);
            let (evidence, premises_id) =
                candidate.proves_atomic_for_derivation_with_id(proposition, for_simp);
            evidence.map(|evidence| (candidate, premises_id, evidence))
        };
        if let Proposition::CMemoryLoadable {
            memory,
            base,
            bytes,
            wide: false,
        } = proposition
            && let Some(premises) = self.adjacent_loadable_region_facts(memory, base, bytes)
            && (!exclude_exact_goal || !premises.contains(&proposition.clone()))
            && let Some(found) = trial(&premises)
        {
            return Some(found);
        }
        let try_each = |candidates: &[Proposition]| {
            for selected in candidates {
                if simp_reasoning_interrupted() {
                    return Err(());
                }
                if let Some(found) = trial(std::slice::from_ref(selected)) {
                    return Ok(Some(found));
                }
            }
            Ok(None)
        };
        match try_each(&candidates) {
            Err(()) => return None,
            Ok(Some(found)) => return Some(found),
            Ok(None) => {}
        }
        // Two loadable ranges justify a goal only by concatenation, and the
        // kernel names the pair that concatenates. The first lookup above
        // may have named the goal's own statement; without it, ask again of
        // the other sources alone instead of trying every pair.
        if exclude_exact_goal
            && let Proposition::CMemoryLoadable {
                memory,
                base,
                bytes,
                wide: false,
            } = proposition
            && candidates.len() > 1
        {
            let (conditions, propositions, _, _) = connected_atomic_premises(
                self,
                proposition,
                &candidates,
                false,
                false,
                exclude_exact_goal,
            )?;
            let sources = atomic_context_from_facts(self, &conditions, &propositions);
            if let Some(premises) = sources.adjacent_loadable_region_facts(memory, base, bytes)
                && let Some(found) = trial(&premises)
            {
                return Some(found);
            }
        }
        let fallback = family_fallback(&candidates);
        // A lone fallback fact will be available to the joint dependency
        // selection below.
        if fallback.len() + candidates.len() > 1 {
            match try_each(&fallback) {
                Err(()) => return None,
                Ok(Some(found)) => return Some(found),
                Ok(None) => {}
            }
        }
        if exclude_exact_goal {
            None
        } else {
            // Smart equality failures can be expensive history walks. Use
            // the shared ambient oracle only to reject an unprovable goal;
            // a positive answer still needs selected premises and a fresh
            // restricted kernel query before it can become evidence.
            if for_simp
                && matches!(
                    proposition,
                    Proposition::ConditionIs(
                        ConditionTerm::Bitvector32Equal(..)
                            | ConditionTerm::Bitvector64Equal(..)
                            | ConditionTerm::PointerOffsetEqual(..),
                        _
                    )
                )
                && self
                    .proves_atomic_for_derivation_with_id(proposition, for_simp)
                    .0
                    .is_none()
            {
                return None;
            }
            // The condition-only query above already checked this fact set.
            // Compare facts, not traversal keys: widening can reach more keys
            // without adding any premise and must not repeat the same query.
            let mut tried = condition_goal.then(|| {
                (
                    condition_sources
                        .iter()
                        .filter_map(|fact| match fact {
                            Proposition::ConditionIs(condition, value) => {
                                Some((condition.clone(), *value))
                            }
                            _ => None,
                        })
                        .collect::<Vec<_>>(),
                    Vec::new(),
                )
            });
            // Condition selection already made the narrow attempt. Its
            // fallback includes frame and quantified dependencies in one
            // query, rather than retrying a partial snapshot context first.
            let widths: &[bool] = if condition_goal {
                &[true]
            } else {
                &[false, true]
            };
            for &widened in widths {
                let selected = connected_atomic_premises(
                    self,
                    proposition,
                    &condition_sources,
                    true,
                    widened,
                    false,
                )?;
                let (conditions, propositions, reached, _) = &selected;
                if tried
                    .as_ref()
                    .is_some_and(|(prior_conditions, prior_propositions)| {
                        prior_conditions == conditions && prior_propositions == propositions
                    })
                {
                    continue;
                }
                let candidate = atomic_context_from_facts(self, conditions, propositions);
                let (evidence, premises_id) =
                    candidate.proves_atomic_for_derivation_with_id(proposition, for_simp);
                if let Some(evidence) = evidence {
                    return Some((candidate, premises_id, evidence));
                }
                if !widened
                    && !atomic_widening_adds_dependencies(self, proposition, &candidate, reached)
                {
                    break;
                }
                tried = Some((conditions.clone(), propositions.clone()));
            }
            None
        }
    }

    #[inline(never)]
    fn derive_proposition_using(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> Option<Box<PropositionDerivation>> {
        let _id_scope = PureFactContextIdScope::enter(self);
        if simp_reasoning_interrupted() {
            return None;
        }
        if solve_builtin_prop(proposition) {
            return Some(Box::new(proposition_derivation(
                proposition,
                PropositionDerivationRule::ContextFree,
            )));
        }
        if let Some(rule) = self.derive_by_algebraic_constructor_rules(proposition, for_simp) {
            return Some(Box::new(proposition_derivation(proposition, rule)));
        }
        let direct = self.derive_structural_rule(proposition, for_simp);
        if let Some(rule) = direct {
            return Some(Box::new(proposition_derivation(proposition, rule)));
        }
        if self.is_inconsistent() {
            return Some(Box::new(proposition_derivation(
                proposition,
                PropositionDerivationRule::Explosion {
                    premises: RetainedPremises::from_context(self),
                },
            )));
        }
        if let Some(rule) = self.derive_by_singleton_substitution(proposition, for_simp) {
            return Some(Box::new(proposition_derivation(proposition, rule)));
        }
        self.derive_by_disjunction_cases(proposition, for_simp)
            .map(|rule| Box::new(proposition_derivation(proposition, rule)))
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
            .map(|(left, right)| PropositionDerivationRule::And { left, right })
    }

    #[inline(never)]
    fn derive_or_rule(
        &self,
        left: &Proposition,
        right: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivationRule> {
        self.derive_proposition_using(left, for_simp)
            .map(PropositionDerivationRule::OrLeft)
            .or_else(|| {
                self.derive_proposition_using(right, for_simp)
                    .map(PropositionDerivationRule::OrRight)
            })
    }

    #[inline(never)]
    fn derive_double_negation_rule(
        &self,
        inner: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivationRule> {
        self.derive_proposition_using(inner, for_simp)
            .map(PropositionDerivationRule::DoubleNegation)
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
                .map(PropositionDerivationRule::ImpliesFalseAntecedent)
        } else {
            self.clone()
                .assume_proposition(antecedent.clone())
                .derive_proposition_using(right, for_simp)
                .map(|body| PropositionDerivationRule::Implies {
                    antecedent: Box::new(antecedent),
                    body,
                })
                .or_else(|| {
                    self.derive_proposition_using(&negated_antecedent, for_simp)
                        .map(PropositionDerivationRule::ImpliesFalseAntecedent)
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
        let body_uses_binder = crate::kernel::proposition_has_free_bitvector_variable(body, var);
        let body_derivation = self
            .derive_proposition_using(body, for_simp)
            .filter(|proof| {
                !body_uses_binder
                    || proof.context_premises().iter().all(|premise| {
                        !crate::kernel::proposition_has_free_bitvector_variable(premise, var)
                    })
            })
            .map(PropositionDerivationRule::ForAllBody);
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
        self.atomic_derivation_premises(proposition, for_simp, false)
            .map(
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
                .map(|field| {
                    self.derive_proposition_using(field, for_simp)
                        .map(|proof| *proof)
                })
                .collect::<Option<Vec<_>>>()?;
            return Some(PropositionDerivationRule::AlgebraicConstructorCongruence { fields });
        }
        self.algebraic_constructor_field_sources(proposition)
            .next()
            .map(|(source, field_index)| {
                PropositionDerivationRule::AlgebraicConstructorInjectivity {
                    source: Box::new(source.clone()),
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
            .map(|instance| {
                self.derive_proposition_using(instance, for_simp)
                    .map(|proof| *proof)
            })
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
                    source: Box::new(source),
                    body: derivation,
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
                    body: derivation,
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
                    source: Box::new(source.clone()),
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
                    source: Box::new(source.clone()),
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
        collect_proposition_connection_variables(proposition, &mut variables);
        let (variable, value, equality) = variables
            .into_iter()
            .filter_map(|variable| {
                self.singleton_constant_equality_evidence(variable)
                    .map(|(value, evidence)| (variable, value, evidence))
            })
            .next()?;
        let instantiated =
            substitute_machine_constant_in_pure_proposition(proposition, variable, value).ok()?;
        if instantiated == *proposition {
            return None;
        }
        let body = self.derive_proposition_using(&instantiated, for_simp)?;
        Some(PropositionDerivationRule::SingletonSubstitution {
            variable,
            value,
            equality,
            body,
        })
    }

    fn derive_by_disjunction_cases(
        &self,
        proposition: &Proposition,
        for_simp: bool,
    ) -> Option<PropositionDerivationRule> {
        // Each case re-enters the whole derivation, which splits again on
        // every remaining disjunction: with a dozen call outcomes in scope
        // (`result == 0 or result == 1` per call) a goal no case helps paid
        // for every nested combination before failing. A split can only help
        // through a case that constrains something the goal names, so a
        // disjunction over machine variables none of which the goal names is
        // not split, and splits nest at most `MAX_DISJUNCTION_SPLIT_DEPTH`
        // deep.
        let _depth = DisjunctionSplitDepth::enter()?;
        let mut goal_variables = BTreeSet::new();
        collect_proposition_bitvector_variables(proposition, &mut goal_variables);
        for disjunction in self.disjunction_fact_propositions() {
            let mut disjunction_variables = BTreeSet::new();
            collect_proposition_bitvector_variables(disjunction, &mut disjunction_variables);
            // A disjunction or goal over no machine variable (predicates,
            // algebraic values) is never judged unrelated.
            if !goal_variables.is_empty()
                && !disjunction_variables.is_empty()
                && disjunction_variables.is_disjoint(&goal_variables)
            {
                continue;
            }
            let mut cases = Vec::new();
            collect_or_cases(disjunction, &mut cases);
            if cases.len() < 2 {
                continue;
            }
            if cases
                .iter()
                .all(|case| self.contains_assumed_exact(&Proposition::Not(Box::new(case.clone()))))
            {
                return Some(PropositionDerivationRule::RefutedDisjunction {
                    disjunction: Box::new(disjunction.clone()),
                });
            }
            // A branch retains the disjunction and adds its chosen case.
            // Once a case is present, splitting this disjunction again adds
            // nothing and would recurse on the same proof context.
            if cases.iter().any(|case| self.contains_assumed_exact(case)) {
                continue;
            }
            let Some(proofs) = cases
                .iter()
                .map(|case| {
                    self.clone()
                        .assume_proposition(case.clone())
                        .derive_proposition_using(proposition, for_simp)
                        .map(|proof| *proof)
                })
                .collect::<Option<Vec<_>>>()
            else {
                continue;
            };
            return Some(PropositionDerivationRule::DisjunctionCases {
                disjunction: Box::new(disjunction.clone()),
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
        collect_proposition_connection_variables(proposition, &mut variables);
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
        let Ok(instantiated) =
            substitute_machine_constant_in_pure_proposition(proposition, variable, value)
        else {
            return false;
        };
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

#[cfg(test)]
mod monotone_forall_tests {
    use super::*;

    #[test]
    fn forall_shadowing_keeps_facts_about_the_outer_variable() {
        let outer = Variable(100);
        let other = Variable(101);
        let equality = |left, right| {
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
                true,
            )
        };
        let old_is_zero = equality(
            Bitvector32Term::Variable(outer),
            Bitvector32Term::Constant(0),
        );
        let old_equals_other = equality(
            Bitvector32Term::Variable(outer),
            Bitvector32Term::Variable(other),
        );
        let body = equality(
            Bitvector32Term::Variable(other),
            Bitvector32Term::Constant(0),
        );
        let goal = Proposition::ForAll {
            var: outer,
            sort: Sort::CInt32,
            body: Box::new(body),
        };
        let facts = PureFactContext::new()
            .assume_proposition(old_is_zero.clone())
            .assume_proposition(old_equals_other);
        let derivation = facts
            .derive_proposition(&goal)
            .expect("a binder-free body may use the outer variable's facts");
        assert!(derivation.check(&facts));

        let invalid = Proposition::ForAll {
            var: outer,
            sort: Sort::CInt32,
            body: Box::new(old_is_zero),
        };
        assert!(
            facts.derive_proposition(&invalid).is_none(),
            "an outer fact cannot establish a body that uses the new binder"
        );
    }
}

#[cfg(test)]
thread_local! {
    static CONDITION_SELECTION_VISITS: std::cell::Cell<usize> =
        const { std::cell::Cell::new(0) };
}

/// How many condition facts premise selection has examined on this thread
/// since the last reset, counted apart from the kernel's checking work.
#[cfg(test)]
pub(crate) fn condition_selection_visits() -> usize {
    CONDITION_SELECTION_VISITS.with(std::cell::Cell::get)
}

#[cfg(test)]
pub(crate) fn reset_condition_selection_visits() {
    CONDITION_SELECTION_VISITS.with(|visits| visits.set(0));
}

/// Follow the variable/fact graph through the context's adjacency indexes.
/// Scalar facts are indexed incrementally; snapshot-dependent facts use a
/// complete, lazy index. Each reachable variable and fact is expanded once.
#[cfg(test)]
fn connected_condition_premises(
    context: &PureFactContext,
    proposition: &Proposition,
    exclude_exact_goal: bool,
) -> Option<Vec<(ConditionTerm, bool)>> {
    let _timing =
        crate::instrumentation::OperationTiming::new("", "", "condition premise selection");
    let mut reached = BTreeSet::new();
    collect_proposition_bitvector_variables(proposition, &mut reached);
    let mut frontier = reached.iter().copied().collect::<Vec<_>>();
    let mut selected = BTreeMap::new();
    while let Some(variable) = frontier.pop() {
        if simp_reasoning_interrupted() {
            return None;
        }
        // The cooperative checkpoint charges this variable visit.
        for (condition, value) in context.condition_facts_mentioning_variable(variable)? {
            #[cfg(test)]
            CONDITION_SELECTION_VISITS.with(|visits| visits.set(visits.get() + 1));
            if simp_reasoning_interrupted() {
                return None;
            }
            // The checkpoint likewise charges each adjacency visit.
            let exact_goal_fact = matches!(
                proposition,
                Proposition::ConditionIs(goal, expected)
                    if goal == condition && *expected == value
            );
            if exclude_exact_goal && exact_goal_fact || selected.contains_key(condition) {
                continue;
            }
            let mut variables = BTreeSet::new();
            collect_condition_bitvector_variables(condition, &mut variables);
            for next in variables {
                crate::instrumentation::record_deterministic_work(1);
                if reached.insert(next) {
                    frontier.push(next);
                }
            }
            selected.insert(condition.clone(), value);
        }
    }
    if !exclude_exact_goal
        && let Proposition::ConditionIs(condition, value) = proposition
        && context.contains_assumed_exact(proposition)
    {
        selected.insert(condition.clone(), *value);
    }
    Some(selected.into_iter().collect())
}

#[cfg(test)]
mod condition_premise_tests {
    use super::*;

    #[test]
    fn indexed_constant_selection_checks_only_its_cited_premises() {
        let equal = |left, right| {
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
                true,
            )
        };
        let constant = Bitvector32Term::Constant(7);
        let left = equal(term(1), constant.clone());
        let right = equal(constant, term(2));
        let goal = equal(term(1), term(2));
        let mut context = PureFactContext::new()
            .assume_proposition(left.clone())
            .assume_proposition(right.clone());
        for index in 8..136 {
            context = context.assume_proposition(Proposition::Not(Box::new(equal(
                term(1),
                Bitvector32Term::Constant(index),
            ))));
        }
        reset_condition_selection_visits();
        let proof = context.derive_atomic_proposition(&goal).unwrap();
        assert!(proof.check(&context));
        assert_eq!(condition_selection_visits(), 0);
        assert_eq!(
            proof
                .context_premises()
                .into_iter()
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([left.clone(), right.clone()])
        );
        for premise in [left.clone(), right] {
            assert!(!proof.check(&context.without_exact_fact(&premise)));
        }
        assert!(
            context
                .derive_atomic_proposition(&equal(term(1), Bitvector32Term::Constant(8)))
                .is_none()
        );
        let exact_constant_only = PureFactContext::new().assume_proposition(left.clone());
        assert!(
            exact_constant_only
                .derive_simp_proposition_without_exact_goal(&left)
                .is_none()
        );
        let exact_only = PureFactContext::new().assume_proposition(goal.clone());
        assert!(
            exact_only
                .derive_simp_proposition_without_exact_goal(&goal)
                .is_none()
        );
    }

    fn term(index: u64) -> Bitvector32Term {
        Bitvector32Term::Variable(Variable(index))
    }

    fn order(left: u64, right: u64) -> ConditionTerm {
        ConditionTerm::Bitvector32SignedLessThan(Box::new(term(left)), Box::new(term(right)))
    }

    fn chain_fact(index: u64) -> ConditionTerm {
        if index == 1 {
            ConditionTerm::Bitvector32SignedLessThan(
                Box::new(term(1)),
                Box::new(Bitvector32Term::Constant(1000)),
            )
        } else {
            order(index, index - 1)
        }
    }

    fn chain(size: usize, unrelated: usize) -> (PureFactContext, Proposition) {
        let mut context = PureFactContext::new();
        // The goal mentions only the highest variable. In ascending fact
        // order each full scan discovers just one new descending chain link.
        for index in (1..=size as u64).rev() {
            context = context.assume_condition(chain_fact(index), true);
        }
        for index in 0..unrelated as u64 {
            context = context.assume_condition(order(10_000 + index * 2, 10_001 + index * 2), true);
        }
        let goal = ConditionTerm::Bitvector32SignedLessThan(
            Box::new(term(size as u64)),
            Box::new(Bitvector32Term::Constant(1000)),
        );
        (context, Proposition::ConditionIs(goal, true))
    }

    // Keep the former planner as a test oracle, counting whole-context
    // visits separately so its quadratic curve cannot hide in kernel work.
    fn scanned_component(
        context: &PureFactContext,
        goal: &Proposition,
    ) -> (Vec<(ConditionTerm, bool)>, usize) {
        let mut connected = BTreeSet::new();
        collect_proposition_bitvector_variables(goal, &mut connected);
        let mut selected = BTreeMap::new();
        let mut visits = 0;
        loop {
            let mut changed = false;
            for (condition, value) in context.condition_fact_pairs() {
                visits += 1;
                if selected.contains_key(condition) {
                    continue;
                }
                let mut variables = BTreeSet::new();
                collect_condition_bitvector_variables(condition, &mut variables);
                if !variables.is_disjoint(&connected) {
                    connected.extend(variables);
                    selected.insert(condition.clone(), value);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        (selected.into_iter().collect(), visits)
    }

    #[test]
    fn indexed_component_preserves_scan_answers_and_removes_its_quadratic_work() {
        let mut visits = Vec::new();
        for size in [8, 16, 32, 64] {
            let (context, goal) = chain(size, size * 4);
            let (scanned, count) = scanned_component(&context, &goal);
            assert_eq!(
                connected_condition_premises(&context, &goal, false).unwrap(),
                scanned
            );
            visits.push(count);
        }
        assert!(
            visits.windows(2).all(|pair| pair[1] > pair[0] * 3),
            "old scan must reproduce superlinear work: {visits:?}"
        );
        eprintln!("former whole-context visits: {visits:?}");
    }

    #[test]
    fn condition_component_keeps_load_address_and_snapshot_variables() {
        let pointer = Pointer {
            block: "cell".into(),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(term(40)),
                byte_width: 4,
            },
        };
        let memory = CMemory::new().with_block("cell", 64).store(
            Pointer {
                block: "cell".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            CValue::Int32(term(70)),
        );
        let load = Bitvector32Term::MemoryLoad(
            intern_c_memory(memory),
            Box::new(pointer),
            LoadKind::Bits32,
        );
        let fact = ConditionTerm::Bitvector32Equal(Box::new(load.clone()), Box::new(term(50)));
        let context = PureFactContext::new()
            .assume_condition(fact.clone(), true)
            .assume_condition(order(40, 41), true)
            .assume_condition(order(70, 71), true)
            .assume_condition(order(90, 91), true);
        let goal = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(Box::new(load), Box::new(term(60))),
            true,
        );
        let selected = connected_condition_premises(&context, &goal, false).unwrap();
        assert_eq!(selected, scanned_component(&context, &goal).0);
        assert_eq!(selected.len(), 3);
    }

    #[test]
    fn wide_condition_index_construction_charges_its_variable_entries() {
        let mut samples = Vec::new();
        for size in [4, 8, 16, 32] {
            let mut terms = (0..size)
                .map(|index| term(40_000 + (size * 100 + index) as u64))
                .collect::<Vec<_>>();
            while terms.len() > 1 {
                terms = terms
                    .chunks(2)
                    .map(|pair| {
                        if pair.len() == 1 {
                            pair[0].clone()
                        } else {
                            Bitvector32Term::Add(
                                Box::new(pair[0].clone()),
                                Box::new(pair[1].clone()),
                            )
                        }
                    })
                    .collect();
            }
            let condition = ConditionTerm::Bitvector32Equal(
                Box::new(terms.pop().unwrap()),
                Box::new(Bitvector32Term::Constant(0)),
            );
            let ((context, work), events) = crate::instrumentation::collect(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    PureFactContext::new().assume_condition(condition, true)
                })
            });
            assert_eq!(context.condition_fact_pairs().count(), 1);
            let index_work = events
                .into_iter()
                .filter_map(|event| {
                    if let crate::instrumentation::VerificationEvent::OperationFinished {
                        name,
                        work,
                        ..
                    } = event
                    {
                        (name == "condition variable indexing").then_some(work)
                    } else {
                        None
                    }
                })
                .sum::<usize>();
            // The existing context-entry charge covers the first variable.
            assert_eq!(index_work, size - 1);
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|pair| pair[1] <= pair[0] * 3),
            "{samples:?}"
        );
    }

    #[test]
    fn snapshot_condition_index_builds_once_and_survives_scalar_updates() {
        let mut cold_samples = Vec::new();
        let mut warm_samples = Vec::new();
        for size in [8, 16, 32, 64] {
            let (mut context, goal) = chain(8, 0);
            let memory = intern_c_memory(CMemory::new().with_block("other", size as u32 * 4));
            let mut snapshot_facts = Vec::new();
            for index in 0..size {
                let condition = ConditionTerm::Bitvector32Equal(
                    Box::new(term(20_000 + index as u64)),
                    Box::new(Bitvector32Term::MemoryLoad(
                        memory.clone(),
                        Box::new(Pointer {
                            block: "other".into(),
                            offset: PointerOffsetTerm::Constant(index as i64 * 4),
                        }),
                        crate::kernel::LoadKind::Bits32,
                    )),
                );
                context = context.assume_condition(condition.clone(), true);
                snapshot_facts.push(Proposition::ConditionIs(condition, true));
            }
            let (selected, cold) = crate::instrumentation::measure_deterministic_work(|| {
                connected_condition_premises(&context, &goal, false).unwrap()
            });
            assert_eq!(selected.len(), 8);
            let (_, warm) = crate::instrumentation::measure_deterministic_work(|| {
                connected_condition_premises(&context, &goal, false).unwrap()
            });
            assert!(
                cold >= warm + size,
                "snapshot construction must be charged: {cold}, {warm}"
            );
            cold_samples.push(cold);
            warm_samples.push(warm);
            let scalar_branch = context
                .clone()
                .assume_condition(order(30_000, 30_001), true);
            let (_, branch_work) = crate::instrumentation::measure_deterministic_work(|| {
                connected_condition_premises(&scalar_branch, &goal, false).unwrap()
            });
            assert_eq!(
                branch_work, warm,
                "scalar insertion must share the completed snapshot index"
            );
            let withdrawn = context.without_exact_fact(&snapshot_facts[0]);
            let (selected, rebuilt) = crate::instrumentation::measure_deterministic_work(|| {
                connected_condition_premises(&withdrawn, &goal, false).unwrap()
            });
            assert_eq!(selected, scanned_component(&withdrawn, &goal).0);
            assert!(
                rebuilt > warm && rebuilt <= warm + 8,
                "snapshot withdrawal must apply only its delta: {rebuilt}, {warm}"
            );
            let extra = ConditionTerm::Bitvector32Equal(
                Box::new(term(90_000)),
                Box::new(Bitvector32Term::MemoryLoad(
                    memory.clone(),
                    Box::new(Pointer {
                        block: "other".into(),
                        offset: PointerOffsetTerm::Constant(0),
                    }),
                    crate::kernel::LoadKind::Bits32,
                )),
            );
            let extended = scalar_branch.assume_condition(extra, true);
            let (selected, extended_work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    connected_condition_premises(&extended, &goal, false).unwrap()
                });
            assert_eq!(selected.len(), 8);
            assert!(
                extended_work > warm && extended_work <= warm + 8,
                "snapshot insertion must apply only its delta: {extended_work}, {warm}"
            );
            eprintln!("snapshot bucket {size}: cold {cold}, warm {warm}");
        }
        assert!(
            warm_samples.iter().all(|work| *work == warm_samples[0]),
            "{warm_samples:?}"
        );
        assert!(
            cold_samples.windows(2).all(|pair| pair[1] <= pair[0] * 3),
            "{cold_samples:?}"
        );
    }

    #[test]
    fn connected_condition_selection_scales_linearly_in_chain_and_context() {
        for grow_chain in [false, true] {
            let mut samples = Vec::new();
            let mut complete = Vec::new();
            for size in [8, 16, 32, 64] {
                let length = if grow_chain { size } else { 8 };
                let (context, goal) = chain(length, size * 4);
                let (selected, work) = crate::instrumentation::measure_deterministic_work(|| {
                    connected_condition_premises(&context, &goal, false).unwrap()
                });
                assert_eq!(selected.len(), length);
                assert!(
                    work >= length && work <= 16 * (length + size * 4),
                    "{length}: {work}"
                );
                samples.push(work);
                let (proof, total) = crate::instrumentation::measure_deterministic_work(|| {
                    context
                        .derive_atomic_proposition(&goal)
                        .expect("connected order chain proves goal")
                });
                complete.push(total);
                assert!(proof.check(&context));
                assert_eq!(proof.context_premises().len(), length);
                eprintln!(
                    "chain {length}, unrelated {}: selection {work}, complete {total}",
                    size * 4
                );
                // Every link is necessary, and withdrawing it must also
                // change the selected component and invalidate the certificate.
                for index in 1..=length as u64 {
                    let weakened = context
                        .without_exact_fact(&Proposition::ConditionIs(chain_fact(index), true));
                    assert!(!proof.check(&weakened));
                }
                let broken = context.without_exact_fact(&Proposition::ConditionIs(
                    chain_fact(length as u64 / 2),
                    true,
                ));
                assert!(broken.derive_atomic_proposition(&goal).is_none());
            }
            if !grow_chain {
                assert!(
                    samples.iter().all(|work| *work == samples[0]),
                    "{samples:?}"
                );
                assert!(
                    complete.iter().all(|work| *work == complete[0]),
                    "{complete:?}"
                );
            }
            for curve in [&samples, &complete] {
                for pair in curve.windows(2) {
                    assert!(pair[1] <= pair[0] * 3, "{curve:?}");
                }
            }
        }
    }

    #[test]
    fn condition_selection_tracks_restriction_replacement_and_exclusion() {
        let (context, goal) = chain(8, 20);
        let selected = connected_condition_premises(&context, &goal, false).unwrap();
        let restricted = context.restricted_to_facts(&selected, &[]);
        assert_eq!(
            connected_condition_premises(&restricted, &goal, false).unwrap(),
            selected
        );
        let condition = chain_fact(1);
        let replaced = context.clone().assume_condition(condition.clone(), false);
        assert!(
            connected_condition_premises(&replaced, &goal, false)
                .unwrap()
                .contains(&(condition, false))
        );
        let stated = context.assume_proposition(goal.clone());
        assert_eq!(
            connected_condition_premises(&stated, &goal, true).unwrap(),
            selected
        );
        let constant = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
        let context = PureFactContext::new().assume_proposition(constant.clone());
        assert_eq!(
            connected_condition_premises(&context, &constant, false)
                .unwrap()
                .len(),
            1
        );
    }
}

#[cfg(test)]
thread_local! {
    static CANDIDATE_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Counts one proposition fact examined as a possible source for an atomic
/// memory or resource goal, apart from the kernel's checking work.
fn record_candidate_visit() {
    let _timing =
        crate::instrumentation::OperationTiming::new("", "", "proposition candidate selection");
    crate::instrumentation::record_deterministic_work(1);
    #[cfg(test)]
    CANDIDATE_VISITS.with(|visits| visits.set(visits.get() + 1));
}

#[cfg(test)]
pub(crate) fn candidate_visits() -> usize {
    CANDIDATE_VISITS.with(std::cell::Cell::get)
}

#[cfg(test)]
pub(crate) fn reset_candidate_visits() {
    CANDIDATE_VISITS.with(|visits| visits.set(0));
}

type AtomicPremiseSelection = (
    Vec<(ConditionTerm, bool)>,
    Vec<Proposition>,
    BTreeSet<AtomicConnectionKey>,
    bool,
);

/// The equality facts connected to `goal` through shared atoms, condition
/// equalities and algebraic `==` facts alike. `auto` offers them to its
/// rewrite chain.
pub(crate) fn solver_connected_equalities(
    context: &PureFactContext,
    goal: &Proposition,
) -> Option<Vec<Proposition>> {
    let (conditions, propositions, _, _) =
        connected_atomic_premises(context, goal, &[], true, true, true)?;
    let mut equalities = Vec::new();
    for (condition, value) in conditions {
        let fact = Proposition::ConditionIs(condition, value);
        if matches!(
            fact,
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(..)
                    | ConditionTerm::Bitvector64Equal(..)
                    | ConditionTerm::PointerEqual(..)
                    | ConditionTerm::PointerOffsetEqual(..)
                    | ConditionTerm::IntegerEqual(..)
                    | ConditionTerm::AlgebraicEqual(..),
                true
            )
        ) {
            equalities.push(fact);
        }
    }
    equalities.extend(
        propositions
            .into_iter()
            .filter(|fact| matches!(fact, Proposition::Equal(..))),
    );
    Some(equalities)
}

/// Walk syntax adjacency, never rebuilding an index of the ambient context.
/// A wider smart fallback follows recent havoc bounds and general facts;
/// its result still has to pass the restricted kernel query.
/// The condition facts connected to `goal` through shared atoms, the same
/// component `simp` selects. The solver behind `auto` reads its premises
/// from this component; it never scans facts unconnected to the goal.
pub(crate) fn solver_connected_premises(
    context: &PureFactContext,
    goal: &Proposition,
) -> Option<Vec<Proposition>> {
    let (conditions, _, _, _) = connected_atomic_premises(context, goal, &[], false, true, true)?;
    Some(
        conditions
            .into_iter()
            .map(|(condition, value)| Proposition::ConditionIs(condition, value))
            .collect(),
    )
}

fn connected_atomic_premises(
    context: &PureFactContext,
    goal: &Proposition,
    sources: &[Proposition],
    include_propositions: bool,
    widened: bool,
    exclude_exact_goal: bool,
) -> Option<AtomicPremiseSelection> {
    let _timing =
        crate::instrumentation::OperationTiming::new("", "", "atomic dependency selection");
    let mut selected = BTreeSet::new();
    let mut visited = BTreeSet::new();
    let mut reached = collect_atomic_connection_keys(goal);
    let mut select = |fact: &Proposition| {
        visited.insert((1, fact as *const Proposition as usize));
        reached.extend(collect_atomic_connection_keys(fact));
        selected.insert(fact.clone());
    };
    for source in sources {
        select(source);
    }
    if widened {
        for fact in context.atomic_general_facts() {
            if simp_reasoning_interrupted() {
                return None;
            }
            if (!exclude_exact_goal || fact != goal)
                && (include_propositions || matches!(fact, Proposition::ConditionIs(..)))
            {
                select(fact);
            }
        }
    }
    if widened {
        let mut frame_variables = BTreeSet::new();
        collect_proposition_frame_variables(goal, &mut frame_variables);
        reached.extend(
            frame_variables
                .into_iter()
                .map(AtomicConnectionKey::Variable),
        );
    }
    let mut joint_adds = false;
    let mut pending = reached.iter().cloned().collect::<Vec<_>>();
    while let Some(key) = pending.pop() {
        if simp_reasoning_interrupted() {
            return None;
        }
        let (facts, has_propositions) =
            context.atomic_facts_connected_to(&key, include_propositions);
        joint_adds |= has_propositions;
        for fact in facts {
            #[cfg(test)]
            if fact.is_condition() {
                CONDITION_SELECTION_VISITS.with(|visits| visits.set(visits.get() + 1));
            }
            if simp_reasoning_interrupted() {
                return None;
            }
            if !visited.insert(fact.identity())
                || (exclude_exact_goal && fact.matches(goal))
                || (!include_propositions && !fact.is_condition())
            {
                continue;
            }
            let fact = fact.to_proposition();
            if selected.contains(&fact) {
                continue;
            }
            for next in collect_atomic_connection_keys(&fact) {
                crate::instrumentation::record_deterministic_work(1);
                if reached.insert(next.clone()) {
                    pending.push(next);
                }
            }
            selected.insert(fact);
        }
    }
    let mut conditions = Vec::new();
    let mut propositions = Vec::new();
    for fact in selected {
        match fact {
            Proposition::ConditionIs(condition, value) => conditions.push((condition, value)),
            other => propositions.push(other),
        }
    }
    Some((conditions, propositions, reached, joint_adds))
}

/// A completed component already contains every dependency of its seeds.
/// Avoid walking it a second time if widening introduces no new seeds.
fn atomic_widening_adds_dependencies(
    context: &PureFactContext,
    goal: &Proposition,
    selected: &PureFactContext,
    reached: &BTreeSet<AtomicConnectionKey>,
) -> bool {
    for fact in context.atomic_general_facts() {
        if simp_reasoning_interrupted() || !selected.contains_assumed_exact(fact) {
            return true;
        }
    }
    let mut frame_variables = BTreeSet::new();
    collect_proposition_frame_variables(goal, &mut frame_variables);
    frame_variables.into_iter().any(|variable| {
        crate::instrumentation::record_deterministic_work(1);
        !reached.contains(&AtomicConnectionKey::Variable(variable))
    })
}

/// Retain typing support only when its defining equation is selected.
fn atomic_context_from_facts(
    available: &PureFactContext,
    conditions: &[(ConditionTerm, bool)],
    propositions: &[Proposition],
) -> PureFactContext {
    // Selections consist of distinct facts drawn from `available`. When
    // every fact was selected, preserve the persistent context and its
    // derived reasoning indexes rather than rebuilding equivalent state.
    if available.fact_counts() == (conditions.len(), propositions.len()) {
        available.clone()
    } else {
        available.restricted_to_facts(conditions, propositions)
    }
}

#[cfg(test)]
mod shared_atomic_premise_tests {
    use super::*;

    #[test]
    fn wide_atomic_premise_cloning_scales_with_its_syntax() {
        let mut samples = Vec::new();
        for size in [8u64, 16, 32, 64] {
            let predicate = |index| Proposition::Predicate {
                name: "wide-index".to_string(),
                arguments: vec![Term::Bitvector32(Bitvector32Term::Variable(Variable(
                    800_000 + index,
                )))],
            };
            let mut body = predicate(0);
            for index in 1..size {
                body = Proposition::And(Box::new(body), Box::new(predicate(index)));
            }
            let source = Proposition::ForAll {
                var: Variable(900_000),
                sort: Sort::CInt32,
                body: Box::new(body),
            };
            let (context, clones) = crate::kernel::count_proposition_clone_nodes(|| {
                let context = PureFactContext::new().assume_proposition(source.clone());
                let (_, selected, _, _) =
                    connected_atomic_premises(&context, &predicate(0), &[], true, false, false)
                        .expect("all variable buckets must lead to the same wide premise");
                assert_eq!(selected, vec![source.clone()]);
                let proof = context
                    .derive_atomic_proposition(&source)
                    .expect("the stated premise is available");
                assert!(proof.check(&context));
                assert!(!proof.check(&context.without_exact_fact(&source)));
                context
            });
            assert!(context.proves_exact(&source));
            samples.push((size, clones));
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1].1 <= pair[0].1 * 3,
                "deep premise cloning became superlinear: {samples:?}"
            );
        }
    }
}
