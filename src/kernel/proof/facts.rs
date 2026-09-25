//! Persistent semantic fact state for checked proofs.

use super::fact_keys::{IntegerConditionAlphaKey, integer_condition_alpha_key};
use super::fact_reasoning::*;
use super::{
    PersistentSequence, QuantifiedEquivalenceKey, SnapshotBlindPropositionKey,
    quantified_equivalence_index_key, snapshot_blind_proposition_key,
};
use crate::kernel::*;
use crate::persistent::{PersistentMap, PersistentSet};
use std::collections::{BTreeSet, HashMap};
use std::hash::{Hash, Hasher};
use std::sync::Arc;

#[cfg(test)]
thread_local! {
    static INDEXED_FACT_ENTRIES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static MATERIALIZED_FACT_ENTRIES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn take_fact_entry_counts() -> (usize, usize) {
    (
        INDEXED_FACT_ENTRIES.with(|count| count.replace(0)),
        MATERIALIZED_FACT_ENTRIES.with(|count| count.replace(0)),
    )
}

/// Persistent semantic fact state shared by every checked proof kind.
///
/// The exact index serves local proof-step queries and `assumptions` retains
/// the kernel's incrementally updated reasoning context. Forking shares both;
/// adding one fact copies only logarithmic index/context paths.
#[derive(Clone, Default)]
pub(crate) struct ProofFacts {
    ordered: PersistentSequence<Proposition>,
    reserved_variables: PersistentSet<Variable>,
    prioritized: Option<Arc<PrioritizedProofFacts>>,
    top_level_exact: PersistentSet<Proposition>,
    exact: PersistentSet<Proposition>,
    /// Every strict subtree of an available top-level conjunction. This is
    /// the exact structural authority for `extract`; top-level facts are not
    /// included merely because they are independently available.
    proper_conjuncts: PersistentSet<Proposition>,
    /// Atomic exact facts after the same direct-load normalization used by
    /// condition check. This lets a branch reject its opposite path with an
    /// indexed lookup instead of scanning every unrelated fact.
    by_snapshot_blind: PersistentMap<SnapshotBlindPropositionKey, PersistentSequence<Proposition>>,
    /// True Integer comparison facts keyed by the typed alpha form of both
    /// operands. This is the bounded equivalence boundary for checked
    /// restatements whose range-fold binders were freshly allocated.
    /// The map key is a compact fingerprint; each bucket retains one exact
    /// alpha key and source proposition per fingerprint collision.
    by_integer_condition_alpha:
        PersistentMap<u64, PersistentSequence<IntegerConditionAlphaCandidate>>,
    /// Exact true int32 equalities keyed by constant, variable, opaque Click
    /// application, or interned memory-load operands. Keys have bounded
    /// comparison cost; a goal-local rewrite search walks only atoms named by
    /// the goal and their buckets.
    bitvector_equalities_by_atom:
        PersistentMap<BitvectorEqualityAtomKey, PersistentSequence<Arc<Proposition>>>,
    /// Implications whose antecedent is only a C definedness guard (the
    /// no-overflow conditions a lowered `old(x) + result` carries) and whose
    /// consequent is an int32 or int64 equality, keyed by the consequent's
    /// atomic operands. A goal-local smart closer selects the guarded
    /// equalities that could rewrite the goal from these buckets alone.
    guarded_equalities_by_atom:
        PersistentMap<BitvectorEqualityAtomKey, PersistentSequence<Arc<Proposition>>>,
    /// True finite-float classifications retain their shared fact identity so
    /// a reflexive comparison does not publish the same premise twice.
    finite_classifications_by_key:
        PersistentMap<SnapshotBlindPropositionKey, PersistentSequence<Arc<Proposition>>>,
    /// Exact algebraic equalities keyed by their root terms.  Goal-local
    /// constructor disequality rewrites need the variable-to-constructor
    /// premise without scanning unrelated proposition facts.
    algebraic_equalities_by_term: PersistentMap<AlgebraicTerm, PersistentSequence<Proposition>>,
    by_quantified_equivalence:
        PersistentMap<QuantifiedEquivalenceKey, PersistentSequence<Proposition>>,
    /// Selected load identities checked while presenting a rewritten goal.
    rewritten_load_evidence: PersistentSequence<CheckedLoadEquality>,
    /// Universal facts introduced specifically by a checked predicate unfold.
    /// Outcome smart search never probes ambient theorem or path universals.
    predicate_unfolded_universal_facts: PersistentSequence<Proposition>,
    implications_by_consequent:
        PersistentMap<SnapshotBlindPropositionKey, PersistentSequence<ImplicationCandidate>>,
    /// Alpha-invariant selection for quantified implication consequents.
    /// Checked equivalence still guards snapshot and free-variable identity.
    implications_by_quantified_consequent:
        PersistentMap<QuantifiedEquivalenceKey, PersistentSequence<ImplicationCandidate>>,
    assumptions: PureFactContext,
    implicit_transport_assumptions: PureFactContext,
    by_predicate: PersistentMap<String, PersistentSequence<Proposition>>,
}

/// A statement transition places its explicitly transported successor facts
/// before the ambient facts retained at their original snapshots. Prefix
/// batches preserve that semantic order without copying the ambient sequence.
struct PrioritizedProofFacts {
    parent: Option<Arc<PrioritizedProofFacts>>,
    facts: Arc<Vec<Proposition>>,
}

/// One indexed prefix of an available implication chain. The consequent key
/// selects this small candidate; checking still validates every antecedent
/// and the exact or alpha-equivalent quantified consequent.
#[derive(Clone)]
struct ImplicationCandidate {
    antecedents: PersistentSequence<Proposition>,
    consequent: Proposition,
}

#[derive(Clone)]
struct IntegerConditionAlphaCandidate {
    key: IntegerConditionAlphaKey,
    proposition: Proposition,
}

/// A bounded-comparison selector for equality rewrite provenance. Complex
/// arithmetic operands remain on the kernel-derivation path; this index covers
/// the atomic value/snapshot operands that outcome arithmetic rewrites need.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum BitvectorEqualityAtomKey {
    Constant(u32),
    Variable(Variable),
    ClickFunctionApplication {
        name: String,
        arguments_hash: u64,
    },
    MemoryLoad {
        memory: (u32, u32),
        pointer_hash: u64,
    },
}

/// Borrowed access to proposition premises. Persistent proofs supply their
/// existing indexes; source/setup slices retain their ordered boundary view.
/// This interface owns neither proof state nor completion evidence.
pub(crate) trait PropositionSource {
    fn propositions(&self) -> impl Iterator<Item = &Proposition>;
    fn pure_context(&self) -> PureFactContext {
        self.propositions()
            .map(crate::kernel::clone_proposition_iteratively)
            .fold(PureFactContext::new(), PureFactContext::assume_proposition)
    }
    fn exact_available(&self, required: &Proposition) -> bool {
        self.propositions()
            .any(|fact| exact_fact_contains_conjunct(fact, required))
    }
}
impl PropositionSource for [Proposition] {
    fn propositions(&self) -> impl Iterator<Item = &Proposition> {
        self.iter()
    }
}
impl PropositionSource for Vec<Proposition> {
    fn propositions(&self) -> impl Iterator<Item = &Proposition> {
        self.iter()
    }
}
impl<const N: usize> PropositionSource for [Proposition; N] {
    fn propositions(&self) -> impl Iterator<Item = &Proposition> {
        self.iter()
    }
}
impl PropositionSource for ProofFacts {
    fn propositions(&self) -> impl Iterator<Item = &Proposition> {
        let mut seen = BTreeSet::new();
        std::iter::successors(self.prioritized.as_deref(), |batch| batch.parent.as_deref())
            .flat_map(|batch| batch.facts.iter())
            .chain(self.ordered.iter())
            .filter(move |fact| seen.insert(*fact))
    }
    fn pure_context(&self) -> PureFactContext {
        self.assumptions().clone()
    }
    fn exact_available(&self, required: &Proposition) -> bool {
        self.contains(required)
    }
}

impl ProofFacts {
    /// Bounded newest-first view for diagnostics. This deliberately exposes
    /// references into the persistent sequence and never materializes the
    /// ambient proof history.
    pub(crate) fn recent_facts(&self, limit: usize) -> Vec<&Proposition> {
        self.ordered.recent(limit)
    }

    pub(crate) fn fact_count(&self) -> usize {
        self.ordered.len()
    }

    /// Check only corresponding leaves of two presentations of one goal.
    /// No ambient fact search or pairwise load census is performed.
    pub(crate) fn with_checked_rewritten_loads(
        &self,
        original: &Proposition,
        presented: &Proposition,
    ) -> Option<Self> {
        let capture = CheckedLoadEqualityCapture::start_with_call_events(
            &super::CheckedCallEvents::default(),
        );
        let mut pending = vec![(original, presented)];
        let mut equalities = Vec::new();
        let mut bound_variables = BTreeSet::new();
        while let Some((left, right)) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            match (left, right) {
                (Proposition::And(a, b), Proposition::And(c, d))
                | (Proposition::Or(a, b), Proposition::Or(c, d))
                | (Proposition::Implies(a, b), Proposition::Implies(c, d)) => {
                    pending.push((a, c));
                    pending.push((b, d));
                }
                (Proposition::Not(a), Proposition::Not(b)) => pending.push((a, b)),
                (
                    Proposition::ForAll {
                        var: a,
                        sort: s,
                        body: b,
                    },
                    Proposition::ForAll {
                        var: c,
                        sort: t,
                        body: d,
                    },
                ) if a == c && s == t => {
                    bound_variables.insert(*a);
                    pending.push((b, d));
                }
                (Proposition::ConditionIs(a, p), Proposition::ConditionIs(b, q)) if p == q => {
                    let pairs = match (a, b) {
                        (
                            ConditionTerm::Bitvector32SignedLessEqual(a, b),
                            ConditionTerm::Bitvector32SignedLessEqual(c, d),
                        )
                        | (
                            ConditionTerm::Bitvector32SignedLessThan(a, b),
                            ConditionTerm::Bitvector32SignedLessThan(c, d),
                        )
                        | (
                            ConditionTerm::Bitvector32Equal(a, b),
                            ConditionTerm::Bitvector32Equal(c, d),
                        ) => [(a, c), (b, d)],
                        _ if a == b => continue,
                        _ => return None,
                    };
                    for (a, b) in pairs {
                        if a == b {
                            continue;
                        }
                        // A load atom is independent of a surrounding binder.
                        // Do not use ambient premises to identify a bound
                        // value, or a load with an explicitly bound address.
                        if !bound_variables.is_empty()
                            && [a, b].iter().any(|term| match term.as_ref() {
                                Bitvector32Term::Variable(variable) => {
                                    bound_variables.contains(variable)
                                }
                                Bitvector32Term::Constant(_) => false,
                                _ => true,
                            })
                        {
                            return None;
                        }
                        let selected = Proposition::ConditionIs(
                            ConditionTerm::equal(a.as_ref().clone(), b.as_ref().clone()),
                            true,
                        );
                        if !self
                            .with_selected_load_equality_bridge(&selected)
                            .contains(&selected)
                            && !checked_origin_load_equality(a, b, self.assumptions())
                            && !checked_stored_origin_equality(a, b, self.assumptions())
                        {
                            return None;
                        }
                        equalities.push(Proposition::ConditionIs(
                            ConditionTerm::equal(a.as_ref().clone(), b.as_ref().clone()),
                            true,
                        ));
                    }
                }
                _ if left == right => (),
                _ => return None,
            }
        }
        let evidence = capture.finish();
        let events = super::CheckedCallEvents::default();
        if evidence
            .iter()
            .any(|e| !e.checks_with_call_events(self.assumptions(), &events))
        {
            return None;
        }
        let mut facts = self.clone();
        for equality in equalities {
            facts = facts.with_fact(equality);
        }
        for witness in evidence {
            facts.rewritten_load_evidence.push(witness);
        }
        Some(facts)
    }
    /// Exact premise-store identity, without comparing ambient propositions.
    pub(super) fn shares_premises_with(&self, other: &Self) -> bool {
        self.top_level_exact
            .shares_root_with(&other.top_level_exact)
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.ordered.len() == 0
    }
    pub(crate) fn predicate_unfolded_universal_facts(&self) -> impl Iterator<Item = &Proposition> {
        self.predicate_unfolded_universal_facts.iter()
    }

    pub(crate) fn from_ordered(facts: &[Proposition]) -> Self {
        let mut ordered = PersistentSequence::default();
        let mut reserved_variables = PersistentSet::default();
        let mut top_level_exact = PersistentSet::default();
        let mut exact = PersistentSet::default();
        let mut proper_conjuncts = PersistentSet::default();
        let mut by_snapshot_blind = PersistentMap::default();
        let mut by_integer_condition_alpha = PersistentMap::default();
        let mut bitvector_equalities_by_atom = PersistentMap::default();
        let mut guarded_equalities_by_atom = PersistentMap::default();
        let mut finite_classifications_by_key = PersistentMap::default();
        let mut algebraic_equalities_by_term = PersistentMap::default();
        let mut by_quantified_equivalence = PersistentMap::default();
        let mut implications_by_consequent = PersistentMap::default();
        let mut implications_by_quantified_consequent = PersistentMap::default();
        let mut assumptions = PureFactContext::new();
        let mut implicit_transport_assumptions = PureFactContext::new();
        let mut by_predicate = PersistentMap::default();
        for fact in facts {
            for variable in crate::kernel::proposition_variables(fact) {
                reserved_variables = reserved_variables.with_value(variable);
            }
            if top_level_exact.contains(fact) {
                continue;
            }
            #[cfg(test)]
            INDEXED_FACT_ENTRIES.with(|count| count.set(count.get() + 1));
            ordered.push(crate::kernel::clone_proposition_iteratively(fact));
            top_level_exact =
                top_level_exact.with_value(crate::kernel::clone_proposition_iteratively(fact));
            by_quantified_equivalence = index_quantified_fact(by_quantified_equivalence, fact);
            (
                implications_by_consequent,
                implications_by_quantified_consequent,
            ) = index_implication_consequents(
                implications_by_consequent,
                implications_by_quantified_consequent,
                fact,
            );
            by_predicate = index_predicate_fact(by_predicate, fact);
            if matches!(fact, Proposition::And(_, _)) {
                proper_conjuncts = index_proper_conjuncts(proper_conjuncts, fact);
                let mut conjuncts = Vec::new();
                collect_owned_atomic_conjuncts(fact, &mut conjuncts);
                for conjunct in conjuncts {
                    let conjunct = Arc::new(conjunct);
                    by_snapshot_blind = index_snapshot_fact(by_snapshot_blind, conjunct.as_ref());
                    by_integer_condition_alpha =
                        index_integer_condition_fact(by_integer_condition_alpha, conjunct.as_ref());
                    bitvector_equalities_by_atom =
                        index_bitvector_equality_fact(bitvector_equalities_by_atom, &conjunct);
                    finite_classifications_by_key =
                        index_finite_classification_fact(finite_classifications_by_key, &conjunct);
                    algebraic_equalities_by_term = index_algebraic_equality_fact(
                        algebraic_equalities_by_term,
                        conjunct.as_ref(),
                    );
                    exact = exact.with_value(conjunct.as_ref().clone());
                }
            }
            let fact = Arc::new(crate::kernel::clone_proposition_iteratively(fact));
            guarded_equalities_by_atom =
                index_guarded_equality_fact(guarded_equalities_by_atom, &fact);
            by_snapshot_blind = index_snapshot_fact(by_snapshot_blind, fact.as_ref());
            by_integer_condition_alpha =
                index_integer_condition_fact(by_integer_condition_alpha, fact.as_ref());
            bitvector_equalities_by_atom =
                index_bitvector_equality_fact(bitvector_equalities_by_atom, &fact);
            finite_classifications_by_key =
                index_finite_classification_fact(finite_classifications_by_key, &fact);
            algebraic_equalities_by_term =
                index_algebraic_equality_fact(algebraic_equalities_by_term, fact.as_ref());
            exact = exact.with_value(crate::kernel::clone_proposition_iteratively(fact.as_ref()));
            assumptions = assumptions
                .assume_proposition(crate::kernel::clone_proposition_iteratively(fact.as_ref()));
            implicit_transport_assumptions =
                index_implicit_transport_context(implicit_transport_assumptions, fact.as_ref());
        }
        Self {
            ordered,
            reserved_variables,
            prioritized: None,
            top_level_exact,
            exact,
            proper_conjuncts,
            by_snapshot_blind,
            by_integer_condition_alpha,
            bitvector_equalities_by_atom,
            guarded_equalities_by_atom,
            finite_classifications_by_key,
            algebraic_equalities_by_term,
            by_quantified_equivalence,
            predicate_unfolded_universal_facts: PersistentSequence::default(),
            rewritten_load_evidence: PersistentSequence::default(),
            implications_by_consequent,
            implications_by_quantified_consequent,
            assumptions,
            implicit_transport_assumptions,
            by_predicate,
        }
    }

    pub(crate) fn with_reserved_variables(
        mut self,
        variables: impl IntoIterator<Item = Variable>,
    ) -> Self {
        for variable in variables {
            self.reserved_variables = self.reserved_variables.with_value(variable);
        }
        self
    }

    pub(crate) fn contains(&self, fact: &Proposition) -> bool {
        self.exact.contains(fact)
    }

    pub(crate) fn contains_top_level(&self, fact: &Proposition) -> bool {
        self.top_level_exact.contains(fact)
    }

    /// Appends a proposition after a checked kernel operation has established
    /// it. Surface proof drivers use this named adapter only to carry facts
    /// returned by those operations; it deliberately does not become a
    /// second semantic checker. The raw index mutation below remains scoped
    /// to the kernel so every such publication is visible in the kernel audit.
    pub(crate) fn with_kernel_checked_fact(&self, fact: Proposition) -> Self {
        self.with_fact(fact)
    }

    pub(in crate::kernel) fn with_fact(&self, fact: Proposition) -> Self {
        if self.top_level_exact.contains(&fact) {
            return self.clone();
        }
        #[cfg(test)]
        INDEXED_FACT_ENTRIES.with(|count| count.set(count.get() + 1));
        let mut exact = self.exact.clone();
        let mut proper_conjuncts = self.proper_conjuncts.clone();
        let mut by_snapshot_blind = self.by_snapshot_blind.clone();
        let mut by_integer_condition_alpha = self.by_integer_condition_alpha.clone();
        let mut bitvector_equalities_by_atom = self.bitvector_equalities_by_atom.clone();
        let mut finite_classifications_by_key = self.finite_classifications_by_key.clone();
        let mut algebraic_equalities_by_term = self.algebraic_equalities_by_term.clone();
        let by_quantified_equivalence =
            index_quantified_fact(self.by_quantified_equivalence.clone(), &fact);
        let (implications_by_consequent, implications_by_quantified_consequent) =
            index_implication_consequents(
                self.implications_by_consequent.clone(),
                self.implications_by_quantified_consequent.clone(),
                &fact,
            );
        if matches!(fact, Proposition::And(_, _)) {
            proper_conjuncts = index_proper_conjuncts(proper_conjuncts, &fact);
            let mut conjuncts = Vec::new();
            collect_owned_atomic_conjuncts(&fact, &mut conjuncts);
            for conjunct in conjuncts {
                let conjunct = Arc::new(conjunct);
                by_snapshot_blind = index_snapshot_fact(by_snapshot_blind, conjunct.as_ref());
                by_integer_condition_alpha =
                    index_integer_condition_fact(by_integer_condition_alpha, conjunct.as_ref());
                bitvector_equalities_by_atom =
                    index_bitvector_equality_fact(bitvector_equalities_by_atom, &conjunct);
                finite_classifications_by_key =
                    index_finite_classification_fact(finite_classifications_by_key, &conjunct);
                algebraic_equalities_by_term =
                    index_algebraic_equality_fact(algebraic_equalities_by_term, conjunct.as_ref());
                exact = exact.with_value(conjunct.as_ref().clone());
            }
        }
        let fact = Arc::new(fact);
        let guarded_equalities_by_atom =
            index_guarded_equality_fact(self.guarded_equalities_by_atom.clone(), &fact);
        by_snapshot_blind = index_snapshot_fact(by_snapshot_blind, fact.as_ref());
        by_integer_condition_alpha =
            index_integer_condition_fact(by_integer_condition_alpha, fact.as_ref());
        bitvector_equalities_by_atom =
            index_bitvector_equality_fact(bitvector_equalities_by_atom, &fact);
        finite_classifications_by_key =
            index_finite_classification_fact(finite_classifications_by_key, &fact);
        algebraic_equalities_by_term =
            index_algebraic_equality_fact(algebraic_equalities_by_term, fact.as_ref());
        exact = exact.with_value(fact.as_ref().clone());
        let mut ordered = self.ordered.clone();
        ordered.push(fact.as_ref().clone());
        let implicit_transport_assumptions = index_implicit_transport_context(
            self.implicit_transport_assumptions.clone(),
            fact.as_ref(),
        );
        let mut reserved_variables = self.reserved_variables.clone();
        for variable in crate::kernel::proposition_variables(fact.as_ref()) {
            reserved_variables = reserved_variables.with_value(variable);
        }
        Self {
            ordered,
            reserved_variables,
            prioritized: self.prioritized.clone(),
            top_level_exact: self.top_level_exact.with_value(fact.as_ref().clone()),
            exact,
            proper_conjuncts,
            by_snapshot_blind,
            by_integer_condition_alpha,
            bitvector_equalities_by_atom,
            guarded_equalities_by_atom,
            finite_classifications_by_key,
            algebraic_equalities_by_term,
            by_quantified_equivalence,
            predicate_unfolded_universal_facts: self.predicate_unfolded_universal_facts.clone(),
            rewritten_load_evidence: self.rewritten_load_evidence.clone(),
            implications_by_consequent,
            implications_by_quantified_consequent,
            assumptions: self
                .assumptions
                .clone()
                .assume_proposition(fact.as_ref().clone()),
            implicit_transport_assumptions,
            by_predicate: index_predicate_fact(self.by_predicate.clone(), fact.as_ref()),
        }
    }

    /// A free identity for a universal introduction's witness, from the range
    /// [`ExecutionBudget::UNIVERSAL_WITNESS_VARIABLE_BASE`] reserves for them.
    ///
    /// Scanning up from `Variable(0)` for an identity no *fact* mentions was
    /// the earlier rule, and it is wrong twice over. The facts are not the
    /// whole state a witness has to stay clear of: a C proof also carries
    /// program variables, a symbolic store, a memory snapshot and a resource
    /// context, and `Variable(0)` is a C identity by the reserved-range
    /// registry, so the first candidate that rule tried was a live program
    /// variable of the function being proved. Taking the identity from a range
    /// nothing else mints makes freshness structural: an identity outside the
    /// range belongs to some other producer and is never chosen, and inside it
    /// this picks one strictly above every witness already visible here.
    ///
    /// Work is proportional to the witnesses in scope, not to the fact set:
    /// the reserved set is ordered, so the highest witness is one backward
    /// walk over that range's tail.
    fn fresh_universal_witness(
        &self,
        body_variables: &std::collections::BTreeSet<Variable>,
    ) -> Option<Variable> {
        let base = crate::kernel::ExecutionBudget::UNIVERSAL_WITNESS_VARIABLE_BASE;
        let ceiling = crate::kernel::ExecutionBudget::UNIVERSAL_WITNESS_VARIABLE_CEILING;
        let reserved_high = highest_universal_witness(self.reserved_variables.iter().copied());
        let body_high = highest_universal_witness(body_variables.iter().copied());
        let next = match reserved_high.into_iter().chain(body_high).max() {
            Some(highest) => highest.checked_add(1)?,
            None => base,
        };
        (next < ceiling).then_some(Variable(next))
    }

    pub(crate) fn freshen_int32_forall_body(
        &self,
        binder: Variable,
        body: &Proposition,
    ) -> Option<(Variable, Proposition)> {
        if !self.reserved_variables.contains(&binder) {
            return Some((binder, body.clone()));
        }
        let body_variables = crate::kernel::proposition_variables(body);
        let fresh = self.fresh_universal_witness(&body_variables)?;
        let renamed = crate::kernel::substitute_int32_variable_in_proposition(
            body,
            binder,
            Bitvector32Term::Variable(fresh),
        );
        let renamed =
            restore_range_extent_spelling(body, renamed, binder, &Bitvector32Term::Variable(fresh));
        Some((fresh, renamed))
    }

    pub(crate) fn freshen_integer_forall_body(
        &self,
        binder: Variable,
        body: &Proposition,
    ) -> Option<(Variable, Proposition)> {
        if !self.reserved_variables.contains(&binder) {
            let replacement = crate::kernel::IntegerTerm::var(binder);
            let body = super::super::reasoning::substitute_integer_variable_in_pure_proposition(
                body,
                binder,
                &replacement,
            )
            .ok()?;
            return Some((binder, body));
        }
        let body_variables = crate::kernel::proposition_variables(body);
        let reserved_max = self.reserved_variables.iter().next_back().copied();
        let body_max = body_variables.iter().next_back().copied();
        let max_variable = reserved_max.into_iter().chain(body_max).max();
        let mut fresh = match max_variable {
            Some(variable) => Variable(variable.0.checked_add(1)?),
            None => Variable(0),
        };
        loop {
            if !self.reserved_variables.contains(&fresh) && !body_variables.contains(&fresh) {
                break;
            }
            fresh = Variable(fresh.0.checked_add(1)?);
        }
        let replacement = crate::kernel::IntegerTerm::var(fresh);
        let body = super::super::reasoning::substitute_integer_variable_in_pure_proposition(
            body,
            binder,
            &replacement,
        )
        .ok()?;
        Some((fresh, body))
    }

    pub(crate) fn freshen_algebraic_forall_body(
        &self,
        binder: Variable,
        algebraic_type: &crate::kernel::AlgebraicType,
        body: &Proposition,
    ) -> Option<(Variable, Proposition)> {
        if !self.reserved_variables.contains(&binder) {
            return Some((binder, body.clone()));
        }
        let body_variables = crate::kernel::proposition_variables(body);
        let fresh = self.fresh_universal_witness(&body_variables)?;
        let replacement = crate::kernel::AlgebraicTerm {
            algebraic_type: algebraic_type.clone(),
            node: crate::kernel::AlgebraicTermNode::Variable(fresh),
        };
        let body = crate::kernel::reasoning::substitute_algebraic_variable_in_proposition(
            body,
            binder,
            &replacement,
        );
        Some((fresh, body))
    }

    pub(crate) fn reserves_variable(&self, variable: Variable) -> bool {
        self.reserved_variables.contains(&variable)
    }

    /// Numeric induction enters once per theorem. Check its domain from
    /// exact signed bounds on this measure, without searching other facts
    /// or deriving a replacement proof state.
    pub(crate) fn has_nonnegative_induction_domain(&self, measure: &Bitvector32Term) -> bool {
        self.assumptions.signed_order_bound_entries(measure).any(
            |(endpoint, bound, strict, forward)| {
                if forward || endpoint != *measure {
                    return false;
                }
                let Bitvector32Term::Constant(bits) = bound else {
                    return false;
                };
                let lower = bits as i32;
                lower >= 0 || (strict && lower == -1)
            },
        )
    }

    pub(crate) fn contradicts(&self, fact: &Proposition) -> bool {
        let negated = Proposition::Not(Box::new(fact.clone()));
        // An introduced guard is held conjunct by conjunct, so a
        // contradiction written over the whole guard finds it that way.
        let mut conjuncts = Vec::new();
        super::fact_reasoning::atomic_conjuncts(fact, &mut conjuncts);
        let held = self.contains(fact)
            || (conjuncts.len() > 1 && conjuncts.iter().all(|conjunct| self.contains(conjunct)));
        held && (self.contains(&negated)
            || matches!(fact, Proposition::ConditionIs(condition, value)
                    if self.contains(&Proposition::ConditionIs(condition.clone(), !value)))
            // `i < 0` and `i >= 0` are different conditions, not one
            // condition at both polarities, so the negation is recognized
            // through the same bounded list of equivalent spellings a
            // disjunct arm already uses at `apply_left`/`apply_right`. This
            // is a fixed-size set of exact lookups, not a fact-set search.
            || super::fact_reasoning::condition_polarity_forms(&negated)
                .iter()
                .any(|form| self.contains(form))
            || super::fact_reasoning::normalizes_context_free_leaf(&negated))
    }

    pub(crate) fn freshen_pointer_forall_body(
        &self,
        binder: Variable,
        c_type: CType,
        body: &Proposition,
    ) -> Option<(Variable, Proposition)> {
        if !self.reserved_variables.contains(&binder) {
            return Some((binder, body.clone()));
        }
        let body_variables = crate::kernel::proposition_variables(body);
        let fresh = self.fresh_universal_witness(&body_variables)?;
        let pointer = if matches!(c_type, CType::FunctionPointer(_)) {
            Pointer::symbolic_function(fresh)
        } else {
            Pointer::symbolic(fresh)
        };
        // A pointer binder never occurs in a range's element endpoints, which
        // are `int32` terms, so the extent has nothing to put back here.
        let body =
            crate::kernel::substitute_pointer_variable_in_proposition(body, binder, &pointer);
        Some((fresh, body))
    }

    pub(crate) fn with_predicate_unfold_fact(&self, fact: Proposition) -> Self {
        let is_universal = matches!(fact, Proposition::ForAll { .. });
        let mut successor = self.with_fact(fact.clone());
        if is_universal
            && !successor
                .predicate_unfolded_universal_facts
                .iter()
                .any(|candidate| candidate == &fact)
        {
            successor.predicate_unfolded_universal_facts.push(fact);
        }
        successor
    }

    /// Materializes only the separations selected by this explicit goal.
    /// A conjunction also needs every other leaf (including range bounds) as
    /// an existing fact. No unrelated resource pairs are enumerated.
    pub(crate) fn with_selected_resource_separation(&self, goal: &Proposition) -> Self {
        self.with_selected_separation_facts(goal, false)
    }

    /// As above, but separation must follow from the compositions alone.
    /// Contextual separation facts retain their explicit derivation.
    pub(crate) fn with_selected_composition_separation(&self, goal: &Proposition) -> Self {
        self.with_selected_separation_facts(goal, true)
    }

    fn with_selected_separation_facts(&self, goal: &Proposition, composition_only: bool) -> Self {
        let mut facts = self.clone();
        let mut pending = vec![goal];
        let mut all_available = true;
        while let Some(part) = pending.pop() {
            if let Proposition::And(left, right) = part {
                pending.push(right);
                pending.push(left);
                continue;
            }
            if matches!(part, Proposition::CResourceSeparate { .. }) && !facts.contains(part) {
                let assumptions = if composition_only {
                    facts.assumptions.compositions_only()
                } else {
                    facts.assumptions.clone()
                };
                if assumptions.proves_exact(part)
                    || assumptions.proves_atomic_memory_or_resource(part)
                {
                    facts = facts.with_fact(part.clone());
                }
            }
            all_available &= facts.pure_assumption_available(part);
        }
        // Publish the requested conjunction once. Publishing every nested
        // prefix would repeatedly clone it and take quadratic work.
        if matches!(goal, Proposition::And(_, _)) && all_available && !facts.contains(goal) {
            facts = facts.with_fact(goal.clone());
        }
        facts
    }

    /// Materializes one selected equality across a checked chain of load
    /// variables. This keeps the ordinary `Assumption` checker exact while
    /// allowing a new fixed-state goal to consume equality transport explicitly
    /// carried through the preceding statement. Selection follows only the
    /// goal's indexed equality buckets; unrelated ambient equalities remain
    /// implicit and are never visited.
    pub(crate) fn with_selected_load_equality_bridge(&self, goal: &Proposition) -> Self {
        if self.pure_assumption_available(goal)
            || !matches!(
                goal,
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32Equal(_, _) | ConditionTerm::PointerOffsetEqual(_, _),
                    true
                )
            )
        {
            return self.clone();
        }
        let candidates = self.load_equalities_mentioning(goal);
        if !candidates.is_empty()
            && premise_bridged_by_load_variable_chain_with_origins(
                goal,
                &candidates,
                &self.assumptions,
            )
        {
            self.with_fact(goal.clone())
        } else {
            self.clone()
        }
    }

    pub(crate) fn assumptions(&self) -> &PureFactContext {
        &self.assumptions
    }

    /// Exact proper-conjunct membership with the same condition-polarity
    /// equivalence as the legacy structural checker.
    pub(crate) fn contains_proper_conjunct(&self, required: &Proposition) -> bool {
        self.proper_conjuncts.contains(required)
            || condition_polarity_forms(required)
                .iter()
                .any(|form| self.proper_conjuncts.contains(form))
    }

    /// Exact or direct-load-materialization-equivalent availability used by
    /// the deterministic rewrite rule. Unlike snapshot check, this does not
    /// admit polarity changes or a semantic bridge beyond normalization.
    pub(crate) fn materialization_available(&self, required: &Proposition) -> bool {
        self.exact.contains(required)
    }

    /// Availability of a proposition to the explicit pure `assumption`
    /// judgment used inside fixed-state proofs. This deliberately excludes
    /// cross-effect snapshot transport: such a transport needs its own
    /// retained proof step before a later assumption may consume it.
    pub(crate) fn pure_assumption_available(&self, required: &Proposition) -> bool {
        self.materialization_available(required)
            || self.integer_alpha_fact_available(required)
            || self.quantified_fact_available(required)
    }

    pub(crate) fn implicit_transport_assumptions(&self) -> &PureFactContext {
        &self.implicit_transport_assumptions
    }

    /// Adds one statement's selected successor context while retaining the
    /// old ambient order by shared prefix. The statement delta is explicit,
    /// so insertion work is proportional only to that delta and index height.
    pub(crate) fn with_statement_facts(&self, facts: Vec<Proposition>) -> Self {
        let ordered = self.ordered.clone();
        let parent = self.prioritized.clone();
        let mut successor = self.clone();
        for fact in &facts {
            successor = successor.with_fact(fact.clone());
        }
        successor.ordered = ordered;
        successor.prioritized = Some(Arc::new(PrioritizedProofFacts {
            parent,
            facts: Arc::new(facts),
        }));
        successor
    }

    /// Availability accepted by explicit check, answered from persistent
    /// indexes. Snapshot-blind buckets only select structurally compatible
    /// candidates; the kernel still proves every cross-snapshot match.
    pub(crate) fn available_across_effects(
        &self,
        required: &Proposition,
        framing: &[ExecutionPureFact],
    ) -> bool {
        if self.exact_available_across_effects(required, framing) {
            return true;
        }

        self.quantified_fact_available(required)
    }

    /// Returns one actual available fact accepted by explicit check. Smart
    /// syntax selection needs the retained fact, not merely a yes/no answer:
    /// its recorded surface form may carry a statement snapshot that the
    /// freshly lowered theorem requirement no longer exposes.
    pub(crate) fn matching_fact_across_effects(
        &self,
        required: &Proposition,
        framing: &[ExecutionPureFact],
    ) -> Option<Proposition> {
        let keys = [snapshot_blind_proposition_key(required)];
        let mut indexed_candidates = Vec::new();
        for key in &keys {
            if let Some(bucket) = self.by_snapshot_blind.get(key) {
                for candidate in bucket.iter() {
                    if !indexed_candidates.contains(candidate) {
                        indexed_candidates.push(candidate.clone());
                    }
                }
            }
        }
        // Preserve the legacy selector's canonical materialization choice,
        // but search only the requirement's persistent shape bucket. The
        // chosen sibling snapshot can have a stable recorded `at(...)`
        // form even when the freshly lowered requirement is also present.
        if let Some(candidate) = exactly_available_fact(required, &indexed_candidates) {
            return Some(candidate.clone());
        }
        if self.exact.contains(required) {
            return Some(required.clone());
        }
        if let Some(form) = condition_polarity_forms(required)
            .into_iter()
            .find(|form| self.exact.contains(form))
        {
            return Some(form);
        }

        // A checked Integer comparison may contain range-fold binders freshly
        // allocated by the preceding rewrite. Return the stored proposition
        // so callers retain the source fact and its certificate provenance;
        // do not synthesize the requested presentation here.
        if let Some(candidate) = self.matching_integer_condition_alpha_fact(required) {
            return Some(candidate);
        }

        if let Some(quantified) = self.matching_quantified_fact(required) {
            return Some(quantified);
        }

        let mut candidates = Vec::new();
        for key in keys {
            let Some(bucket) = self.by_snapshot_blind.get(&key) else {
                continue;
            };
            for candidate in bucket.iter() {
                if !candidates.contains(candidate) {
                    candidates.push(candidate.clone());
                }
                if candidate == required
                    || separation_bridged_fact_is_available(
                        required,
                        std::slice::from_ref(candidate),
                        &self.assumptions,
                        framing,
                    )
                {
                    return Some(candidate.clone());
                }
            }
        }
        separation_bridged_fact_is_available(required, &candidates, &self.assumptions, framing)
            .then(|| required.clone())
    }

    pub(crate) fn matching_quantified_fact(&self, required: &Proposition) -> Option<Proposition> {
        self.quantified_matches(required).next().cloned()
    }

    pub(crate) fn matching_quantified_facts(&self, required: &Proposition) -> Vec<Proposition> {
        self.quantified_matches(required).cloned().collect()
    }

    fn quantified_matches<'a>(
        &'a self,
        required: &'a Proposition,
    ) -> impl Iterator<Item = &'a Proposition> {
        quantified_equivalence_index_key(required)
            .and_then(|key| self.by_quantified_equivalence.get(&key))
            .into_iter()
            .flat_map(PersistentSequence::iter)
            .filter(move |candidate| quantified_binder_equivalent(required, candidate))
    }

    pub(crate) fn quantified_fact_available(&self, required: &Proposition) -> bool {
        self.matching_quantified_fact(required).is_some()
    }

    /// Returns a stored true Integer comparison whose typed alpha form matches
    /// `required`. The candidate is selected by the persistent alpha bucket,
    /// so unrelated ambient facts are never scanned.
    fn matching_integer_condition_alpha_fact(&self, required: &Proposition) -> Option<Proposition> {
        let key = integer_condition_alpha_key(required)?;
        let fingerprint = key.checked_fingerprint()?;
        let bucket = self.by_integer_condition_alpha.get(&fingerprint)?;
        for candidate in bucket {
            match candidate.key.checked_eq(&key) {
                Some(true) => return Some(candidate.proposition.clone()),
                Some(false) => {}
                None => return None,
            }
        }
        None
    }

    fn integer_alpha_fact_available(&self, required: &Proposition) -> bool {
        self.matching_integer_condition_alpha_fact(required)
            .is_some()
    }

    pub(crate) fn contains_discharged_implication_consequent(
        &self,
        required: &Proposition,
    ) -> bool {
        let antecedents_available = |candidate: &ImplicationCandidate| {
            candidate
                .antecedents
                .iter()
                .all(|antecedent| self.available_across_effects(antecedent, &[]))
        };
        if self
            .implications_by_consequent
            .get(&snapshot_blind_proposition_key(required))
            .is_some_and(|bucket| {
                bucket.iter().any(|candidate| {
                    &candidate.consequent == required && antecedents_available(candidate)
                })
            })
        {
            return true;
        }
        quantified_equivalence_index_key(required)
            .and_then(|key| self.implications_by_quantified_consequent.get(&key))
            .is_some_and(|bucket| {
                bucket.iter().any(|candidate| {
                    quantified_binder_equivalent(required, &candidate.consequent)
                        && antecedents_available(candidate)
                })
            })
    }

    pub(crate) fn exact_available_across_effects(
        &self,
        required: &Proposition,
        framing: &[ExecutionPureFact],
    ) -> bool {
        if self.contains(required)
            || condition_polarity_forms(required)
                .iter()
                .any(|form| self.exact.contains(form))
        {
            return true;
        }

        if self.integer_alpha_fact_available(required) {
            return true;
        }

        // The snapshot-blind index already bounds candidate selection. Check
        // each candidate in place rather than cloning a deduplicated Vec:
        // duplicate entries can only arise from index aliases, and a bridge
        // succeeds if any one indexed fact supplies it. This keeps the loop
        // lookup output-sized and avoids an uncharged deep Proposition Eq.
        let key = snapshot_blind_proposition_key(required);
        let Some(bucket) = self.by_snapshot_blind.get(&key) else {
            return false;
        };
        bucket.iter().any(|candidate| {
            if crate::instrumentation::deadline_exceeded_with_work(1) {
                return false;
            }
            separation_bridged_fact_is_available(
                required,
                std::slice::from_ref(candidate),
                &self.assumptions,
                framing,
            ) || condition_bridged_fact_is_available(
                required,
                std::slice::from_ref(candidate),
                &self.assumptions,
            )
        })
    }

    pub(crate) fn directly_conflicts_with(&self, fact: &Proposition) -> bool {
        directly_conflicts_with_normalized_index(&self.exact, fact)
    }

    /// Returns exact equality facts attached to terms occurring in this
    /// proposition. Selection cost follows the proposition and the matching
    /// equality buckets; unrelated ambient equalities are never visited.
    pub(crate) fn bitvector_equalities_mentioning(
        &self,
        proposition: &Proposition,
    ) -> Vec<Proposition> {
        self.load_equalities_mentioning(proposition)
            .into_iter()
            .filter(|equality| {
                matches!(
                    equality,
                    Proposition::ConditionIs(
                        ConditionTerm::Bitvector32Equal(_, _)
                            | ConditionTerm::Bitvector64Equal(_, _),
                        true
                    )
                )
            })
            .collect()
    }

    /// Returns the indexed pointer/bitvector relations which share atoms with
    /// a special-arithmetic goal.  This is deliberately narrower than
    /// `to_vec`: unrelated ambient facts are never materialized for smart
    /// certificate planning.
    pub(crate) fn special_candidates_mentioning(
        &self,
        proposition: &Proposition,
    ) -> Vec<Proposition> {
        // A fact can be indexed under both operands of a relation, and the
        // finite classification lookup below can return the same fact again.
        // Keep deduplication logarithmic and deterministic instead of using
        // Vec::contains, whose repeated structural comparisons are quadratic
        // in a matching bucket.
        let mut candidates = Vec::new();
        let mut candidate_ids = BTreeSet::new();
        for candidate in self.indexed_load_equalities_mentioning(proposition) {
            let id = Arc::as_ptr(&candidate) as usize;
            if candidate_ids.insert(id) {
                candidates.push(candidate);
            }
        }
        if let Proposition::ConditionIs(condition, _) = proposition {
            let finite: Vec<_> = match condition {
                ConditionTerm::Float32(CFloatCondition::Comparison { left, right, .. }) => {
                    vec![(32, left), (32, right)]
                }
                ConditionTerm::Float64(CFloatCondition::Comparison { left, right, .. }) => {
                    vec![(64, left), (64, right)]
                }
                _ => Vec::new(),
            };
            for (width, value) in finite {
                let classification = match width {
                    32 => Proposition::ConditionIs(
                        ConditionTerm::Float32(CFloatCondition::Classification {
                            classification: CFloatClassification::Finite,
                            value: value.clone(),
                        }),
                        true,
                    ),
                    64 => Proposition::ConditionIs(
                        ConditionTerm::Float64(CFloatCondition::Classification {
                            classification: CFloatClassification::Finite,
                            value: value.clone(),
                        }),
                        true,
                    ),
                    _ => continue,
                };
                if let Some(candidate) =
                    self.matching_indexed_finite_classification(&classification)
                {
                    // Classification facts are not stored in the bitvector
                    // relation index; the dedicated index preserves their
                    // identity across both operands.
                    let id = Arc::as_ptr(&candidate) as usize;
                    if candidate_ids.insert(id) {
                        candidates.push(candidate);
                    }
                }
            }
        }
        candidates
            .into_iter()
            .map(|candidate| candidate.as_ref().clone())
            .collect()
    }

    /// Returns exact algebraic equalities attached to terms occurring in
    /// this proposition.  The persistent term index keeps constructor
    /// disequality rewrites goal-local; callers never inspect unrelated
    /// proposition facts.
    pub(crate) fn algebraic_equalities_mentioning(
        &self,
        proposition: &Proposition,
    ) -> Vec<Proposition> {
        let mut terms = BTreeSet::new();
        collect_proposition_algebraic_terms(proposition, &mut terms);
        let mut equalities = BTreeSet::new();
        for term in terms {
            if let Some(bucket) = self.algebraic_equalities_by_term.get(&term) {
                equalities.extend(bucket.iter().cloned());
            }
        }
        equalities.into_iter().collect()
    }

    /// Like [`Self::bitvector_equalities_mentioning`], also returning indexed
    /// pointer-offset equalities between scaled offsets, for the pointer side
    /// of the load-variable chain bridge.
    pub(crate) fn load_equalities_mentioning(&self, proposition: &Proposition) -> Vec<Proposition> {
        self.indexed_load_equalities_mentioning(proposition)
            .into_iter()
            .map(|fact| fact.as_ref().clone())
            .collect()
    }

    /// Definedness-guarded equalities (`defined(e) implies a == b`) whose
    /// consequent shares an atomic operand with `proposition`, oldest first
    /// within each atom and deduplicated by identity. The lookup visits only
    /// the buckets of the atoms the proposition names.
    pub(crate) fn guarded_equalities_mentioning(
        &self,
        proposition: &Proposition,
    ) -> Vec<Proposition> {
        let mut atoms = BTreeSet::new();
        collect_proposition_bitvector_atoms(proposition, &mut atoms);
        let mut seen = BTreeSet::new();
        let mut implications = Vec::new();
        for atom in atoms {
            if let Some(bucket) = self.guarded_equalities_by_atom.get(&atom) {
                for implication in bucket.iter() {
                    crate::instrumentation::record_deterministic_work(1);
                    if seen.insert(Arc::as_ptr(implication) as usize) {
                        implications.push(implication.as_ref().clone());
                    }
                }
            }
        }
        implications
    }

    /// The same query retaining the compact identity of each indexed fact.
    /// One fact may occur in both operand buckets; pointer identity removes
    /// that duplicate without recursively comparing proposition payloads.
    fn indexed_load_equalities_mentioning(
        &self,
        proposition: &Proposition,
    ) -> Vec<Arc<Proposition>> {
        let mut atoms = BTreeSet::new();
        collect_proposition_bitvector_atoms(proposition, &mut atoms);
        let mut equalities = Vec::new();
        for atom in atoms {
            if let Some(bucket) = self.bitvector_equalities_by_atom.get(&atom) {
                for equality in bucket.iter() {
                    equalities.push(equality.clone());
                }
            }
        }
        equalities
    }

    fn matching_indexed_finite_classification(
        &self,
        required: &Proposition,
    ) -> Option<Arc<Proposition>> {
        let key = snapshot_blind_proposition_key(required);
        self.finite_classifications_by_key
            .get(&key)
            .and_then(|bucket| {
                bucket
                    .iter()
                    .find(|candidate| self.exact.contains(candidate.as_ref()))
                    .cloned()
            })
    }

    /// The facts this context introduced after `ancestor`, oldest first.
    ///
    /// Both fact stores are parent-linked and append-only, so the delta is
    /// recovered by walking only the appended suffixes — prioritized
    /// statement batches first, then ordinary insertions — and pointer
    /// identity proves the shared history. Returns `None` when `ancestor`
    /// is not this context's ancestor. This is the output-sensitive
    /// introduction delta the execution sibling-split joins consume.
    pub(crate) fn introduced_since(&self, ancestor: &Self) -> Option<Vec<Proposition>> {
        let mut new_batches = Vec::new();
        let mut current = self.prioritized.clone();
        loop {
            match (&current, &ancestor.prioritized) {
                (Some(node), Some(ancestor_head)) if Arc::ptr_eq(node, ancestor_head) => break,
                (None, None) => break,
                (Some(node), _) => {
                    new_batches.push(node.facts.clone());
                    current = node.parent.clone();
                }
                (None, Some(_)) => return None,
            }
        }
        let ordered_suffix = self.ordered.suffix_since(&ancestor.ordered)?;
        let mut introduced = Vec::new();
        for batch in new_batches.iter().rev() {
            introduced.extend(batch.iter().cloned());
        }
        introduced.extend(ordered_suffix);
        Some(introduced)
    }

    pub(crate) fn to_vec(&self) -> Vec<Proposition> {
        let mut ordered = Vec::new();
        let mut seen = BTreeSet::new();
        let mut batch = self.prioritized.as_deref();
        while let Some(current) = batch {
            for fact in current.facts.iter() {
                let owned = crate::kernel::clone_proposition_iteratively(fact);
                if seen.insert(crate::kernel::clone_proposition_iteratively(fact)) {
                    ordered.push(owned);
                }
            }
            batch = current.parent.as_deref();
        }
        for fact in self.ordered.iter() {
            let owned = crate::kernel::clone_proposition_iteratively(fact);
            if seen.insert(crate::kernel::clone_proposition_iteratively(fact)) {
                ordered.push(owned);
            }
        }
        #[cfg(test)]
        MATERIALIZED_FACT_ENTRIES.with(|count| count.set(count.get() + ordered.len()));
        ordered
    }

    pub(crate) fn mentioning_predicate(&self, name: &String) -> impl Iterator<Item = &Proposition> {
        self.by_predicate
            .get(name)
            .into_iter()
            .flat_map(PersistentSequence::iter)
    }

    #[cfg(test)]
    pub(crate) fn lookup_comparisons(&self, fact: &Proposition) -> usize {
        self.exact.lookup_comparisons(fact)
    }

    #[cfg(test)]
    pub(crate) fn equality_atom_lookup_comparisons(&self, term: &Bitvector32Term) -> usize {
        let key = bitvector_equality_atom_key(term).expect("test term should be an indexed atom");
        self.bitvector_equalities_by_atom.lookup_comparisons(&key)
    }

    #[cfg(test)]
    pub(crate) fn shares_exact_index_with(&self, other: &Self) -> bool {
        self.exact.shares_root_with(&other.exact)
    }

    #[cfg(test)]
    pub(crate) fn shares_assumptions_with(&self, other: &Self) -> bool {
        self.assumptions
            .shares_persistent_storage_with(&other.assumptions)
    }

    #[cfg(test)]
    pub(crate) fn shares_ordered_tail_with(&self, other: &Self) -> bool {
        self.ordered.shares_tail_with(&other.ordered)
    }

    #[cfg(test)]
    pub(crate) fn shares_predicate_index_with(&self, other: &Self) -> bool {
        self.by_predicate.shares_root_with(&other.by_predicate)
    }

    #[cfg(test)]
    pub(crate) fn implication_bucket_len(
        &self,
        key: &SnapshotBlindPropositionKey,
    ) -> Option<usize> {
        self.implications_by_consequent
            .get(key)
            .map(PersistentSequence::len)
    }

    #[cfg(test)]
    pub(crate) fn quantified_bucket_len(&self, key: &QuantifiedEquivalenceKey) -> Option<usize> {
        self.by_quantified_equivalence
            .get(key)
            .map(PersistentSequence::len)
    }
}

/// Puts back the extent spelling a range carried before its binder was
/// renamed.
///
/// Renaming a bound variable is supposed to change what a proposition's binder
/// is called and nothing else. Substitution rebuilds every term it walks with
/// the kernel's folding constructors, though, and those fold strictly more
/// than the one `memory_range_byte_count` builds a range's extent with: the
/// extent of `a[k..k + 1]` is written `((k + 1) - k) * w` and comes back from
/// a substitution as the constant `w`. Both spell the same extent, and a
/// proof state matches a goal against a fact syntactically, so the rename
/// moved the goal out of the form every re-lowering of the written range
/// produces and the narrowing that had just worked stopped matching.
///
/// The two forms cannot simply be merged. The extent is also where surface
/// synthesis recovers a range's written ends from — folding `(k + 1) - k` to a
/// constant loses them, and `loadable(p[k..k + 1])` then spells back as a
/// zero-based range over a displaced base. So the rename keeps the spelling
/// instead: where the original carried a range extent, the renamed
/// proposition gets that extent's endpoints substituted and reassembled in the
/// written shape rather than the folded one.
///
/// This walks only the logical structure the two propositions share, and only
/// as far as the range leaves; it changes no other term and decides nothing.
fn restore_range_extent_spelling(
    original: &Proposition,
    renamed: Proposition,
    from: Variable,
    to: &Bitvector32Term,
) -> Proposition {
    let recurse = |original: &Proposition, renamed: Proposition| {
        Box::new(restore_range_extent_spelling(original, renamed, from, to))
    };
    match (original, renamed) {
        (
            Proposition::CMemoryLoadable { bytes, .. },
            Proposition::CMemoryLoadable {
                memory,
                base,
                bytes: folded,
            },
        ) => Proposition::CMemoryLoadable {
            memory,
            base,
            bytes: substituted_range_extent(bytes, from, to).unwrap_or(folded),
        },
        (Proposition::And(left, right), Proposition::And(renamed_left, renamed_right)) => {
            Proposition::And(recurse(left, *renamed_left), recurse(right, *renamed_right))
        }
        (Proposition::Or(left, right), Proposition::Or(renamed_left, renamed_right)) => {
            Proposition::Or(recurse(left, *renamed_left), recurse(right, *renamed_right))
        }
        (
            Proposition::Implies(antecedent, consequent),
            Proposition::Implies(renamed_antecedent, renamed_consequent),
        ) => Proposition::Implies(
            recurse(antecedent, *renamed_antecedent),
            recurse(consequent, *renamed_consequent),
        ),
        (Proposition::Not(body), Proposition::Not(renamed_body)) => {
            Proposition::Not(recurse(body, *renamed_body))
        }
        (
            Proposition::ForAll { body, .. },
            Proposition::ForAll {
                var,
                sort,
                body: renamed_body,
            },
        ) => Proposition::ForAll {
            var,
            sort,
            body: recurse(body, *renamed_body),
        },
        (_, renamed) => renamed,
    }
}

/// A written range extent with its endpoints substituted, reassembled in the
/// shape [`crate::kernel::memory_range_byte_count`] builds rather than the
/// shape the folding constructors would collapse it to. `None` when the term
/// is not a written range extent, which is every other byte count.
fn substituted_range_extent(
    bytes: &Bitvector32Term,
    from: Variable,
    to: &Bitvector32Term,
) -> Option<Bitvector32Term> {
    let substitute = |term: &Bitvector32Term| {
        crate::kernel::reasoning::substitute_bitvector_variable(term, from, to)
    };
    let (count, width) = match bytes {
        Bitvector32Term::Multiply(count, width) => match width.as_ref() {
            Bitvector32Term::Constant(_) => (count.as_ref(), Some(width.as_ref().clone())),
            _ => return None,
        },
        count @ Bitvector32Term::Subtract(_, _) => (count, None),
        _ => return None,
    };
    let Bitvector32Term::Subtract(end, start) = count else {
        return None;
    };
    let count = Bitvector32Term::Subtract(Box::new(substitute(end)), Box::new(substitute(start)));
    Some(match width {
        Some(width) => Bitvector32Term::Multiply(Box::new(count), Box::new(width)),
        None => count,
    })
}

/// The largest universal-introduction witness identity in an ascending set of
/// variables, or `None` when the set holds none.
///
/// The set is ordered, so this walks back from the top and stops at the first
/// identity below the witness range. Identities above the range would be some
/// other producer's, and the registry mints none, so they are skipped rather
/// than treated as the end of the walk.
fn highest_universal_witness(variables: impl DoubleEndedIterator<Item = Variable>) -> Option<u64> {
    variables
        .rev()
        .skip_while(|variable| {
            variable.0 >= crate::kernel::ExecutionBudget::UNIVERSAL_WITNESS_VARIABLE_CEILING
        })
        .take_while(|variable| {
            crate::kernel::ExecutionBudget::is_universal_witness_variable(*variable)
        })
        .map(|variable| variable.0)
        .next()
}

fn index_snapshot_fact(
    mut by_snapshot_blind: PersistentMap<
        SnapshotBlindPropositionKey,
        PersistentSequence<Proposition>,
    >,
    fact: &Proposition,
) -> PersistentMap<SnapshotBlindPropositionKey, PersistentSequence<Proposition>> {
    for key in [snapshot_blind_proposition_key(fact)] {
        if !key.forgets_a_snapshot() {
            continue;
        }
        let mut bucket = by_snapshot_blind.get(&key).cloned().unwrap_or_default();
        if !bucket.iter().any(|candidate| candidate == fact) {
            bucket.push(fact.clone());
            by_snapshot_blind = by_snapshot_blind.with_inserted(key, bucket);
        }
    }
    by_snapshot_blind
}

fn index_integer_condition_fact(
    mut index: PersistentMap<u64, PersistentSequence<IntegerConditionAlphaCandidate>>,
    fact: &Proposition,
) -> PersistentMap<u64, PersistentSequence<IntegerConditionAlphaCandidate>> {
    let Some(key) = integer_condition_alpha_key(fact) else {
        return index;
    };
    let Some(fingerprint) = key.checked_fingerprint() else {
        return index;
    };
    let mut bucket = index.get(&fingerprint).cloned().unwrap_or_default();
    // Keep one source proposition for each exact alpha key. Equivalent
    // restatements are common after fold freshening; appending each one would
    // make lookup and persistent updates grow with the ambient proof history.
    let mut equivalent = false;
    for candidate in &bucket {
        match candidate.key.checked_eq(&key) {
            Some(true) => {
                equivalent = true;
                break;
            }
            Some(false) => {}
            None => return index,
        }
    }
    if !equivalent {
        bucket.push(IntegerConditionAlphaCandidate {
            key,
            proposition: fact.clone(),
        });
        index = index.with_inserted(fingerprint, bucket);
    }
    index
}

fn index_bitvector_equality_fact(
    mut index: PersistentMap<BitvectorEqualityAtomKey, PersistentSequence<Arc<Proposition>>>,
    fact: &Arc<Proposition>,
) -> PersistentMap<BitvectorEqualityAtomKey, PersistentSequence<Arc<Proposition>>> {
    let (left, right) = match fact.as_ref() {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(left, right)
            | ConditionTerm::Bitvector64Equal(left, right),
            true,
        ) => (left.as_ref(), right.as_ref()),
        // A pointer-offset equality between two scaled offsets (how a
        // pointer-valued field's preservation is recorded) is indexed by the
        // same atoms so the load-variable chain bridge can select it.
        Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(left, right), true) => {
            match (left.as_ref(), right.as_ref()) {
                (
                    PointerOffsetTerm::Int32Scaled { value: left, .. },
                    PointerOffsetTerm::Int32Scaled { value: right, .. },
                ) => (left.as_ref(), right.as_ref()),
                _ => return index,
            }
        }
        Proposition::ConditionIs(ConditionTerm::PointerEqual(left, right), true) => {
            match (&left.offset, &right.offset) {
                (
                    PointerOffsetTerm::Int32Scaled { value: left, .. },
                    PointerOffsetTerm::Int32Scaled { value: right, .. },
                ) => (left.as_ref(), right.as_ref()),
                _ => return index,
            }
        }
        _ => return index,
    };
    for term in [left, right] {
        let Some(key) = bitvector_equality_atom_key(term) else {
            continue;
        };
        let mut bucket = index.get(&key).cloned().unwrap_or_default();
        if !bucket.iter().any(|candidate| Arc::ptr_eq(candidate, fact)) {
            bucket.push(fact.clone());
            index = index.with_inserted(key, bucket);
        }
    }
    index
}

/// Whether a proposition is only a C definedness guard: a conjunction of
/// the no-overflow conditions lowering attaches to partial arithmetic.
pub(crate) fn is_definedness_guard(proposition: &Proposition) -> bool {
    match proposition {
        Proposition::And(left, right) => is_definedness_guard(left) && is_definedness_guard(right),
        Proposition::ConditionIs(condition, false) => matches!(
            condition,
            ConditionTerm::Bitvector32SignedAddOverflows(..)
                | ConditionTerm::Bitvector32SignedSubtractOverflows(..)
                | ConditionTerm::Bitvector32SignedMultiplyOverflows(..)
                | ConditionTerm::Bitvector32SignedDivideOverflows(..)
                | ConditionTerm::Bitvector32SignedShiftLeftOverflows(..)
                | ConditionTerm::Bitvector64SignedAddOverflows(..)
                | ConditionTerm::Bitvector64SignedSubtractOverflows(..)
                | ConditionTerm::Bitvector64SignedMultiplyOverflows(..)
                | ConditionTerm::Bitvector64SignedDivideOverflows(..)
                | ConditionTerm::Bitvector64SignedShiftLeftOverflows(..)
        ),
        _ => false,
    }
}

fn index_guarded_equality_fact(
    mut index: PersistentMap<BitvectorEqualityAtomKey, PersistentSequence<Arc<Proposition>>>,
    fact: &Arc<Proposition>,
) -> PersistentMap<BitvectorEqualityAtomKey, PersistentSequence<Arc<Proposition>>> {
    let Proposition::Implies(guard, consequent) = fact.as_ref() else {
        return index;
    };
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(left, right) | ConditionTerm::Bitvector64Equal(left, right),
        true,
    ) = consequent.as_ref()
    else {
        return index;
    };
    if !is_definedness_guard(guard) {
        return index;
    }
    for term in [left.as_ref(), right.as_ref()] {
        let Some(key) = bitvector_equality_atom_key(term) else {
            continue;
        };
        let mut bucket = index.get(&key).cloned().unwrap_or_default();
        if !bucket.iter().any(|candidate| Arc::ptr_eq(candidate, fact)) {
            bucket.push(fact.clone());
            index = index.with_inserted(key, bucket);
        }
    }
    index
}

fn index_finite_classification_fact(
    mut index: PersistentMap<SnapshotBlindPropositionKey, PersistentSequence<Arc<Proposition>>>,
    fact: &Arc<Proposition>,
) -> PersistentMap<SnapshotBlindPropositionKey, PersistentSequence<Arc<Proposition>>> {
    if !matches!(
        fact.as_ref(),
        Proposition::ConditionIs(
            ConditionTerm::Float32(CFloatCondition::Classification { .. })
                | ConditionTerm::Float64(CFloatCondition::Classification { .. }),
            true,
        )
    ) {
        return index;
    }
    let key = snapshot_blind_proposition_key(fact.as_ref());
    let mut bucket = index.get(&key).cloned().unwrap_or_default();
    if !bucket.iter().any(|candidate| Arc::ptr_eq(candidate, fact)) {
        bucket.push(fact.clone());
        index = index.with_inserted(key, bucket);
    }
    index
}

fn index_algebraic_equality_fact(
    mut index: PersistentMap<AlgebraicTerm, PersistentSequence<Proposition>>,
    fact: &Proposition,
) -> PersistentMap<AlgebraicTerm, PersistentSequence<Proposition>> {
    let Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) = fact else {
        return index;
    };
    for term in [left, right]
        .into_iter()
        .filter(|term| !matches!(term.node, AlgebraicTermNode::Constructor { .. }))
    {
        let mut bucket = index.get(term).cloned().unwrap_or_default();
        if !bucket.iter().any(|candidate| candidate == fact) {
            bucket.push(fact.clone());
            index = index.with_inserted(term.clone(), bucket);
        }
    }
    index
}

fn collect_proposition_algebraic_terms(
    proposition: &Proposition,
    terms: &mut BTreeSet<AlgebraicTerm>,
) {
    match proposition {
        Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) => {
            collect_algebraic_term_roots(left, terms);
            collect_algebraic_term_roots(right, terms);
        }
        Proposition::ConditionIs(ConditionTerm::AlgebraicEqual(left, right), _) => {
            collect_algebraic_term_roots(left, terms);
            collect_algebraic_term_roots(right, terms);
        }
        Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), _) => {
            for value in [left.as_ref(), right.as_ref()] {
                if let Bitvector32Term::AlgebraicMatch { scrutinee, .. } = value {
                    collect_algebraic_term_roots(scrutinee, terms);
                }
            }
        }
        Proposition::Not(body)
        | Proposition::ForAll { body, .. }
        | Proposition::Exists { body, .. } => collect_proposition_algebraic_terms(body, terms),
        Proposition::And(left, right)
        | Proposition::Or(left, right)
        | Proposition::Implies(left, right) => {
            collect_proposition_algebraic_terms(left, terms);
            collect_proposition_algebraic_terms(right, terms);
        }
        _ => {}
    }
}

fn collect_algebraic_term_roots(term: &AlgebraicTerm, terms: &mut BTreeSet<AlgebraicTerm>) {
    terms.insert(term.clone());
    match &term.node {
        AlgebraicTermNode::Variable(_) => {}
        AlgebraicTermNode::Constructor { fields, .. } => {
            for field in fields {
                if let AlgebraicValue::Algebraic(value) = field {
                    collect_algebraic_term_roots(value, terms);
                }
            }
        }
        AlgebraicTermNode::Match { scrutinee, arms } => {
            collect_algebraic_term_roots(scrutinee, terms);
            for arm in arms {
                for binding in &arm.bindings {
                    if let AlgebraicValue::Algebraic(value) = binding {
                        collect_algebraic_term_roots(value, terms);
                    }
                }
                collect_algebraic_term_roots(&arm.body, terms);
            }
        }
        AlgebraicTermNode::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                if let PureFunctionArgument::Algebraic(value) = argument {
                    collect_algebraic_term_roots(value, terms);
                }
            }
        }
    }
}

fn bitvector_equality_atom_key(term: &Bitvector32Term) -> Option<BitvectorEqualityAtomKey> {
    match term {
        Bitvector32Term::Constant(value) => Some(BitvectorEqualityAtomKey::Constant(*value)),
        Bitvector32Term::Variable(variable) => Some(BitvectorEqualityAtomKey::Variable(*variable)),
        Bitvector32Term::ClickFunctionApplication { name, arguments } => {
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            for argument in arguments {
                match argument {
                    PureFunctionArgument::Value(value) => {
                        0u8.hash(&mut hasher);
                        value.hash(&mut hasher);
                    }
                    PureFunctionArgument::Algebraic(value) => {
                        1u8.hash(&mut hasher);
                        value.hash(&mut hasher);
                    }
                    PureFunctionArgument::Integer(value) => {
                        3u8.hash(&mut hasher);
                        value.hash(&mut hasher);
                    }
                    PureFunctionArgument::ArrayRef {
                        memory,
                        pointer,
                        element_type,
                    } => {
                        2u8.hash(&mut hasher);
                        intern_c_memory_ref(memory).arena_id().hash(&mut hasher);
                        pointer.hash(&mut hasher);
                        element_type.hash(&mut hasher);
                    }
                }
            }
            Some(BitvectorEqualityAtomKey::ClickFunctionApplication {
                name: name.clone(),
                arguments_hash: hasher.finish(),
            })
        }
        Bitvector32Term::MemoryLoad(memory, pointer) => {
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            std::hash::Hash::hash(pointer.as_ref(), &mut hasher);
            Some(BitvectorEqualityAtomKey::MemoryLoad {
                memory: memory.arena_id(),
                pointer_hash: std::hash::Hasher::finish(&hasher),
            })
        }
        _ => None,
    }
}

fn collect_proposition_bitvector_atoms(
    proposition: &Proposition,
    atoms: &mut BTreeSet<BitvectorEqualityAtomKey>,
) {
    match proposition {
        Proposition::ConditionIs(condition, _) => {
            collect_condition_bitvector_atoms(condition, atoms)
        }
        Proposition::CResourceSeparate { left, right } => {
            for resource in [left, right] {
                if let CResource::Memory(range) = resource {
                    collect_pointer_offset_bitvector_atoms(&range.base.offset, atoms);
                    collect_bitvector_atoms(&range.start, atoms);
                    collect_bitvector_atoms(&range.end, atoms);
                }
            }
        }
        Proposition::ForAll { body, .. }
        | Proposition::Exists { body, .. }
        | Proposition::Not(body) => collect_proposition_bitvector_atoms(body, atoms),
        Proposition::And(left, right)
        | Proposition::Or(left, right)
        | Proposition::Implies(left, right) => {
            collect_proposition_bitvector_atoms(left, atoms);
            collect_proposition_bitvector_atoms(right, atoms);
        }
        _ => {}
    }
}

fn collect_condition_bitvector_atoms(
    condition: &ConditionTerm,
    atoms: &mut BTreeSet<BitvectorEqualityAtomKey>,
) {
    match condition {
        ConditionTerm::AlgebraicEqual(left, right) => {
            left.for_each_bitvector_term(|term| collect_bitvector_atoms(term, atoms));
            right.for_each_bitvector_term(|term| collect_bitvector_atoms(term, atoms));
        }
        ConditionTerm::Bitvector32SignedLessThan(left, right)
        | ConditionTerm::Bitvector32SignedLessEqual(left, right)
        | ConditionTerm::Bitvector32SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector32Equal(left, right)
        | ConditionTerm::Bitvector32SignedAddOverflows(left, right)
        | ConditionTerm::Bitvector32SignedSubtractOverflows(left, right)
        | ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right)
        | ConditionTerm::Bitvector32SignedDivideOverflows(left, right)
        | ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right)
        | ConditionTerm::Bitvector64SignedLessThan(left, right)
        | ConditionTerm::Bitvector64SignedLessEqual(left, right)
        | ConditionTerm::Bitvector64SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector64SignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector64UnsignedLessThan(left, right)
        | ConditionTerm::Bitvector64UnsignedLessEqual(left, right)
        | ConditionTerm::Bitvector64UnsignedGreaterThan(left, right)
        | ConditionTerm::Bitvector64UnsignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector64Equal(left, right)
        | ConditionTerm::Bitvector64SignedAddOverflows(left, right)
        | ConditionTerm::Bitvector64SignedSubtractOverflows(left, right)
        | ConditionTerm::Bitvector64SignedMultiplyOverflows(left, right)
        | ConditionTerm::Bitvector64SignedDivideOverflows(left, right)
        | ConditionTerm::Bitvector64SignedShiftLeftOverflows(left, right) => {
            collect_bitvector_atoms(left, atoms);
            collect_bitvector_atoms(right, atoms);
        }
        ConditionTerm::IntegerLessThan(_, _)
        | ConditionTerm::IntegerLessEqual(_, _)
        | ConditionTerm::IntegerGreaterThan(_, _)
        | ConditionTerm::IntegerGreaterEqual(_, _)
        | ConditionTerm::IntegerEqual(_, _)
        | ConditionTerm::IntegerNotEqual(_, _) => {}
        ConditionTerm::Float32(float_condition) | ConditionTerm::Float64(float_condition) => {
            float_condition.for_each_bitvector_term(|term| collect_bitvector_atoms(term, atoms));
        }
        ConditionTerm::PointerOffsetEqual(left, right) => {
            collect_pointer_offset_bitvector_atoms(left, atoms);
            collect_pointer_offset_bitvector_atoms(right, atoms);
        }
        ConditionTerm::PointerEqual(left, right) => {
            collect_pointer_offset_bitvector_atoms(&left.offset, atoms);
            collect_pointer_offset_bitvector_atoms(&right.offset, atoms);
        }
        ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => {}
    }
}

fn collect_bitvector_atoms(term: &Bitvector32Term, atoms: &mut BTreeSet<BitvectorEqualityAtomKey>) {
    if let Some(atom) = bitvector_equality_atom_key(term) {
        atoms.insert(atom);
    }
    match term {
        Bitvector32Term::Add(left, right)
        | Bitvector32Term::Subtract(left, right)
        | Bitvector32Term::Multiply(left, right)
        | Bitvector32Term::Divide(left, right)
        | Bitvector32Term::UnsignedDivide(left, right)
        | Bitvector32Term::Remainder(left, right)
        | Bitvector32Term::UnsignedRemainder(left, right)
        | Bitvector32Term::ShiftLeft(left, right)
        | Bitvector32Term::ArithmeticShiftRight(left, right)
        | Bitvector32Term::LogicalShiftRight(left, right)
        | Bitvector32Term::BitwiseAnd(left, right)
        | Bitvector32Term::BitwiseOr(left, right)
        | Bitvector32Term::BitwiseXor(left, right)
        | Bitvector32Term::Int64Add(left, right)
        | Bitvector32Term::Int64Subtract(left, right)
        | Bitvector32Term::Int64Multiply(left, right)
        | Bitvector32Term::Int64Divide(left, right)
        | Bitvector32Term::Int64Remainder(left, right)
        | Bitvector32Term::Int64ShiftLeft(left, right)
        | Bitvector32Term::Int64ArithmeticShiftRight(left, right)
        | Bitvector32Term::Int64BitwiseAnd(left, right)
        | Bitvector32Term::Int64BitwiseOr(left, right)
        | Bitvector32Term::Int64BitwiseXor(left, right)
        | Bitvector32Term::UInt64Add(left, right)
        | Bitvector32Term::UInt64Subtract(left, right)
        | Bitvector32Term::UInt64Multiply(left, right)
        | Bitvector32Term::UInt64Divide(left, right)
        | Bitvector32Term::UInt64Remainder(left, right)
        | Bitvector32Term::UInt64ShiftLeft(left, right)
        | Bitvector32Term::UInt64LogicalShiftRight(left, right)
        | Bitvector32Term::UInt64BitwiseAnd(left, right)
        | Bitvector32Term::UInt64BitwiseOr(left, right)
        | Bitvector32Term::UInt64BitwiseXor(left, right) => {
            collect_bitvector_atoms(left, atoms);
            collect_bitvector_atoms(right, atoms);
        }
        Bitvector32Term::Float32Binary { left, right, .. }
        | Bitvector32Term::Float64Binary { left, right, .. } => {
            collect_bitvector_atoms(left, atoms);
            collect_bitvector_atoms(right, atoms);
        }
        Bitvector32Term::BitwiseNot(value)
        | Bitvector32Term::Int64BitwiseNot(value)
        | Bitvector32Term::UInt64BitwiseNot(value)
        | Bitvector32Term::Int64From32(value)
        | Bitvector32Term::UInt64From32(value)
        | Bitvector32Term::UInt32From64(value)
        | Bitvector32Term::Int64FromUInt32(value)
        | Bitvector32Term::UInt64FromInt32(value)
        | Bitvector32Term::UInt64FromInt64(value)
        | Bitvector32Term::Float32Negate(value)
        | Bitvector32Term::Float64Negate(value) => collect_bitvector_atoms(value, atoms),
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_bitvector_atoms(condition, atoms);
            collect_bitvector_atoms(then_term, atoms);
            collect_bitvector_atoms(else_term, atoms);
        }
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            collect_bitvector_atoms(start, atoms);
            collect_bitvector_atoms(end, atoms);
            collect_bitvector_atoms(initial, atoms);
            collect_bitvector_atoms(body, atoms);
        }
        Bitvector32Term::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                collect_bitvector_atoms(argument, atoms);
            }
        }
        Bitvector32Term::ClickFunctionApplication { .. } => {}
        Bitvector32Term::AlgebraicMatch { arms, .. } => {
            for arm in arms {
                collect_bitvector_atoms(&arm.body, atoms);
            }
        }
        Bitvector32Term::MemoryLoad(_, pointer) => {
            collect_pointer_offset_bitvector_atoms(&pointer.offset, atoms)
        }
        Bitvector32Term::PointerAddress(pointer) => {
            collect_pointer_offset_bitvector_atoms(&pointer.offset, atoms)
        }
        Bitvector32Term::Constant(_)
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_)
        | Bitvector32Term::Variable(_) => {}
        Bitvector32Term::IntegerToMachine { .. } => {}
    }
}

fn collect_pointer_offset_bitvector_atoms(
    offset: &PointerOffsetTerm,
    atoms: &mut BTreeSet<BitvectorEqualityAtomKey>,
) {
    match offset {
        PointerOffsetTerm::Add(left, right) => {
            collect_pointer_offset_bitvector_atoms(left, atoms);
            collect_pointer_offset_bitvector_atoms(right, atoms);
        }
        PointerOffsetTerm::Int32Scaled { value, .. }
        | PointerOffsetTerm::Int64Scaled { value, .. } => collect_bitvector_atoms(value, atoms),
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {}
    }
}

fn index_quantified_fact(
    mut index: PersistentMap<QuantifiedEquivalenceKey, PersistentSequence<Proposition>>,
    fact: &Proposition,
) -> PersistentMap<QuantifiedEquivalenceKey, PersistentSequence<Proposition>> {
    let Some(key) = quantified_equivalence_index_key(fact) else {
        return index;
    };
    let mut bucket = index.get(&key).cloned().unwrap_or_default();
    if !bucket.iter().any(|candidate| candidate == fact) {
        bucket.push(fact.clone());
        index = index.with_inserted(key, bucket);
    }
    index
}

fn index_implication_consequents(
    mut index: PersistentMap<SnapshotBlindPropositionKey, PersistentSequence<ImplicationCandidate>>,
    mut quantified_index: PersistentMap<
        QuantifiedEquivalenceKey,
        PersistentSequence<ImplicationCandidate>,
    >,
    fact: &Proposition,
) -> (
    PersistentMap<SnapshotBlindPropositionKey, PersistentSequence<ImplicationCandidate>>,
    PersistentMap<QuantifiedEquivalenceKey, PersistentSequence<ImplicationCandidate>>,
) {
    let mut depth = 0;
    let mut depth_cursor = fact;
    while let Proposition::Implies(_, consequent) = depth_cursor {
        depth += 1;
        depth_cursor = consequent;
    }
    if depth > 128 {
        // This index is an optional search accelerator. Keep a very deep
        // implication in the authoritative fact stores without materializing
        // one candidate per suffix.
        return (index, quantified_index);
    }
    let mut antecedents = PersistentSequence::default();
    let mut current = fact;
    while let Proposition::Implies(antecedent, consequent) = current {
        antecedents.push(antecedent.as_ref().clone());
        let candidate = ImplicationCandidate {
            antecedents: antecedents.clone(),
            consequent: consequent.as_ref().clone(),
        };
        let normalized = consequent.clone();
        let mut keys = vec![snapshot_blind_proposition_key(consequent)];
        let normalized_key = snapshot_blind_proposition_key(&normalized);
        if !keys.contains(&normalized_key) {
            keys.push(normalized_key);
        }
        for key in keys {
            let mut bucket = index.get(&key).cloned().unwrap_or_default();
            bucket.push(candidate.clone());
            index = index.with_inserted(key, bucket);
        }
        if let Some(key) = quantified_equivalence_index_key(consequent) {
            let mut bucket = quantified_index.get(&key).cloned().unwrap_or_default();
            bucket.push(candidate);
            quantified_index = quantified_index.with_inserted(key, bucket);
        }
        current = consequent;
    }
    (index, quantified_index)
}

fn index_proper_conjuncts(
    mut index: PersistentSet<Proposition>,
    fact: &Proposition,
) -> PersistentSet<Proposition> {
    let Proposition::And(left, right) = fact else {
        return index;
    };
    // Walk the conjunction without consuming stack for source depth.  Keep
    // only subtrees whose depth is bounded before cloning them into the
    // persistent set: a deep right-nested conjunction otherwise causes the
    // first clone to recurse through the entire remaining spine.
    const MAX_INDEXED_CONJUNCT_DEPTH: usize = 64;
    enum Task<'a> {
        Visit(&'a Proposition),
        Finish(&'a Proposition),
    }
    let mut depths: HashMap<*const Proposition, usize> = HashMap::new();
    let mut pending = vec![Task::Visit(left.as_ref()), Task::Visit(right.as_ref())];
    while let Some(task) = pending.pop() {
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            break;
        }
        match task {
            Task::Visit(conjunct) => match conjunct {
                Proposition::And(left, right) => {
                    pending.push(Task::Finish(conjunct));
                    pending.push(Task::Visit(right));
                    pending.push(Task::Visit(left));
                }
                _ => {
                    depths.insert(conjunct as *const Proposition, 1);
                    index = index.with_value(conjunct.clone());
                }
            },
            Task::Finish(conjunct) => {
                let Proposition::And(left, right) = conjunct else {
                    continue;
                };
                let Some(left_depth) = depths.get(&(left.as_ref() as *const Proposition)) else {
                    break;
                };
                let Some(right_depth) = depths.get(&(right.as_ref() as *const Proposition)) else {
                    break;
                };
                let depth = 1usize.saturating_add((*left_depth).max(*right_depth));
                depths.insert(conjunct as *const Proposition, depth);
                if depth <= MAX_INDEXED_CONJUNCT_DEPTH {
                    index = index.with_value(conjunct.clone());
                }
            }
        }
    }
    index
}

fn index_implicit_transport_context(
    mut implicit: PureFactContext,
    fact: &Proposition,
) -> PureFactContext {
    if let Proposition::And(left, right) = fact {
        let implicit = index_implicit_transport_context(implicit, left);
        return index_implicit_transport_context(implicit, right);
    }
    if is_implicit_fact_transport_context(fact) {
        implicit = implicit.assume_proposition(fact.clone());
    }
    implicit
}

fn directly_conflicts_with_normalized_index(
    exact: &PersistentSet<Proposition>,
    fact: &Proposition,
) -> bool {
    match fact {
        Proposition::And(left, right) => {
            directly_conflicts_with_normalized_index(exact, left)
                || directly_conflicts_with_normalized_index(exact, right)
        }
        Proposition::ConditionIs(condition, value) => {
            exact.contains(&Proposition::ConditionIs(condition.clone(), !value))
        }
        Proposition::Not(body) => exact.contains(body),
        other => exact.contains(&Proposition::Not(Box::new(other.clone()))),
    }
}

fn index_predicate_fact(
    mut index: PersistentMap<String, PersistentSequence<Proposition>>,
    fact: &Proposition,
) -> PersistentMap<String, PersistentSequence<Proposition>> {
    let mut names = BTreeSet::new();
    collect_fact_predicate_names(fact, &mut names);
    for name in names {
        let mut facts = index.get(&name).cloned().unwrap_or_default();
        facts.push(fact.clone());
        index = index.with_inserted(name, facts);
    }
    index
}

fn collect_fact_predicate_names(fact: &Proposition, names: &mut BTreeSet<String>) {
    match fact {
        Proposition::Predicate { name, .. } => {
            names.insert(name.clone());
        }
        Proposition::And(left, right)
        | Proposition::Or(left, right)
        | Proposition::Implies(left, right) => {
            collect_fact_predicate_names(left, names);
            collect_fact_predicate_names(right, names);
        }
        Proposition::Not(body)
        | Proposition::ForAll { body, .. }
        | Proposition::Exists { body, .. } => collect_fact_predicate_names(body, names),
        _ => {}
    }
}

fn collect_owned_atomic_conjuncts(fact: &Proposition, output: &mut Vec<Proposition>) {
    match fact {
        Proposition::And(left, right) => {
            collect_owned_atomic_conjuncts(left, output);
            collect_owned_atomic_conjuncts(right, output);
        }
        _ => output.push(fact.clone()),
    }
}

#[cfg(test)]
mod integer_equality_fact_index_tests {
    use super::*;
    use crate::kernel::{
        Bitvector32Term, CMemory, CValue, IntegerRangeFoldIndex, IntegerTerm, MachineIntegerType,
        Pointer, PointerOffsetTerm, SharedIntegerRangeEndpoint, SharedIntegerTerm,
        SharedMachineIntegerTerm, Sort, Variable,
    };

    fn integer_index() -> IntegerRangeFoldIndex {
        IntegerRangeFoldIndex::Integer {
            start: IntegerTerm::constant_i64(0).into(),
            end: IntegerTerm::constant_i64(2).into(),
        }
    }

    fn int32_index() -> IntegerRangeFoldIndex {
        IntegerRangeFoldIndex::Int32 {
            start: SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(0)),
            end: SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(2)),
        }
    }

    fn fold(
        index: IntegerRangeFoldIndex,
        accumulator: Variable,
        item: Variable,
        body: IntegerTerm,
    ) -> IntegerTerm {
        IntegerTerm::range_fold(index, IntegerTerm::constant_i64(0), accumulator, item, body)
    }

    fn equality(left: IntegerTerm, right: IntegerTerm) -> Proposition {
        Proposition::ConditionIs(ConditionTerm::IntegerEqual(left.into(), right.into()), true)
    }

    fn less_equal(left: IntegerTerm, right: IntegerTerm) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::IntegerLessEqual(left.into(), right.into()),
            true,
        )
    }

    fn less_than(left: IntegerTerm, right: IntegerTerm) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::IntegerLessThan(left.into(), right.into()),
            true,
        )
    }

    fn explicit_load_fold(
        memory: &crate::kernel::SharedCMemory,
        accumulator: Variable,
        item: Variable,
    ) -> IntegerTerm {
        fold(
            int32_index(),
            accumulator,
            item,
            IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int32,
                Bitvector32Term::MemoryLoad(
                    memory.clone(),
                    Box::new(Pointer {
                        block: "snapshot-alpha-facts".into(),
                        offset: PointerOffsetTerm::Constant(0),
                    }),
                ),
            )),
        )
    }

    fn loadable_forall(
        memory: &CMemory,
        binder: Variable,
        block: &str,
        free_offset: Option<Variable>,
        bytes: u32,
    ) -> Proposition {
        let bound_offset = PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(binder)),
            byte_width: 4,
        };
        let offset = free_offset.map_or(bound_offset.clone(), |free| {
            PointerOffsetTerm::Add(
                Box::new(bound_offset),
                Box::new(PointerOffsetTerm::Int32Scaled {
                    value: Box::new(Bitvector32Term::Variable(free)),
                    byte_width: 1,
                }),
            )
        });
        Proposition::ForAll {
            var: binder,
            sort: Sort::CInt32,
            body: Box::new(Proposition::CMemoryLoadable {
                memory: memory.clone(),
                base: Pointer {
                    block: block.into(),
                    offset,
                },
                bytes: Bitvector32Term::Constant(bytes),
            }),
        }
    }

    fn loadable_exists(
        memory: &CMemory,
        name: &str,
        binder: Variable,
        block: &str,
        free_offset: Option<Variable>,
        bytes: u32,
    ) -> Proposition {
        let bound_offset = PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(binder)),
            byte_width: 4,
        };
        let offset = free_offset.map_or(bound_offset.clone(), |free| {
            PointerOffsetTerm::Add(
                Box::new(bound_offset),
                Box::new(PointerOffsetTerm::Int32Scaled {
                    value: Box::new(Bitvector32Term::Variable(free)),
                    byte_width: 1,
                }),
            )
        });
        Proposition::Exists {
            name: name.into(),
            var: binder,
            sort: Sort::CInt32,
            body: Box::new(Proposition::CMemoryLoadable {
                memory: memory.clone(),
                base: Pointer {
                    block: block.into(),
                    offset,
                },
                bytes: Bitvector32Term::Constant(bytes),
            }),
        }
    }

    #[test]
    fn transport_index_extracts_separation_without_importing_arithmetic() {
        let range = |block: &str| {
            crate::kernel::CResource::Memory(crate::kernel::CMemoryRange::new(
                Pointer {
                    block: block.into(),
                    offset: PointerOffsetTerm::Constant(0),
                },
                Bitvector32Term::Constant(0),
                Bitvector32Term::Variable(Variable(210_000)),
            ))
        };
        let separation = Proposition::CResourceSeparate {
            left: range("a"),
            right: range("b"),
        };
        let bound = Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(
                Bitvector32Term::Constant(0),
                Bitvector32Term::Variable(Variable(210_000)),
            ),
            true,
        );
        let conjunction = Proposition::And(Box::new(separation.clone()), Box::new(bound.clone()));
        for facts in [
            ProofFacts::from_ordered(std::slice::from_ref(&conjunction)),
            ProofFacts::from_ordered(&[]).with_fact(conjunction),
        ] {
            assert!(
                facts
                    .implicit_transport_assumptions()
                    .contains_assumed_exact(&separation)
            );
            assert!(
                !facts
                    .implicit_transport_assumptions()
                    .contains_assumed_exact(&bound)
            );
        }
        let conditional = Proposition::Implies(Box::new(bound), Box::new(separation.clone()));
        let facts = ProofFacts::from_ordered(&[conditional]);
        assert!(
            !facts
                .implicit_transport_assumptions()
                .contains_assumed_exact(&separation)
        );
    }

    #[test]
    fn wide_equality_decision_uses_only_its_indexed_component() {
        let left = Bitvector32Term::Variable(Variable(211_000));
        let middle = Bitvector32Term::Variable(Variable(211_001));
        let equality = |a: Bitvector32Term, b: Bitvector32Term| {
            Proposition::ConditionIs(
                ConditionTerm::Bitvector64Equal(Box::new(a), Box::new(b)),
                true,
            )
        };
        let required = equality(left.clone(), Bitvector32Term::UInt64Constant(7));
        let wrong = equality(left.clone(), Bitvector32Term::UInt64Constant(9));
        let mut work = Vec::new();
        for size in [8, 16, 32, 64] {
            let unrelated = (0..size)
                .map(|index| {
                    equality(
                        Bitvector32Term::Variable(Variable(212_000 + index)),
                        Bitvector32Term::UInt64Constant(index),
                    )
                })
                .collect::<Vec<_>>();
            let facts = ProofFacts::from_ordered(&unrelated)
                .with_kernel_checked_fact(equality(left.clone(), middle.clone()))
                .with_kernel_checked_fact(equality(
                    middle.clone(),
                    Bitvector32Term::UInt64Constant(7),
                ));
            let (proved, measured) = crate::instrumentation::measure_deterministic_work(|| {
                facts.assumptions().proves_atomic_without_search(&required)
            });
            assert!(proved);
            assert!(!facts.assumptions().proves_atomic_without_search(&wrong));
            work.push(measured);
        }
        assert!(work.windows(2).all(|pair| pair[0] == pair[1]), "{work:?}");
        let narrow = ProofFacts::from_ordered(&[
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(middle.clone())),
                true,
            ),
            equality(middle, Bitvector32Term::UInt64Constant(7)),
        ]);
        assert!(!narrow.assumptions().proves_atomic_without_search(&required));
    }

    #[test]
    fn induction_domain_uses_only_the_selected_signed_bound_bucket() {
        let measure = Bitvector32Term::Variable(Variable(123456));
        for size in [8, 32, 128, 512] {
            let unrelated = (0..size)
                .map(|index| {
                    Proposition::ConditionIs(
                        ConditionTerm::Bitvector32SignedGreaterEqual(
                            Box::new(Bitvector32Term::Variable(Variable(index))),
                            Box::new(Bitvector32Term::Constant(0)),
                        ),
                        true,
                    )
                })
                .collect::<Vec<_>>();
            let base = ProofFacts::from_ordered(&unrelated);
            assert!(!base.has_nonnegative_induction_domain(&measure));
            for (bound, strict, expected) in [
                (5i32, false, true),
                (-1, true, true),
                (-1, false, false),
                (-2, true, false),
            ] {
                let condition = if strict {
                    ConditionTerm::Bitvector32SignedGreaterThan(
                        Box::new(measure.clone()),
                        Box::new(Bitvector32Term::Constant(bound as u32)),
                    )
                } else {
                    ConditionTerm::Bitvector32SignedGreaterEqual(
                        Box::new(measure.clone()),
                        Box::new(Bitvector32Term::Constant(bound as u32)),
                    )
                };
                let facts =
                    base.with_kernel_checked_fact(Proposition::ConditionIs(condition, true));
                assert_eq!(
                    facts
                        .assumptions()
                        .signed_order_bound_entries(&measure)
                        .count(),
                    1
                );
                assert_eq!(facts.has_nonnegative_induction_domain(&measure), expected);
            }
        }
    }

    fn unrelated_fact(value: i64) -> Proposition {
        equality(
            IntegerTerm::constant_i64(value),
            IntegerTerm::constant_i64(value + 1),
        )
    }

    fn growing_shared_scalar_dag(depth: usize) -> IntegerTerm {
        let mut term = IntegerTerm::var(Variable(204_000));
        for _ in 0..depth {
            let child: SharedIntegerTerm = term.into();
            term = IntegerTerm::Add(child.clone(), child);
        }
        term
    }

    #[test]
    fn integer_alpha_fact_lookup_returns_the_stored_bound_source() {
        let source = fold(
            integer_index(),
            Variable(200_000),
            Variable(200_001),
            IntegerTerm::add(
                IntegerTerm::var(Variable(200_000)),
                IntegerTerm::var(Variable(200_001)),
            ),
        );
        let required = fold(
            integer_index(),
            Variable(200_100),
            Variable(200_101),
            IntegerTerm::add(
                IntegerTerm::var(Variable(200_100)),
                IntegerTerm::var(Variable(200_101)),
            ),
        );
        let source_fact = equality(IntegerTerm::constant_i64(9), source);
        let required_fact = equality(IntegerTerm::constant_i64(9), required);
        let facts = ProofFacts::from_ordered(std::slice::from_ref(&source_fact));

        assert_eq!(
            facts.matching_fact_across_effects(&required_fact, &[]),
            Some(source_fact.clone())
        );
        assert!(facts.exact_available_across_effects(&required_fact, &[]));
        assert!(facts.pure_assumption_available(&required_fact));
    }

    #[test]
    fn integer_alpha_fact_lookup_matches_alpha_renamed_fold_inequality() {
        let source = fold(
            integer_index(),
            Variable(200_200),
            Variable(200_201),
            IntegerTerm::add(
                IntegerTerm::var(Variable(200_200)),
                IntegerTerm::var(Variable(200_201)),
            ),
        );
        let required = fold(
            integer_index(),
            Variable(200_300),
            Variable(200_301),
            IntegerTerm::add(
                IntegerTerm::var(Variable(200_300)),
                IntegerTerm::var(Variable(200_301)),
            ),
        );
        let source_fact = less_equal(source, IntegerTerm::constant_i64(9));
        let required_fact = less_equal(required, IntegerTerm::constant_i64(9));
        let facts = ProofFacts::from_ordered(std::slice::from_ref(&source_fact));

        assert_eq!(
            facts.matching_fact_across_effects(&required_fact, &[]),
            Some(source_fact.clone())
        );
        assert!(facts.exact_available_across_effects(&required_fact, &[]));
        assert!(facts.pure_assumption_available(&required_fact));
    }

    #[test]
    fn integer_alpha_fact_lookup_keeps_inequality_snapshot_identity() {
        let before =
            crate::kernel::intern_c_memory(CMemory::new().with_block("snapshot-alpha-facts", 8));
        let changed = crate::kernel::intern_c_memory(before.as_ref().clone().store(
            Pointer {
                block: "snapshot-alpha-facts".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            CValue::Int32(Bitvector32Term::Constant(7)),
        ));
        let source_fact = less_equal(
            IntegerTerm::constant_i64(9),
            explicit_load_fold(&before, Variable(200_400), Variable(200_401)),
        );
        let renamed_fact = less_equal(
            IntegerTerm::constant_i64(9),
            explicit_load_fold(&before, Variable(200_500), Variable(200_501)),
        );
        let changed_snapshot_fact = less_equal(
            IntegerTerm::constant_i64(9),
            explicit_load_fold(&changed, Variable(200_500), Variable(200_501)),
        );
        let facts = ProofFacts::from_ordered(std::slice::from_ref(&source_fact));

        assert_eq!(
            facts.matching_fact_across_effects(&renamed_fact, &[]),
            Some(source_fact)
        );
        assert!(
            facts
                .matching_fact_across_effects(&changed_snapshot_fact, &[])
                .is_none()
        );
    }

    #[test]
    fn quantified_loadable_alpha_index_renames_binder_but_keeps_exact_payload() {
        let memory = CMemory::new().with_block("quantified-viewable", 32).store(
            Pointer {
                block: "quantified-viewable".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            CValue::Int32(Bitvector32Term::Variable(Variable(207_000))),
        );
        let changed_memory = memory.clone().store(
            Pointer {
                block: "quantified-viewable".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            CValue::Int32(Bitvector32Term::Constant(7)),
        );
        let source = loadable_forall(
            &memory,
            Variable(207_000),
            "quantified-viewable",
            Some(Variable(207_001)),
            4,
        );
        let renamed = loadable_forall(
            &memory,
            Variable(207_100),
            "quantified-viewable",
            Some(Variable(207_001)),
            4,
        );
        let changed_snapshot = loadable_forall(
            &changed_memory,
            Variable(207_100),
            "quantified-viewable",
            Some(Variable(207_001)),
            4,
        );
        let changed_pointer = loadable_forall(
            &memory,
            Variable(207_100),
            "different-viewable",
            Some(Variable(207_001)),
            4,
        );
        let changed_width = loadable_forall(
            &memory,
            Variable(207_100),
            "quantified-viewable",
            Some(Variable(207_001)),
            8,
        );
        let free_mismatch = loadable_forall(
            &memory,
            Variable(207_100),
            "quantified-viewable",
            Some(Variable(207_002)),
            4,
        );
        let facts = ProofFacts::from_ordered(std::slice::from_ref(&source));

        assert_eq!(
            facts.matching_fact_across_effects(&renamed, &[]),
            Some(source.clone())
        );
        for mismatch in [
            changed_snapshot,
            changed_pointer,
            changed_width,
            free_mismatch,
        ] {
            assert!(
                facts.matching_fact_across_effects(&mismatch, &[]).is_none(),
                "viewability alpha matching must retain snapshot, pointer, width, and free IDs"
            );
        }
    }

    #[test]
    fn quantified_loadable_root_existential_ignores_display_name() {
        let memory = CMemory::new().with_block("root-existential-viewable", 32);
        let source = loadable_exists(
            &memory,
            "source_witness",
            Variable(207_500),
            "root-existential-viewable",
            Some(Variable(207_501)),
            4,
        );
        let renamed = loadable_exists(
            &memory,
            "required_witness",
            Variable(207_600),
            "root-existential-viewable",
            Some(Variable(207_501)),
            4,
        );
        let facts = ProofFacts::from_ordered(std::slice::from_ref(&source));

        assert_eq!(
            facts.matching_quantified_fact(&renamed),
            Some(source.clone())
        );
        assert_eq!(
            facts.matching_fact_across_effects(&renamed, &[]),
            Some(source.clone())
        );
        assert!(facts.available_across_effects(&renamed, &[]));

        let context = PureFactContext::new().assume_proposition(source);
        assert!(context.states_required_goal(&renamed));
    }

    #[test]
    fn quantified_predicate_alpha_lookup_checks_state_after_memory_bucket() {
        let predicate = |name: &str, binder: Variable, state: CState| Proposition::Exists {
            name: name.to_string(),
            var: binder,
            sort: Sort::CInt32,
            body: Box::new(Proposition::Predicate {
                name: "sample".to_string(),
                arguments: vec![
                    Term::CState(Box::new(state)),
                    Term::CValue(CValue::Int32(Bitvector32Term::Variable(binder))),
                ],
            }),
        };
        let state = CState::new().with_local("x", CValue::Int32(Bitvector32Term::Constant(7)));
        let available = predicate("first", Variable(300_001), state.clone());
        let renamed = predicate("second", Variable(300_002), state.clone());
        let independently_empty = predicate("second", Variable(300_002), CState::new());
        let empty = predicate("first", Variable(300_001), CState::new());
        let changed_state = predicate(
            "second",
            Variable(300_002),
            state.with_local("x", CValue::Int32(Bitvector32Term::Constant(8))),
        );
        assert_eq!(
            quantified_equivalence_index_key(&available),
            quantified_equivalence_index_key(&renamed)
        );
        assert_eq!(
            quantified_equivalence_index_key(&available),
            quantified_equivalence_index_key(&changed_state),
            "the memory-only bucket must leave the final state check to the matcher"
        );
        assert!(quantified_binder_equivalent(&available, &renamed));
        assert!(quantified_binder_equivalent(&empty, &independently_empty));
        assert!(!quantified_binder_equivalent(&available, &changed_state));
        let facts = ProofFacts::from_ordered(std::slice::from_ref(&available));
        assert_eq!(facts.matching_quantified_fact(&renamed), Some(available));
        assert!(facts.matching_quantified_fact(&changed_state).is_none());
    }

    #[test]
    fn implication_extract_renames_existential_but_keeps_snapshot_and_antecedent() {
        let block = "implication-existential-viewable";
        let memory = CMemory::new().with_block(block, 32);
        let changed_memory = memory.clone().store(
            Pointer {
                block: block.into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            CValue::Int32(Bitvector32Term::Constant(1)),
        );
        let consequent = loadable_exists(&memory, "callee", Variable(207_700), block, None, 4);
        let renamed = loadable_exists(&memory, "caller", Variable(207_800), block, None, 4);
        let changed_snapshot =
            loadable_exists(&changed_memory, "caller", Variable(207_800), block, None, 4);
        let antecedent = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
        let implication = Proposition::Implies(Box::new(antecedent.clone()), Box::new(consequent));
        let without_antecedent = ProofFacts::from_ordered(std::slice::from_ref(&implication));
        assert!(!without_antecedent.contains_discharged_implication_consequent(&renamed));

        let facts = ProofFacts::from_ordered(&[implication, antecedent]);
        assert!(facts.contains_discharged_implication_consequent(&renamed));
        assert!(!facts.contains_discharged_implication_consequent(&changed_snapshot));
    }

    #[test]
    fn implication_extract_renames_path_inside_function_equality() {
        let path_type = crate::kernel::AlgebraicType::parameter("Path".into());
        let path_reaches = |name: &str, binder: Variable| Proposition::Exists {
            name: name.into(),
            var: binder,
            sort: Sort::Algebraic(path_type.clone()),
            body: Box::new(Proposition::Equal(
                Term::Bitvector32(Bitvector32Term::ClickFunctionApplication {
                    name: "walk".into(),
                    arguments: vec![PureFunctionArgument::Algebraic(AlgebraicTerm {
                        algebraic_type: path_type.clone(),
                        node: AlgebraicTermNode::Variable(binder),
                    })],
                }),
                Term::Bitvector32(Bitvector32Term::Constant(1)),
            )),
        };
        let source = path_reaches("callee_path", Variable(207_750));
        let required = path_reaches("caller_path", Variable(207_751));
        let antecedent = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
        let facts = ProofFacts::from_ordered(&[
            Proposition::Implies(Box::new(antecedent.clone()), Box::new(source)),
            antecedent,
        ]);
        assert!(facts.contains_discharged_implication_consequent(&required));
    }

    #[test]
    fn quantified_implication_extract_does_not_scan_unrelated_consequents() {
        let memory = CMemory::new().with_block("selected-implication", 32);
        let antecedent = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
        let selected = loadable_exists(
            &memory,
            "callee",
            Variable(207_900),
            "selected-implication",
            None,
            4,
        );
        let required = loadable_exists(
            &memory,
            "caller",
            Variable(207_901),
            "selected-implication",
            None,
            4,
        );
        let mut visits = Vec::new();
        for count in [8_u64, 16, 32, 64] {
            let mut ordered = vec![
                Proposition::Implies(Box::new(antecedent.clone()), Box::new(selected.clone())),
                antecedent.clone(),
            ];
            ordered.extend((0..count).map(|index| {
                Proposition::Implies(
                    Box::new(antecedent.clone()),
                    Box::new(loadable_exists(
                        &memory,
                        "unrelated",
                        Variable(208_000 + index),
                        &format!("unrelated-implication-{index}"),
                        None,
                        4,
                    )),
                )
            }));
            let facts = ProofFacts::from_ordered(&ordered);
            crate::kernel::proof::reset_alpha_proposition_key_visits();
            assert!(facts.contains_discharged_implication_consequent(&required));
            visits.push(crate::kernel::proof::alpha_proposition_key_visits());
        }
        assert!(
            visits.windows(2).all(|pair| pair[0] == pair[1]),
            "{visits:?}"
        );
    }

    #[test]
    fn quantified_loadable_alpha_index_query_does_not_scan_unrelated_facts() {
        let memory = CMemory::new().with_block("quantified-viewable-scale", 32);
        let source = loadable_forall(
            &memory,
            Variable(208_000),
            "quantified-viewable-scale",
            Some(Variable(208_001)),
            4,
        );
        let required = loadable_forall(
            &memory,
            Variable(208_100),
            "quantified-viewable-scale",
            Some(Variable(208_001)),
            4,
        );
        let mut visits = Vec::new();
        for count in [8usize, 16, 32, 64] {
            let mut ordered = vec![source.clone()];
            ordered.extend((0..count).map(|index| {
                loadable_forall(
                    &memory,
                    Variable(208_200 + index as u64),
                    "unrelated-viewable",
                    Some(Variable(208_201 + index as u64)),
                    4,
                )
            }));
            let facts = ProofFacts::from_ordered(&ordered);
            crate::kernel::proof::reset_alpha_proposition_key_visits();
            assert!(facts.matching_fact_across_effects(&required, &[]).is_some());
            visits.push(crate::kernel::proof::alpha_proposition_key_visits());
        }
        assert!(
            visits.windows(2).all(|pair| pair[1] == pair[0]),
            "{visits:?}"
        );
    }

    #[test]
    fn quantified_loadable_alpha_query_ignores_unrelated_snapshot_size() {
        let mut work = Vec::new();
        for size in [8usize, 16, 32, 64] {
            let mut source_memory = CMemory::new();
            for index in 0..size {
                source_memory =
                    source_memory.with_block(format!("quantified-viewable-work-{index}"), 8);
            }
            source_memory = source_memory.store(
                Pointer {
                    block: "quantified-viewable-work-0".into(),
                    offset: PointerOffsetTerm::Constant(0),
                },
                CValue::Int32(Bitvector32Term::Variable(Variable(209_000))),
            );
            let source = loadable_forall(
                &source_memory,
                Variable(209_000),
                "quantified-viewable-work-0",
                Some(Variable(209_001)),
                4,
            );
            let required = loadable_forall(
                &source_memory,
                Variable(209_100),
                "quantified-viewable-work-0",
                Some(Variable(209_001)),
                4,
            );
            let facts = ProofFacts::from_ordered(std::slice::from_ref(&source));
            let (matched, measured) = crate::instrumentation::measure_deterministic_work(|| {
                facts.matching_quantified_fact(&required)
            });
            assert_eq!(matched, Some(source.clone()));
            work.push(measured);
        }
        for pair in work.windows(2) {
            assert_eq!(pair[1], pair[0], "{work:?}");
        }
    }

    #[test]
    fn quantified_loadable_alpha_budget_fails_closed_before_memory_substitution() {
        let memory = CMemory::new().with_block("quantified-viewable-budget", 8);
        let source = loadable_forall(
            &memory,
            Variable(210_000),
            "quantified-viewable-budget",
            None,
            4,
        );
        let renamed = loadable_forall(
            &memory,
            Variable(210_100),
            "quantified-viewable-budget",
            None,
            4,
        );
        let tactic = crate::instrumentation::TacticEvent {
            claim: "quantified_loadable_alpha_budget".into(),
            tactic_index: 0,
            tactic_name: "quantified_loadable_alpha_budget".into(),
            class: "simple".into(),
            statement_index: 0,
            source_index: 0,
        };
        let limits = crate::instrumentation::TacticWorkLimits {
            simple: 1,
            smart: 1,
            control: 1,
        };
        let ((equivalent, work), events) =
            crate::instrumentation::with_tactic_work_limits(limits, || {
                crate::instrumentation::collect(|| {
                    crate::instrumentation::emit(
                        crate::instrumentation::VerificationEvent::TacticStarted(tactic.clone()),
                    );
                    let result = crate::instrumentation::measure_deterministic_work(|| {
                        crate::kernel::proof::fact_keys::snapshot_quantified_alpha_equivalent(
                            &source, &renamed,
                        )
                    });
                    crate::instrumentation::emit(
                        crate::instrumentation::VerificationEvent::TacticFailed(tactic.clone()),
                    );
                    result
                })
            });
        assert_eq!(equivalent, Some(false));
        assert!(work <= 4, "budgeted alpha comparison exceeded work: {work}");
        assert!(events.iter().any(|event| matches!(
            event,
            crate::instrumentation::VerificationEvent::TacticWorkBudgetExceeded { .. }
        )));
    }

    #[test]
    fn integer_alpha_fact_lookup_rejects_inequality_kind_truth_and_free_binder_mismatches() {
        let source = fold(
            integer_index(),
            Variable(200_600),
            Variable(200_601),
            IntegerTerm::add(
                IntegerTerm::var(Variable(200_600)),
                IntegerTerm::var(Variable(200_601)),
            ),
        );
        let required = fold(
            integer_index(),
            Variable(200_700),
            Variable(200_701),
            IntegerTerm::add(
                IntegerTerm::var(Variable(200_700)),
                IntegerTerm::var(Variable(200_701)),
            ),
        );
        let source_fact = less_equal(source, IntegerTerm::constant_i64(9));
        let wrong_kind = less_than(required.clone(), IntegerTerm::constant_i64(9));
        let false_fact = Proposition::ConditionIs(
            ConditionTerm::IntegerLessEqual(required.into(), IntegerTerm::constant_i64(9).into()),
            false,
        );
        let free_binder = less_equal(
            fold(
                integer_index(),
                Variable(200_700),
                Variable(200_701),
                IntegerTerm::add(
                    IntegerTerm::var(Variable(200_700)),
                    IntegerTerm::var(Variable(200_999)),
                ),
            ),
            IntegerTerm::constant_i64(9),
        );
        let facts = ProofFacts::from_ordered(std::slice::from_ref(&source_fact));

        for candidate in [wrong_kind, false_fact, free_binder] {
            assert!(
                facts
                    .matching_fact_across_effects(&candidate, &[])
                    .is_none()
            );
            assert!(!facts.exact_available_across_effects(&candidate, &[]));
            assert!(!facts.pure_assumption_available(&candidate));
        }
    }

    #[test]
    fn integer_alpha_fact_lookup_rejects_free_bound_and_carrier_mismatches() {
        let accumulator = Variable(201_000);
        let item = Variable(201_001);
        let source = fold(
            integer_index(),
            accumulator,
            item,
            IntegerTerm::add(IntegerTerm::var(accumulator), IntegerTerm::var(item)),
        );
        let source_fact = equality(IntegerTerm::constant_i64(9), source);

        let free_mismatch = fold(
            integer_index(),
            Variable(201_100),
            Variable(201_101),
            IntegerTerm::add(
                IntegerTerm::var(Variable(201_100)),
                IntegerTerm::var(Variable(201_999)),
            ),
        );
        let bound_mismatch = fold(
            integer_index(),
            Variable(202_000),
            Variable(202_001),
            IntegerTerm::add(
                IntegerTerm::var(Variable(202_001)),
                IntegerTerm::constant_i64(1),
            ),
        );
        let carrier_mismatch = fold(
            int32_index(),
            accumulator,
            item,
            IntegerTerm::add(
                IntegerTerm::var(accumulator),
                IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                    MachineIntegerType::Int32,
                    Bitvector32Term::Variable(item),
                )),
            ),
        );

        let facts = ProofFacts::from_ordered(std::slice::from_ref(&source_fact));
        for candidate in [free_mismatch, bound_mismatch, carrier_mismatch] {
            let required = equality(IntegerTerm::constant_i64(9), candidate);
            assert!(facts.matching_fact_across_effects(&required, &[]).is_none());
            assert!(!facts.exact_available_across_effects(&required, &[]));
        }
    }

    #[test]
    fn integer_alpha_fact_lookup_requires_the_same_load_snapshot() {
        let before =
            crate::kernel::intern_c_memory(CMemory::new().with_block("snapshot-alpha-facts", 8));
        let changed = crate::kernel::intern_c_memory(before.as_ref().clone().store(
            Pointer {
                block: "snapshot-alpha-facts".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            CValue::Int32(Bitvector32Term::Constant(7)),
        ));
        let source_fact = equality(
            IntegerTerm::constant_i64(9),
            explicit_load_fold(&before, Variable(206_000), Variable(206_001)),
        );
        let renamed_fact = equality(
            IntegerTerm::constant_i64(9),
            explicit_load_fold(&before, Variable(206_100), Variable(206_101)),
        );
        let changed_snapshot_fact = equality(
            IntegerTerm::constant_i64(9),
            explicit_load_fold(&changed, Variable(206_100), Variable(206_101)),
        );
        let facts = ProofFacts::from_ordered(std::slice::from_ref(&source_fact));

        assert_eq!(
            facts.matching_fact_across_effects(&renamed_fact, &[]),
            Some(source_fact)
        );
        assert!(
            facts
                .matching_fact_across_effects(&changed_snapshot_fact, &[])
                .is_none()
        );
    }

    #[test]
    fn integer_alpha_fact_lookup_ignores_unrelated_facts_without_scanning_them() {
        let source = fold(
            integer_index(),
            Variable(203_000),
            Variable(203_001),
            IntegerTerm::add(
                IntegerTerm::var(Variable(203_000)),
                IntegerTerm::var(Variable(203_001)),
            ),
        );
        let required = fold(
            integer_index(),
            Variable(203_100),
            Variable(203_101),
            IntegerTerm::add(
                IntegerTerm::var(Variable(203_100)),
                IntegerTerm::var(Variable(203_101)),
            ),
        );
        let source_fact = equality(IntegerTerm::constant_i64(9), source);
        let required_fact = equality(IntegerTerm::constant_i64(9), required);

        let mut small = vec![source_fact.clone()];
        small.extend((0..8).map(unrelated_fact));
        let mut large = vec![source_fact];
        large.extend((0..128).map(|value| unrelated_fact(value + 100)));
        let small_facts = ProofFacts::from_ordered(&small);
        let large_facts = ProofFacts::from_ordered(&large);

        crate::kernel::proof::reset_alpha_proposition_key_visits();
        assert!(
            small_facts
                .matching_fact_across_effects(&required_fact, &[])
                .is_some()
        );
        let small_visits = crate::kernel::proof::alpha_proposition_key_visits();
        crate::kernel::proof::reset_alpha_proposition_key_visits();
        assert!(
            large_facts
                .matching_fact_across_effects(&required_fact, &[])
                .is_some()
        );
        let large_visits = crate::kernel::proof::alpha_proposition_key_visits();
        assert_eq!(small_visits, large_visits);
    }

    #[test]
    fn integer_alpha_index_skips_growing_scalar_certificate_facts() {
        let mut samples = Vec::new();
        for depth in [8usize, 16, 32, 64] {
            let scalar = growing_shared_scalar_dag(depth);
            let facts = (0..depth)
                .map(|value| equality(scalar.clone(), IntegerTerm::constant_i64(value as i64)))
                .collect::<Vec<_>>();

            crate::kernel::proof::reset_alpha_proposition_key_visits();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut index: PersistentMap<
                    u64,
                    PersistentSequence<IntegerConditionAlphaCandidate>,
                > = PersistentMap::default();
                for fact in &facts {
                    index = index_integer_condition_fact(index, fact);
                }
                index
            });
            assert_eq!(
                crate::kernel::proof::alpha_proposition_key_visits(),
                0,
                "scalar certificate facts must stay off the fold alpha index"
            );
            samples.push(work);
        }
        for pair in samples.windows(2) {
            assert!(pair[1] <= pair[0] * 3 + 32, "{samples:?}");
        }
    }

    #[test]
    fn integer_alpha_index_keeps_one_source_for_renamed_fold_restatements() {
        let mut samples = Vec::new();
        for depth in [8usize, 16, 32, 64] {
            let (index, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut index: PersistentMap<
                    u64,
                    PersistentSequence<IntegerConditionAlphaCandidate>,
                > = PersistentMap::default();
                for restatement in 0..depth {
                    let accumulator = Variable(205_000 + restatement as u64 * 2);
                    let item = Variable(205_001 + restatement as u64 * 2);
                    let fold = fold(
                        integer_index(),
                        accumulator,
                        item,
                        IntegerTerm::add(IntegerTerm::var(accumulator), IntegerTerm::var(item)),
                    );
                    index = index_integer_condition_fact(
                        index,
                        &equality(IntegerTerm::constant_i64(9), fold),
                    );
                }
                index
            });
            let representative = equality(
                IntegerTerm::constant_i64(9),
                fold(
                    integer_index(),
                    Variable(205_000),
                    Variable(205_001),
                    IntegerTerm::add(
                        IntegerTerm::var(Variable(205_000)),
                        IntegerTerm::var(Variable(205_001)),
                    ),
                ),
            );
            let key = integer_condition_alpha_key(&representative)
                .expect("fold equality should be alpha-indexed")
                .fingerprint();
            let bucket = index.get(&key).expect("representative bucket");
            assert_eq!(
                bucket.len(),
                1,
                "renamed folds must not grow one alpha bucket"
            );
            assert_eq!(bucket.iter().next().unwrap().proposition, representative);
            samples.push(work);
        }
        for pair in samples.windows(2) {
            assert!(pair[1] <= pair[0] * 3 + 32, "{samples:?}");
        }
    }

    #[test]
    fn proper_conjunct_index_walks_deep_conjunction_iteratively() {
        let leaf = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::Constant(0)),
                Box::new(Bitvector32Term::Constant(0)),
            ),
            true,
        );
        let mut fact = leaf.clone();
        for _ in 0..10_000 {
            fact = Proposition::And(Box::new(leaf.clone()), Box::new(fact));
        }
        let (indexed, work) = crate::instrumentation::measure_deterministic_work(|| {
            index_proper_conjuncts(PersistentSet::default(), &fact)
        });
        assert!(indexed.contains(&leaf));
        assert!(work > 0);
    }

    #[test]
    fn snapshot_blind_same_bucket_lookup_scales_without_deep_dedup() {
        let mut samples = Vec::new();
        for size in [4usize, 16, 64, 128] {
            let mut memories = Vec::with_capacity(size + 1);
            let base = CMemory::new().with_block("same-bucket-facts", 8);
            for value in 0..=size {
                let memory = base.clone().store(
                    Pointer {
                        block: "same-bucket-facts".into(),
                        offset: PointerOffsetTerm::Constant(0),
                    },
                    CValue::Int32(Bitvector32Term::Constant(value as u32)),
                );
                memories.push(crate::kernel::intern_c_memory(memory));
            }
            let load = |memory: &crate::kernel::SharedCMemory| {
                Bitvector32Term::MemoryLoad(
                    memory.clone(),
                    Box::new(Pointer {
                        block: "same-bucket-facts".into(),
                        offset: PointerOffsetTerm::Constant(0),
                    }),
                )
            };
            let facts = memories[..size]
                .iter()
                .map(|memory| {
                    Proposition::ConditionIs(
                        ConditionTerm::Bitvector32Equal(
                            Box::new(load(memory)),
                            Box::new(Bitvector32Term::Constant(0)),
                        ),
                        true,
                    )
                })
                .collect::<Vec<_>>();
            let required = Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(
                    Box::new(load(memories.last().unwrap())),
                    Box::new(Bitvector32Term::Constant(0)),
                ),
                true,
            );
            let proof_facts = ProofFacts::from_ordered(&facts);
            let key = snapshot_blind_proposition_key(&required);
            let bucket_len = proof_facts
                .by_snapshot_blind
                .get(&key)
                .map(PersistentSequence::len)
                .unwrap_or(0);
            assert_eq!(bucket_len, size);
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                assert!(!proof_facts.exact_available_across_effects(&required, &[]));
            });
            samples.push(work);
        }
        for pair in samples.windows(2) {
            assert!(pair[1] >= pair[0]);
            assert!(pair[1] <= pair[0] * 8 + 32, "{samples:?}");
        }
    }
}
