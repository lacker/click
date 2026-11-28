//! Persistent semantic fact state for checked proofs.

mod presentation;
use presentation::FactPresentation;
mod selected_atoms;
pub(in crate::kernel) use selected_atoms::clear_selected_atom_cache;

use super::fact_keys::{IntegerConditionAlphaKey, integer_condition_alpha_key};
use super::fact_reasoning::*;
use super::{
    MemoryErasedPropositionKey, PersistentSequence, QuantifiedEquivalenceKey,
    memory_erased_proposition_key, quantified_equivalence_index_key,
};
use crate::kernel::CompareRelation;
use crate::kernel::assumptions::observation_comparisons::PropositionKey;
use crate::kernel::binary_node;
use crate::kernel::binary_term;
use crate::kernel::*;
use crate::kernel::{OffsetTree, OffsetView};
use crate::kernel::{bits32_constant, constant_u32};
use crate::persistent::{PersistentMap, PersistentSet};
use std::collections::{BTreeSet, HashMap};
use std::hash::{Hash, Hasher};
use std::sync::Arc;

/// Separation describes physical regions, not authority to access them. Keep
/// the address, endpoints, index domain and width exact, but omit the carrier
/// ancestry that ownership and typed access must continue to distinguish.
/// This key is only for memory/memory separation, never containment or views.
fn spatial_separation_key(fact: &Proposition) -> Option<Proposition> {
    let Proposition::ResourceSeparate { left, right } = fact else {
        return None;
    };
    let (Resource::Memory(left), Resource::Memory(right)) = (&**left, &**right) else {
        return None;
    };
    Some(Proposition::ResourceSeparate {
        left: Box::new(Resource::Memory(left.spatial_key())),
        right: Box::new(Resource::Memory(right.spatial_key())),
    })
}

#[cfg(test)]
mod constant_truth_tests {
    use super::*;

    #[test]
    fn equivalent_false_polarities_are_available_only_in_their_scope() {
        let positive_false = Proposition::condition_is(OldConditionTerm::Constant(false), true);
        let negative_true = Proposition::condition_is(OldConditionTerm::Constant(true), false);
        let root = PureFactStore::from_ordered(&[]);
        let true_branch = root.with_fact(Proposition::condition_is(
            OldConditionTerm::Constant(true),
            true,
        ));
        for (held, requested) in [
            (&positive_false, &negative_true),
            (&negative_true, &positive_false),
        ] {
            let branch = root.with_fact(held.clone());
            assert!(branch.pure_known_available(requested));
            assert!(!root.pure_known_available(requested));
            assert!(!true_branch.pure_known_available(requested));
        }
    }

    #[test]
    fn either_false_polarity_is_a_contradiction() {
        let positive_false = Proposition::condition_is(OldConditionTerm::Constant(false), true);
        let negative_true = Proposition::condition_is(OldConditionTerm::Constant(true), false);
        let root = PureFactStore::from_ordered(&[]);
        for held in [&positive_false, &negative_true] {
            let branch = root.with_fact(held.clone());
            for cited in [&positive_false, &negative_true] {
                assert!(branch.contradicts(cited));
            }
        }
        assert!(!root.contradicts(&positive_false));
        assert!(!root.contradicts(&negative_true));
    }

    #[test]
    fn integer_equality_and_disequality_are_exact_opposites_in_their_branch() {
        let a: crate::kernel::SharedIntegerTerm =
            crate::kernel::IntegerTerm::Variable(Variable(901_001)).into();
        let b: crate::kernel::SharedIntegerTerm =
            crate::kernel::IntegerTerm::Variable(Variable(901_002)).into();
        let equality =
            Proposition::condition_is(OldConditionTerm::IntegerEqual(a.clone(), b.clone()), true);
        let root = PureFactStore::from_ordered(std::slice::from_ref(&equality));
        assert!(!root.contradicts(&equality));
        for (left, right) in [(a.clone(), b.clone()), (b, a)] {
            let disequality =
                Proposition::condition_is(OldConditionTerm::IntegerNotEqual(left, right), true);
            let branch = root.with_fact(disequality.clone());
            assert!(branch.contradicts(&equality));
            assert!(branch.contradicts(&disequality));
            assert!(!root.contradicts(&equality));
        }
    }
}

#[cfg(test)]
thread_local! {
    static INDEXED_FACT_ENTRIES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static STATEMENT_PRIORITY_ENTRIES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static STATEMENT_PRIORITY_MAX_SUFFIX: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static STATEMENT_PRIORITY_NONLOCAL_BATCHES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static MATERIALIZED_FACT_ENTRIES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn take_fact_entry_counts() -> (usize, usize) {
    (
        INDEXED_FACT_ENTRIES.with(|count| count.replace(0)),
        MATERIALIZED_FACT_ENTRIES.with(|count| count.replace(0)),
    )
}

#[cfg(test)]
pub(crate) fn take_statement_priority_entries() -> (usize, usize, usize) {
    (
        STATEMENT_PRIORITY_ENTRIES.with(|count| count.replace(0)),
        STATEMENT_PRIORITY_MAX_SUFFIX.with(|count| count.replace(0)),
        STATEMENT_PRIORITY_NONLOCAL_BATCHES.with(|count| count.replace(0)),
    )
}

#[cfg(test)]
thread_local! {
    static RESERVED_FACT_VARIABLES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// The variables facts handed to their fact sets' reservations on this
/// thread so far, beyond those of states already reserved.
#[cfg(test)]
pub(crate) fn reserved_fact_variable_entries() -> usize {
    RESERVED_FACT_VARIABLES.with(std::cell::Cell::get)
}

/// Adds `fact`'s variables to `pending` and the states they reserve to
/// `retained_states`: afterwards every variable `proposition_variables(fact)`
/// lists is in `reserved` or `pending`, and every state named in
/// `retained_states` has all its variables there. Several facts accumulate into
/// one plain set, so a variable many of them mention costs one persistent
/// insertion when the caller commits `pending`.
fn reserve_fact_variables(
    fact: &Proposition,
    reserved: &PersistentSet<Variable>,
    pending: &mut BTreeSet<Variable>,
    retained_states: &mut crate::kernel::reasoning::variable_collection::ReservedStates,
) {
    // Only the debug cross-check reads the already reserved set.
    #[cfg(not(debug_assertions))]
    let _ = reserved;
    #[cfg(debug_assertions)]
    let before = crate::instrumentation::lazy_reservation_cross_checks_enabled().then(|| {
        let mut whole = BTreeSet::new();
        crate::instrumentation::uncharged_debug_check(|| {
            whole = crate::kernel::proposition_variables(fact);
        });
        (pending.clone(), whole)
    });
    let variables = crate::kernel::reasoning::variable_collection::proposition_variables_reserving(
        fact,
        retained_states,
    );
    #[cfg(test)]
    RESERVED_FACT_VARIABLES.with(|count| count.set(count.get() + variables.len()));
    pending.extend(variables);
    #[cfg(debug_assertions)]
    if let Some((earlier, whole)) = before {
        assert!(
            whole
                .iter()
                .all(|variable| reserved.contains(variable) || pending.contains(variable))
                && pending
                    .iter()
                    .all(|variable| earlier.contains(variable) || whole.contains(variable)),
            "a fact's reserved variables differ from its whole collection"
        );
    }
}

/// `reserved` with every variable of `pending` added.
/// `highest_witness` is raised to the highest witness added.
fn commit_reserved_variables(
    mut reserved: PersistentSet<Variable>,
    pending: BTreeSet<Variable>,
    highest_witness: &mut Option<u64>,
) -> PersistentSet<Variable> {
    for variable in pending {
        if variable.is_witness() {
            *highest_witness = (*highest_witness).max(Some(variable.0));
        }
        if !reserved.contains(&variable) {
            reserved = reserved.with_value(variable);
        }
    }
    reserved
}

/// Persistent semantic fact state shared by every checked proof kind.
///
/// The exact index serves local proof-step queries and `assumptions` retains
/// the kernel's incrementally updated reasoning context. Forking shares both;
/// adding one fact copies only logarithmic index/context paths.
#[derive(Clone, Default)]
pub(crate) struct PureFactStore {
    ordered: PersistentSequence<Arc<Proposition>>,
    reserved_variables: PersistentSet<Variable>,
    /// The highest witness `reserved_variables` holds, maintained as
    /// variables are reserved so a new witness is found without a scan.
    highest_reserved_witness: Option<u64>,
    /// The interned states whose every variable `reserved_variables`
    /// holds, so a fact naming one again, or naming a state derived from
    /// one, reserves only what differs (`proposition_variables_reserving`).
    reserved_states: crate::kernel::reasoning::variable_collection::ReservedStates,
    statement_batches: Option<Arc<StatementFactBatch>>,
    top_level_exact: PersistentSet<Arc<Proposition>>,
    /// Shared occurrence and unique-order indexes, with strict syntax selection.
    presentation: FactPresentation,
    exact: PersistentSet<Arc<Proposition>>,
    /// Exact typed call payloads ignore only the native/shared argument
    /// carrier choice; they retain state, argument order and type keys.
    call_payloads: PersistentSet<CallPayloadKey>,
    /// Every strict subtree of an available top-level conjunction. This is
    /// used for selected conjunction sources; top-level facts are not
    /// included merely because they are independently available.
    proper_conjuncts: PersistentSet<PropositionKey>,
    /// The quantified atomic conjuncts of available conjunctions, keyed by
    /// their alpha form: quantifier binders are numbered per lowering, so a
    /// citation of the second universal of a conjunction lowers with other
    /// binder numbers than the conjunct it names.
    quantified_proper_conjuncts:
        PersistentMap<QuantifiedEquivalenceKey, PersistentSequence<Arc<Proposition>>>,
    /// Atomic exact facts after the same direct-load normalization used by
    /// condition check. This lets a branch reject its opposite path with an
    /// indexed lookup instead of scanning every unrelated fact.
    by_memory_erased:
        PersistentMap<MemoryErasedPropositionKey, PersistentSequence<Arc<Proposition>>>,
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
    guarded_implications_by_atom:
        PersistentMap<BitvectorEqualityAtomKey, PersistentSequence<Arc<Proposition>>>,
    /// True finite-float classifications retain their shared fact identity so
    /// a reflexive comparison does not publish the same premise twice.
    finite_classifications_by_key:
        PersistentMap<MemoryErasedPropositionKey, PersistentSequence<Arc<Proposition>>>,
    /// Exact algebraic equalities keyed by their root terms.  Goal-local
    /// constructor disequality rewrites need the variable-to-constructor
    /// premise without scanning unrelated proposition facts.
    algebraic_equalities_by_term:
        PersistentMap<AlgebraicTerm, PersistentSequence<Arc<Proposition>>>,
    by_quantified_equivalence:
        PersistentMap<QuantifiedEquivalenceKey, PersistentSequence<Arc<Proposition>>>,
    /// Full snapshot-aware alpha identities for explicit quantified inputs.
    /// Built with each fact, so a simple lookup never forces a deferred
    /// assumptions index or visits a related-fact bucket.
    by_quantified_identity: PersistentMap<super::PropositionIdentityKey, Arc<Proposition>>,
    /// Guarded universals whose conclusion is a conjunction, keyed by the
    /// alpha form of each proper sub-conjunction restated under the same
    /// binder and guards: `forall k { G implies A and B }` is found under
    /// `forall k { G implies A }`. A goal of that shape selects its source
    /// with one probe; unrelated universals are never visited.
    quantified_conjunct_projections:
        PersistentMap<QuantifiedEquivalenceKey, PersistentSequence<Arc<Proposition>>>,
    implications_by_consequent:
        PersistentMap<MemoryErasedPropositionKey, PersistentSequence<ImplicationCandidate>>,
    /// Alpha-invariant selection for quantified implication consequents.
    /// Checked equivalence still guards state and free-variable identity.
    implications_by_quantified_consequent:
        PersistentMap<QuantifiedEquivalenceKey, PersistentSequence<ImplicationCandidate>>,
    assumptions: PureFactContext,
    implicit_transport_assumptions: PureFactContext,
    by_predicate: PersistentMap<String, PersistentSequence<Arc<Proposition>>>,
}

/// An introduction log for statement ancestry and explicit-delta queries.
/// Presentation order and proposition ownership stay in the store's indexes.
struct StatementFactBatch {
    parent: Option<Arc<StatementFactBatch>>,
    introduced: Arc<Vec<Arc<Proposition>>>,
}

/// One indexed prefix of an available implication chain. The consequent key
/// selects this small candidate; checking still validates every antecedent
/// and the exact or alpha-equivalent quantified consequent.
#[derive(Clone)]
struct ImplicationCandidate {
    antecedents: PersistentSequence<Proposition>,
    consequent: Proposition,
    /// For an entry filed under one conjunct of a conjunctive consequent,
    /// that whole consequent. Such an entry serves only the search for a
    /// conjunct (`discharged_implication_containing`); the `extract` rule's
    /// own lookup reads the entries without one.
    whole: Option<Proposition>,
}

#[derive(Clone)]
struct IntegerConditionAlphaCandidate {
    key: IntegerConditionAlphaKey,
    proposition: Proposition,
}

/// A bounded-comparison selector for equality rewrite derivations. Complex
/// arithmetic operands remain on the kernel-derivation path; this index covers
/// the atomic value/state operands that outcome arithmetic rewrites need.
#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum BitvectorEqualityAtomKey {
    Constant(u32),
    Variable(Variable),
    PointerReadSource(u64),
    ClickFunctionApplication {
        name: String,
        arguments_hash: u64,
        // Keep ID-based numeric keys alive as long as the indexed fact.
        machine_identities: Vec<SharedMachineIntegerTerm>,
    },
    MemoryLoad {
        memory: (u32, u32),
        pointer_hash: u64,
    },
    /// A slice application's count, by its application's identity; holding
    /// the application keeps the identity alive as long as the indexed fact.
    PureApplicationCount(crate::kernel::SharedPureApplication),
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum AlgebraicCallOperandKey {
    Call(AlgebraicType, SharedPureApplication),
    Variable(AlgebraicType, Variable),
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum CallPayloadKey {
    Machine(
        MachineIntegerType,
        u8,
        bool,
        [crate::kernel::equality_graph::MachineAtom; 2],
    ),
    AlgebraicCondition(bool, [AlgebraicCallOperandKey; 2]),
    AlgebraicEquation([AlgebraicCallOperandKey; 2]),
}

fn call_payload_identity_key(fact: &Proposition) -> Option<CallPayloadKey> {
    fn algebraic(term: &AlgebraicTerm) -> Option<AlgebraicCallOperandKey> {
        Some(match &term.node {
            AlgebraicTermNode::PureFunctionApplication { name, arguments } => {
                AlgebraicCallOperandKey::Call(
                    term.algebraic_type.clone(),
                    SharedPureApplication::intern(name.clone(), arguments.clone()),
                )
            }
            AlgebraicTermNode::Variable(variable) => {
                AlgebraicCallOperandKey::Variable(term.algebraic_type.clone(), *variable)
            }
            _ => return None,
        })
    }
    let machine_call =
        |term: &OldMachineTerm| matches!(term, OldMachineTerm::ClickFunctionApplication { .. });
    let algebraic_call = |term: &AlgebraicTerm| {
        matches!(term.node, AlgebraicTermNode::PureFunctionApplication { .. })
    };
    Some(match fact {
        condition_source_0 @ Proposition::ConditionIs(_, truth)
            if let Some((
                OldConditionTerm::Compare {
                    format,
                    relation,
                    left,
                    right,
                },
                _,
            )) = condition_source_0.old_condition()
                && (machine_call(left) || machine_call(right)) =>
        {
            CallPayloadKey::Machine(
                *format,
                *relation as u8,
                *truth,
                [
                    crate::kernel::equality_graph::MachineAtom::from_operand(
                        *format,
                        MachineOperandView::Old(left),
                    ),
                    crate::kernel::equality_graph::MachineAtom::from_operand(
                        *format,
                        MachineOperandView::Old(right),
                    ),
                ],
            )
        }
        condition_source_0 @ Proposition::ConditionIs(_, truth)
            if let Some((OldConditionTerm::AlgebraicEqual(left, right), _)) =
                condition_source_0.old_condition()
                && (algebraic_call(left) || algebraic_call(right)) =>
        {
            CallPayloadKey::AlgebraicCondition(*truth, [algebraic(left)?, algebraic(right)?])
        }
        Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right))
            if algebraic_call(left.old_form()) || algebraic_call(right.old_form()) =>
        {
            CallPayloadKey::AlgebraicEquation([
                algebraic(left.old_form())?,
                algebraic(right.old_form())?,
            ])
        }
        _ => return None,
    })
}

fn index_call_payload(
    keys: PersistentSet<CallPayloadKey>,
    fact: &Proposition,
) -> PersistentSet<CallPayloadKey> {
    match call_payload_identity_key(fact) {
        Some(key) => keys.with_value(key),
        None => keys,
    }
}

/// Borrowed access to proposition premises. Persistent proofs supply their
/// existing indexes; source/setup slices retain their ordered boundary view.
/// This interface owns neither proof state nor completion evidence.
pub(crate) trait PropositionSource {
    fn propositions(&self) -> impl Iterator<Item = &Proposition>;
    fn pure_context(&self) -> PureFactContext {
        self.propositions()
            .inspect(|_| crate::kernel::reasoning::path_facts::count_context_rebuild_entries(1))
            .map(crate::kernel::clone_proposition_iteratively)
            .fold(PureFactContext::new(), PureFactContext::assume_proposition)
    }
    fn exact_available(&self, required: &Proposition) -> bool {
        self.propositions()
            .any(|fact| exact_fact_contains_conjunct(fact, required))
    }
    fn ordered_fact_store(&self) -> PureFactStore {
        self.fact_store()
    }
    /// Retain a source's available facts and reasoning state directly.
    /// Explicit input sequences construct a scope; retained sources share one.
    fn fact_store(&self) -> PureFactStore {
        PureFactStore::from_source_retaining_reservations(self, None)
    }
}
impl<T: PropositionSource + ?Sized> PropositionSource for &T {
    fn propositions(&self) -> impl Iterator<Item = &Proposition> {
        (**self).propositions()
    }
    fn pure_context(&self) -> PureFactContext {
        (**self).pure_context()
    }
    fn exact_available(&self, required: &Proposition) -> bool {
        (**self).exact_available(required)
    }
    fn fact_store(&self) -> PureFactStore {
        (**self).fact_store()
    }
    fn ordered_fact_store(&self) -> PureFactStore {
        (**self).ordered_fact_store()
    }
}
impl<T: PropositionSource + ?Sized> PropositionSource for Arc<T> {
    fn propositions(&self) -> impl Iterator<Item = &Proposition> {
        (**self).propositions()
    }
    fn pure_context(&self) -> PureFactContext {
        (**self).pure_context()
    }
    fn exact_available(&self, required: &Proposition) -> bool {
        (**self).exact_available(required)
    }
    fn fact_store(&self) -> PureFactStore {
        (**self).fact_store()
    }
    fn ordered_fact_store(&self) -> PureFactStore {
        (**self).ordered_fact_store()
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
impl PropositionSource for PureFactStore {
    fn propositions(&self) -> impl Iterator<Item = &Proposition> {
        self.presentation.unique_iter()
    }
    fn ordered_fact_store(&self) -> PureFactStore {
        self.unique_presentation()
    }
    fn pure_context(&self) -> PureFactContext {
        self.assumptions().clone()
    }
    fn exact_available(&self, required: &Proposition) -> bool {
        self.contains(required) || self.matching_quantified_fact(required).is_some()
    }
    fn fact_store(&self) -> PureFactStore {
        self.clone()
    }
}

/// Whether `proposition` equates two constructors of different variants of
/// one algebraic type, which no value satisfies.
pub(super) fn is_constructor_clash(proposition: &Proposition) -> bool {
    matches!(proposition,
        Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right))
            if left.old_form().algebraic_type == right.old_form().algebraic_type
                && matches!((&left.old_form().node, &right.old_form().node), (
                    AlgebraicTermNode::Constructor { variant: left, .. },
                    AlgebraicTermNode::Constructor { variant: right, .. },
                ) if left != right))
}

/// What an implication chain `a implies .. z implies c` whose consequent `c`
/// equates two constructors says once those are decided: for different
/// variants, `c` is false, so `a implies .. not z`; for one variant, `c` is
/// its fields' equalities, each `a implies .. z implies f`. Empty for any
/// other proposition.
pub(crate) fn constructor_consequent_instances(proposition: &Proposition) -> Vec<Proposition> {
    let Proposition::Implies(antecedent, consequent) = proposition else {
        return Vec::new();
    };
    if is_constructor_clash(consequent) {
        return vec![match antecedent.as_ref() {
            // The refuted condition in a positive form where one exists,
            // `x > 100` rather than `x <= 100` false, as a branch states it.
            Proposition::ConditionIs(condition, value) => {
                let refuted = Proposition::condition_is(condition.clone(), !value);
                condition_polarity_forms(&refuted)
                    .into_iter()
                    .rev()
                    .find(|form| matches!(form, Proposition::ConditionIs(_, true)))
                    .unwrap_or(refuted)
            }
            other => Proposition::Not(Box::new(other.clone())),
        }];
    }
    let inner = match crate::kernel::assumptions::algebraic_constructor_field_equalities(consequent)
    {
        Some(fields) => fields,
        None => constructor_consequent_instances(consequent),
    };
    inner
        .into_iter()
        .map(|instance| Proposition::Implies(antecedent.clone(), Box::new(instance)))
        .collect()
}

impl PureFactStore {
    pub(crate) fn len(&self) -> usize {
        self.presentation.len()
    }

    /// Strict written membership, independent of the comparison aliases
    /// admitted by checked proof queries.
    pub(crate) fn has_stated_conjunct(&self, fact: &Proposition) -> bool {
        self.presentation.has_conjunct(fact)
    }

    pub(crate) fn contains_presented(&self, fact: &Proposition) -> bool {
        self.presentation.contains(fact)
    }

    pub(crate) fn occurrences(
        &self,
    ) -> impl DoubleEndedIterator<Item = &Proposition> + ExactSizeIterator {
        self.presentation.iter()
    }

    pub(crate) fn occurrence(&self, index: usize) -> Option<&Proposition> {
        self.presentation.get(index)
    }
    pub(crate) fn unique_presentation(&self) -> Self {
        Self {
            presentation: self.presentation.unique(),
            ..self.clone()
        }
    }

    pub(crate) fn with_list_fact(&self, fact: Proposition) -> Self {
        if let Some(shared) = self.top_level_exact.get(&fact) {
            let mut successor = self.clone();
            successor.presentation.append(shared.clone());
            successor
        } else {
            self.with_fact(fact)
        }
    }

    /// Explicitly restrict the available scope. An unchanged selection keeps
    /// context lineage; a changed selection constructs a new root, never an
    /// in-place withdrawal from a branch's reasoning graph.
    pub(crate) fn retaining(&self, mut keep: impl FnMut(&Proposition) -> bool) -> Self {
        let selected = self
            .occurrences()
            .filter(|fact| keep(fact))
            .cloned()
            .collect::<Vec<_>>();
        if selected.len() == self.len() {
            return self.clone();
        }
        Self::from_source_retaining_reservations(&selected, Some(self))
    }

    /// Show only the statement's explicit premises while using the incoming
    /// proof's reasoning indexes. Branch conflicts and exact written citations
    /// still consult the selected presentation.
    pub(crate) fn statement_view(&self, facts: Vec<Proposition>) -> Self {
        let mut view = Self {
            presentation: FactPresentation::default(),
            ..self.clone()
        };
        for fact in facts {
            view = view.with_list_fact(fact);
        }
        view
    }

    /// Bounded newest-first view for diagnostics. This deliberately exposes
    /// references into the persistent sequence and never materializes the
    /// ambient proof history.
    pub(crate) fn recent_facts(&self, limit: usize) -> Vec<&Proposition> {
        self.ordered
            .recent(limit)
            .into_iter()
            .map(Arc::as_ref)
            .collect()
    }

    pub(crate) fn fact_count(&self) -> usize {
        self.ordered.len()
    }

    /// Exact premise-store identity, without comparing ambient propositions.
    pub(super) fn shares_premises_with(&self, other: &Self) -> bool {
        self.top_level_exact
            .shares_root_with(&other.top_level_exact)
    }

    pub(crate) fn shared_presented_propositions(
        &self,
    ) -> impl Iterator<Item = Arc<Proposition>> + '_ {
        self.presentation.shared_unique_iter()
    }
    pub(crate) fn is_empty(&self) -> bool {
        self.presentation.len() == 0
    }
    /// Search candidates from the ordinary quantified-fact index, independent
    /// of which proof operation introduced them. Explicit instantiation uses
    /// the selected-fact lookup instead.
    pub(crate) fn universal_facts_for_search(
        &self,
        _permission: crate::kernel::search::SearchPermission,
    ) -> impl Iterator<Item = &Proposition> {
        self.by_quantified_equivalence
            .values()
            .flat_map(|bucket| bucket.iter().map(Arc::as_ref))
            .filter(|fact| matches!(fact, Proposition::ForAll { .. }))
    }

    pub(crate) fn from_ordered(facts: &[Proposition]) -> Self {
        Self::from_source(facts)
    }

    /// Index the explicitly supplied root facts while retaining their pure
    /// context. Cached sources carry the trusted graph lineage already paired
    /// with entry resources; rebuilding it would disconnect that publication.
    /// Uncached sources build their context once through PropositionSource.
    pub(crate) fn from_source(facts: &(impl PropositionSource + ?Sized)) -> Self {
        facts.fact_store()
    }

    fn from_source_retaining_reservations(
        facts: &(impl PropositionSource + ?Sized),
        reservations: Option<&Self>,
    ) -> Self {
        let mut ordered = PersistentSequence::default();
        // A local statement scope may reserve more names than its own facts
        // mention. Sharing the enclosing scope's freshness indexes avoids
        // enumerating variables of already-retained memory states again.
        let reserved_variables = reservations.map_or_else(PersistentSet::default, |base| {
            base.reserved_variables.clone()
        });
        let mut highest_reserved_witness =
            reservations.and_then(|base| base.highest_reserved_witness);
        let mut reserved_states = reservations.map_or_else(
            crate::kernel::reasoning::variable_collection::ReservedStates::default,
            |base| base.reserved_states.clone(),
        );
        let mut top_level_exact = PersistentSet::default();
        let mut presentation = FactPresentation::default();
        let mut exact = PersistentSet::default();
        let mut call_payloads = PersistentSet::default();
        let mut proper_conjuncts = PersistentSet::default();
        let mut quantified_proper_conjuncts = PersistentMap::default();
        let mut by_memory_erased = PersistentMap::default();
        let mut by_integer_condition_alpha = PersistentMap::default();
        let mut bitvector_equalities_by_atom = PersistentMap::default();
        let mut guarded_implications_by_atom = PersistentMap::default();
        let mut finite_classifications_by_key = PersistentMap::default();
        let mut algebraic_equalities_by_term = PersistentMap::default();
        let mut by_quantified_equivalence = PersistentMap::default();
        let mut by_quantified_identity = PersistentMap::default();
        let mut quantified_conjunct_projections = PersistentMap::default();
        let mut implications_by_consequent = PersistentMap::default();
        let mut implications_by_quantified_consequent = PersistentMap::default();
        let assumptions = facts.pure_context();
        let mut implicit_transport_assumptions = PureFactContext::new();
        let mut by_predicate = PersistentMap::default();
        // Many facts read one entry memory: its variables are reserved once,
        // and the facts' variables are committed together after the loop.
        let mut pending_variables = BTreeSet::new();
        for fact in facts.propositions() {
            reserve_fact_variables(
                fact,
                &reserved_variables,
                &mut pending_variables,
                &mut reserved_states,
            );
            if let Some(shared) = top_level_exact.get(fact) {
                presentation.append(Arc::clone(shared));
                continue;
            }
            #[cfg(test)]
            INDEXED_FACT_ENTRIES.with(|count| count.set(count.get() + 1));
            // The one copy of this fact. Every index below shares it.
            let fact = &assumptions
                .shared_assumed_proposition(fact)
                .unwrap_or_else(|| Arc::new(crate::kernel::clone_proposition_iteratively(fact)));
            presentation.append(Arc::clone(fact));
            ordered.push(Arc::clone(fact));
            top_level_exact = top_level_exact.with_value(Arc::clone(fact));
            by_quantified_equivalence = index_quantified_fact(by_quantified_equivalence, fact);
            by_quantified_identity = index_quantified_identity(by_quantified_identity, fact);
            quantified_conjunct_projections =
                index_quantified_conjunct_projections(quantified_conjunct_projections, fact);
            (
                implications_by_consequent,
                implications_by_quantified_consequent,
            ) = index_implication_consequents(
                implications_by_consequent,
                implications_by_quantified_consequent,
                fact,
            );
            by_predicate = index_predicate_fact(by_predicate, fact);
            if matches!(**fact, Proposition::And(_, _)) {
                proper_conjuncts = index_proper_conjuncts(proper_conjuncts, fact);
                let mut conjuncts = Vec::new();
                collect_owned_atomic_conjuncts(fact, &mut conjuncts);
                for conjunct in conjuncts {
                    let conjunct = Arc::new(conjunct);
                    quantified_proper_conjuncts =
                        index_quantified_fact(quantified_proper_conjuncts, &conjunct);
                    by_quantified_identity =
                        index_quantified_identity(by_quantified_identity, &conjunct);
                    quantified_conjunct_projections = index_quantified_conjunct_projections(
                        quantified_conjunct_projections,
                        &conjunct,
                    );
                    by_memory_erased = index_state_fact(by_memory_erased, &conjunct);
                    by_integer_condition_alpha =
                        index_integer_condition_fact(by_integer_condition_alpha, conjunct.as_ref());
                    bitvector_equalities_by_atom =
                        index_bitvector_equality_fact(bitvector_equalities_by_atom, &conjunct);
                    finite_classifications_by_key =
                        index_finite_classification_fact(finite_classifications_by_key, &conjunct);
                    algebraic_equalities_by_term =
                        index_algebraic_equality_fact(algebraic_equalities_by_term, &conjunct);
                    call_payloads = index_call_payload(call_payloads, &conjunct);
                    if let Some(key) = spatial_separation_key(&conjunct) {
                        exact = exact.with_value(Arc::new(key));
                    }
                    exact = exact.with_value(conjunct);
                }
            }
            guarded_implications_by_atom =
                index_guarded_implication_fact(guarded_implications_by_atom, fact);
            by_memory_erased = index_state_fact(by_memory_erased, fact);
            by_integer_condition_alpha =
                index_integer_condition_fact(by_integer_condition_alpha, fact.as_ref());
            bitvector_equalities_by_atom =
                index_bitvector_equality_fact(bitvector_equalities_by_atom, fact);
            finite_classifications_by_key =
                index_finite_classification_fact(finite_classifications_by_key, fact);
            algebraic_equalities_by_term =
                index_algebraic_equality_fact(algebraic_equalities_by_term, fact);
            call_payloads = index_call_payload(call_payloads, fact);
            if let Some(key) = spatial_separation_key(fact) {
                exact = exact.with_value(Arc::new(key));
            }
            exact = exact.with_value(Arc::clone(fact));
            implicit_transport_assumptions =
                index_implicit_transport_context(implicit_transport_assumptions, fact.as_ref());
        }
        let reserved_variables = commit_reserved_variables(
            reserved_variables,
            pending_variables,
            &mut highest_reserved_witness,
        );
        let mut result = Self {
            ordered,
            reserved_variables,
            highest_reserved_witness,
            reserved_states,
            statement_batches: None,
            top_level_exact,
            presentation,
            exact,
            call_payloads,
            proper_conjuncts,
            quantified_proper_conjuncts,
            by_memory_erased,
            by_integer_condition_alpha,
            bitvector_equalities_by_atom,
            guarded_implications_by_atom,
            finite_classifications_by_key,
            algebraic_equalities_by_term,
            by_quantified_equivalence,
            by_quantified_identity,
            quantified_conjunct_projections,
            implications_by_consequent,
            implications_by_quantified_consequent,
            assumptions,
            implicit_transport_assumptions,
            by_predicate,
        };
        let consequences = result
            .assumptions
            .propagation_consequences_since(&PureFactContext::new());
        for consequence in consequences {
            let assumptions = result.assumptions.clone();
            result = result.with_indexed_fact(consequence.clone(), assumptions);
        }
        result
    }

    pub(crate) fn with_reserved_variables(
        mut self,
        variables: impl IntoIterator<Item = Variable>,
    ) -> Self {
        for variable in variables {
            if variable.is_witness() {
                self.highest_reserved_witness = self.highest_reserved_witness.max(Some(variable.0));
            }
            self.reserved_variables = self.reserved_variables.with_value(variable);
        }
        self
    }

    /// Indexed membership for fact bookkeeping and certificate construction,
    /// by the fact itself or by its comparison form
    /// (`kernel::comparison_form`), under which every fact is filed too.
    pub(crate) fn contains(&self, fact: &Proposition) -> bool {
        self.exact.contains(fact)
            || spatial_separation_key(fact).is_some_and(|key| self.exact.contains(&key))
            || call_payload_identity_key(fact).is_some_and(|key| self.call_payloads.contains(&key))
            || crate::kernel::comparison_form(fact)
                .is_some_and(|comparison| self.exact.contains(&comparison))
    }

    /// Exact alpha membership of one explicitly selected quantified fact.
    /// Conjunctions consist of the selected leaves, each an indexed query.
    pub(crate) fn contains_quantified_identity(&self, fact: &Proposition) -> bool {
        if self.contains(fact) {
            return true;
        }
        if let Proposition::And(left, right) = fact {
            return self.contains_quantified_identity(left)
                && self.contains_quantified_identity(right);
        }
        if !quantified_identity_shape(fact) {
            return false;
        }
        super::proposition_identity_key(fact)
            .and_then(|key| self.by_quantified_identity.get(&key))
            .is_some_and(|candidate| super::propositions_are_alpha_equal(candidate, fact))
    }

    /// Semantic availability for checking a requested premise or goal, as
    /// written or by its comparison form (`kernel::comparison_form`).
    pub(crate) fn available(&self, fact: &Proposition) -> bool {
        self.available_as_written(fact)
            || crate::kernel::comparison_form(fact)
                .is_some_and(|comparison| self.available_as_written(&comparison))
    }

    fn available_as_written(&self, fact: &Proposition) -> bool {
        closed_condition_holds(fact)
            || self.contains(fact)
            || self.assumptions.contains_known(fact)
            || self.contains_opposite_constant_polarity(fact)
    }

    /// Introduction and normalization can retain opposite constant
    /// polarities for the same truth claim: `false` holds, or `true` does
    /// not, as the infeasible arm of a case split on a decided condition
    /// states it. This is one equivalent fact, one exact lookup, not a search
    /// for an arbitrary contradiction.
    fn contains_opposite_constant_polarity(&self, fact: &Proposition) -> bool {
        fact.literal_condition().is_some_and(|(value, truth)| {
            self.contains(&Proposition::condition_is(
                crate::kernel::StoredConditionTerm::constant(!value),
                !truth,
            ))
        })
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

    /// A checked `have` keeps its exact judgment for replay and rewriting.
    /// Use its definitional form when adding it to the reasoning context.
    pub(crate) fn with_kernel_checked_have(&self, fact: Proposition) -> Self {
        self.with_fact_in_context(fact, true)
    }

    /// Reuse the checked path's reasoning context for the outcome, retaining
    /// the ordinary proof's premise indexes and reasoning policy. The selected
    /// statement's publication is the only ordinary delta since its entry.
    pub(super) fn with_outcome_context(
        &self,
        mut context: PureFactContext,
        entry: &Self,
    ) -> Option<Self> {
        let published = self.introduced_since(entry)?;
        context = context.with_reasoning_policy_of(&self.assumptions);
        for proposition in published {
            if !context.contains_assumed_exact(&proposition) {
                context = context.assume_proposition(proposition);
            }
        }
        Some(Self {
            assumptions: context,
            ..self.clone()
        })
    }

    /// Retain producer evidence for a read whose defining proposition was
    /// already published by the checked statement. Plain propositions and
    /// evidence outside this branch cannot introduce a typed read bridge.
    pub(crate) fn retain_checked_read_fact(&mut self, fact: &ExecutionPureFact) {
        if fact.is_certified() && fact.has_checked_pointer_read() {
            self.assumptions = self.assumptions.clone().assume_execution_pure_fact(fact);
            return;
        }
        if fact.is_certified()
            && fact.generated_load_binding().is_some()
            && self.assumptions.contains_assumed_exact(fact.proposition())
        {
            self.assumptions = self.assumptions.clone().assume_execution_pure_fact(fact);
            fact.retain_pointer_read_definition(&self.assumptions);
        }
    }

    pub(in crate::kernel) fn with_fact(&self, fact: Proposition) -> Self {
        self.with_fact_in_context(fact, false)
    }

    fn with_fact_in_context(&self, fact: Proposition, canonicalize: bool) -> Self {
        // A closed comparison that holds, which lowering retains as written
        // (`3 == 3`), carries no information the context can use: checking
        // decides it from its literals (`available_as_written`). It is still
        // a held fact with its own spelling, so membership and the ordered
        // delta record it, but it needs no search index, mentions no
        // variable, and adds nothing to the reasoning context.
        if closed_condition_holds(&fact) {
            if self.top_level_exact.contains(&fact) {
                return self.clone();
            }
            let fact = Arc::new(fact);
            let mut ordered = self.ordered.clone();
            ordered.push(Arc::clone(&fact));
            return Self {
                ordered,
                top_level_exact: self.top_level_exact.with_value(Arc::clone(&fact)),
                presentation: {
                    let mut presentation = self.presentation.clone();
                    presentation.append(fact.clone());
                    presentation
                },
                exact: self.exact.with_value(fact),
                ..self.clone()
            };
        }
        if self.top_level_exact.contains(&fact) {
            return self.clone();
        }
        let fact = Arc::new(fact);
        let context_fact = if canonicalize {
            let canonical = crate::kernel::canonical_condition_fact(&fact);
            if canonical == *fact {
                fact.clone()
            } else {
                Arc::new(canonical)
            }
        } else {
            fact.clone()
        };
        let assumptions = self
            .assumptions
            .clone()
            .assume_shared_proposition(context_fact);
        let consequences = assumptions.propagation_consequences_since(&self.assumptions);
        let mut result = self.with_indexed_fact(fact, assumptions);
        for consequence in consequences {
            let assumptions = result.assumptions.clone();
            result = result.with_indexed_fact(consequence.clone(), assumptions);
        }
        result
    }

    /// Publish a fact already constructed by admission, without asking the
    /// fact store to derive or validate that same consequence again.
    fn with_indexed_fact(&self, fact: Arc<Proposition>, assumptions: PureFactContext) -> Self {
        if self.top_level_exact.contains(&fact) {
            return self.clone();
        }
        #[cfg(test)]
        INDEXED_FACT_ENTRIES.with(|count| count.set(count.get() + 1));
        // Index the checked judgment, including when the reasoning context
        // received its definitional form.
        let mut exact = self.exact.clone();
        let mut call_payloads = self.call_payloads.clone();
        let mut proper_conjuncts = self.proper_conjuncts.clone();
        let mut quantified_proper_conjuncts = self.quantified_proper_conjuncts.clone();
        let mut by_memory_erased = self.by_memory_erased.clone();
        let mut by_integer_condition_alpha = self.by_integer_condition_alpha.clone();
        let mut bitvector_equalities_by_atom = self.bitvector_equalities_by_atom.clone();
        let mut finite_classifications_by_key = self.finite_classifications_by_key.clone();
        let mut algebraic_equalities_by_term = self.algebraic_equalities_by_term.clone();
        let by_quantified_equivalence =
            index_quantified_fact(self.by_quantified_equivalence.clone(), &fact);
        let mut by_quantified_identity =
            index_quantified_identity(self.by_quantified_identity.clone(), &fact);
        let mut quantified_conjunct_projections = index_quantified_conjunct_projections(
            self.quantified_conjunct_projections.clone(),
            &fact,
        );
        let (implications_by_consequent, implications_by_quantified_consequent) =
            index_implication_consequents(
                self.implications_by_consequent.clone(),
                self.implications_by_quantified_consequent.clone(),
                &fact,
            );
        if matches!(*fact, Proposition::And(_, _)) {
            proper_conjuncts = index_proper_conjuncts(proper_conjuncts, &fact);
            let mut conjuncts = Vec::new();
            collect_owned_atomic_conjuncts(&fact, &mut conjuncts);
            for conjunct in conjuncts {
                let conjunct = Arc::new(conjunct);
                quantified_proper_conjuncts =
                    index_quantified_fact(quantified_proper_conjuncts, &conjunct);
                by_quantified_identity =
                    index_quantified_identity(by_quantified_identity, &conjunct);
                quantified_conjunct_projections = index_quantified_conjunct_projections(
                    quantified_conjunct_projections,
                    &conjunct,
                );
                by_memory_erased = index_state_fact(by_memory_erased, &conjunct);
                by_integer_condition_alpha =
                    index_integer_condition_fact(by_integer_condition_alpha, conjunct.as_ref());
                bitvector_equalities_by_atom =
                    index_bitvector_equality_fact(bitvector_equalities_by_atom, &conjunct);
                finite_classifications_by_key =
                    index_finite_classification_fact(finite_classifications_by_key, &conjunct);
                algebraic_equalities_by_term =
                    index_algebraic_equality_fact(algebraic_equalities_by_term, &conjunct);
                call_payloads = index_call_payload(call_payloads, &conjunct);
                if let Some(key) = spatial_separation_key(&conjunct) {
                    exact = exact.with_value(Arc::new(key));
                }
                exact = exact.with_value(conjunct);
            }
        }
        let guarded_implications_by_atom =
            index_guarded_implication_fact(self.guarded_implications_by_atom.clone(), &fact);
        by_memory_erased = index_state_fact(by_memory_erased, &fact);
        by_integer_condition_alpha =
            index_integer_condition_fact(by_integer_condition_alpha, fact.as_ref());
        bitvector_equalities_by_atom =
            index_bitvector_equality_fact(bitvector_equalities_by_atom, &fact);
        finite_classifications_by_key =
            index_finite_classification_fact(finite_classifications_by_key, &fact);
        algebraic_equalities_by_term =
            index_algebraic_equality_fact(algebraic_equalities_by_term, &fact);
        call_payloads = index_call_payload(call_payloads, &fact);
        if let Some(key) = spatial_separation_key(&fact) {
            exact = exact.with_value(Arc::new(key));
        }
        exact = exact.with_value(Arc::clone(&fact));
        // Filed under its comparison form too, so a lookup of either form,
        // or of another proposition with that comparison form, finds it.
        if let Some(comparison) = crate::kernel::comparison_form(&fact) {
            exact = exact.with_value(Arc::new(comparison));
        }
        let mut ordered = self.ordered.clone();
        ordered.push(Arc::clone(&fact));
        let implicit_transport_assumptions = index_implicit_transport_context(
            self.implicit_transport_assumptions.clone(),
            fact.as_ref(),
        );
        let mut pending_variables = BTreeSet::new();
        let mut reserved_states = self.reserved_states.clone();
        reserve_fact_variables(
            fact.as_ref(),
            &self.reserved_variables,
            &mut pending_variables,
            &mut reserved_states,
        );
        let mut highest_reserved_witness = self.highest_reserved_witness;
        let reserved_variables = commit_reserved_variables(
            self.reserved_variables.clone(),
            pending_variables,
            &mut highest_reserved_witness,
        );
        Self {
            ordered,
            reserved_variables,
            highest_reserved_witness,
            reserved_states,
            statement_batches: self.statement_batches.clone(),
            top_level_exact: self.top_level_exact.with_value(Arc::clone(&fact)),
            presentation: {
                let mut presentation = self.presentation.clone();
                presentation.append(fact.clone());
                presentation
            },
            exact,
            call_payloads,
            proper_conjuncts,
            quantified_proper_conjuncts,
            by_memory_erased,
            by_integer_condition_alpha,
            bitvector_equalities_by_atom,
            guarded_implications_by_atom,
            finite_classifications_by_key,
            algebraic_equalities_by_term,
            by_quantified_equivalence,
            by_quantified_identity,
            quantified_conjunct_projections,
            implications_by_consequent,
            implications_by_quantified_consequent,
            assumptions,
            implicit_transport_assumptions,
            by_predicate: index_predicate_fact(self.by_predicate.clone(), &fact),
        }
    }

    /// A free logical-witness identity, of the witness origin no other
    /// producer mints.
    ///
    /// Scanning up from `Variable(0)` for an identity no *fact* mentions was
    /// the earlier rule, and it is wrong twice over. The facts are not the
    /// whole state a witness has to stay clear of: a C proof also carries
    /// program variables, a symbolic store, a memory state and a resource
    /// context, and `Variable(0)` is a C identity by the reserved-range
    /// registry, so the first candidate that rule tried was a live program
    /// variable of the function being proved. Taking the identity from an
    /// origin nothing else mints makes freshness structural: an identity of
    /// another origin belongs to some other producer and is never chosen, and
    /// among witnesses this picks one strictly above every witness already
    /// visible here.
    ///
    /// Work does not grow with the fact set: the store keeps its highest
    /// reserved witness as variables are reserved, and only `body_variables`,
    /// which the caller collected, is read.
    pub(super) fn fresh_universal_witness(
        &self,
        body_variables: &std::collections::BTreeSet<Variable>,
    ) -> Option<Variable> {
        let reserved_high = self.highest_reserved_witness;
        let body_high = body_variables
            .iter()
            .filter(|variable| variable.is_witness())
            .map(|variable| variable.0)
            .max();
        let next = match reserved_high.into_iter().chain(body_high).max() {
            Some(highest) => highest.checked_add(1)?,
            None => 0,
        };
        (next < crate::kernel::ExecutionBudget::UNIVERSAL_WITNESS_LIMIT)
            .then_some(Variable::witness(next))
    }

    /// The witness `intro` opens a universal over `binder` with, and the body
    /// with `binder` renamed to it. The witness is always fresh: `binder` is a
    /// quantifier's bound variable, which no free occurrence may share.
    fn opened_forall_body(
        &self,
        binder: Variable,
        sort: &Sort,
        body: &Proposition,
    ) -> Option<(Variable, Proposition)> {
        let body_variables = crate::kernel::proposition_variables(body);
        let fresh = self.fresh_universal_witness(&body_variables)?;
        let renamed =
            crate::kernel::quantifiers::rename_quantified_variable(body, binder, fresh, sort)?;
        Some((fresh, renamed))
    }

    pub(crate) fn freshen_int32_forall_body(
        &self,
        binder: Variable,
        body: &Proposition,
    ) -> Option<(Variable, Proposition)> {
        self.opened_forall_body(binder, &Sort::ProgramInt32, body)
    }

    pub(crate) fn freshen_integer_forall_body(
        &self,
        binder: Variable,
        body: &Proposition,
    ) -> Option<(Variable, Proposition)> {
        self.opened_forall_body(binder, &Sort::Integer, body)
    }

    pub(crate) fn freshen_algebraic_forall_body(
        &self,
        binder: Variable,
        algebraic_type: &crate::kernel::AlgebraicType,
        body: &Proposition,
    ) -> Option<(Variable, Proposition)> {
        self.opened_forall_body(binder, &Sort::Algebraic(algebraic_type.clone()), body)
    }

    pub(crate) fn reserves_variable(&self, variable: Variable) -> bool {
        self.reserved_variables.contains(&variable)
    }

    /// Numeric induction enters once per theorem. Check its domain from
    /// exact signed bounds on this measure, without searching other facts
    /// or deriving a replacement proof state.
    pub(crate) fn has_nonnegative_induction_domain(&self, measure: &OldMachineTerm) -> bool {
        use crate::kernel::MachineOperandView as V;
        use crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey as Key;
        let measure = Key::new(V::Old(measure));
        self.assumptions
            .signed_order_bound_views(measure.operand_view())
            .any(|(endpoint, bound, strict, forward)| {
                if forward || Key::new(endpoint) != measure {
                    return false;
                }
                let Some(bits) = bound.word32_constant() else {
                    return false;
                };
                let lower = bits as i32;
                lower >= 0 || (strict && lower == -1)
            })
    }

    /// Exact membership of false (or the equivalent negated true) in this branch.
    pub(crate) fn holds_false(&self) -> bool {
        let falsehood = Proposition::condition_is(OldConditionTerm::Constant(false), true);
        self.contains(&falsehood)
            || self.assumptions.contains_assumed_exact(&falsehood)
            || self.contains_opposite_constant_polarity(&falsehood)
    }

    /// Whether the selected fact is held in one of its exact forms.
    pub(crate) fn holds_contradiction_fact(&self, fact: &Proposition) -> bool {
        // An introduced guard is held conjunct by conjunct, so a
        // contradiction written over the whole guard finds it that way.
        let mut conjuncts = Vec::new();
        super::fact_reasoning::atomic_conjuncts(fact, &mut conjuncts);
        self.contains(fact)
            || self.contains_opposite_constant_polarity(fact)
            || super::fact_reasoning::order_claim_forms(fact)
                .iter()
                .any(|form| self.contains(form))
            || (conjuncts.len() > 1 && conjuncts.iter().all(|conjunct| self.contains(conjunct)))
    }

    pub(crate) fn contradicts(&self, fact: &Proposition) -> bool {
        let negated = Proposition::Not(Box::new(fact.clone()));
        let held = self.holds_contradiction_fact(fact);
        held && (self.contains(&negated)
            || matches!(fact, Proposition::ConditionIs(condition, value)
                    if self.contains(&Proposition::condition_is(condition.clone(), !value)))
            // `i < 0` and `i >= 0` are different conditions, not one
            // condition at both polarities, so the negation is recognized
            // through the bounded list of equivalent spellings the other
            // explicit closers use, in every order family (`x >= 32u64`
            // beside `x < 32u64` as well as the `int32` pair). This is a
            // fixed-size set of exact lookups, not a fact-set search.
            || super::fact_reasoning::order_claim_forms(&negated)
                .iter()
                .any(|form| self.contains(form))
            || super::fact_reasoning::normalizes_context_free_leaf(&match fact {
                // A condition's negation is the same condition at the other
                // polarity, the form `normalize()` decides, as for
                // `to_integer(x) + 1 == to_integer(x)`.
                Proposition::ConditionIs(condition, value) => {
                    Proposition::condition_is(condition.clone(), !value)
                }
                _ => negated,
            }))
    }

    pub(crate) fn freshen_pointer_forall_body(
        &self,
        binder: Variable,
        program_type: ProgramType,
        body: &Proposition,
    ) -> Option<(Variable, Proposition)> {
        self.opened_forall_body(binder, &Sort::ProgramPointer(program_type), body)
    }

    /// Materializes only the separations selected by this explicit goal.
    /// A conjunction also needs every other leaf (including range bounds) as
    /// an existing fact. No unrelated resource pairs are enumerated.
    pub(crate) fn with_selected_resource_separation(&self, goal: &Proposition) -> Self {
        self.with_selected_separation_facts(goal)
    }

    /// Apply the exact partition rule to the written separation leaves only.
    /// No containment, aliases, composition traversal or fact search occurs.
    pub(crate) fn with_exact_partition_separation(
        &self,
        goal: &Proposition,
        resources: &ResourceContext,
    ) -> Self {
        let mut facts = self.clone();
        let mut pending = vec![goal];
        while let Some(part) = pending.pop() {
            match part {
                Proposition::And(left, right) => pending.extend([right.as_ref(), left.as_ref()]),
                Proposition::ResourceSeparate { left, right }
                    if !facts.contains(part)
                        && resources.proves_exact_partition_separation(left, right) =>
                {
                    facts = facts.with_fact(part.clone());
                }
                _ => {}
            }
        }
        facts
    }

    /// Observes only the separation explicitly requested at this checked C
    /// state. Unfolding independent instances exposes members of the same
    /// live partition, even when their retained body compositions are separate.
    /// Do not retain/hash the whole state composition or enumerate its pairs.
    pub(crate) fn with_selected_held_resource_separation(
        &self,
        goal: &Proposition,
        state: &crate::kernel::ExecutionState,
    ) -> Self {
        let Proposition::ResourceSeparate { left, right } = goal else {
            return self.clone();
        };
        if !self.contains(goal)
            && self
                .assumptions
                .proves_held_resources_separate(state.resources(), left, right)
        {
            self.with_fact(goal.clone())
        } else {
            self.clone()
        }
    }

    fn with_selected_separation_facts(&self, goal: &Proposition) -> Self {
        let mut facts = self.clone();
        let mut pending = vec![goal];
        let mut all_available = true;
        while let Some(part) = pending.pop() {
            if let Proposition::And(left, right) = part {
                pending.push(right);
                pending.push(left);
                continue;
            }
            if matches!(part, Proposition::ResourceSeparate { .. }) && !facts.contains(part) {
                let assumptions = &facts.assumptions;
                if assumptions.proves_exact(part)
                    || assumptions.proves_atomic_memory_or_resource(part)
                {
                    facts = facts.with_fact(part.clone());
                }
            }
            all_available &= facts.pure_known_available(part);
        }
        // Publish the requested conjunction once. Publishing every nested
        // prefix would repeatedly clone it and take quadratic work.
        if matches!(goal, Proposition::And(_, _)) && all_available && !facts.contains(goal) {
            facts = facts.with_fact(goal.clone());
        }
        facts
    }

    /// Publish the explicit entry resource input in the fact context retained
    /// by the body proof. This builds address indexes without changing facts
    /// or permissions, before any checked step can depend on that lineage.
    pub(super) fn prepare_entry_resources(&mut self, resources: &crate::kernel::ResourceContext) {
        resources.synchronize_memory_equalities(&self.assumptions);
        self.assumptions = self
            .assumptions
            .clone()
            .with_prepared_resource_addresses(resources);
    }

    pub(crate) fn assumptions(&self) -> &PureFactContext {
        &self.assumptions
    }

    /// Proper-conjunct membership uses the same observation identity for native
    /// and retained comparisons, without consulting unrelated held facts.
    pub(crate) fn contains_proper_conjunct(&self, required: &Proposition) -> bool {
        self.proper_conjuncts
            .contains(&PropositionKey::new(required))
            || condition_polarity_forms(required)
                .iter()
                .any(|form| self.proper_conjuncts.contains(&PropositionKey::new(form)))
    }

    /// The available proper conjunct that `required` names up to the
    /// renaming of its quantifier binders, selected by its alpha bucket.
    pub(crate) fn alpha_equivalent_proper_conjunct(
        &self,
        required: &Proposition,
    ) -> Option<Proposition> {
        let key = quantified_equivalence_index_key(required)?;
        self.quantified_proper_conjuncts
            .get(&key)?
            .iter()
            .map(Arc::as_ref)
            .find(|candidate| quantified_binder_equivalent(required, candidate))
            .cloned()
    }

    /// Availability modulo the shared equality closure for deterministic
    /// rewriting. This admits no unfolding or cross-state transport.
    pub(crate) fn materialization_available(&self, required: &Proposition) -> bool {
        self.available(required)
    }

    /// The shared machine reading of this selected Integer fact, only when exact
    /// indexed range premises establish that its operations cannot wrap.
    /// This produces a consequence of the supplied fact; it does not choose
    /// a different ambient premise to discharge the caller's guard.
    pub(crate) fn shared_operation_reading(&self, fact: &Proposition) -> Option<Proposition> {
        let Proposition::ConditionIs(condition, truth) = fact else {
            return None;
        };
        let (view, bounds) =
            crate::kernel::machine_integer::comparison::comparison_view_through_integer_operations(
                condition.old_form(),
                *truth,
            )?;
        if !bounds
            .iter()
            .all(|bound| self.assumptions().knows_operation_range_bound(bound))
        {
            return None;
        }
        Some(view.integer_proposition())
    }

    /// Availability of a proposition to the explicit pure `known`
    /// judgment used inside fixed-state proofs. This deliberately excludes
    /// cross-effect state transport: such a transport needs its own
    /// retained proof step before a later `known` step may consume it.
    pub(crate) fn pure_known_available(&self, required: &Proposition) -> bool {
        self.materialization_available(required)
            || self.integer_alpha_fact_available(required)
            || self.quantified_fact_available(required)
    }

    /// Implicit closure after introducing facts preserves the structural
    /// proof script. New graph consequences are consumed by explicit closers.
    pub(crate) fn introduced_goal_available(&self, required: &Proposition) -> bool {
        self.contains(required)
            || self.integer_alpha_fact_available(required)
            || self.quantified_fact_available(required)
    }

    #[cfg(test)]
    pub(crate) fn implicit_transport_assumptions(&self) -> &PureFactContext {
        &self.implicit_transport_assumptions
    }

    /// Each of `facts` with every algebraic variable these facts equate to a
    /// constructor replaced by it, so a `match` on the variable reduces: a
    /// callee's `result == match o { .. }` where the caller knows
    /// `o == Option::Some(x)`. A proof `match` arm instantiates earlier facts
    /// at the constructor it learns; this is the other order. Each fact's
    /// variables are looked up in the constructor index; nothing is read
    /// where no fact equates a variable to a constructor.
    fn known_constructor_instances(&self, facts: &[Proposition]) -> Vec<Proposition> {
        let variables = self.assumptions().has_algebraic_constructor_facts();
        let mut instances = Vec::new();
        for fact in facts {
            if matches!(
                fact,
                Proposition::Equal(Term::Algebraic(_), Term::Algebraic(_))
            ) {
                continue;
            }
            let mut instance = fact.clone();
            // So does a load of an enum's value the facts equate to a
            // constructor: a callee's `result == match *o { .. }` after
            // `*o == Option::None`. A leaf fact binds no variable, so the
            // load is replaced wherever it occurs.
            if matches!(fact, Proposition::Equal(..) | Proposition::ConditionIs(..)) {
                let mut terms = BTreeSet::new();
                collect_proposition_algebraic_terms(fact, &mut terms);
                for term in terms
                    .iter()
                    .filter(|term| matches!(term.node, AlgebraicTermNode::MemoryLoad { .. }))
                {
                    if let Some(constructor) = self.assumptions().known_algebraic_constructor(term)
                    {
                        let mut rewrite = crate::kernel::proof::term_rewrite::TermRewrite::new(
                            term,
                            &constructor,
                        );
                        instance = match &instance {
                            Proposition::Equal(left, right) => {
                                Proposition::Equal(rewrite.term(left), rewrite.term(right))
                            }
                            leaf => rewrite.proposition(leaf),
                        };
                    }
                }
            }
            if !variables {
                if instance != *fact && !instances.contains(&instance) {
                    instances.push(instance);
                }
                continue;
            }
            for key in crate::kernel::reasoning::collect_atomic_connection_keys(fact) {
                let crate::kernel::AtomicConnectionKey::Variable(variable) = key else {
                    continue;
                };
                if let Some(constructor) =
                    self.assumptions().variable_algebraic_constructor(variable)
                {
                    instance =
                        crate::kernel::reasoning::substitute_algebraic_variable_in_proposition(
                            &instance,
                            variable,
                            &constructor,
                        );
                }
            }
            if instance != *fact && !instances.contains(&instance) {
                // An implication whose consequent the substitution made a
                // clash of two constructors refutes its antecedent:
                // `x == 0 implies Ok(y) == Err(e)` is `x != 0`.
                for decided in constructor_consequent_instances(&instance) {
                    if !instances.contains(&decided) {
                        instances.push(decided);
                    }
                }
                instances.push(instance);
            }
        }
        instances
    }

    #[cfg(test)]
    pub(crate) fn with_statement_facts(&self, facts: Vec<Proposition>) -> Self {
        let view = self.statement_view(facts);
        self.publish_statement_view(view, &ExecutionFacts::new())
    }

    /// Commit the selected fork's semantic indexes and prioritize its
    /// statement-local presentation in the encompassing proof.
    pub(crate) fn publish_statement_view(
        &self,
        mut successor: Self,
        _prefix: &ExecutionFacts,
    ) -> Self {
        let mut facts = successor
            .occurrences()
            .map(crate::kernel::clone_proposition_iteratively)
            .collect::<Vec<_>>();
        let ordered = self.ordered.clone();
        let parent = self.statement_batches.clone();
        let mut introduced = facts
            .iter()
            .filter(|fact| !self.top_level_exact.contains(*fact))
            .cloned()
            .collect::<Vec<_>>();
        for instance in successor.known_constructor_instances(&introduced) {
            let before = successor.fact_count();
            successor = successor.with_fact(instance.clone());
            if successor.fact_count() != before {
                introduced.push(instance);
            }
        }
        let additions = successor
            .ordered
            .suffix_since(&ordered)
            .expect("statement facts extend the ordered prefix");
        let mut listed = facts.iter().cloned().collect::<BTreeSet<_>>();
        introduced.clear();
        for fact in additions {
            introduced.push(fact.as_ref().clone());
            if listed.insert(fact.as_ref().clone()) {
                facts.push(fact.as_ref().clone());
            }
        }
        successor.ordered = ordered;
        successor.presentation = self.presentation.unique();
        let displayed = facts
            .iter()
            .map(|fact| {
                successor
                    .top_level_exact
                    .get(fact)
                    .expect("admitted statement fact")
                    .clone()
            })
            .collect::<Vec<_>>();
        successor.presentation.prioritize(displayed);
        #[cfg(test)]
        {
            let shared_prefix = facts.len() >= _prefix.len()
                && facts
                    .iter()
                    .zip(_prefix)
                    .all(|(fact, retained)| fact == retained.proposition());
            let suffix_len = facts.len() - if shared_prefix { _prefix.len() } else { 0 };
            STATEMENT_PRIORITY_ENTRIES.with(|count| count.set(count.get() + suffix_len));
            STATEMENT_PRIORITY_MAX_SUFFIX.with(|count| count.set(count.get().max(suffix_len)));
            if suffix_len > 1 {
                STATEMENT_PRIORITY_NONLOCAL_BATCHES.with(|count| count.set(count.get() + 1));
            }
        }
        successor.statement_batches = Some(Arc::new(StatementFactBatch {
            parent,
            introduced: Arc::new(
                introduced
                    .iter()
                    .map(|fact| {
                        successor
                            .top_level_exact
                            .get(fact)
                            .expect("introduced statement fact")
                            .clone()
                    })
                    .collect(),
            ),
        }));
        successor
    }

    /// Availability accepted by explicit check, answered from persistent
    /// indexes. MemoryState-blind buckets only select structurally compatible
    /// candidates; the kernel still proves every cross-state match.
    pub(crate) fn available_across_effects(
        &self,
        required: &Proposition,
        framing: &(impl ExecutionFactSource + ?Sized),
    ) -> bool {
        if self.exact_available_across_effects(required, framing) {
            return true;
        }

        self.quantified_fact_available(required)
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
            .map(Arc::as_ref)
            .filter(move |candidate| quantified_binder_equivalent(required, candidate))
    }

    pub(crate) fn quantified_fact_available(&self, required: &Proposition) -> bool {
        self.matching_quantified_fact(required).is_some()
    }

    /// An available guarded universal that entails `required` by dropping
    /// conjuncts of its conclusion under identical binder and guards:
    /// `forall k { G implies A and B }` for `forall k { G implies A }`.
    ///
    /// One probe of the projection index selects the candidates, and each is
    /// accepted only when one of its own projections is binder-equivalent to
    /// `required` by the same check `known` applies to quantified facts.
    /// A different guard, binder sort, or conjunct has a different key or
    /// fails that check. The returned fact is not itself `required`; the
    /// caller must still establish the weakening with checked steps.
    pub(crate) fn quantified_conjunct_projection_source(
        &self,
        required: &Proposition,
    ) -> Option<&Proposition> {
        if !matches!(required, Proposition::ForAll { .. }) {
            return None;
        }
        let key = quantified_equivalence_index_key(required)?;
        self.quantified_conjunct_projections
            .get(&key)?
            .iter()
            .map(Arc::as_ref)
            .find(|source| {
                guarded_universal_conjunct_projections(source)
                    .iter()
                    .any(|projection| quantified_binder_equivalent(required, projection))
            })
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

    /// Returns one actual available fact accepted by explicit check. Smart
    /// syntax selection needs the retained fact, not merely a yes/no answer:
    /// its recorded surface form may carry a statement state that the
    /// freshly lowered theorem requirement no longer exposes.
    #[cfg(test)]
    pub(crate) fn matching_fact_across_effects(
        &self,
        required: &Proposition,
        framing: &(impl ExecutionFactSource + ?Sized),
    ) -> Option<Proposition> {
        let keys = [memory_erased_proposition_key(required)];
        let mut indexed_candidates = Vec::new();
        for key in &keys {
            if let Some(bucket) = self.by_memory_erased.get(key) {
                for candidate in bucket.iter() {
                    if !indexed_candidates.contains(candidate.as_ref()) {
                        indexed_candidates.push(candidate.as_ref().clone());
                    }
                }
            }
        }
        // Preserve the legacy selector's canonical materialization choice,
        // but search only the requirement's persistent shape bucket. The
        // chosen sibling state can have a stable recorded `at(...)`
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

        // A scoped equality derivation can establish this exact requirement
        // without any one stored proposition spelling the whole chain. The
        // explicit checker accepts it through the same indexed graph lookup.
        if self.available(required) {
            return Some(required.clone());
        }

        // A checked Integer comparison may contain range-fold binders freshly
        // allocated by the preceding rewrite. Return the stored proposition
        // so callers retain the source fact and its certificate evidence;
        // do not synthesize the requested presentation here.
        if let Some(candidate) = self.matching_integer_condition_alpha_fact(required) {
            return Some(candidate);
        }

        if let Some(quantified) = self.matching_quantified_fact(required) {
            return Some(quantified);
        }

        let mut candidates = Vec::new();
        for key in keys {
            let Some(bucket) = self.by_memory_erased.get(&key) else {
                continue;
            };
            for candidate in bucket.iter() {
                let candidate = candidate.as_ref();
                if !candidates.contains(candidate) {
                    candidates.push(candidate.clone());
                }
                if candidate == required
                    || condition_bridged_fact_is_available(
                        required,
                        std::slice::from_ref(candidate),
                        &self.assumptions,
                    )
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
            .get(&memory_erased_proposition_key(required))
            .is_some_and(|bucket| {
                bucket.iter().any(|candidate| {
                    candidate.whole.is_none()
                        && &candidate.consequent == required
                        && antecedents_available(candidate)
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

    /// An implication whose antecedents are all available and whose
    /// consequent is a conjunction with `required` among its conjuncts: the
    /// implication fact itself and that whole consequent. `apply(fact)` states
    /// the whole consequent from the fact, and `required` is then a proper
    /// conjunct of an available fact.
    pub(crate) fn discharged_implication_containing(
        &self,
        required: &Proposition,
    ) -> Option<(Proposition, Proposition)> {
        let bucket = self
            .implications_by_consequent
            .get(&memory_erased_proposition_key(required))?;
        bucket.iter().find_map(|candidate| {
            let whole = candidate.whole.as_ref()?;
            if &candidate.consequent != required
                || !candidate
                    .antecedents
                    .iter()
                    .all(|antecedent| self.available_across_effects(antecedent, &[]))
            {
                return None;
            }
            let fact =
                candidate
                    .antecedents
                    .iter()
                    .rev()
                    .fold(whole.clone(), |rest, antecedent| {
                        Proposition::Implies(Box::new(antecedent.clone()), Box::new(rest))
                    });
            Some((fact, whole.clone()))
        })
    }

    /// Sources for an expandable implication application. The capability
    /// keeps candidate enumeration out of checked operations.
    pub(crate) fn implication_sources_for_search(
        &self,
        required: &Proposition,
        _permission: crate::SearchPermission,
    ) -> Vec<Proposition> {
        let ordinary = self
            .implications_by_consequent
            .get(&memory_erased_proposition_key(required));
        let quantified = quantified_equivalence_index_key(required)
            .and_then(|key| self.implications_by_quantified_consequent.get(&key));
        ordinary
            .into_iter()
            .chain(quantified)
            .flat_map(|bucket| bucket.iter())
            .take(64)
            .inspect(|_| crate::instrumentation::record_deterministic_work(1))
            .filter(|candidate| {
                candidate.consequent == *required
                    || quantified_binder_equivalent(required, &candidate.consequent)
            })
            .map(|candidate| {
                candidate.antecedents.iter().rev().fold(
                    candidate
                        .whole
                        .as_ref()
                        .unwrap_or(&candidate.consequent)
                        .clone(),
                    |rest, antecedent| {
                        Proposition::Implies(Box::new(antecedent.clone()), Box::new(rest))
                    },
                )
            })
            .collect()
    }

    /// Availability of one premise a `using` list names.
    ///
    /// A listed premise that holds with no facts at all — a ground constant
    /// that is the value it asserts (`0 <= 0`), or a comparison of a term with
    /// itself (`n <= n`) — needs no fact behind it; every other premise must
    /// be available from checked facts or their scoped equality closure,
    /// across effects when `across_quantifiers` also
    /// admits a binder-equivalent quantified fact. Every `using` list checks
    /// its premises through this one method, so a premise is accepted by one
    /// list exactly when it is accepted by another. Goal-closing tactics such
    /// as `known` use the same scoped equality knowledge directly.
    pub(crate) fn listed_premise_available(
        &self,
        premise: &Proposition,
        framing: &(impl ExecutionFactSource + ?Sized),
        across_quantifiers: bool,
    ) -> bool {
        crate::kernel::listed_premise_holds(premise, |premise| {
            if across_quantifiers {
                self.available_across_effects(premise, framing)
            } else {
                self.exact_available_across_effects(premise, framing)
            }
        })
    }

    pub(crate) fn exact_available_across_effects(
        &self,
        required: &Proposition,
        framing: &(impl ExecutionFactSource + ?Sized),
    ) -> bool {
        if self.available(required)
            || condition_polarity_forms(required)
                .iter()
                .any(|form| self.exact.contains(form))
        {
            return true;
        }

        if self.integer_alpha_fact_available(required) {
            return true;
        }

        // The state-blind index already bounds candidate selection. Check
        // each candidate in place rather than cloning a deduplicated Vec:
        // duplicate entries can only arise from index aliases, and a bridge
        // succeeds if any one indexed fact supplies it. This keeps the loop
        // lookup output-sized and avoids an uncharged deep Proposition Eq.
        let key = memory_erased_proposition_key(required);
        self.by_memory_erased.get(&key).is_some_and(|bucket| {
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
        }) || self.available_definedness_bound(required)
    }

    /// One ordinary exact-result bound supplied by a held nonoverflow fact.
    /// This selects the same source as the former boxed-query adapter, then
    /// checks its operands through the common across-effect load authority.
    fn available_definedness_bound(&self, required: &Proposition) -> bool {
        use crate::kernel::machine_integer::definedness::{
            defined_formats, overflow_query_of_integer_bound,
        };
        let Some(query) = overflow_query_of_integer_bound(required, defined_formats()) else {
            return false;
        };
        if self
            .assumptions
            .contains_known_overflow_query(&query, false)
        {
            return true;
        }
        let key = super::fact_keys::memory_erased_nonoverflow_key(&query);
        self.by_memory_erased.get(&key).is_some_and(|bucket| {
            bucket.iter().any(|candidate| {
                if crate::instrumentation::deadline_exceeded_with_work(1) {
                    return false;
                }
                let Some((
                    OldConditionTerm::Overflows {
                        format,
                        op,
                        left,
                        right,
                    },
                    false,
                )) = candidate.as_ref().old_condition()
                else {
                    return false;
                };
                *format == query.format
                    && *op == query.operation_kind()
                    && [left.as_ref(), right.as_ref()]
                        .into_iter()
                        .zip(&query.operands)
                        .all(|(source, operand)| {
                            self.assumptions.operands_equal_modulo_origin_unchanged(
                                query.format,
                                MachineOperandView::Old(source),
                                operand.operand_view(),
                            )
                        })
            })
        })
    }

    pub(crate) fn directly_conflicts_with(&self, fact: &Proposition) -> bool {
        directly_conflicts_with_normalized_index(&self.exact, fact)
    }

    /// Returns exact equality facts attached to terms occurring in this
    /// proposition. Selection cost follows the proposition and the matching
    /// equality buckets; unrelated ambient equalities are never visited.
    #[cfg(test)]
    pub(crate) fn bitvector_equalities_mentioning(
        &self,
        proposition: &Proposition,
    ) -> Vec<Proposition> {
        self.load_equalities_mentioning(proposition)
            .into_iter()
            .filter(|equality| {
                matches!(&equality, condition_source_0 @ Proposition::ConditionIs(
                        _,
                        true
                    ) if matches!(condition_source_0.old_condition(), Some((OldConditionTerm::Compare {
                            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                            relation: CompareRelation::Equal,
                            left: _,
                            right: _
                        } | OldConditionTerm::Compare {
                            format: MachineIntegerType::Int64,
                            relation: CompareRelation::Equal,
                            left: _,
                            right: _
                        }, _))))
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
            let finite: Vec<_> = match condition.old_form() {
                OldConditionTerm::Float32(FloatCondition::Comparison { left, right, .. }) => {
                    vec![(32, left), (32, right)]
                }
                OldConditionTerm::Float64(FloatCondition::Comparison { left, right, .. }) => {
                    vec![(64, left), (64, right)]
                }
                _ => Vec::new(),
            };
            for (width, value) in finite {
                let classification = match width {
                    32 => Proposition::condition_is(
                        OldConditionTerm::Float32(FloatCondition::Classification {
                            classification: FloatClassification::Finite,
                            value: value.clone(),
                        }),
                        true,
                    ),
                    64 => Proposition::condition_is(
                        OldConditionTerm::Float64(FloatCondition::Classification {
                            classification: FloatClassification::Finite,
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
                equalities.extend(bucket.iter().map(Arc::as_ref));
            }
        }
        equalities.into_iter().cloned().collect()
    }

    /// The exact bitvector equalities attached to terms of this proposition
    /// (through the addresses of its loads), together with the indexed
    /// pointer equalities between scaled offsets, each fact once.
    pub(crate) fn load_equalities_mentioning(&self, proposition: &Proposition) -> Vec<Proposition> {
        self.indexed_load_equalities_mentioning(proposition)
            .into_iter()
            .map(|fact| fact.as_ref().clone())
            .collect()
    }

    /// Read the same equality index under the active search budget, with a
    /// bound on how many candidates the source-proof planner will spell.
    pub(crate) fn load_equality_candidates_for_solve(
        &self,
        proposition: &Proposition,
        limit: usize,
        _permission: crate::kernel::search::SearchPermission,
    ) -> Vec<Proposition> {
        self.collect_indexed_load_equalities(proposition, Some(limit))
            .into_iter()
            .map(|fact| fact.as_ref().clone())
            .collect()
    }

    /// Definedness-guarded comparisons (`defined(e) implies a == b`) whose
    /// consequent shares an atomic operand with `proposition`, oldest first
    /// within each atom and deduplicated by identity. The lookup visits only
    /// the buckets of the atoms the proposition names.
    pub(crate) fn guarded_implications_mentioning(
        &self,
        proposition: &Proposition,
    ) -> Vec<Proposition> {
        let mut atoms = BTreeSet::new();
        collect_proposition_bitvector_atoms(proposition, &mut atoms);
        let mut seen = BTreeSet::new();
        let mut implications = Vec::new();
        for atom in atoms {
            if let Some(bucket) = self.guarded_implications_by_atom.get(&atom) {
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
        self.collect_indexed_load_equalities(proposition, None)
    }

    fn collect_indexed_load_equalities(
        &self,
        proposition: &Proposition,
        search_limit: Option<usize>,
    ) -> Vec<Arc<Proposition>> {
        let mut atoms = BTreeSet::new();
        collect_proposition_bitvector_atoms(proposition, &mut atoms);
        // One fact is filed under each of its operands' atoms; pointer
        // identity drops the repeat without comparing payloads.
        let mut seen = BTreeSet::new();
        let mut equalities = Vec::new();
        // Exact pointer operands select their own equalities before a
        // shared base nominates every older pointer into that object.
        // Literals never nominate aliases: automatic rewriting reduces
        // symbolic operands to literals, not a literal to an unrelated
        // symbolic value which happens to equal it.
        let mut exact_pointers = atoms
            .iter()
            .filter(|atom| matches!(atom, BitvectorEqualityAtomKey::PointerReadSource(_)))
            .collect::<Vec<_>>();
        exact_pointers.sort_by_key(|atom| {
            self.bitvector_equalities_by_atom
                .get(*atom)
                .map_or(0, PersistentSequence::len)
        });
        let other_operands = atoms.iter().filter(|atom| {
            !matches!(
                atom,
                BitvectorEqualityAtomKey::PointerReadSource(_)
                    | BitvectorEqualityAtomKey::Constant(_)
            )
        });
        for atom in exact_pointers.into_iter().chain(other_operands) {
            if let Some(bucket) = self.bitvector_equalities_by_atom.get(atom) {
                for equality in bucket.iter() {
                    if let Some(limit) = search_limit
                        && (equalities.len() == limit
                            || crate::instrumentation::deadline_exceeded_with_work(1))
                    {
                        return equalities;
                    }
                    if seen.insert(Arc::as_ptr(equality) as usize) {
                        equalities.push(equality.clone());
                    }
                }
            }
        }
        equalities
    }

    fn matching_indexed_finite_classification(
        &self,
        required: &Proposition,
    ) -> Option<Arc<Proposition>> {
        let key = memory_erased_proposition_key(required);
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
    /// recovered by walking only the appended suffixes — statement
    /// batches first, then ordinary insertions — and pointer
    /// identity proves the shared history. Returns `None` when `ancestor`
    /// is not this context's ancestor. This is the output-sensitive
    /// introduction delta the execution sibling-split joins consume.
    pub(crate) fn introduced_since(&self, ancestor: &Self) -> Option<Vec<Proposition>> {
        self.introduced_since_within(ancestor, usize::MAX)
    }

    /// [`Self::introduced_since`], or `None` once the delta would exceed
    /// `limit` facts: the walk stops there, so a caller that would rather
    /// rebuild than fold a large delta pays at most `limit` to find out.
    pub(crate) fn introduced_since_within(
        &self,
        ancestor: &Self,
        limit: usize,
    ) -> Option<Vec<Proposition>> {
        let mut remaining =
            limit.checked_sub(self.ordered.len().checked_sub(ancestor.ordered.len())?)?;
        let mut new_batches = Vec::new();
        let mut current = self.statement_batches.clone();
        loop {
            match (&current, &ancestor.statement_batches) {
                (Some(node), Some(ancestor_head)) if Arc::ptr_eq(node, ancestor_head) => break,
                (None, None) => break,
                (Some(node), _) => {
                    // An empty batch still costs a step of the walk.
                    remaining = remaining.checked_sub(node.introduced.len().max(1))?;
                    new_batches.push(node.introduced.clone());
                    current = node.parent.clone();
                }
                (None, Some(_)) => return None,
            }
        }
        let ordered_suffix = self.ordered.suffix_since(&ancestor.ordered)?;
        let mut introduced = Vec::new();
        for batch in new_batches.iter().rev() {
            introduced.extend(batch.iter().map(|fact| fact.as_ref().clone()));
        }
        introduced.extend(ordered_suffix.iter().map(|fact| fact.as_ref().clone()));
        Some(introduced)
    }

    pub(crate) fn to_vec(&self) -> Vec<Proposition> {
        let ordered = self
            .propositions()
            .map(crate::kernel::clone_proposition_iteratively)
            .collect::<Vec<_>>();
        #[cfg(test)]
        MATERIALIZED_FACT_ENTRIES.with(|count| count.set(count.get() + ordered.len()));
        ordered
    }

    pub(crate) fn mentioning_predicate(&self, name: &String) -> impl Iterator<Item = &Proposition> {
        self.by_predicate
            .get(name)
            .into_iter()
            .flat_map(PersistentSequence::iter)
            .map(Arc::as_ref)
    }

    #[cfg(test)]
    pub(crate) fn lookup_comparisons(&self, fact: &Proposition) -> usize {
        self.exact.lookup_comparisons(&Arc::new(fact.clone()))
    }

    #[cfg(test)]
    pub(crate) fn equality_atom_lookup_comparisons(&self, term: &OldMachineTerm) -> usize {
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
    pub(crate) fn implication_bucket_len(&self, key: &MemoryErasedPropositionKey) -> Option<usize> {
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

/// Puts back the span spelling a range carried before its binder was
/// renamed.
///
/// Renaming a bound variable is supposed to change what a proposition's binder
/// is called and nothing else. Substitution rebuilds every term it walks with
/// the kernel's folding constructors, though, and those fold strictly more
/// than the one `memory_range_byte_count` builds a range's span with: the
/// span of `a[k..k + 1]` is written `((k + 1) - k) * w` and comes back from
/// a substitution as the constant `w`. Both spell the same span, and a
/// proof state matches a goal against a fact syntactically, so the rename
/// moved the goal out of the form every re-lowering of the written range
/// produces and the narrowing that had just worked stopped matching.
///
/// The two forms cannot simply be merged. The span is also where surface
/// synthesis recovers a range's written ends from — folding `(k + 1) - k` to a
/// constant loses them, and `loadable(p[k..k + 1])` then spells back as a
/// zero-based range over a displaced base. So the rename keeps the spelling
/// instead: where the original carried a range span, the renamed
/// proposition gets that span's endpoints substituted and reassembled in the
/// written shape rather than the folded one.
///
/// This walks only the logical structure the two propositions share, and only
/// as far as the range leaves; it changes no other term and decides nothing.
pub(crate) fn restore_range_span_spelling(
    original: &Proposition,
    renamed: Proposition,
    from: Variable,
    to: &OldMachineTerm,
) -> Proposition {
    let recurse = |original: &Proposition, renamed: Proposition| {
        Box::new(restore_range_span_spelling(original, renamed, from, to))
    };
    match (original, renamed) {
        (
            Proposition::MemoryLoadable { bytes, .. },
            Proposition::MemoryLoadable {
                memory,
                base,
                bytes: folded,
                wide: false,
                point,
            },
        ) => Proposition::MemoryLoadable {
            point: point.clone(),
            memory,
            base,
            bytes: substituted_range_span(bytes.old_form(), from, to)
                .map(Into::into)
                .unwrap_or(folded),
            wide: false,
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
                name,
            },
        ) => Proposition::ForAll {
            var,
            sort,
            body: recurse(body, *renamed_body),
            name,
        },
        (_, renamed) => renamed,
    }
}

/// A written range span with its endpoints substituted, reassembled in the
/// shape [`crate::kernel::memory_range_byte_count`] builds rather than the
/// shape the folding constructors would collapse it to. `None` when the term
/// is not a written range span, which is every other byte count.
fn substituted_range_span(
    bytes: &OldMachineTerm,
    from: Variable,
    to: &OldMachineTerm,
) -> Option<OldMachineTerm> {
    let substitute = |term: &OldMachineTerm| {
        crate::kernel::reasoning::substitute_bitvector_variable(term, from, to)
    };
    let (count, width) = match bytes {
        binary_term!(Int32, Multiply, count, width) => match width.as_ref() {
            bits32_constant!(_) => (count.as_ref(), Some(width.as_ref().clone())),
            _ => return None,
        },
        count @ binary_term!(Int32, Subtract, _, _) => (count, None),
        _ => return None,
    };
    let binary_term!(Int32, Subtract, end, start) = count else {
        return None;
    };
    let count = binary_node!(
        Int32,
        Subtract,
        Box::new(substitute(end)),
        Box::new(substitute(start))
    );
    Some(match width {
        Some(width) => binary_node!(Int32, Multiply, Box::new(count), Box::new(width)),
        None => count,
    })
}

fn index_state_fact(
    mut by_memory_erased: PersistentMap<
        MemoryErasedPropositionKey,
        PersistentSequence<Arc<Proposition>>,
    >,
    fact: &Arc<Proposition>,
) -> PersistentMap<MemoryErasedPropositionKey, PersistentSequence<Arc<Proposition>>> {
    for key in [memory_erased_proposition_key(fact)] {
        if !key.requires_checked_match() {
            continue;
        }
        let mut bucket = by_memory_erased.get(&key).cloned().unwrap_or_default();
        if !bucket.iter().any(|candidate| candidate == fact) {
            bucket.push(fact.clone());
            by_memory_erased = by_memory_erased.with_inserted(key, bucket);
        }
    }
    by_memory_erased
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
        condition_source_0 @ Proposition::ConditionIs(_, true)
            if let Some((
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                }
                | OldConditionTerm::Compare {
                    format: MachineIntegerType::Int64,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                },
                _,
            )) = condition_source_0.old_condition() =>
        {
            (left.as_ref(), right.as_ref())
        }
        // A native 8- or 16-bit equality is the same fact as the `int32`
        // equality of its operands' widenings (rule K8), whose atoms are its
        // operands' atoms; it is filed under them as that equality is.
        condition_source_0 @ Proposition::ConditionIs(_, true)
            if let Some((
                OldConditionTerm::Compare {
                    format,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                },
                _,
            )) = condition_source_0.old_condition()
                && (format.format().bits() < 32) =>
        {
            (left.as_ref(), right.as_ref())
        }
        // A pointer-offset equality between two scaled offsets (how a
        // pointer-valued field's preservation is recorded) is indexed by the
        // same atoms so the load-variable chain bridge can select it.
        condition_source_0 @ Proposition::ConditionIs(_, true)
            if let Some((OldConditionTerm::AddressOffsetEqual(left, right), _)) =
                condition_source_0.old_condition() =>
        {
            match (left.view(), right.view()) {
                (
                    OffsetView::Int32Scaled { index: left, .. },
                    OffsetView::Int32Scaled { index: right, .. },
                ) => {
                    let mut atoms = BTreeSet::new();
                    selected_atoms::collect(&left, &mut atoms);
                    selected_atoms::collect(&right, &mut atoms);
                    for atom in atoms {
                        let mut bucket = index.get(&atom).cloned().unwrap_or_default();
                        bucket.push(fact.clone());
                        index = index.with_inserted(atom, bucket);
                    }
                    return index;
                }
                _ => return index,
            }
        }
        // An Integer equality over machine observations, such as a premise
        // `to_integer(count(r)) == 0`, is filed under the machine operands
        // it observes, so a goal over those operands selects it as `solve`
        // selects their native equalities.
        condition_source_0 @ Proposition::ConditionIs(_, true)
            if let Some((
                condition @ (OldConditionTerm::AddressEqual(_, _)
                | OldConditionTerm::PointerEqual(_, _)
                | OldConditionTerm::IntegerEqual(_, _)),
                _,
            )) = condition_source_0.old_condition() =>
        {
            let mut atoms = BTreeSet::new();
            collect_condition_bitvector_atoms(condition, &mut atoms);
            for atom in atoms {
                let mut bucket = index.get(&atom).cloned().unwrap_or_default();
                // Each fact is published once and the atom set is unique.
                // Do not scan a bucket to rediscover that identity.
                bucket.push(fact.clone());
                index = index.with_inserted(atom, bucket);
            }
            return index;
        }
        _ => return index,
    };
    let mut atoms = BTreeSet::new();
    for term in [left, right] {
        collect_bitvector_atoms(term, &mut atoms);
    }
    for key in atoms {
        let mut bucket = index.get(&key).cloned().unwrap_or_default();
        bucket.push(fact.clone());
        index = index.with_inserted(key, bucket);
    }
    index
}

/// Whether a proposition is only a C definedness guard: a conjunction of
/// the no-overflow conditions lowering attaches to partial arithmetic.
pub(crate) fn is_definedness_guard(proposition: &Proposition) -> bool {
    if crate::kernel::machine_integer::definedness::ordinary_arithmetic_guard_view(proposition)
        .is_some()
    {
        return true;
    }
    match proposition {
        Proposition::And(left, right) => is_definedness_guard(left) && is_definedness_guard(right),
        Proposition::ConditionIs(condition, false) => condition
            .operand_view()
            .overflow()
            .is_some_and(|(format, _, _)| {
                crate::kernel::machine_integer::representation::files_definedness(format)
            }),
        _ => false,
    }
}

/// A closed comparison that holds: decided from its literal roots alone
/// (`machine_integer::comparison::closed_condition_value`). The constant
/// `true` itself is an ordinary fact and is not included.
fn closed_condition_holds(fact: &Proposition) -> bool {
    matches!(fact, Proposition::ConditionIs(condition, value)
    if condition.operand_view().closed_float_predicate_value().map_or_else(
        || condition.operand_view().constant().is_none()
            && crate::kernel::machine_integer::comparison::closed_condition_value(condition.operand_view()) == Some(*value),
        |actual| actual == *value,
    ))
}

fn index_guarded_implication_fact(
    mut index: PersistentMap<BitvectorEqualityAtomKey, PersistentSequence<Arc<Proposition>>>,
    fact: &Arc<Proposition>,
) -> PersistentMap<BitvectorEqualityAtomKey, PersistentSequence<Arc<Proposition>>> {
    let Proposition::Implies(guard, consequent) = fact.as_ref() else {
        return index;
    };
    let Proposition::ConditionIs(condition, _) = consequent.as_ref() else {
        return index;
    };
    let Some(view) = crate::kernel::machine_integer::comparison::structural_comparison_view(
        condition.old_form(),
    ) else {
        return index;
    };
    if !matches!(
        view.format,
        MachineIntegerType::Int32 | MachineIntegerType::Int64
    ) && !(matches!(
        view.format,
        MachineIntegerType::UInt32 | MachineIntegerType::UInt64
    ) && view.relation == CompareRelation::Equal)
    {
        return index;
    }
    // Only a definedness guard: applying an ambient implication under an
    // ordinary condition stays an explicit `apply(fact)`
    // (`verified_call_ensure_premise_needs_its_discharge.md`), while a
    // no-overflow guard is a side condition of the arithmetic the
    // consequent states.
    if !is_definedness_guard(guard) {
        return index;
    }
    for operand in &view.operands {
        let term = operand.operand_view();
        let atom = match term {
            MachineOperandView::Old(term) => bitvector_equality_atom_key(term),
            MachineOperandView::Shared(root) => root
                .machine_conversion_leaf()
                .or_else(|| root.machine_read_leaf())
                .and_then(bitvector_equality_atom_key)
                .or_else(|| {
                    term.variable()
                        .and_then(|v| bitvector_equality_atom_key(&OldMachineTerm::Variable(*v)))
                })
                .or_else(|| {
                    term.literal()
                        .as_ref()
                        .and_then(bitvector_equality_atom_key)
                }),
        };
        let Some(key) = atom else {
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
    mut index: PersistentMap<MemoryErasedPropositionKey, PersistentSequence<Arc<Proposition>>>,
    fact: &Arc<Proposition>,
) -> PersistentMap<MemoryErasedPropositionKey, PersistentSequence<Arc<Proposition>>> {
    if !matches!(&fact.as_ref(), condition_source_0 @ Proposition::ConditionIs(
            _,
            true,
        ) if matches!(condition_source_0.old_condition(), Some((OldConditionTerm::Float32(FloatCondition::Classification { .. })
                | OldConditionTerm::Float64(FloatCondition::Classification { .. }), _))))
    {
        return index;
    }
    let key = memory_erased_proposition_key(fact.as_ref());
    let mut bucket = index.get(&key).cloned().unwrap_or_default();
    if !bucket.iter().any(|candidate| Arc::ptr_eq(candidate, fact)) {
        bucket.push(fact.clone());
        index = index.with_inserted(key, bucket);
    }
    index
}

fn index_algebraic_equality_fact(
    mut index: PersistentMap<AlgebraicTerm, PersistentSequence<Arc<Proposition>>>,
    fact: &Arc<Proposition>,
) -> PersistentMap<AlgebraicTerm, PersistentSequence<Arc<Proposition>>> {
    let Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) = fact.as_ref() else {
        return index;
    };
    for term in [left, right]
        .into_iter()
        .filter(|term| !matches!(term.old_form().node, AlgebraicTermNode::Constructor { .. }))
    {
        let mut bucket = index.get(term.old_form()).cloned().unwrap_or_default();
        if !bucket.iter().any(|candidate| candidate == fact) {
            bucket.push(fact.clone());
            index = index.with_inserted(term.old_form().clone(), bucket);
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
            collect_algebraic_term_roots(left.old_form(), terms);
            collect_algebraic_term_roots(right.old_form(), terms);
        }
        condition_source_0 @ Proposition::ConditionIs(_, _)
            if let Some((OldConditionTerm::AlgebraicEqual(left, right), _)) =
                condition_source_0.old_condition() =>
        {
            collect_algebraic_term_roots(left, terms);
            collect_algebraic_term_roots(right, terms);
        }
        condition_source_0 @ Proposition::ConditionIs(_, _)
            if let Some((
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                },
                _,
            )) = condition_source_0.old_condition() =>
        {
            for value in [left.as_ref(), right.as_ref()] {
                if let OldMachineTerm::AlgebraicMatch { scrutinee, .. } = value {
                    collect_algebraic_term_roots(scrutinee, terms);
                }
            }
        }
        condition_source_0 @ Proposition::ConditionIs(_, _)
            if let Some((OldConditionTerm::IntegerEqual(left, right), _)) =
                condition_source_0.old_condition() =>
        {
            for value in [left.as_ref(), right.as_ref()] {
                if let crate::kernel::IntegerTerm::AlgebraicMatch { scrutinee, .. } = value {
                    collect_algebraic_term_roots(scrutinee, terms);
                } else if let crate::kernel::IntegerTerm::Machine(machine) = value
                    && matches!(
                        machine.ty(),
                        MachineIntegerType::Int32 | MachineIntegerType::UInt32
                    )
                    && let Some(scrutinee) = machine.operand_view().match_scrutinee()
                {
                    // Shared word comparisons use Integer observations. Keep
                    // the native equality's existing scrutinee selection.
                    collect_algebraic_term_roots(&scrutinee, terms);
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
        AlgebraicTermNode::Variable(_) | AlgebraicTermNode::MemoryLoad { .. } => {}
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
        AlgebraicTermNode::If {
            then_term,
            else_term,
            ..
        } => {
            collect_algebraic_term_roots(then_term, terms);
            collect_algebraic_term_roots(else_term, terms);
        }
    }
}

fn bitvector_equality_atom_key(term: &OldMachineTerm) -> Option<BitvectorEqualityAtomKey> {
    match term {
        // A `uint32` constant is its word's `Constant` (rule K1).
        bits32_constant!(value) => Some(BitvectorEqualityAtomKey::Constant(constant_u32(*value))),
        OldMachineTerm::Variable(variable) => {
            if let Some(read) = crate::kernel::registered_load_term_for_variable(variable) {
                bitvector_equality_atom_key(&read)
            } else {
                Some(BitvectorEqualityAtomKey::Variable(*variable))
            }
        }
        OldMachineTerm::ClickFunctionApplication { name, arguments } => {
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            let mut machine_identities = Vec::new();
            for argument in arguments {
                if let Some(value) = argument.machine_identity() {
                    4u8.hash(&mut hasher);
                    value.hash(&mut hasher);
                    machine_identities.push(value);
                    continue;
                }
                match argument {
                    PureFunctionArgument::SharedMachine(_) => {
                        unreachable!("machine argument identity")
                    }
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
                        point: memory,
                        pointer,
                        element_type,
                    } => {
                        2u8.hash(&mut hasher);
                        memory.read_key().hash(&mut hasher);
                        pointer.hash(&mut hasher);
                        element_type.hash(&mut hasher);
                    }
                }
            }
            Some(BitvectorEqualityAtomKey::ClickFunctionApplication {
                name: name.clone(),
                arguments_hash: hasher.finish(),
                machine_identities,
            })
        }
        OldMachineTerm::MemoryLoad(memory, pointer, kind) => {
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            std::hash::Hash::hash(pointer.as_ref(), &mut hasher);
            std::hash::Hash::hash(kind, &mut hasher);
            Some(BitvectorEqualityAtomKey::MemoryLoad {
                memory: memory.shared_memory().arena_id(),
                pointer_hash: std::hash::Hasher::finish(&hasher),
            })
        }
        OldMachineTerm::PureApplicationCount(application) => Some(
            BitvectorEqualityAtomKey::PureApplicationCount(application.clone()),
        ),
        _ => None,
    }
}

fn collect_proposition_bitvector_atoms(
    proposition: &Proposition,
    atoms: &mut BTreeSet<BitvectorEqualityAtomKey>,
) {
    match proposition {
        Proposition::ConditionIs(condition, _) => {
            collect_condition_bitvector_atoms(condition.old_form(), atoms)
        }
        Proposition::ResourceSeparate { left, right } => {
            for resource in [left, right] {
                if let Resource::Memory(range) = &**resource {
                    collect_pointer_offset_bitvector_atoms(&range.base.offset, atoms);
                    collect_bitvector_atoms(range.bound_terms().0, atoms);
                    collect_bitvector_atoms(range.bound_terms().1, atoms);
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
    condition: &OldConditionTerm,
    atoms: &mut BTreeSet<BitvectorEqualityAtomKey>,
) {
    match condition {
        OldConditionTerm::PointerEqual(left, right) => {
            for pointer in left.pointers().chain(right.pointers()) {
                collect_pointer_bitvector_atoms(pointer, atoms);
            }
            for count in left.metadata_terms().chain(right.metadata_terms()) {
                collect_bitvector_atoms(count, atoms);
            }
        }

        OldConditionTerm::AlgebraicEqual(left, right) => {
            left.for_each_machine_operand(|view| match view {
                MachineOperandView::Old(term) => collect_bitvector_atoms(term, atoms),
                MachineOperandView::Shared(_) => {
                    selected_atoms::collect(&view.retain(MachineIntegerType::Int32), atoms)
                }
            });
            right.for_each_machine_operand(|view| match view {
                MachineOperandView::Old(term) => collect_bitvector_atoms(term, atoms),
                MachineOperandView::Shared(_) => {
                    selected_atoms::collect(&view.retain(MachineIntegerType::Int32), atoms)
                }
            });
        }
        crate::kernel::binary_bitvector_condition!(left, right) => {
            collect_bitvector_atoms(left, atoms);
            collect_bitvector_atoms(right, atoms);
        }
        crate::kernel::integer_comparison_condition!(left, right) => {
            let mut visited = BTreeSet::new();
            collect_integer_bitvector_atoms(left, atoms, &mut visited);
            collect_integer_bitvector_atoms(right, atoms, &mut visited);
        }
        OldConditionTerm::Float32(float_condition) | OldConditionTerm::Float64(float_condition) => {
            float_condition.for_each_bitvector_term(|term| collect_bitvector_atoms(term, atoms));
        }
        OldConditionTerm::AddressOffsetEqual(left, right) => {
            collect_pointer_offset_bitvector_atoms(left, atoms);
            collect_pointer_offset_bitvector_atoms(right, atoms);
        }
        OldConditionTerm::AddressEqual(left, right) => {
            collect_pointer_bitvector_atoms(left, atoms);
            collect_pointer_bitvector_atoms(right, atoms);
        }
        OldConditionTerm::Constant(_) | OldConditionTerm::Variable(_) => {}
        // As a word-valued Click application's: opaque.
        OldConditionTerm::BoolApplication(_) => {}
        OldConditionTerm::BoolIf {
            condition,
            then_condition,
            else_condition,
        } => {
            for condition in [condition, then_condition, else_condition] {
                collect_condition_bitvector_atoms(condition, atoms);
            }
        }
        OldConditionTerm::BoolEqual(left, right) => {
            collect_condition_bitvector_atoms(left, atoms);
            collect_condition_bitvector_atoms(right, atoms);
        }
    }
}

/// The atoms of the machine values an Integer term observes. Arithmetic is
/// walked once per shared node; applications, matches and folds are opaque.
fn collect_integer_bitvector_atoms(
    term: &SharedIntegerTerm,
    atoms: &mut BTreeSet<BitvectorEqualityAtomKey>,
    visited: &mut BTreeSet<u64>,
) {
    if !visited.insert(term.id()) {
        return;
    }
    match &**term {
        IntegerTerm::Machine(machine) => selected_atoms::collect(machine, atoms),
        IntegerTerm::Negate(inner) => collect_integer_bitvector_atoms(inner, atoms, visited),
        crate::kernel::binary_integer_term!(left, right) => {
            collect_integer_bitvector_atoms(left, atoms, visited);
            collect_integer_bitvector_atoms(right, atoms, visited);
        }
        IntegerTerm::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_bitvector_atoms(condition, atoms);
            collect_integer_bitvector_atoms(then_term, atoms, visited);
            collect_integer_bitvector_atoms(else_term, atoms, visited);
        }
        _ => {}
    }
}

fn collect_bitvector_atoms(term: &OldMachineTerm, atoms: &mut BTreeSet<BitvectorEqualityAtomKey>) {
    if let Some(atom) = bitvector_equality_atom_key(term) {
        atoms.insert(atom);
    }
    match term {
        OldMachineTerm::ThreadHandle(_) => {}
        crate::kernel::binary_machine_term!(left, right) => {
            collect_bitvector_atoms(left, atoms);
            collect_bitvector_atoms(right, atoms);
        }
        OldMachineTerm::Float32Binary { left, right, .. }
        | OldMachineTerm::Float64Binary { left, right, .. } => {
            collect_bitvector_atoms(left, atoms);
            collect_bitvector_atoms(right, atoms);
        }
        crate::kernel::unary_machine_term!(value) => collect_bitvector_atoms(value, atoms),
        OldMachineTerm::BoolCast { value, .. } => collect_condition_bitvector_atoms(value, atoms),
        OldMachineTerm::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_bitvector_atoms(condition, atoms);
            collect_bitvector_atoms(then_term, atoms);
            collect_bitvector_atoms(else_term, atoms);
        }
        OldMachineTerm::RangeFold {
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
        OldMachineTerm::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                collect_bitvector_atoms(argument, atoms);
            }
        }
        OldMachineTerm::ClickFunctionApplication { .. }
        | OldMachineTerm::PureApplicationCount(_) => {}
        OldMachineTerm::AlgebraicMatch { arms, .. } => {
            for arm in arms {
                collect_bitvector_atoms(&arm.body, atoms);
            }
        }
        OldMachineTerm::MemoryLoad(_, pointer, _) => {
            collect_pointer_bitvector_atoms(pointer, atoms)
        }
        OldMachineTerm::IntegerAddress(pointer, _) => {
            collect_pointer_bitvector_atoms(pointer, atoms)
        }
        // A load variable names one read; the atoms of the address it read
        // are the atoms an equality must rewrite to reach it (`p->q->x`
        // under `p->q == r`). Follow registered addresses a bounded number
        // of levels, so the selection stays proportional to the term.
        OldMachineTerm::Variable(variable) => collect_load_address_atoms(*variable, atoms, 0),
        OldMachineTerm::Constant { .. } => {}
        OldMachineTerm::IntegerToMachine { .. } => {}
    }
}

/// Load-address levels followed when collecting a term's atoms.
const LOAD_ADDRESS_ATOM_DEPTH: usize = 3;

fn collect_load_address_atoms(
    variable: Variable,
    atoms: &mut BTreeSet<BitvectorEqualityAtomKey>,
    depth: usize,
) {
    if depth >= LOAD_ADDRESS_ATOM_DEPTH || !crate::kernel::is_load_variable(&variable) {
        return;
    }
    let Some((_, pointer)) = crate::kernel::eval::registered_load_for_variable(&variable) else {
        return;
    };
    let mut source_hasher = std::collections::hash_map::DefaultHasher::new();
    pointer.hash(&mut source_hasher);
    atoms.insert(BitvectorEqualityAtomKey::PointerReadSource(
        source_hasher.finish(),
    ));
    if let AddressBase::Symbolic(inner) = pointer.base {
        atoms.insert(BitvectorEqualityAtomKey::Variable(inner));
        collect_load_address_atoms(inner, atoms, depth + 1);
    }
    let mut pending = vec![&pointer.offset];
    while let Some(offset) = pending.pop() {
        match offset.view() {
            OffsetView::Add(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            OffsetView::Int32Scaled { index: value, .. }
            | OffsetView::Int64Scaled { index: value, .. } => {
                if let Some(atom) = selected_atoms::root_atom(value.operand_view()) {
                    atoms.insert(atom);
                }
                if let Some(inner) = value.operand_view().variable() {
                    collect_load_address_atoms(*inner, atoms, depth + 1);
                }
            }
            OffsetView::Constant(_) | OffsetView::Variable(_) => {}
        }
    }
}

fn collect_pointer_bitvector_atoms(
    pointer: &Address,
    atoms: &mut BTreeSet<BitvectorEqualityAtomKey>,
) {
    let mut address_hasher = std::collections::hash_map::DefaultHasher::new();
    pointer.hash(&mut address_hasher);
    atoms.insert(BitvectorEqualityAtomKey::PointerReadSource(
        address_hasher.finish(),
    ));
    if let AddressBase::Symbolic(variable) = pointer.base {
        atoms.insert(BitvectorEqualityAtomKey::Variable(variable));
        collect_load_address_atoms(variable, atoms, 0);
    }
    collect_pointer_offset_bitvector_atoms(&pointer.offset, atoms);
}

fn collect_pointer_offset_bitvector_atoms(
    offset: &AddressOffset,
    atoms: &mut BTreeSet<BitvectorEqualityAtomKey>,
) {
    offset.for_each_scaled_operand(|value| selected_atoms::collect(value, atoms));
}

fn quantified_identity_shape(mut fact: &Proposition) -> bool {
    while let Proposition::Implies(_, body) = fact {
        fact = body;
    }
    matches!(
        fact,
        Proposition::ForAll { .. } | Proposition::Exists { .. }
    )
}

fn index_quantified_identity(
    index: PersistentMap<super::PropositionIdentityKey, Arc<Proposition>>,
    fact: &Arc<Proposition>,
) -> PersistentMap<super::PropositionIdentityKey, Arc<Proposition>> {
    if !quantified_identity_shape(fact) {
        return index;
    }
    let Some(key) = super::proposition_identity_key(fact) else {
        return index;
    };
    if index.get(&key).is_some() {
        index
    } else {
        index.with_inserted(key, fact.clone())
    }
}

fn index_quantified_fact(
    mut index: PersistentMap<QuantifiedEquivalenceKey, PersistentSequence<Arc<Proposition>>>,
    fact: &Arc<Proposition>,
) -> PersistentMap<QuantifiedEquivalenceKey, PersistentSequence<Arc<Proposition>>> {
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

/// The most guards and sub-conjunctions a guarded universal contributes to
/// the projection index. A fact past either bound is indexed only up to it:
/// the index is a bounded selector, and a miss leaves the goal to the
/// explicit `intro`/`instantiate` proof.
const MAX_PROJECTED_UNIVERSAL_GUARDS: usize = 8;
const MAX_PROJECTED_UNIVERSAL_CONJUNCTS: usize = 16;

/// Each proper sub-conjunction of a guarded universal's conclusion, restated
/// under the same binder and guards. `forall k { G implies (A and B) and C }`
/// yields the universals concluding `A and B`, `A`, `B`, and `C`, in that
/// order. Anything other than a universal whose guard chain ends in a
/// conjunction yields nothing.
pub(crate) fn guarded_universal_conjunct_projections(fact: &Proposition) -> Vec<Proposition> {
    let Proposition::ForAll {
        var,
        sort,
        body,
        name,
    } = fact
    else {
        return Vec::new();
    };
    let mut guards = Vec::new();
    let mut conclusion = body.as_ref();
    while let Proposition::Implies(guard, consequent) = conclusion {
        if guards.len() == MAX_PROJECTED_UNIVERSAL_GUARDS {
            return Vec::new();
        }
        guards.push(guard.as_ref());
        conclusion = consequent;
    }
    let Proposition::And(left, right) = conclusion else {
        return Vec::new();
    };
    let mut parts = Vec::new();
    let mut pending = vec![right.as_ref(), left.as_ref()];
    while let Some(part) = pending.pop() {
        if parts.len() == MAX_PROJECTED_UNIVERSAL_CONJUNCTS {
            break;
        }
        parts.push(part);
        if let Proposition::And(left, right) = part {
            pending.push(right);
            pending.push(left);
        }
    }
    parts
        .into_iter()
        .map(|part| {
            let body = guards.iter().rev().fold(
                crate::kernel::clone_proposition_iteratively(part),
                |body, guard| {
                    Proposition::Implies(
                        Box::new(crate::kernel::clone_proposition_iteratively(guard)),
                        Box::new(body),
                    )
                },
            );
            Proposition::ForAll {
                var: *var,
                sort: sort.clone(),
                body: Box::new(body),
                name: name.clone(),
            }
        })
        .collect()
}

fn index_quantified_conjunct_projections(
    mut index: PersistentMap<QuantifiedEquivalenceKey, PersistentSequence<Arc<Proposition>>>,
    fact: &Arc<Proposition>,
) -> PersistentMap<QuantifiedEquivalenceKey, PersistentSequence<Arc<Proposition>>> {
    for projection in guarded_universal_conjunct_projections(fact) {
        let Some(key) = quantified_equivalence_index_key(&projection) else {
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

fn index_implication_consequents(
    mut index: PersistentMap<MemoryErasedPropositionKey, PersistentSequence<ImplicationCandidate>>,
    mut quantified_index: PersistentMap<
        QuantifiedEquivalenceKey,
        PersistentSequence<ImplicationCandidate>,
    >,
    fact: &Proposition,
) -> (
    PersistentMap<MemoryErasedPropositionKey, PersistentSequence<ImplicationCandidate>>,
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
            whole: None,
        };
        // Each conjunct of a conjunctive consequent is filed too, naming the
        // whole consequent, so a goal that is one conjunct finds the
        // implication in one probe.
        if matches!(consequent.as_ref(), Proposition::And(..)) {
            let mut conjuncts = Vec::new();
            collect_owned_atomic_conjuncts(consequent, &mut conjuncts);
            for conjunct in &conjuncts {
                let key = memory_erased_proposition_key(conjunct);
                let mut bucket = index.get(&key).cloned().unwrap_or_default();
                bucket.push(ImplicationCandidate {
                    antecedents: antecedents.clone(),
                    consequent: conjunct.clone(),
                    whole: Some(consequent.as_ref().clone()),
                });
                index = index.with_inserted(key, bucket);
            }
        }
        let normalized = consequent.clone();
        let mut keys = vec![memory_erased_proposition_key(consequent)];
        let normalized_key = memory_erased_proposition_key(&normalized);
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
    mut index: PersistentSet<PropositionKey>,
    fact: &Proposition,
) -> PersistentSet<PropositionKey> {
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
                    index = index.with_value(PropositionKey::new(conjunct));
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
                    index = index.with_value(PropositionKey::new(conjunct));
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
    exact: &PersistentSet<Arc<Proposition>>,
    fact: &Proposition,
) -> bool {
    match fact {
        Proposition::And(left, right) => {
            directly_conflicts_with_normalized_index(exact, left)
                || directly_conflicts_with_normalized_index(exact, right)
        }
        Proposition::ConditionIs(condition, value) => {
            exact.contains(&Proposition::condition_is(condition.clone(), !value))
        }
        Proposition::Not(body) => exact.contains(body.as_ref()),
        other => exact.contains(&Proposition::Not(Box::new(other.clone()))),
    }
}

fn index_predicate_fact(
    mut index: PersistentMap<String, PersistentSequence<Arc<Proposition>>>,
    fact: &Arc<Proposition>,
) -> PersistentMap<String, PersistentSequence<Arc<Proposition>>> {
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
        Address, AddressOffset, IntegerRangeFoldIndex, IntegerTerm, MachineIntegerType,
        OldMachineTerm, ProgramValue, SharedIntegerRangeEndpoint, SharedIntegerTerm,
        SharedMachineIntegerTerm, Sort, SymbolicMemory, Variable,
    };

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: 1.4s in the parallel gate"]
    fn opaque_pointer_alias_selection_ignores_unrelated_facts() {
        let read = Address::symbolic(Variable(949_001));
        let target = Address::symbolic(Variable(949_002));
        let alias =
            Proposition::condition_is(OldConditionTerm::address_equal(read.clone(), target), true);
        let goal = Proposition::condition_is(
            OldConditionTerm::equal(
                OldMachineTerm::read_named(
                    ProgramPoint::at(&(crate::kernel::intern_memory(SymbolicMemory::new()))),
                    Box::new(read.offset_by_bytes(4)),
                    crate::kernel::LoadKind::Int32,
                ),
                OldMachineTerm::constant(42),
            ),
            true,
        );
        for size in [16_u32, 64, 256, 1024, 4096] {
            let mut facts = PureFactStore::default();
            for index in 0..size {
                facts = facts.with_kernel_checked_fact(Proposition::condition_is(
                    OldConditionTerm::address_equal(
                        Address::symbolic(Variable(950_000 + 2 * u64::from(index))),
                        Address::symbolic(Variable(950_001 + 2 * u64::from(index))),
                    ),
                    true,
                ));
            }
            facts = facts.with_kernel_checked_fact(alias.clone());
            assert_eq!(facts.load_equalities_mentioning(&goal), vec![alias.clone()]);
            let comparisons = facts
                .equality_atom_lookup_comparisons(&OldMachineTerm::Variable(Variable(949_001)));
            let height = (u32::BITS - size.leading_zeros()) as usize;
            assert!(comparisons <= 2 * height + 4, "{size}: {comparisons}");
            assert!(
                !facts.contains(&goal),
                "candidate selection grants no equality"
            );
        }
    }

    fn integer_index() -> IntegerRangeFoldIndex {
        IntegerRangeFoldIndex::Integer {
            start: IntegerTerm::constant_i64(0).into(),
            end: IntegerTerm::constant_i64(2).into(),
        }
    }

    fn int32_index() -> IntegerRangeFoldIndex {
        IntegerRangeFoldIndex::Int32 {
            start: SharedIntegerRangeEndpoint::intern(OldMachineTerm::constant(0)),
            end: SharedIntegerRangeEndpoint::intern(OldMachineTerm::constant(2)),
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
        Proposition::condition_is(
            OldConditionTerm::IntegerEqual(left.into(), right.into()),
            true,
        )
    }

    fn less_equal(left: IntegerTerm, right: IntegerTerm) -> Proposition {
        Proposition::condition_is(
            OldConditionTerm::IntegerLessEqual(left.into(), right.into()),
            true,
        )
    }

    fn less_than(left: IntegerTerm, right: IntegerTerm) -> Proposition {
        Proposition::condition_is(
            OldConditionTerm::IntegerLessThan(left.into(), right.into()),
            true,
        )
    }

    fn explicit_load_fold(
        memory: &crate::kernel::SharedMemory,
        accumulator: Variable,
        item: Variable,
    ) -> IntegerTerm {
        fold(
            int32_index(),
            accumulator,
            item,
            IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int32,
                OldMachineTerm::read_named(
                    ProgramPoint::at(memory),
                    Box::new(Address::new(
                        "retained_state-alpha-facts".into(),
                        AddressOffset::constant(0),
                    )),
                    crate::kernel::LoadKind::Int32,
                ),
            )),
        )
    }

    fn loadable_forall(
        memory: &SymbolicMemory,
        binder: Variable,
        block: &str,
        free_offset: Option<Variable>,
        bytes: u32,
    ) -> Proposition {
        let bound_offset = AddressOffset::scaled_int32_node(OldMachineTerm::Variable(binder), 4);
        let offset = free_offset.map_or(bound_offset.clone(), |free| {
            AddressOffset::raw_add(
                bound_offset,
                AddressOffset::scaled_int32_node(OldMachineTerm::Variable(free), 1),
            )
        });
        crate::kernel::quantifiers::test_forall(
            Default::default(),
            binder,
            Sort::ProgramInt32,
            Proposition::MemoryLoadable {
                point: Default::default(),
                memory: memory.clone(),
                base: Address::new(block.into(), offset),
                bytes: (OldMachineTerm::constant(bytes)).into(),
                wide: false,
            },
        )
    }

    fn loadable_exists(
        memory: &SymbolicMemory,
        name: &str,
        binder: Variable,
        block: &str,
        free_offset: Option<Variable>,
        bytes: u32,
    ) -> Proposition {
        let bound_offset = AddressOffset::scaled_int32_node(OldMachineTerm::Variable(binder), 4);
        let offset = free_offset.map_or(bound_offset.clone(), |free| {
            AddressOffset::raw_add(
                bound_offset,
                AddressOffset::scaled_int32_node(OldMachineTerm::Variable(free), 1),
            )
        });
        crate::kernel::quantifiers::test_exists(
            name.into(),
            binder,
            Sort::ProgramInt32,
            Proposition::MemoryLoadable {
                point: Default::default(),
                memory: memory.clone(),
                base: Address::new(block.into(), offset),
                bytes: (OldMachineTerm::constant(bytes)).into(),
                wide: false,
            },
        )
    }

    #[test]
    fn transport_index_extracts_separation_without_importing_arithmetic() {
        let range = |block: &str| {
            crate::kernel::Resource::Memory(crate::kernel::MemoryRange::new(
                Address::new(block.into(), AddressOffset::constant(0)),
                OldMachineTerm::constant(0),
                OldMachineTerm::Variable(Variable(210_000)),
            ))
        };
        let separation = Proposition::ResourceSeparate {
            left: Box::new(range("a")),
            right: Box::new(range("b")),
        };
        let bound = Proposition::condition_is(
            OldConditionTerm::signed_less_equal(
                OldMachineTerm::constant(0),
                OldMachineTerm::Variable(Variable(210_000)),
            ),
            true,
        );
        let conjunction = Proposition::And(Box::new(separation.clone()), Box::new(bound.clone()));
        for facts in [
            PureFactStore::from_ordered(std::slice::from_ref(&conjunction)),
            PureFactStore::from_ordered(&[]).with_fact(conjunction),
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
        let facts = PureFactStore::from_ordered(&[conditional]);
        assert!(
            !facts
                .implicit_transport_assumptions()
                .contains_assumed_exact(&separation)
        );
    }

    #[test]
    fn induction_domain_uses_only_the_selected_signed_bound_bucket() {
        let measure = OldMachineTerm::Variable(Variable(123456));
        for size in [8, 32, 128, 512] {
            let unrelated = (0..size)
                .map(|index| {
                    Proposition::condition_is(
                        OldConditionTerm::Compare {
                            format: MachineIntegerType::Int32,
                            relation: CompareRelation::GreaterEqual,
                            left: Box::new(OldMachineTerm::Variable(Variable(index))),
                            right: Box::new(OldMachineTerm::constant(0)),
                        },
                        true,
                    )
                })
                .collect::<Vec<_>>();
            let base = PureFactStore::from_ordered(&unrelated);
            assert!(!base.has_nonnegative_induction_domain(&measure));
            for (bound, strict, expected) in [
                (5i32, false, true),
                (-1, true, true),
                (-1, false, false),
                (-2, true, false),
            ] {
                let condition = if strict {
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterThan,
                        left: Box::new(measure.clone()),
                        right: Box::new(OldMachineTerm::constant(bound as u32)),
                    }
                } else {
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterEqual,
                        left: Box::new(measure.clone()),
                        right: Box::new(OldMachineTerm::constant(bound as u32)),
                    }
                };
                let facts =
                    base.with_kernel_checked_fact(Proposition::condition_is(condition, true));
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
        let facts = PureFactStore::from_ordered(std::slice::from_ref(&source_fact));

        assert_eq!(
            facts.matching_fact_across_effects(&required_fact, &[]),
            Some(source_fact.clone())
        );
        assert!(facts.exact_available_across_effects(&required_fact, &[]));
        assert!(facts.pure_known_available(&required_fact));
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
        let facts = PureFactStore::from_ordered(std::slice::from_ref(&source_fact));

        assert_eq!(
            facts.matching_fact_across_effects(&required_fact, &[]),
            Some(source_fact.clone())
        );
        assert!(facts.exact_available_across_effects(&required_fact, &[]));
        assert!(facts.pure_known_available(&required_fact));
    }

    #[test]
    fn integer_alpha_fact_lookup_keeps_inequality_state_identity() {
        let before = crate::kernel::intern_memory(
            SymbolicMemory::new().with_block("retained_state-alpha-facts", 8),
        );
        let changed = crate::kernel::intern_memory(before.as_ref().clone().store(
            Address::new(
                "retained_state-alpha-facts".into(),
                AddressOffset::constant(0),
            ),
            ProgramValue::Int32(OldMachineTerm::constant(7)),
        ));
        let source_fact = less_equal(
            IntegerTerm::constant_i64(9),
            explicit_load_fold(&before, Variable(200_400), Variable(200_401)),
        );
        let renamed_fact = less_equal(
            IntegerTerm::constant_i64(9),
            explicit_load_fold(&before, Variable(200_500), Variable(200_501)),
        );
        let changed_state_fact = less_equal(
            IntegerTerm::constant_i64(9),
            explicit_load_fold(&changed, Variable(200_500), Variable(200_501)),
        );
        let facts = PureFactStore::from_ordered(std::slice::from_ref(&source_fact));

        assert_eq!(
            facts.matching_fact_across_effects(&renamed_fact, &[]),
            Some(source_fact)
        );
        assert!(
            facts
                .matching_fact_across_effects(&changed_state_fact, &[])
                .is_none()
        );
    }

    #[test]
    fn quantified_loadable_alpha_index_renames_binder_but_keeps_exact_payload() {
        let memory = SymbolicMemory::new()
            .with_block("quantified-viewable", 32)
            .store(
                Address::new("quantified-viewable".into(), AddressOffset::constant(0)),
                // A value the binder does not name: an occurrence of the
                // binder inside the body's state would be bound too.
                ProgramValue::Int32(OldMachineTerm::Variable(Variable(207_900))),
            );
        let changed_memory = memory.clone().store(
            Address::new("quantified-viewable".into(), AddressOffset::constant(0)),
            ProgramValue::Int32(OldMachineTerm::constant(7)),
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
        let changed_memory_state = loadable_forall(
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
        let facts = PureFactStore::from_ordered(std::slice::from_ref(&source));

        assert_eq!(
            facts.matching_fact_across_effects(&renamed, &[]),
            Some(source.clone())
        );
        for mismatch in [
            changed_memory_state,
            changed_pointer,
            changed_width,
            free_mismatch,
        ] {
            assert!(
                facts.matching_fact_across_effects(&mismatch, &[]).is_none(),
                "viewability alpha matching must retain state, pointer, width, and free IDs"
            );
        }
    }

    #[test]
    fn quantified_loadable_root_existential_ignores_display_name() {
        let memory = SymbolicMemory::new().with_block("root-existential-viewable", 32);
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
        let facts = PureFactStore::from_ordered(std::slice::from_ref(&source));

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
        let predicate = |name: &str, binder: Variable, state: ExecutionState| {
            crate::kernel::quantifiers::test_exists(
                name.to_string(),
                binder,
                Sort::ProgramInt32,
                Proposition::Predicate {
                    name: "sample".to_string(),
                    arguments: vec![
                        Term::ExecutionState(Box::new(state)),
                        Term::ProgramValue(
                            (ProgramValue::Int32(OldMachineTerm::Variable(binder))).into(),
                        ),
                    ],
                },
            )
        };
        let state =
            ExecutionState::new().with_local("x", ProgramValue::Int32(OldMachineTerm::constant(7)));
        let available = predicate("first", Variable(300_001), state.clone());
        let renamed = predicate("second", Variable(300_002), state.clone());
        let independently_empty = predicate("second", Variable(300_002), ExecutionState::new());
        let empty = predicate("first", Variable(300_001), ExecutionState::new());
        let changed_state = predicate(
            "second",
            Variable(300_002),
            state.with_local("x", ProgramValue::Int32(OldMachineTerm::constant(8))),
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
        let facts = PureFactStore::from_ordered(std::slice::from_ref(&available));
        assert_eq!(facts.matching_quantified_fact(&renamed), Some(available));
        assert!(facts.matching_quantified_fact(&changed_state).is_none());
    }

    #[test]
    fn implication_extract_renames_existential_but_keeps_state_and_antecedent() {
        let block = "implication-existential-viewable";
        let memory = SymbolicMemory::new().with_block(block, 32);
        let changed_memory = memory.clone().store(
            Address::new(block.into(), AddressOffset::constant(0)),
            ProgramValue::Int32(OldMachineTerm::constant(1)),
        );
        let consequent = loadable_exists(&memory, "callee", Variable(207_700), block, None, 4);
        let renamed = loadable_exists(&memory, "caller", Variable(207_800), block, None, 4);
        let changed_memory_state =
            loadable_exists(&changed_memory, "caller", Variable(207_800), block, None, 4);
        let antecedent = Proposition::condition_is(OldConditionTerm::Constant(true), true);
        let implication = Proposition::Implies(Box::new(antecedent.clone()), Box::new(consequent));
        let without_antecedent = PureFactStore::from_ordered(std::slice::from_ref(&implication));
        assert!(!without_antecedent.contains_discharged_implication_consequent(&renamed));

        let facts = PureFactStore::from_ordered(&[implication, antecedent]);
        assert!(facts.contains_discharged_implication_consequent(&renamed));
        assert!(!facts.contains_discharged_implication_consequent(&changed_memory_state));
    }

    #[test]
    fn implication_extract_renames_path_inside_function_equality() {
        let path_type = crate::kernel::AlgebraicType::parameter("Path".into());
        let path_reaches = |name: &str, binder: Variable| {
            crate::kernel::quantifiers::test_exists(
                name.into(),
                binder,
                Sort::Algebraic(path_type.clone()),
                Proposition::Equal(
                    Term::Bitvector32(
                        OldMachineTerm::ClickFunctionApplication {
                            name: "walk".into(),
                            arguments: vec![PureFunctionArgument::Algebraic(AlgebraicTerm {
                                algebraic_type: path_type.clone(),
                                node: AlgebraicTermNode::Variable(binder),
                            })],
                        }
                        .into(),
                    ),
                    Term::Bitvector32(OldMachineTerm::constant(1).into()),
                ),
            )
        };
        let source = path_reaches("callee_path", Variable(207_750));
        let required = path_reaches("caller_path", Variable(207_751));
        let antecedent = Proposition::condition_is(OldConditionTerm::Constant(true), true);
        let facts = PureFactStore::from_ordered(&[
            Proposition::Implies(Box::new(antecedent.clone()), Box::new(source)),
            antecedent,
        ]);
        assert!(facts.contains_discharged_implication_consequent(&required));
    }

    #[test]
    fn quantified_implication_extract_does_not_scan_unrelated_consequents() {
        let memory = SymbolicMemory::new().with_block("selected-implication", 32);
        let antecedent = Proposition::condition_is(OldConditionTerm::Constant(true), true);
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
            let facts = PureFactStore::from_ordered(&ordered);
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
        let memory = SymbolicMemory::new().with_block("quantified-viewable-scale", 32);
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
            let facts = PureFactStore::from_ordered(&ordered);
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
    fn quantified_loadable_alpha_budget_fails_closed_before_memory_substitution() {
        let memory = SymbolicMemory::new().with_block("quantified-viewable-budget", 8);
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
            source_tactic_path: None,
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
                        crate::kernel::proof::fact_keys::state_quantified_alpha_equivalent(
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
        let false_fact = Proposition::condition_is(
            OldConditionTerm::IntegerLessEqual(
                required.into(),
                IntegerTerm::constant_i64(9).into(),
            ),
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
        let facts = PureFactStore::from_ordered(std::slice::from_ref(&source_fact));

        for candidate in [wrong_kind, false_fact, free_binder] {
            assert!(
                facts
                    .matching_fact_across_effects(&candidate, &[])
                    .is_none()
            );
            assert!(!facts.exact_available_across_effects(&candidate, &[]));
            assert!(!facts.pure_known_available(&candidate));
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
                    OldMachineTerm::Variable(item),
                )),
            ),
        );

        let facts = PureFactStore::from_ordered(std::slice::from_ref(&source_fact));
        for candidate in [free_mismatch, bound_mismatch, carrier_mismatch] {
            let required = equality(IntegerTerm::constant_i64(9), candidate);
            assert!(facts.matching_fact_across_effects(&required, &[]).is_none());
            assert!(!facts.exact_available_across_effects(&required, &[]));
        }
    }

    #[test]
    fn integer_alpha_fact_lookup_requires_the_same_load_state() {
        let before = crate::kernel::intern_memory(
            SymbolicMemory::new().with_block("retained_state-alpha-facts", 8),
        );
        let changed = crate::kernel::intern_memory(before.as_ref().clone().store(
            Address::new(
                "retained_state-alpha-facts".into(),
                AddressOffset::constant(0),
            ),
            ProgramValue::Int32(OldMachineTerm::constant(7)),
        ));
        let source_fact = equality(
            IntegerTerm::constant_i64(9),
            explicit_load_fold(&before, Variable(206_000), Variable(206_001)),
        );
        let renamed_fact = equality(
            IntegerTerm::constant_i64(9),
            explicit_load_fold(&before, Variable(206_100), Variable(206_101)),
        );
        let changed_state_fact = equality(
            IntegerTerm::constant_i64(9),
            explicit_load_fold(&changed, Variable(206_100), Variable(206_101)),
        );
        let facts = PureFactStore::from_ordered(std::slice::from_ref(&source_fact));

        assert_eq!(
            facts.matching_fact_across_effects(&renamed_fact, &[]),
            Some(source_fact)
        );
        assert!(
            facts
                .matching_fact_across_effects(&changed_state_fact, &[])
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
        let small_facts = PureFactStore::from_ordered(&small);
        let large_facts = PureFactStore::from_ordered(&large);

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

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/proof/facts/integer_equality_fact_index_tests.rs");
    }
}

#[cfg(test)]
mod retained_root_context_tests {
    use super::*;

    #[test]
    fn cached_root_sources_share_the_graph_without_readmitting_history() {
        for size in [16u32, 64, 256, 1024] {
            let inputs = (0..size)
                .map(|index| {
                    Proposition::condition_is(
                        OldConditionTerm::equal(
                            OldMachineTerm::Variable(Variable(970_000 + u64::from(index))),
                            OldMachineTerm::constant(index),
                        ),
                        true,
                    )
                })
                .collect::<Vec<_>>();
            let source = PureFactStore::from_ordered(&inputs);
            let before = crate::kernel::reasoning::path_facts::context_rebuild_entries();
            let retained = PureFactStore::from_source(&source);
            let rebuilt = crate::kernel::reasoning::path_facts::context_rebuild_entries() - before;
            assert_eq!(rebuilt, 0, "cached root readmitted {size} input facts");
            assert!(
                retained.assumptions().equality_graph.input_key()
                    == source.assumptions().equality_graph.input_key(),
                "root conversion changed the trusted graph lineage"
            );
            assert!(retained.contains(inputs.last().unwrap()));
            assert_eq!(retained.fact_count(), size as usize);
        }
    }
}

#[cfg(test)]
mod held_separation_tests {
    use super::*;

    fn alternate_carrier(resource: Resource) -> Resource {
        let Resource::Memory(range) = resource else {
            unreachable!()
        };
        let Resource::Memory(origin) = cell(999) else {
            unreachable!()
        };
        Resource::Memory(
            range
                .with_provenance(origin.base().clone())
                .with_bounds_owner(Some(origin.base().clone()), false)
                .with_typed_carrier(),
        )
    }

    #[test]
    fn partition_spatial_lookup_keeps_access_support_and_branch_scope() {
        let a = cell(0);
        let a_other = alternate_carrier(a.clone());
        let b = cell(1);
        let owner = ResourceFact::own(a.clone());
        let root = ResourceContext::new()
            .unchecked_with_facts([owner.clone(), ResourceFact::own(b.clone())]);
        assert!(root.proves_exact_partition_separation(&a_other, &b));
        assert!(!root.proves_exact_partition_separation(&a_other, &a));
        let removed = root.clone().without_exact_representation(&owner).unwrap();
        assert!(!removed.proves_exact_partition_separation(&a_other, &b));
        assert!(root.proves_exact_partition_separation(&a_other, &b));
        let views = ResourceContext::new()
            .unchecked_with_facts([ResourceFact::View(a.clone()), ResourceFact::View(b.clone())]);
        assert!(!views.proves_exact_partition_separation(&a_other, &b));
        let projected = ResourceContext::new()
            .unchecked_with_facts([ResourceFact::own(b.clone())])
            .unchecked_with_supported_facts(
                &ResourceFact::own(b.clone()),
                [ResourceFact::View(a.clone())],
            );
        assert!(!projected.proves_exact_partition_separation(&a_other, &b));
        let non_unit = ResourceContext::new().unchecked_with_facts([
            ResourceFact::Own(a, Box::new(OldMachineTerm::constant(0).into())),
            ResourceFact::own(b.clone()),
        ]);
        assert!(!non_unit.proves_exact_partition_separation(&a_other, &b));
    }

    #[test]
    fn separation_reuses_physical_ranges_without_reusing_authority() {
        let left = range(0, 1, 3, 4);
        let other_carrier = alternate_carrier(left.clone());
        assert_ne!(left, other_carrier);
        let right = cell(1);
        let original = separation(left.clone(), right.clone());
        let restated = separation(other_carrier.clone(), right.clone());
        for (held, goal) in [(&original, &restated), (&restated, &original)] {
            for source in [
                held.clone(),
                Proposition::And(Box::new(held.clone()), Box::new(held.clone())),
            ] {
                let root = PureFactStore::default();
                let facts = root.with_fact(source);
                assert!(facts.pure_known_available(goal));
                assert!(!root.contains(goal));
                for changed in [
                    range(2, 1, 3, 4),
                    range(0, 0, 3, 4),
                    range(0, 1, 4, 4),
                    range(0, 1, 3, 8),
                ] {
                    assert!(!facts.contains(&separation(changed, right.clone())));
                }
                let Resource::Memory(narrow) = &left else {
                    unreachable!()
                };
                let wide = Resource::Memory(MemoryRange::new_wide(
                    narrow.base().clone(),
                    narrow.start().clone(),
                    narrow.end().clone(),
                    4,
                ));
                assert!(!facts.contains(&separation(wide, right.clone())));
            }
        }
        // The spatial equivalence does not generalize to containment authority.
        let contains = |part| Proposition::ResourceContains {
            parent: Box::new(part),
            child: Box::new(right.clone()),
        };
        let facts = PureFactStore::default().with_fact(contains(left));
        assert!(!facts.contains(&contains(other_carrier)));
    }

    fn cell(index: u64) -> Resource {
        Resource::Memory(MemoryRange::new(
            Address::new(
                "shared".into(),
                AddressOffset::variable(Variable(980_000 + index)),
            ),
            OldMachineTerm::constant(0),
            OldMachineTerm::constant(1),
        ))
    }

    fn separation(left: Resource, right: Resource) -> Proposition {
        Proposition::ResourceSeparate {
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    fn range(index: u64, start: u32, end: u32, width: u32) -> Resource {
        let Resource::Memory(cell) = cell(index) else {
            unreachable!()
        };
        Resource::Memory(MemoryRange::new_with_element_width(
            cell.base().clone(),
            OldMachineTerm::constant(start),
            OldMachineTerm::constant(end),
            width,
        ))
    }

    #[test]
    fn held_separation_uses_transitive_address_classes_without_leaking_scope() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = |index| {
            let Resource::Memory(range) = cell(index) else {
                unreachable!()
            };
            range.base().clone()
        };
        let link = |a, b| {
            Proposition::condition_is(
                OldConditionTerm::address_equal(pointer(a), pointer(b)),
                true,
            )
        };
        let first = link(0, 2);
        let second = link(2, 3);
        let facts = PureFactStore::from_ordered(&[first.clone(), second]);
        assert!(
            facts
                .assumptions()
                .pointers_known_equal(&pointer(0), &pointer(3))
        );
        let resources = ResourceContext::new_with_equalities(facts.assumptions())
            .unchecked_with_facts([
                ResourceFact::own(range(0, 0, 6, 4)),
                ResourceFact::own(range(1, 0, 3, 8)),
            ]);
        let state = ExecutionState::new().with_resource_context(resources);
        let goal = separation(range(3, 1, 2, 8), range(1, 0, 1, 8));
        assert!(
            facts
                .with_selected_held_resource_separation(&goal, &state)
                .contains(&goal)
        );
        let unseparated = PureFactStore::from_ordered(&[first]);
        assert!(
            !unseparated
                .with_selected_held_resource_separation(&goal, &state)
                .contains(&goal)
        );
        assert!(
            facts
                .with_selected_held_resource_separation(&goal, &state)
                .contains(&goal)
        );
        for refused in [
            separation(range(3, 0, 1, 8), range(0, 1, 2, 8)),
            separation(range(3, 2, 4, 8), range(1, 0, 1, 8)),
        ] {
            assert!(
                !facts
                    .with_selected_held_resource_separation(&refused, &state)
                    .contains(&refused)
            );
        }
    }

    #[test]
    fn held_separation_covers_wide_fields_and_explicit_aliases() {
        let state = ExecutionState::new().with_resource_context(
            ResourceContext::new().unchecked_with_facts([
                ResourceFact::own(range(0, 0, 6, 4)),
                ResourceFact::own(range(1, 0, 3, 8)),
            ]),
        );
        let (Resource::Memory(alias), Resource::Memory(owner)) = (cell(2), cell(0)) else {
            unreachable!()
        };
        let facts = PureFactStore::from_ordered(&[Proposition::condition_is(
            OldConditionTerm::AddressEqual(
                Box::new(alias.base().clone()),
                Box::new(owner.base().clone()),
            ),
            true,
        )]);
        for left in [range(0, 0, 1, 8), range(0, 1, 3, 8), range(2, 0, 1, 8)] {
            let goal = separation(left, range(1, 1, 2, 8));
            assert!(
                facts
                    .with_selected_held_resource_separation(&goal, &state)
                    .contains(&goal)
            );
        }
    }

    #[test]
    fn held_field_separation_requires_complete_distinct_owners() {
        let state = ExecutionState::new().with_resource_context(
            ResourceContext::new().unchecked_with_facts([
                ResourceFact::own(range(0, 0, 6, 4)),
                ResourceFact::own(range(1, 0, 1, 4)),
                ResourceFact::View(range(2, 0, 6, 4)),
            ]),
        );
        for goal in [
            separation(range(0, 0, 1, 8), range(0, 1, 2, 8)),
            separation(range(0, 0, 1, 8), range(0, 0, 2, 8)),
            separation(range(0, 0, 1, 8), range(1, 0, 1, 8)),
            separation(range(0, 0, 1, 8), range(2, 0, 1, 8)),
            separation(range(0, 2, 4, 8), cell(1)),
            separation(range(0, u32::MAX, 1, 8), cell(1)),
        ] {
            assert!(
                !PureFactStore::default()
                    .with_selected_held_resource_separation(&goal, &state)
                    .contains(&goal)
            );
        }
    }

    #[test]
    fn held_field_separation_rejects_aliased_owners() {
        let (Resource::Memory(left), Resource::Memory(right)) = (cell(0), cell(1)) else {
            unreachable!()
        };
        let facts = PureFactStore::from_ordered(&[Proposition::condition_is(
            OldConditionTerm::AddressEqual(
                Box::new(left.base().clone()),
                Box::new(right.base().clone()),
            ),
            true,
        )]);
        let state = ExecutionState::new().with_resource_context(
            ResourceContext::new().unchecked_with_facts([
                ResourceFact::own(range(0, 0, 6, 4)),
                ResourceFact::own(range(1, 0, 6, 4)),
            ]),
        );
        // Even disjoint selected fields must not turn aliased, overlapping
        // owners into a valid partition.
        let goal = separation(range(0, 0, 1, 8), range(1, 1, 2, 8));
        assert!(
            !facts
                .with_selected_held_resource_separation(&goal, &state)
                .contains(&goal)
        );
    }

    /// Views, repeated selection of one owner, and stale/unheld members
    /// cannot manufacture separation from the live ownership partition.
    #[test]
    fn held_separation_requires_two_distinct_current_owners() {
        let state = ExecutionState::new().with_resource_context(
            ResourceContext::new()
                .unchecked_with_facts([ResourceFact::own(cell(0)), ResourceFact::View(cell(1))]),
        );
        for goal in [
            separation(cell(0), cell(0)),
            separation(cell(0), cell(1)),
            separation(cell(0), cell(2)),
        ] {
            assert!(
                !PureFactStore::default()
                    .with_selected_held_resource_separation(&goal, &state)
                    .contains(&goal)
            );
        }
    }

    #[test]
    fn held_separation_does_not_override_pointer_alias_facts() {
        let left = cell(0);
        let right = cell(1);
        let (Resource::Memory(left_range), Resource::Memory(right_range)) = (&left, &right) else {
            unreachable!()
        };
        let alias = Proposition::condition_is(
            OldConditionTerm::AddressEqual(
                Box::new(left_range.base().clone()),
                Box::new(right_range.base().clone()),
            ),
            true,
        );
        // Deliberately assemble a stale partition: the explicit equality
        // must prevent using it as fresh evidence of separation.
        let state = ExecutionState::new().with_resource_context(
            ResourceContext::new().unchecked_with_facts([
                ResourceFact::own(left.clone()),
                ResourceFact::own(right.clone()),
            ]),
        );
        let goal = separation(left, right);
        let facts = PureFactStore::from_ordered(&[alias]);
        assert!(
            !facts
                .with_selected_held_resource_separation(&goal, &state)
                .contains(&goal)
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/proof/facts/held_separation_tests.rs");
    }
}

#[cfg(test)]
mod statement_publication_delta_tests {
    use super::*;
    // Repeated statement premises keep their priority but must not become a new introduction delta.
    #[test]
    fn statement_batches_publish_only_new_facts_and_preserve_order() {
        let fact = |index| Proposition::Predicate {
            name: format!("priority_{index}"),
            arguments: vec![],
        };
        for size in [16, 64, 256, 1024] {
            let prefix = (0..size).map(fact).collect::<Vec<_>>();
            let root = PureFactStore::from_ordered(&prefix);
            let fresh = fact(size);
            let successor =
                root.with_statement_facts(vec![prefix[size - 1].clone(), fresh.clone()]);
            assert_eq!(successor.introduced_since(&root), Some(vec![fresh.clone()]));
            assert_eq!(
                successor.to_vec()[..2],
                [prefix[size - 1].clone(), fresh.clone()]
            );
            assert_eq!(root.to_vec(), prefix);
            let repeated = successor.with_statement_facts(vec![prefix[0].clone(), fresh]);
            assert_eq!(repeated.introduced_since(&successor), Some(vec![]));
            assert_eq!(repeated.to_vec()[0], prefix[0]);
        }
    }
    // Original and reordered case prefixes preserve the selected order and canonical values.
    #[test]
    fn statement_priority_shares_values_for_original_and_reordered_prefixes() {
        let fact = |index| Proposition::Predicate {
            name: format!("case_{index}"),
            arguments: vec![],
        };
        for size in [16, 64, 256, 1024] {
            let prefix_facts = (0..size).map(fact).collect::<Vec<_>>();
            let prefix: ExecutionFacts = prefix_facts
                .iter()
                .cloned()
                .map(ExecutionPureFact::new)
                .collect();
            let root = PureFactStore::from_ordered(&prefix_facts);
            let fresh = fact(size);
            let mut selected = prefix_facts.clone();
            selected.push(fresh.clone());
            let successor =
                root.publish_statement_view(root.statement_view(selected.clone()), &prefix);
            for proposition in &prefix_facts {
                assert!(Arc::ptr_eq(
                    root.top_level_exact.get(proposition).unwrap(),
                    successor.top_level_exact.get(proposition).unwrap(),
                ));
            }
            assert_eq!(successor.to_vec(), selected);
            assert_eq!(successor.introduced_since(&root), Some(vec![fresh]));
            selected.swap(0, 1);
            let reordered =
                root.publish_statement_view(root.statement_view(selected.clone()), &prefix);
            for proposition in &prefix_facts {
                assert!(Arc::ptr_eq(
                    root.top_level_exact.get(proposition).unwrap(),
                    reordered.top_level_exact.get(proposition).unwrap(),
                ));
            }
            assert_eq!(reordered.to_vec(), selected);
            assert_eq!(root.to_vec(), prefix_facts);
        }
    }
}

#[cfg(test)]
mod integer_witness_freshness_tests {
    use super::*;

    #[test]
    fn integer_universal_witnesses_come_from_the_witness_band() {
        let binder = Variable(3_200_000);
        let load = Variable((1 << 40) + 7);
        let integer_fact = |variable| {
            Proposition::condition_is(
                OldConditionTerm::IntegerEqual(
                    crate::kernel::IntegerTerm::var(variable).into(),
                    crate::kernel::IntegerTerm::constant_i64(0).into(),
                ),
                true,
            )
        };
        let facts = PureFactStore::from_ordered(&[
            Proposition::condition_is(
                OldConditionTerm::equal(
                    OldMachineTerm::Variable(load),
                    OldMachineTerm::constant(0),
                ),
                true,
            ),
            integer_fact(binder),
        ]);
        let body = integer_fact(binder);
        let (witness, _) = facts.freshen_integer_forall_body(binder, &body).unwrap();
        assert!(
            crate::kernel::ExecutionBudget::is_universal_witness_variable(witness),
            "{witness:?}"
        );
    }
}

#[cfg(test)]
mod pointer_memory_transport_tests {
    use super::*;
    mod scaling_tests {
        include!("../../scaling_tests/kernel/proof/facts/pointer_memory_transport_tests.rs");
    }
}

#[cfg(test)]
mod quantified_conjunct_projection_tests {
    use super::*;

    fn equals(var: u64, constant: u32) -> Proposition {
        Proposition::condition_is(
            OldConditionTerm::equal(
                OldMachineTerm::Variable(Variable(var)),
                OldMachineTerm::constant(constant),
            ),
            true,
        )
    }
    fn at_most(var: u64, bound: u32) -> Proposition {
        Proposition::condition_is(
            OldConditionTerm::signed_less_equal(
                OldMachineTerm::Variable(Variable(var)),
                OldMachineTerm::constant(bound),
            ),
            true,
        )
    }
    fn and(left: Proposition, right: Proposition) -> Proposition {
        Proposition::And(Box::new(left), Box::new(right))
    }
    /// `forall var { var <= bound implies conclusion(var) }`.
    fn guarded(var: u64, bound: u32, conclusion: impl Fn(u64) -> Proposition) -> Proposition {
        crate::kernel::quantifiers::test_forall(
            Default::default(),
            Variable(var),
            Sort::ProgramInt32,
            Proposition::Implies(Box::new(at_most(var, bound)), Box::new(conclusion(var))),
        )
    }

    #[test]
    fn a_guarded_conjunction_supplies_each_conjunct_under_the_same_guard() {
        let source = guarded(1, 4, |k| and(at_most(k, 9), equals(k, 7)));
        let facts = PureFactStore::from_ordered(std::slice::from_ref(&source));
        // A renamed binder is the same claim.
        for goal in [
            guarded(2, 4, |k| equals(k, 7)),
            guarded(3, 4, |k| at_most(k, 9)),
        ] {
            assert_eq!(
                facts.quantified_conjunct_projection_source(&goal),
                Some(&source)
            );
        }
    }

    #[test]
    fn a_nested_conjunction_supplies_its_inner_conjunctions() {
        let source = guarded(1, 4, |k| {
            and(and(equals(k, 7), at_most(k, 9)), at_most(k, 12))
        });
        let facts = PureFactStore::from_ordered(std::slice::from_ref(&source));
        for goal in [
            guarded(2, 4, |k| and(equals(k, 7), at_most(k, 9))),
            guarded(2, 4, |k| at_most(k, 9)),
            guarded(2, 4, |k| at_most(k, 12)),
        ] {
            assert_eq!(
                facts.quantified_conjunct_projection_source(&goal),
                Some(&source)
            );
        }
    }

    #[test]
    fn a_projection_keeps_the_guard_and_the_conjuncts_exactly() {
        let source = guarded(1, 4, |k| and(at_most(k, 9), equals(k, 7)));
        let facts = PureFactStore::from_ordered(&[source]);
        for goal in [
            // A different guard is a different claim.
            guarded(2, 5, |k| equals(k, 7)),
            // A conjunct the source does not state.
            guarded(2, 4, |k| equals(k, 8)),
            // The whole conjunction is the source itself, not a projection.
            guarded(2, 4, |k| and(at_most(k, 9), equals(k, 7))),
            // A conjunct that is not about the binder.
            guarded(2, 4, |_| equals(50, 7)),
        ] {
            assert_eq!(facts.quantified_conjunct_projection_source(&goal), None);
        }
    }

    #[test]
    fn a_universal_without_a_conjunction_supplies_nothing() {
        let source = guarded(1, 4, |k| equals(k, 7));
        assert!(guarded_universal_conjunct_projections(&source).is_empty());
        let facts = PureFactStore::from_ordered(&[source]);
        assert_eq!(
            facts.quantified_conjunct_projection_source(&guarded(2, 4, |k| equals(k, 7))),
            None
        );
    }

    #[test]
    fn a_conjunct_of_a_conjunction_fact_is_indexed_too() {
        let source = guarded(1, 4, |k| and(at_most(k, 9), equals(k, 7)));
        let facts = PureFactStore::from_ordered(&[]).with_fact(and(equals(60, 1), source.clone()));
        assert_eq!(
            facts.quantified_conjunct_projection_source(&guarded(2, 4, |k| equals(k, 7))),
            Some(&source)
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/proof/facts/quantified_conjunct_projection_tests.rs");
    }
}

#[cfg(test)]
mod shared_memory_reservation_tests {
    use super::*;
    mod scaling_tests {
        include!("../../scaling_tests/kernel/proof/facts/shared_memory_reservation_tests.rs");
    }
}

#[cfg(test)]
mod retained_match_root_tests {
    use super::*;
    #[test]
    fn shared_match_equalities_select_the_native_algebraic_scrutinee() {
        let _session = VerificationSession::enter();
        let native = OldMachineTerm::AlgebraicMatch {
            scrutinee: Box::new(crate::kernel::KernelMatch::test_scrutinee(vec![])),
            arms: vec![crate::kernel::AlgebraicBitvectorMatchArm {
                variant: "Arm".into(),
                bindings: vec![],
                binding_names: Default::default(),
                body: OldMachineTerm::constant(0),
            }],
        };
        let machine = SharedMachineIntegerTerm::intern(MachineIntegerType::Int32, native.clone());
        let written = Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(native),
                right: Box::new(OldMachineTerm::constant(1)),
            },
            true,
        );
        let common = Proposition::condition_is(
            OldConditionTerm::IntegerEqual(
                crate::kernel::IntegerTerm::Machine(machine).into(),
                crate::kernel::IntegerTerm::constant_i64(1).into(),
            ),
            true,
        );
        let mut expected = BTreeSet::new();
        collect_proposition_algebraic_terms(&written, &mut expected);
        let exports = crate::kernel::KernelTermExport::machine_export_count();
        let mut actual = BTreeSet::new();
        collect_proposition_algebraic_terms(&common, &mut actual);
        assert!(!actual.is_empty());
        assert_eq!(actual, expected);
        assert_eq!(
            crate::kernel::KernelTermExport::machine_export_count(),
            exports
        );
    }
}

#[cfg(test)]
mod propagated_fact_publication_tests {
    use super::*;
    fn atom(name: &str) -> Proposition {
        Proposition::Predicate {
            name: name.into(),
            arguments: vec![],
        }
    }
    fn rule() -> Proposition {
        Proposition::Implies(Box::new(atom("trigger")), Box::new(atom("result")))
    }

    #[test]
    fn propagation_is_published_in_root_updates_and_statement_batches() {
        let root = PureFactStore::from_ordered(&[rule()]);
        assert!(!root.contains(&atom("result")));
        for child in [
            root.with_fact(atom("trigger")),
            root.with_statement_facts(vec![atom("trigger")]),
            PureFactStore::from_ordered(&[rule(), atom("trigger")]),
        ] {
            assert!(child.contains(&atom("result")));
            assert!(child.propositions().any(|p| p == &atom("result")));
            assert!(Arc::ptr_eq(
                child.top_level_exact.get(&atom("result")).unwrap(),
                &child
                    .assumptions()
                    .shared_assumed_proposition(&atom("result"))
                    .unwrap(),
            ));
            assert!(!root.contains(&atom("result")));
        }
    }

    mod scaling_tests {
        use super::*;
        include!("../../scaling_tests/kernel/proof/facts/propagated_publication.rs");
    }
}

#[cfg(test)]
mod unified_store_tests {
    use super::*;
    fn fact(name: &str) -> Proposition {
        Proposition::Predicate {
            name: name.to_string(),
            arguments: Vec::new(),
        }
    }
    #[test]
    fn restriction_builds_a_new_scope_without_mutating_parent() {
        let (a, b) = (fact("scope_a"), fact("scope_b"));
        let root = PureFactStore::from_ordered(&[a.clone(), b.clone(), a.clone()]);
        let unchanged = root.retaining(|_| true);
        assert!(unchanged.shares_assumptions_with(&root));
        let restricted = root.retaining(|prop| prop != &b);
        assert_eq!(restricted.occurrences().collect::<Vec<_>>(), vec![&a, &a]);
        assert!(!restricted.contains(&b));
        assert!(!restricted.assumptions().contains_assumed_exact(&b));
        assert!(root.assumptions().contains_assumed_exact(&b));
    }
    #[test]
    fn publication_and_membership_share_the_stored_proposition() {
        let a = fact("shared_at_root");
        let b = fact("shared_after_append");
        let condition = Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(OldMachineTerm::Variable(Variable(901_091))),
                right: Box::new(OldMachineTerm::constant(7)),
            },
            true,
        );
        let store =
            PureFactStore::from_ordered(&[a.clone(), condition.clone()]).with_fact(b.clone());
        let mut published = ExecutionFacts::new();
        published.append_context(&store.assumptions.execution_fact_projection);
        for proposition in [&a, &b, &condition] {
            let stored = store.top_level_exact.get(proposition).unwrap();
            let emitted = published
                .iter()
                .find(|fact| fact.proposition() == proposition)
                .unwrap();
            assert!(Arc::ptr_eq(stored, &emitted.shared_proposition()));
            assert!(published.contains_proposition(proposition));
        }
        let producer = ExecutionPureFact::new(fact("producer")).into_certified();
        let context = PureFactContext::new().assume_execution_pure_fact(&producer);
        assert!(Arc::ptr_eq(
            &producer.shared_proposition(),
            &context
                .shared_assumed_proposition(producer.proposition())
                .unwrap()
        ));
        assert!(producer.is_certified());
    }
}
