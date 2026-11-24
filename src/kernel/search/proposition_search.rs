//! Logical proposition discovery over kernel terms.
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
//! [`PureFactContext::restricted_to_facts`]) and public exact queries, and
//! everything it finds is returned as a [`PropositionDerivation`] whose
//! checker is local, deterministic, and still in the kernel. The atomic
//! theory checkers the leaves call (`decide`, `proves_memory_loadable`,
//! `proves_memory_access`, `proves_resource_separate`,
//! `proves_resource_contains`, and the canonicalization equality walks)
//! stay in the kernel and are unchanged;
//! see the kernel authority boundary in `docs/internals/proof-objects.md`.
//!
//! Fast kernel proof operations may not call into this module. A kernel
//! operation that needs to know whether a proposition holds uses an exact
//! route or emits the proposition as an obligation.

use super::SearchPermission;
use crate::kernel::planning_api::*;
use crate::kernel::*;
use crate::kernel::{CompareRelation, MachineIntegerType};
use crate::kernel::{constant_u64, uint64_constant};
use std::collections::BTreeMap;
use std::collections::BTreeSet;

type ReducedAtomicPremises = (PureFactContext, u64, AtomicPropositionDerivationEvidence);
#[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
enum AtomicReductionQuery {
    VariableEquality32(Variable, Variable),
    UnsignedSubtractionLessThan(Variable, u64, Variable),
    IntegerLessEqual(u64, u64),
    IntegerEqual(u64, u64),
}

type AtomicReductionKey = (u64, (bool, bool), AtomicReductionQuery);

thread_local! {
    static SOLVE_ATOMIC_REDUCTIONS: std::cell::RefCell<Option<BTreeMap<AtomicReductionKey, ReducedAtomicPremises>>> = const { std::cell::RefCell::new(None) };
}

/// Share completed scalar reductions across one simplification's strategies.
/// Keys use the selected context's identity and logical-read generation,
/// scoped reasoning modes, and fixed-size operands or interned Integer ids.
/// No ambient context or term tree is hashed.
pub(crate) fn with_solve_atomic_reduction_cache<T>(body: impl FnOnce() -> T) -> T {
    let root = SOLVE_ATOMIC_REDUCTIONS.with(|cache| {
        let mut cache = cache.borrow_mut();
        if cache.is_some() {
            false
        } else {
            *cache = Some(BTreeMap::new());
            true
        }
    });
    struct Scope(bool);
    impl Drop for Scope {
        fn drop(&mut self) {
            if self.0 {
                SOLVE_ATOMIC_REDUCTIONS.with(|cache| *cache.borrow_mut() = None);
            }
        }
    }
    let _scope = Scope(root);
    body()
}

/// Nested disjunction case splits allowed inside one derivation.
const MAX_DISJUNCTION_SPLIT_DEPTH: usize = 2;

thread_local! {
    static DISJUNCTION_SPLIT_DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    /// The connected-premise trials decided under the outermost disjunction
    /// split now in progress, by selected premises and goal.
    static SPLIT_CONNECTED_TRIALS: std::cell::RefCell<BTreeMap<ConnectedTrialKey, ConnectedTrial>> =
        const { std::cell::RefCell::new(BTreeMap::new()) };
    /// The case derivations decided under the outermost disjunction split
    /// now in progress, by case context and goal. Nested splits reach one
    /// context through either order of its two cases.
    static SPLIT_CASE_DERIVATIONS: std::cell::RefCell<BTreeMap<(u64, Proposition, bool), Option<Box<PropositionDerivation>>>> =
        const { std::cell::RefCell::new(BTreeMap::new()) };
}

type ConnectedTrialKey = (Vec<(ConditionTerm, bool)>, Proposition, bool);
type ConnectedTrial = Option<(PureFactContext, u64, AtomicPropositionDerivationEvidence)>;

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

    fn active() -> bool {
        DISJUNCTION_SPLIT_DEPTH.with(|depth| depth.get() > 0)
    }
}

impl Drop for DisjunctionSplitDepth {
    fn drop(&mut self) {
        let depth = DISJUNCTION_SPLIT_DEPTH.with(|depth| {
            depth.set(depth.get().saturating_sub(1));
            depth.get()
        });
        if depth == 0 {
            SPLIT_CONNECTED_TRIALS.with(|trials| trials.borrow_mut().clear());
            SPLIT_CASE_DERIVATIONS.with(|cases| cases.borrow_mut().clear());
        }
    }
}

/// Decides the goal from exactly `selected`, reusing the answer an earlier
/// case of the same disjunction split reached. Every case of a split keeps
/// the goal and the context it was cut from, plus its case; when the case is
/// not among the connected premises, each case selects the same facts, and
/// the restricted context they rebuild is the same context.
fn connected_trial(
    context: &PureFactContext,
    selected: &[(ConditionTerm, bool)],
    proposition: &Proposition,
    extended_rules: bool,
) -> ConnectedTrial {
    let decide = || {
        let candidate = atomic_context_from_facts(context, selected, &[]);
        let (evidence, premises_id) =
            crate::kernel::SelectedFacts::for_search(&candidate, SearchPermission::new())
                .proves_atomic_for_derivation_with_id(proposition, extended_rules);
        evidence.map(|evidence| (candidate, premises_id, evidence))
    };
    if !DisjunctionSplitDepth::active() {
        return decide();
    }
    let key = (selected.to_vec(), proposition.clone(), extended_rules);
    if let Some(known) = SPLIT_CONNECTED_TRIALS.with(|trials| trials.borrow().get(&key).cloned()) {
        return known;
    }
    let decided = decide();
    SPLIT_CONNECTED_TRIALS.with(|trials| trials.borrow_mut().insert(key, decided.clone()));
    decided
}

/// Logical proposition discovery over the supplied kernel fact context.
impl super::ProofSearch<PureFactContext> {
    pub(crate) fn signed_order_chain_premises(
        context: &PureFactContext,
        goal: &Proposition,
    ) -> Option<Vec<Proposition>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("signed_order_chain_premises");
        let Proposition::ConditionIs(condition, truth) = goal else {
            return None;
        };
        let view = crate::kernel::assumptions::order_view_at_format(
            condition.native_compat(),
            *truth,
            MachineIntegerType::Int32,
        )?;
        context
            .exact_signed_order_source_path(
                view.operands[0].operand_view(),
                view.operands[1].operand_view(),
                view.relation == crate::kernel::machine_integer::Relation::Less,
            )
            .map(|path| {
                path.into_iter()
                    .map(|step| step.premise().clone())
                    .collect()
            })
    }

    pub(crate) fn proves(context: &PureFactContext, proposition: &Proposition) -> bool {
        #[cfg(test)]
        crate::kernel::search::record_discovery("proves");
        if crate::instrumentation::replay_forbids_discovery("proposition search")
            || reasoning_interrupted()
        {
            return false;
        }
        // One id resolution up front so every decision this proof attempt
        // makes shares it instead of rehashing the fact set per decision.
        let _id_scope = PureFactContextIdScope::enter(context);
        if solve_builtin_prop(proposition) {
            return true;
        }

        if context.contains_proposition_fact(proposition) {
            return true;
        }

        if let Some(rule) =
            crate::kernel::search::ProofSearch::derive_by_algebraic_constructor_rules(
                context,
                proposition,
                false,
            )
        {
            let proof = proposition_derivation(proposition, rule);
            if proof.check(context) {
                record_implicit_consulted_premises(context, proposition);
                return true;
            }
        }

        let direct = match proposition {
            Proposition::ConditionIs(condition, value) => {
                context.decide(condition.native_compat()) == Some(*value)
                    // The memory DAG answers first where it can: a bounded
                    // walk over named derivation edges, ahead of the deep
                    // canonicalization below.
                    || *value
                        && matches!(
                            condition.native_compat(),
                            ConditionTerm::Compare { format: MachineIntegerType::Int32 | MachineIntegerType::UInt32, relation: CompareRelation::Equal, left, right }
                                if atomic_loads_equal_along_memory_derivations(
                                    left, right, context,
                                )
                        )
                    // Two terms for one value that differ only
                    // representationally (memory states embedded in loads,
                    // including under folds and conditionals) are equal by
                    // deep canonicalization; both calls use complete,
                    // input-linear worklists.
                    || *value
                        && matches!(
                            condition.native_compat(),
                            ConditionTerm::Compare { format: MachineIntegerType::Int32 | MachineIntegerType::UInt32, relation: CompareRelation::Equal, left, right }
                                if canonicalize_atomic_loads(left)
                                        == canonicalize_atomic_loads(right)
                        )
                    || context.proves_condition_from_facts(SearchPermission::new(), condition.native_compat(), *value)
            }
            Proposition::And(left, right) => {
                crate::kernel::search::ProofSearch::proves(context, left)
                    && crate::kernel::search::ProofSearch::proves(context, right)
            }
            Proposition::Or(left, right) => {
                crate::kernel::search::ProofSearch::proves(context, left)
                    || crate::kernel::search::ProofSearch::proves(context, right)
            }
            Proposition::Not(body) => crate::kernel::search::ProofSearch::proves_not(context, body),
            Proposition::Implies(left, right) => {
                crate::kernel::search::ProofSearch::proves_not(context, left)
                    || crate::kernel::search::ProofSearch::proves(
                        &(context.clone().assume_proposition(left.as_ref().clone())),
                        right,
                    )
            }
            Proposition::ForAll {
                var,
                sort: Sort::ProgramInt32,
                body,
                ..
            } => {
                crate::kernel::search::ProofSearch::proves_finite_forall(context, proposition)
                    || crate::kernel::search::ProofSearch::derive_forall_rule(
                        context,
                        proposition,
                        **var,
                        body,
                        false,
                    )
                    .is_some_and(|rule| proposition_derivation(proposition, rule).check(context))
            }
            Proposition::MemoryReadDefined {
                memory,
                pointer,
                value_type,
                ..
            } => context.proves_memory_read_defined(memory, pointer, *value_type),
            Proposition::MemoryLoadable {
                memory,
                base,
                bytes,
                wide: true,
            } => context.proves_native_memory_loadable(memory, base, bytes.native_compat()),
            Proposition::MemoryLoadable {
                memory,
                base,
                bytes,
                wide: false,
            } => context.proves_memory_loadable(memory, base, bytes.native_compat()),
            Proposition::MemoryCanStore {
                memory,
                pointer,
                byte_width,
            } => context.proves_memory_access(memory, pointer, *byte_width),
            Proposition::ResourceSeparate { left, right } => {
                context.contains_proposition_fact(proposition)
                    || context.proves_resource_separate(left, right)
            }
            Proposition::ResourceContains { parent, child } => {
                context.contains_proposition_fact(proposition)
                    || context.proves_resource_contains(parent, child)
            }
            _ => context.contains_proposition_fact(proposition),
        };
        let proved = direct
            || crate::instrumentation::measure_operation(
                "kernel",
                "general proposition proof",
                "proposition proof: context inconsistency",
                || context.is_inconsistent(),
            )
            || crate::instrumentation::measure_operation(
                "kernel",
                "general proposition proof",
                "proposition proof: singleton substitution",
                || {
                    crate::kernel::search::ProofSearch::proves_by_singleton_substitution(
                        context,
                        proposition,
                    )
                },
            );
        if proved {
            record_implicit_consulted_premises(context, proposition);
        }
        proved
    }

    /// Search for an explicit proof tree for a contextual consequence.
    ///
    /// This is the proof-producing counterpart to [`Self::proves`]. Atomic
    /// leaves retain the complete context used to check them; minimizing that
    /// context would require repeated arithmetic calls and is not part of proof
    /// correctness.
    pub(crate) fn derive_proposition(
        context: &PureFactContext,
        proposition: &Proposition,
    ) -> Option<PropositionDerivation> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("derive_proposition");
        crate::kernel::search::ProofSearch::derive_proposition_using(context, proposition, false)
            .map(|derivation| *derivation)
    }

    pub(crate) fn derive_solve_proposition(
        context: &PureFactContext,
        proposition: &Proposition,
    ) -> Option<PropositionDerivation> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("derive_solve_proposition");
        crate::kernel::search::ProofSearch::derive_proposition_using(context, proposition, true)
            .map(|derivation| *derivation)
    }

    /// Selects an independent derivation without taking the goal's own exact
    /// ambient fact as a premise. Keep the ambient graph intact: dropping a
    /// fact from it would rebuild its equality closure just to avoid the
    /// circular `close()` candidate.
    pub(crate) fn derive_solve_proposition_without_exact_goal(
        context: &PureFactContext,
        proposition: &Proposition,
    ) -> Option<PropositionDerivation> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("derive_solve_proposition_without_exact_goal");
        if let Some(derivation) =
            crate::kernel::search::ProofSearch::derive_solve_proposition(context, proposition)
            && !derivation.context_premises().contains(proposition)
        {
            return Some(derivation);
        }
        crate::kernel::search::ProofSearch::atomic_derivation_premises(
            context,
            proposition,
            true,
            true,
        )
        .and_then(|selected| reduce_solve_atomic_premises(proposition, true, selected))
        .map(|(premises, premises_id, evidence)| {
            proposition_derivation(
                proposition,
                PropositionDerivationRule::ContextualAtomic {
                    premises: RetainedPremises::from_context(&premises),
                    premises_id,
                    extended_rules: true,
                    evidence,
                },
            )
        })
    }

    /// Choose one bound from the goal's existing dependency buckets. The
    /// certificate checks only that bound and any explicit count evidence.
    pub(crate) fn select_arithmetic_bound(
        context: &PureFactContext,
        goal: &Proposition,
    ) -> Option<Proposition> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("select_arithmetic_bound");
        use crate::kernel::proof::arithmetic_special::{
            float_bound_weakens, is_float_bound, same_signed_max_shift_bound,
            signed_max_shift_count_bound,
        };
        let float = is_float_bound(goal);
        if !float && signed_max_shift_count_bound(goal).is_none() {
            return None;
        }
        Self::find_connected_arithmetic_bound(context, goal, float, |premise| {
            let checks = if float {
                float_bound_weakens(premise, goal)
            } else {
                same_signed_max_shift_bound(premise, goal)
            };
            checks.then(|| premise.clone())
        })
    }

    pub(crate) fn select_float_bound_chain(
        context: &PureFactContext,
        goal: &Proposition,
    ) -> Option<Vec<Proposition>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("select_float_bound_chain");
        use crate::kernel::proof::arithmetic_special::{
            float_bound_chain, is_compound_float_bound,
        };
        if !is_compound_float_bound(goal) {
            return None;
        }
        Self::find_connected_arithmetic_bound(context, goal, true, |premise| {
            float_bound_chain(premise, goal)
        })
    }

    /// Select bounds independently, so a large premise bucket cannot
    /// cause a Cartesian product of candidate pairs.
    pub(crate) fn select_float_pair_bounds(
        context: &PureFactContext,
        goal: &Proposition,
    ) -> Option<Vec<Proposition>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("select_float_pair_bounds");
        let pair = crate::kernel::proof::arithmetic_special::FloatPairBound::new(goal)?;
        let mut best: [Option<(u64, Proposition)>; 4] = [None, None, None, None];
        Self::find_connected_arithmetic_bound(context, goal, true, |premise| {
            let count = pair.premise_count();
            for (index, slot) in best[..count].iter_mut().enumerate() {
                if let Some(endpoint) = pair.operand_endpoint(index, premise)
                    && slot.as_ref().is_none_or(|(previous, _)| {
                        pair.stronger_endpoint(index, endpoint, *previous)
                    })
                {
                    *slot = Some((endpoint, premise.clone()));
                }
            }
            for length in [2, 4] {
                if length > count {
                    break;
                }
                let mut endpoints = [0; 4];
                if !best[..length].iter().enumerate().all(|(index, source)| {
                    source.as_ref().is_some_and(|(endpoint, _)| {
                        endpoints[index] = *endpoint;
                        true
                    })
                }) {
                    continue;
                }
                if pair.established_by(&endpoints[..length]) {
                    let mut premises: Vec<_> = best[..length]
                        .iter()
                        .flatten()
                        .map(|(_, premise)| premise.clone())
                        .collect();
                    if length == 4 && pair.is_square() {
                        premises.dedup();
                    }
                    return Some(premises);
                }
            }
            None
        })
    }

    fn find_connected_arithmetic_bound<T>(
        context: &PureFactContext,
        goal: &Proposition,
        float: bool,
        mut select: impl FnMut(&Proposition) -> Option<T>,
    ) -> Option<T> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("find_connected_arithmetic_bound");
        for key in collect_atomic_connection_keys(goal) {
            for fact in context.atomic_facts_connected_to(&key, false).0 {
                if crate::instrumentation::deadline_exceeded_with_work(1) {
                    return None;
                }
                match fact {
                    AtomicConnectedFact::Condition(condition, expected)
                        if !float
                            || (expected
                                && matches!(
                                    condition,
                                    ConditionTerm::Float32(_) | ConditionTerm::Float64(_)
                                )) =>
                    {
                        let premise = Proposition::condition_is(condition.clone(), expected);
                        if let Some(selected) = select(&premise) {
                            return Some(selected);
                        }
                    }
                    AtomicConnectedFact::Proposition(premise) => {
                        if let Some(selected) = select(premise) {
                            return Some(selected);
                        }
                    }
                    _ => {}
                }
            }
        }
        None
    }

    /// Check one atomic theory consequence against this exact premise set.
    ///
    /// Unlike [`Self::derive_proposition`], this does not introduce logical
    /// structure or attempt finite case splits.
    pub(crate) fn derive_atomic_proposition(
        context: &PureFactContext,
        proposition: &Proposition,
    ) -> Option<PropositionDerivation> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("derive_atomic_proposition");
        crate::kernel::search::ProofSearch::derive_atomic_proposition_using(
            context,
            proposition,
            false,
        )
    }

    /// The simplifier's atomic theory check, without structural proof search.
    pub(crate) fn derive_solve_atomic_proposition(
        context: &PureFactContext,
        proposition: &Proposition,
    ) -> Option<PropositionDerivation> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("derive_solve_atomic_proposition");
        crate::kernel::search::ProofSearch::derive_atomic_proposition_using(
            context,
            proposition,
            true,
        )
    }

    pub(crate) fn derive_atomic_proposition_using(
        context: &PureFactContext,
        proposition: &Proposition,
        extended_rules: bool,
    ) -> Option<PropositionDerivation> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("derive_atomic_proposition_using");
        if solve_reasoning_interrupted() {
            return None;
        }
        crate::kernel::search::ProofSearch::atomic_derivation_premises(
            context,
            proposition,
            extended_rules,
            false,
        )
        .and_then(|selected| reduce_solve_atomic_premises(proposition, extended_rules, selected))
        .map(|(premises, premises_id, evidence)| {
            proposition_derivation(
                proposition,
                PropositionDerivationRule::ContextualAtomic {
                    premises: RetainedPremises::from_context(&premises),
                    premises_id,
                    extended_rules,
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
    /// pointer/state equality can depend on explicit frame facts.
    pub(crate) fn atomic_derivation_premises(
        context: &PureFactContext,
        proposition: &Proposition,
        extended_rules: bool,
        exclude_exact_goal: bool,
    ) -> Option<(PureFactContext, u64, AtomicPropositionDerivationEvidence)> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("atomic_derivation_premises");
        if !exclude_exact_goal && context.proves_exact(proposition) {
            let exact = PureFactContext::new().assume_proposition(proposition.clone());
            let (evidence, premises_id) =
                crate::kernel::SelectedFacts::for_search(&exact, SearchPermission::new())
                    .proves_atomic_for_derivation_with_id(proposition, extended_rules);
            if let Some(evidence) = evidence {
                return Some((exact, premises_id, evidence));
            }
        }
        // A constant-pinned equality needs at most two indexed premises, even
        // when the same variable occurs in every preceding branch guard.
        // Recheck that small selection before trying the connected component.
        if let Some(premises) = context.indexed_constant_equality_premises(proposition)
            && (!exclude_exact_goal || !premises.contains(proposition))
        {
            let candidate = premises
                .into_iter()
                .fold(PureFactContext::new(), |context, premise| {
                    context.assume_proposition(premise)
                });
            let (evidence, premises_id) =
                crate::kernel::SelectedFacts::for_search(&candidate, SearchPermission::new())
                    .proves_atomic_for_derivation_with_id(proposition, extended_rules);
            if let Some(evidence) = evidence {
                return Some((candidate, premises_id, evidence));
            }
        }
        if let Proposition::ConditionIs(condition, _) = proposition
            && let Some(selected) =
                context.widened_unsigned_sum_bound_premises(condition.native_compat())
        {
            let candidate = selected
                .into_iter()
                .fold(PureFactContext::new(), |context, premise| {
                    context.assume_proposition(premise)
                });
            let (evidence, premises_id) =
                crate::kernel::SelectedFacts::for_search(&candidate, SearchPermission::new())
                    .proves_atomic_for_derivation_with_id(proposition, extended_rules);
            if matches!(
                evidence,
                Some(AtomicPropositionDerivationEvidence::WidenedUnsignedSumBound)
            ) {
                return evidence.map(|evidence| (candidate, premises_id, evidence));
            }
        }
        let interval_query =
            crate::kernel::machine_integer::definedness::interval_query_form(proposition);
        let selection_goal = interval_query.as_ref().unwrap_or(proposition);
        let condition_goal = match selection_goal {
            Proposition::ConditionIs(_, _) => true,
            Proposition::Not(body) => matches!(body.as_ref(), Proposition::ConditionIs(_, _)),
            _ => false,
        };
        if let Some(selected) = context.select_forall_int32_instantiation_evidence(proposition) {
            let mut candidate = PureFactContext::new().assume_proposition(selected.quantified);
            for premise in selected.guard_premises {
                candidate = candidate.assume_proposition(premise);
            }
            let (evidence, premises_id) =
                crate::kernel::SelectedFacts::for_search(&candidate, SearchPermission::new())
                    .proves_atomic_for_derivation_with_id(proposition, extended_rules);
            if matches!(
                evidence,
                Some(AtomicPropositionDerivationEvidence::ForallInt32Instantiation(_))
            ) {
                return evidence.map(|evidence| (candidate, premises_id, evidence));
            }
        }
        let mut condition_sources = Vec::new();
        // Speculative equality rewrites often leave an unprovable Integer
        // comparison. Query the existing indexes before rebuilding the facts
        // connected through its operands. A positive answer still needs the
        // ordinary selected-premise derivation below.
        if extended_rules
            && matches!(&proposition, condition_source_0 @ Proposition::ConditionIs(_, _) if matches!(condition_source_0.condition_native(), Some((ConditionTerm::IntegerEqual(..), _))))
            && crate::kernel::SelectedFacts::for_search(context, SearchPermission::new())
                .proves_atomic_for_derivation_with_id(proposition, extended_rules)
                .0
                .is_none()
        {
            return None;
        }
        if condition_goal {
            let (selected, _, _, _) = connected_atomic_premises(
                context,
                selection_goal,
                &[],
                false,
                true,
                exclude_exact_goal,
            )?;
            if let Some(found) = connected_trial(context, &selected, proposition, extended_rules) {
                return Some(found);
            }
            condition_sources = selected
                .into_iter()
                .map(|(condition, value)| Proposition::condition_is(condition, value))
                .collect();
        }

        let candidate_family = |fact: &Proposition| match proposition {
            Proposition::MemoryReadDefined { .. } => matches!(
                fact,
                Proposition::MemoryReadDefined { .. } | Proposition::MemoryLoadable { .. }
            ),
            Proposition::MemoryLoadable { .. } | Proposition::MemoryCanStore { .. } => {
                matches!(fact, Proposition::MemoryLoadable { .. })
            }
            Proposition::ResourceSeparate { .. } => {
                matches!(fact, Proposition::ResourceSeparate { .. })
            }
            _ => false,
        };
        // The planner may enumerate an address's ambiguous loadability
        // bucket. Each trial below gives the checker an explicitly selected
        // source; the checker itself refuses ambiguous buckets. Other address
        // shapes remain unvisited unless a structural anchor or alias names them.
        let goal_base = match proposition {
            Proposition::MemoryLoadable { base, .. } => Some(base),
            Proposition::MemoryCanStore { pointer, .. } => Some(pointer),
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
                context
                    .search_memory_loadable_candidates_for_base(SearchPermission::new(), base)
                    .inspect(|_| record_candidate_visit())
                    .filter(usable)
                    .cloned()
                    .collect::<Vec<_>>()
            }),
            Proposition::MemoryReadDefined {
                pointer,
                value_type,
                ..
            } => Some(
                context
                    .search_memory_read_defined_candidates(
                        SearchPermission::new(),
                        pointer,
                        *value_type,
                    )
                    .into_iter()
                    .chain(context.search_memory_loadable_candidates_for_base(
                        SearchPermission::new(),
                        pointer,
                    ))
                    .inspect(|_| record_candidate_visit())
                    .filter(usable)
                    .cloned()
                    .collect(),
            ),
            Proposition::ResourceSeparate { left, right } => context
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
                Proposition::MemoryReadDefined { .. } | Proposition::ResourceSeparate { .. }
            ) {
                return Vec::new();
            }
            let tried = tried.iter().collect::<BTreeSet<_>>();
            context
                .proposition_facts(SearchPermission::new())
                .inspect(|_| record_candidate_visit())
                .filter(|fact| candidate_family(fact) && usable(fact) && !tried.contains(fact))
                .cloned()
                .collect::<Vec<_>>()
        };
        let candidates = indexed.unwrap_or_default();
        // Every trial is rebuilt only from explicitly selected dependencies.
        // The kernel must establish the goal again in that restricted context.
        let trial = |sources: &[Proposition]| {
            let direct = atomic_context_from_facts(context, &[], sources);
            let (evidence, premises_id) =
                crate::kernel::SelectedFacts::for_search(&direct, SearchPermission::new())
                    .proves_atomic_for_derivation_with_id(proposition, extended_rules);
            if let Some(evidence) = evidence {
                return Some((direct, premises_id, evidence));
            }
            // A native prefix needs its source view and the selected coverage
            // path, not every comparison connected to the source's length.
            if extended_rules
                && sources.len() == 1
                && let Some(premises) =
                    native_view_prefix_premises(context, proposition, &sources[0])
            {
                let candidate = premises
                    .into_iter()
                    .fold(PureFactContext::new(), |context, fact| {
                        context.assume_proposition(fact)
                    });
                let (evidence, premises_id) =
                    crate::kernel::SelectedFacts::for_search(&candidate, SearchPermission::new())
                        .proves_atomic_for_derivation_with_id(proposition, extended_rules);
                if let Some(evidence) = evidence {
                    return Some((candidate, premises_id, evidence));
                }
            }
            let (conditions, propositions, _, _) = connected_atomic_premises(
                context,
                proposition,
                sources,
                false,
                false,
                exclude_exact_goal,
            )?;
            let candidate = atomic_context_from_facts(context, &conditions, &propositions);
            let (evidence, premises_id) =
                crate::kernel::SelectedFacts::for_search(&candidate, SearchPermission::new())
                    .proves_atomic_for_derivation_with_id(proposition, extended_rules);
            evidence.map(|evidence| (candidate, premises_id, evidence))
        };
        let try_each = |candidates: &[Proposition]| {
            for selected in candidates {
                if solve_reasoning_interrupted() {
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
        // Try a covering source before searching the ambient block for a
        // concatenation: unknown offsets in unrelated ranges can otherwise
        // trigger order reasoning over unrelated conditions for every range.
        if let Proposition::MemoryLoadable {
            memory,
            base,
            bytes,
            wide: false,
        } = proposition
            && let Some(premises) =
                context.adjacent_loadable_region_facts(memory, base, bytes.native_compat())
            && (!exclude_exact_goal || !premises.contains(&proposition.clone()))
            && let Some(found) = trial(&premises)
        {
            return Some(found);
        }
        // Two loadable ranges justify a goal only by concatenation, and the
        // kernel names the pair that concatenates. The first lookup above
        // may have named the goal's own statement; without it, ask again of
        // the other sources alone instead of trying every pair.
        if exclude_exact_goal
            && let Proposition::MemoryLoadable {
                memory,
                base,
                bytes,
                wide: false,
            } = proposition
            && candidates.len() > 1
        {
            let (conditions, propositions, _, _) = connected_atomic_premises(
                context,
                proposition,
                &candidates,
                false,
                false,
                exclude_exact_goal,
            )?;
            let sources = atomic_context_from_facts(context, &conditions, &propositions);
            if let Some(premises) =
                sources.adjacent_loadable_region_facts(memory, base, bytes.native_compat())
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
            if extended_rules
                && matches!(&proposition, condition_source_0 @ Proposition::ConditionIs(
                        _,
                        _
                    ) if matches!(condition_source_0.condition_native(), Some((ConditionTerm::Compare {
                            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                            relation: CompareRelation::Equal,
                            ..
                        } | ConditionTerm::Compare {
                            format: MachineIntegerType::Int64,
                            relation: CompareRelation::Equal,
                            ..
                        } | ConditionTerm::AddressOffsetEqual(..), _))))
                && crate::kernel::SelectedFacts::for_search(context, SearchPermission::new())
                    .proves_atomic_for_derivation_with_id(proposition, extended_rules)
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
                                Some((condition.native_compat().clone(), *value))
                            }
                            _ => None,
                        })
                        .collect::<Vec<_>>(),
                    Vec::new(),
                )
            });
            // Condition selection already made the narrow attempt. Its
            // fallback includes frame and quantified dependencies in one
            // query, rather than retrying a partial state context first.
            let widths: &[bool] = if condition_goal {
                &[true]
            } else {
                &[false, true]
            };
            for &widened in widths {
                let selected = connected_atomic_premises(
                    context,
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
                let candidate = atomic_context_from_facts(context, conditions, propositions);
                let (evidence, premises_id) =
                    crate::kernel::SelectedFacts::for_search(&candidate, SearchPermission::new())
                        .proves_atomic_for_derivation_with_id(proposition, extended_rules);
                if let Some(evidence) = evidence {
                    return Some((candidate, premises_id, evidence));
                }
                if !widened
                    && !atomic_widening_adds_dependencies(context, proposition, &candidate, reached)
                {
                    break;
                }
                tried = Some((conditions.clone(), propositions.clone()));
            }
            None
        }
    }

    #[inline(never)]
    pub(crate) fn derive_proposition_using(
        context: &PureFactContext,
        proposition: &Proposition,
        extended_rules: bool,
    ) -> Option<Box<PropositionDerivation>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("derive_proposition_using");
        let _id_scope = PureFactContextIdScope::enter(context);
        if solve_reasoning_interrupted() {
            return None;
        }
        if solve_builtin_prop(proposition) {
            return Some(Box::new(proposition_derivation(
                proposition,
                PropositionDerivationRule::ContextFree,
            )));
        }
        if let Some(rule) =
            crate::kernel::search::ProofSearch::derive_by_algebraic_constructor_rules(
                context,
                proposition,
                extended_rules,
            )
        {
            return Some(Box::new(proposition_derivation(proposition, rule)));
        }
        let direct = crate::kernel::search::ProofSearch::derive_structural_rule(
            context,
            proposition,
            extended_rules,
        );
        if let Some(rule) = direct {
            return Some(Box::new(proposition_derivation(proposition, rule)));
        }
        if let Some(rule) = crate::kernel::search::ProofSearch::derive_by_singleton_substitution(
            context,
            proposition,
            extended_rules,
        ) {
            return Some(Box::new(proposition_derivation(proposition, rule)));
        }
        if let Some(rule) = crate::kernel::search::ProofSearch::derive_by_disjunction_cases(
            context,
            proposition,
            extended_rules,
        ) {
            return Some(Box::new(proposition_derivation(proposition, rule)));
        }
        // A selected equality or case proof needs no global contradiction
        // search. Building consistency indexes first would charge a local
        // successful proof for unrelated ambient order facts.
        context.is_inconsistent().then(|| {
            Box::new(proposition_derivation(
                proposition,
                PropositionDerivationRule::Explosion {
                    premises: RetainedPremises::from_context(context),
                },
            ))
        })
    }

    #[inline(never)]
    pub(crate) fn derive_structural_rule(
        context: &PureFactContext,
        proposition: &Proposition,
        extended_rules: bool,
    ) -> Option<PropositionDerivationRule> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("derive_structural_rule");
        // Range conjunctions are also conclusions of the signed arithmetic
        // theorems. Try those whole-goal certificates before splitting the
        // two bounds; retain the ordinary conjunction as their conclusion.
        if crate::kernel::machine_integer::definedness::ordinary_arithmetic_guard_view(proposition)
            .is_some()
            && let Some(rule) = crate::kernel::search::ProofSearch::derive_atomic_rule(
                context,
                proposition,
                extended_rules,
            )
        {
            return Some(rule);
        }
        match proposition {
            Proposition::And(left, right) => crate::kernel::search::ProofSearch::derive_and_rule(
                context,
                left,
                right,
                extended_rules,
            ),
            Proposition::Or(left, right) => crate::kernel::search::ProofSearch::derive_or_rule(
                context,
                left,
                right,
                extended_rules,
            ),
            Proposition::Not(body) => match body.as_ref() {
                Proposition::Not(inner) => {
                    crate::kernel::search::ProofSearch::derive_double_negation_rule(
                        context,
                        inner,
                        extended_rules,
                    )
                }
                _ => crate::kernel::search::ProofSearch::derive_atomic_rule(
                    context,
                    proposition,
                    extended_rules,
                ),
            },
            Proposition::Implies(left, right) => {
                crate::kernel::search::ProofSearch::derive_implies_rule(
                    context,
                    left,
                    right,
                    extended_rules,
                )
            }
            Proposition::ForAll { var, body, .. } => {
                crate::kernel::search::ProofSearch::derive_forall_rule(
                    context,
                    proposition,
                    **var,
                    body,
                    extended_rules,
                )
            }
            Proposition::Exists {
                var, sort, body, ..
            } => crate::kernel::search::ProofSearch::derive_exists_from_witness(
                context, **var, sort, body,
            )
            .or_else(|| {
                crate::kernel::search::ProofSearch::derive_exists_from_fact(
                    context, **var, sort, body,
                )
            }),
            _ => crate::kernel::search::ProofSearch::derive_atomic_rule(
                context,
                proposition,
                extended_rules,
            ),
        }
    }

    #[inline(never)]
    pub(crate) fn derive_and_rule(
        context: &PureFactContext,
        left: &Proposition,
        right: &Proposition,
        extended_rules: bool,
    ) -> Option<PropositionDerivationRule> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("derive_and_rule");
        crate::kernel::search::ProofSearch::derive_proposition_using(context, left, extended_rules)
            .zip(
                crate::kernel::search::ProofSearch::derive_proposition_using(
                    context,
                    right,
                    extended_rules,
                ),
            )
            .map(|(left, right)| PropositionDerivationRule::And { left, right })
    }

    #[inline(never)]
    pub(crate) fn derive_or_rule(
        context: &PureFactContext,
        left: &Proposition,
        right: &Proposition,
        extended_rules: bool,
    ) -> Option<PropositionDerivationRule> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("derive_or_rule");
        // Unsigned arithmetic guards often lower to `false or bound`. Try
        // the bound before spending the context on contradiction search for
        // the false arm. Keep that arm as a fallback for inconsistent contexts.
        if matches!(&left, condition_source_0 @ Proposition::ConditionIs(_, expected) if matches!(condition_source_0.condition_native(), Some((ConditionTerm::Constant(actual), _)) if (actual != expected)))
        {
            return crate::kernel::search::ProofSearch::derive_proposition_using(
                context,
                right,
                extended_rules,
            )
            .map(PropositionDerivationRule::OrRight)
            .or_else(|| {
                crate::kernel::search::ProofSearch::derive_proposition_using(
                    context,
                    left,
                    extended_rules,
                )
                .map(PropositionDerivationRule::OrLeft)
            });
        }
        crate::kernel::search::ProofSearch::derive_proposition_using(context, left, extended_rules)
            .map(PropositionDerivationRule::OrLeft)
            .or_else(|| {
                crate::kernel::search::ProofSearch::derive_proposition_using(
                    context,
                    right,
                    extended_rules,
                )
                .map(PropositionDerivationRule::OrRight)
            })
    }

    #[inline(never)]
    pub(crate) fn derive_double_negation_rule(
        context: &PureFactContext,
        inner: &Proposition,
        extended_rules: bool,
    ) -> Option<PropositionDerivationRule> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("derive_double_negation_rule");
        crate::kernel::search::ProofSearch::derive_proposition_using(context, inner, extended_rules)
            .map(PropositionDerivationRule::DoubleNegation)
    }

    #[inline(never)]
    pub(crate) fn derive_implies_rule(
        context: &PureFactContext,
        left: &Proposition,
        right: &Proposition,
        extended_rules: bool,
    ) -> Option<PropositionDerivationRule> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("derive_implies_rule");
        let antecedent = left.clone();
        let negated_antecedent = Proposition::Not(Box::new(antecedent.clone()));
        if context.proves_exact(&negated_antecedent) {
            crate::kernel::search::ProofSearch::derive_proposition_using(
                context,
                &negated_antecedent,
                extended_rules,
            )
            .map(PropositionDerivationRule::ImpliesFalseAntecedent)
        } else {
            crate::kernel::search::ProofSearch::derive_proposition_using(
                &(context.clone().assume_proposition(antecedent.clone())),
                right,
                extended_rules,
            )
            .map(|body| PropositionDerivationRule::Implies {
                antecedent: Box::new(antecedent),
                body,
            })
            .or_else(|| {
                crate::kernel::search::ProofSearch::derive_proposition_using(
                    context,
                    &negated_antecedent,
                    extended_rules,
                )
                .map(PropositionDerivationRule::ImpliesFalseAntecedent)
            })
        }
    }

    #[inline(never)]
    pub(crate) fn derive_forall_rule(
        context: &PureFactContext,
        proposition: &Proposition,
        var: Variable,
        body: &Proposition,
        extended_rules: bool,
    ) -> Option<PropositionDerivationRule> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("derive_forall_rule");
        // Derive the body opened at a fresh witness: the binder is a bound
        // variable, which means nothing outside its quantifier.
        let body_derivation = match proposition {
            Proposition::ForAll { sort, .. } => crate::kernel::quantifiers::opening_witness()
                .and_then(|witness| {
                    let opened = crate::kernel::quantifiers::rename_quantified_variable(
                        body, var, witness, sort,
                    )?;
                    crate::kernel::search::ProofSearch::derive_proposition_using(
                        context,
                        &opened,
                        extended_rules,
                    )
                    .filter(|proof| {
                        proof.context_premises().iter().all(|premise| {
                            !crate::kernel::proposition_has_free_bitvector_variable(
                                premise, witness,
                            )
                        })
                    })
                    .map(|proof| PropositionDerivationRule::ForAllBody { witness, proof })
                }),
            _ => None,
        };
        body_derivation
            .or_else(|| {
                crate::kernel::search::ProofSearch::derive_forall_loadable_range(
                    context,
                    proposition,
                )
            })
            .or_else(|| {
                crate::kernel::search::ProofSearch::derive_finite_forall(
                    context,
                    proposition,
                    extended_rules,
                )
            })
            .or_else(|| {
                crate::kernel::search::ProofSearch::derive_atomic_rule(
                    context,
                    proposition,
                    extended_rules,
                )
            })
    }

    #[inline(never)]
    pub(crate) fn derive_atomic_rule(
        context: &PureFactContext,
        proposition: &Proposition,
        extended_rules: bool,
    ) -> Option<PropositionDerivationRule> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("derive_atomic_rule");
        crate::kernel::search::ProofSearch::atomic_derivation_premises(
            context,
            proposition,
            extended_rules,
            false,
        )
        .and_then(|selected| reduce_solve_atomic_premises(proposition, extended_rules, selected))
        .map(|(premises, premises_id, evidence)| {
            PropositionDerivationRule::ContextualAtomic {
                premises: RetainedPremises::from_context(&premises),
                premises_id,
                extended_rules,
                evidence,
            }
        })
    }

    pub(crate) fn derive_by_algebraic_constructor_rules(
        context: &PureFactContext,
        proposition: &Proposition,
        extended_rules: bool,
    ) -> Option<PropositionDerivationRule> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("derive_by_algebraic_constructor_rules");
        if let Some(fields) = algebraic_constructor_field_equalities(proposition)
            && !fields.is_empty()
        {
            let fields = fields
                .iter()
                .map(|field| {
                    crate::kernel::search::ProofSearch::derive_proposition_using(
                        context,
                        field,
                        extended_rules,
                    )
                    .map(|proof| *proof)
                })
                .collect::<Option<Vec<_>>>()?;
            return Some(PropositionDerivationRule::AlgebraicConstructorCongruence { fields });
        }
        context
            .algebraic_constructor_field_sources(proposition)
            .next()
            .map(|(source, field_index)| {
                PropositionDerivationRule::AlgebraicConstructorInjectivity {
                    source: Box::new(source.clone()),
                    field_index: *field_index,
                }
            })
    }

    pub(crate) fn derive_finite_forall(
        context: &PureFactContext,
        proposition: &Proposition,
        extended_rules: bool,
    ) -> Option<PropositionDerivationRule> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("derive_finite_forall");
        let mut instances = context.finite_forall_instantiations(proposition).peekable();
        instances.peek()?;
        instances
            .map(|instance| {
                crate::kernel::search::ProofSearch::derive_proposition_using(
                    context,
                    &instance,
                    extended_rules,
                )
                .map(|proof| *proof)
            })
            .collect::<Option<Vec<_>>>()
            .map(|instances| PropositionDerivationRule::FiniteForAll { instances })
    }

    /// Open the goal and one selected existential fact at the same fresh
    /// witness. The source conjuncts are local assumptions of the child proof.
    pub(crate) fn derive_exists_from_fact(
        context: &PureFactContext,
        var: Variable,
        sort: &Sort,
        body: &Proposition,
    ) -> Option<PropositionDerivationRule> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("derive_exists_from_fact");
        let witness = crate::kernel::quantifiers::opening_witness()?;
        let opened_goal =
            crate::kernel::quantifiers::rename_quantified_variable(body, var, witness, sort)?;
        let candidates = context
            .proposition_facts(SearchPermission::new())
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
                let renamed = crate::kernel::quantifiers::rename_quantified_variable(
                    source_body,
                    **source_var,
                    witness,
                    sort,
                )?;
                Some((source.clone(), renamed))
            })
            .collect::<Vec<_>>();
        for (source, renamed_source_body) in candidates {
            let mut witness_assumptions = context.clone();
            let mut conjuncts = Vec::new();
            collect_proposition_conjuncts(&renamed_source_body, &mut conjuncts);
            for conjunct in conjuncts {
                witness_assumptions = witness_assumptions.assume_proposition(conjunct);
            }
            let derivation = crate::kernel::search::ProofSearch::derive_proposition_using(
                &(witness_assumptions),
                &opened_goal,
                false,
            );
            if let Some(derivation) = derivation {
                return Some(PropositionDerivationRule::ExistsFromFact {
                    source: Box::new(source),
                    witness,
                    body: derivation,
                });
            }
        }
        None
    }

    pub(crate) fn derive_exists_from_witness(
        context: &PureFactContext,
        var: Variable,
        sort: &Sort,
        body: &Proposition,
    ) -> Option<PropositionDerivationRule> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("derive_exists_from_witness");
        if sort != &Sort::ProgramInt32 {
            return None;
        }
        let mut variables = BTreeSet::new();
        for fact in context.memory_loadable_fact_propositions(SearchPermission::new()) {
            if reasoning_interrupted() {
                return None;
            }
            collect_proposition_bitvector_variables(fact, &mut variables);
        }
        variables.remove(&var);
        for variable in variables {
            if reasoning_interrupted() {
                return None;
            }
            let witness = MachineTerm::Variable(variable);
            let instantiated = substitute_bitvector_variable_in_proposition(body, var, &witness);
            let derivation = crate::kernel::search::ProofSearch::derive_proposition_using(
                context,
                &instantiated,
                false,
            );
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
    pub(crate) fn derive_forall_loadable_range(
        context: &PureFactContext,
        proposition: &Proposition,
    ) -> Option<PropositionDerivationRule> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("derive_forall_loadable_range");
        let (premises, conclusion) = forall_loadable_range_parts(proposition)?;
        let Proposition::MemoryLoadable { base, bytes, .. } = conclusion else {
            return None;
        };
        if bytes.as_const() != Some(1) {
            return None;
        }
        for source in
            context.search_memory_loadable_candidates_for_base(SearchPermission::new(), base)
        {
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

    pub(crate) fn derive_by_singleton_substitution(
        context: &PureFactContext,
        proposition: &Proposition,
        extended_rules: bool,
    ) -> Option<PropositionDerivationRule> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("derive_by_singleton_substitution");
        let mut variables = BTreeSet::new();
        collect_proposition_connection_variables(proposition, &mut variables);
        let (variable, value, equality) = variables
            .into_iter()
            .filter_map(|variable| {
                context
                    .singleton_constant_equality_evidence(variable)
                    .map(|(value, evidence)| (variable, value, evidence))
            })
            .next()?;
        let instantiated =
            substitute_machine_constant_in_pure_proposition(proposition, variable, value).ok()?;
        if instantiated == *proposition {
            return None;
        }
        let body = crate::kernel::search::ProofSearch::derive_proposition_using(
            context,
            &instantiated,
            extended_rules,
        )?;
        Some(PropositionDerivationRule::SingletonSubstitution {
            variable,
            value,
            equality,
            body,
        })
    }

    pub(crate) fn derive_by_disjunction_cases(
        context: &PureFactContext,
        proposition: &Proposition,
        extended_rules: bool,
    ) -> Option<PropositionDerivationRule> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("derive_by_disjunction_cases");
        // Each case re-enters the whole derivation, which splits again on
        // every remaining disjunction: with a dozen call outcomes in scope
        // (`result == 0 or result == 1` per call) a goal no case helps paid
        // for every nested combination before failing. A split can only help
        // through a case that constrains something the goal names, so a
        // disjunction over machine variables none of which the goal names,
        // or over variables of any kind none of which the goal names, is not
        // split, and splits nest at most `MAX_DISJUNCTION_SPLIT_DEPTH` deep.
        let _depth = DisjunctionSplitDepth::enter()?;
        let mut goal_variables = BTreeSet::new();
        collect_proposition_bitvector_variables(proposition, &mut goal_variables);
        let goal_all_variables = crate::kernel::proposition_variables(proposition);
        for disjunction in context.disjunction_fact_propositions(SearchPermission::new()) {
            let mut disjunction_variables = BTreeSet::new();
            collect_proposition_bitvector_variables(disjunction, &mut disjunction_variables);
            // A disjunction or goal over no machine variable (an algebraic
            // value's constructors) is judged by all its variables; one over
            // no variable at all (a predicate) is never judged unrelated.
            if !goal_variables.is_empty()
                && !disjunction_variables.is_empty()
                && disjunction_variables.is_disjoint(&goal_variables)
            {
                continue;
            }
            let disjunction_all_variables = crate::kernel::proposition_variables(disjunction);
            if !goal_all_variables.is_empty()
                && !disjunction_all_variables.is_empty()
                && disjunction_all_variables
                    .iter()
                    .all(|variable| !goal_all_variables.contains(variable))
            {
                continue;
            }
            let mut cases = Vec::new();
            collect_or_cases(disjunction, &mut cases);
            if cases.len() < 2 {
                continue;
            }
            if cases.iter().all(|case| {
                context.contains_assumed_exact(&Proposition::Not(Box::new(case.clone())))
            }) {
                return Some(PropositionDerivationRule::RefutedDisjunction {
                    disjunction: Box::new(disjunction.clone()),
                });
            }
            // A branch retains the disjunction and adds its chosen case.
            // Once a case is present, splitting this disjunction again adds
            // nothing and would recurse on the same proof context.
            if cases
                .iter()
                .any(|case| context.contains_assumed_exact(case))
            {
                continue;
            }
            let Some(proofs) = cases
                .iter()
                .map(|case| {
                    let context = context.clone().assume_proposition(case.clone());
                    let key = (
                        crate::kernel::assumptions::unsalted_assumptions_memo_id(&context),
                        proposition.clone(),
                        extended_rules,
                    );
                    let known =
                        SPLIT_CASE_DERIVATIONS.with(|cases| cases.borrow().get(&key).cloned());
                    let derived = match known {
                        Some(known) => known,
                        None => {
                            let derived =
                                crate::kernel::search::ProofSearch::derive_proposition_using(
                                    &(context),
                                    proposition,
                                    extended_rules,
                                );
                            SPLIT_CASE_DERIVATIONS
                                .with(|cases| cases.borrow_mut().insert(key, derived.clone()));
                            derived
                        }
                    };
                    derived.map(|proof| *proof)
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

    pub(crate) fn proves_finite_forall(
        context: &PureFactContext,
        proposition: &Proposition,
    ) -> bool {
        #[cfg(test)]
        crate::kernel::search::record_discovery("proves_finite_forall");
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
        crate::kernel::search::ProofSearch::proves_finite_forall_instantiations(
            context,
            body,
            &variables,
            &ranges,
            &mut values,
        )
    }

    pub(crate) fn proves_finite_forall_instantiations(
        context: &PureFactContext,
        body: &Proposition,
        variables: &[Variable],
        ranges: &[FiniteForAllRange],
        values: &mut Vec<i64>,
    ) -> bool {
        #[cfg(test)]
        crate::kernel::search::record_discovery("proves_finite_forall_instantiations");
        if values.len() == variables.len() {
            let mut instantiated = body.clone();
            for (variable, value) in variables.iter().zip(values.iter()) {
                instantiated = substitute_bitvector_variable_in_proposition(
                    &instantiated,
                    *variable,
                    &signed_i64_bitvector_constant(*value),
                );
            }
            return crate::kernel::search::ProofSearch::proves(context, &instantiated);
        }

        let range = &ranges[values.len()];
        for value in range.lower..=range.upper {
            values.push(value);
            if !crate::kernel::search::ProofSearch::proves_finite_forall_instantiations(
                context, body, variables, ranges, values,
            ) {
                values.pop();
                return false;
            }
            values.pop();
        }
        true
    }

    pub(crate) fn proves_by_singleton_substitution(
        context: &PureFactContext,
        proposition: &Proposition,
    ) -> bool {
        #[cfg(test)]
        crate::kernel::search::record_discovery("proves_by_singleton_substitution");
        let mut variables = BTreeSet::new();
        collect_proposition_connection_variables(proposition, &mut variables);
        let Some((variable, value)) = variables
            .into_iter()
            .filter_map(|variable| {
                context
                    .singleton_constant_equality_evidence(variable)
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
        crate::kernel::search::ProofSearch::proves(context, &instantiated)
    }

    pub(crate) fn proves_not(context: &PureFactContext, proposition: &Proposition) -> bool {
        #[cfg(test)]
        crate::kernel::search::record_discovery("proves_not");
        match proposition {
            Proposition::ConditionIs(condition, value) => {
                context.decide(condition.native_compat()) == Some(!*value)
            }
            Proposition::Not(body) => crate::kernel::search::ProofSearch::proves(context, body),
            _ => {
                context.contains_proposition_fact(&Proposition::Not(Box::new(proposition.clone())))
            }
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
            Proposition::condition_is(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(left),
                    right: Box::new(right),
                },
                true,
            )
        };
        let old_is_zero = equality(MachineTerm::Variable(outer), MachineTerm::constant(0));
        let old_equals_other = equality(MachineTerm::Variable(outer), MachineTerm::Variable(other));
        let body = equality(MachineTerm::Variable(other), MachineTerm::constant(0));
        let goal = crate::kernel::quantifiers::test_forall(
            Default::default(),
            outer,
            Sort::ProgramInt32,
            body,
        );
        let facts = PureFactContext::new()
            .assume_proposition(old_is_zero.clone())
            .assume_proposition(old_equals_other);
        let derivation = crate::kernel::search::ProofSearch::derive_proposition(&(facts), &goal)
            .expect("a binder-free body may use the outer variable's facts");
        assert!(derivation.check(&facts));

        let invalid = crate::kernel::quantifiers::test_forall(
            Default::default(),
            outer,
            Sort::ProgramInt32,
            old_is_zero,
        );
        assert!(
            crate::kernel::search::ProofSearch::derive_proposition(&(facts), &invalid).is_none(),
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
/// Scalar facts are indexed incrementally; state-dependent facts use a
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
        if solve_reasoning_interrupted() {
            return None;
        }
        // The cooperative checkpoint charges this variable visit.
        for (condition, value) in context.condition_facts_mentioning_variable(variable)? {
            #[cfg(test)]
            CONDITION_SELECTION_VISITS.with(|visits| visits.set(visits.get() + 1));
            if solve_reasoning_interrupted() {
                return None;
            }
            // The checkpoint likewise charges each adjacency visit.
            let exact_goal_fact = matches!(
                proposition,
                Proposition::ConditionIs(goal, expected)
                    if goal.native_compat() == condition && *expected == value
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
        selected.insert((condition.clone()).native_compat().clone(), *value);
    }
    Some(selected.into_iter().collect())
}

#[cfg(test)]
mod condition_premise_tests {
    use super::*;

    #[test]
    fn indexed_constant_selection_checks_only_its_cited_premises() {
        let equal = |left, right| {
            Proposition::condition_is(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(left),
                    right: Box::new(right),
                },
                true,
            )
        };
        let constant = MachineTerm::constant(7);
        let left = equal(term(1), constant.clone());
        let right = equal(constant, term(2));
        let goal = equal(term(1), term(2));
        let mut context = PureFactContext::new()
            .assume_proposition(left.clone())
            .assume_proposition(right.clone());
        for index in 8..136 {
            context = context.assume_proposition(Proposition::Not(Box::new(equal(
                term(1),
                MachineTerm::constant(index),
            ))));
        }
        reset_condition_selection_visits();
        let proof =
            crate::kernel::search::ProofSearch::derive_atomic_proposition(&(context), &goal)
                .unwrap();
        assert!(proof.check(&context));
        assert_eq!(condition_selection_visits(), 0);
        assert_eq!(
            proof
                .context_premises()
                .into_iter()
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([left.clone(), right.clone()])
        );
        for remaining in [left.clone(), right] {
            assert!(!proof.check(&PureFactContext::new().assume_proposition(remaining)));
        }
        assert!(
            crate::kernel::search::ProofSearch::derive_atomic_proposition(
                &(context),
                &equal(term(1), MachineTerm::constant(8))
            )
            .is_none()
        );
        let exact_constant_only = PureFactContext::new().assume_proposition(left.clone());
        assert!(
            crate::kernel::search::ProofSearch::derive_solve_proposition_without_exact_goal(
                &(exact_constant_only),
                &left
            )
            .is_none()
        );
        let exact_only = PureFactContext::new().assume_proposition(goal.clone());
        assert!(
            crate::kernel::search::ProofSearch::derive_solve_proposition_without_exact_goal(
                &(exact_only),
                &goal
            )
            .is_none()
        );
    }

    fn term(index: u64) -> MachineTerm {
        MachineTerm::Variable(Variable(index))
    }

    fn order(left: u64, right: u64) -> ConditionTerm {
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left: Box::new(term(left)),
            right: Box::new(term(right)),
        }
    }

    fn chain_fact(index: u64) -> ConditionTerm {
        if index == 1 {
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: Box::new(term(1)),
                right: Box::new(MachineTerm::constant(1000)),
            }
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
        let goal = ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left: Box::new(term(size as u64)),
            right: Box::new(MachineTerm::constant(1000)),
        };
        (context, Proposition::condition_is(goal, true))
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
            for (condition, value) in context.condition_fact_pairs(SearchPermission::new()) {
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
    fn condition_component_keeps_load_address_and_state_variables() {
        let pointer = Address {
            base: "cell".into(),
            offset: AddressOffset::scaled_int32_node(term(40), 4),
        };
        let memory = SymbolicMemory::new().with_block("cell", 64).store(
            Address {
                base: "cell".into(),
                offset: AddressOffset::Constant(0),
            },
            ProgramValue::Int32(term(70)),
        );
        let load = MachineTerm::read_named(
            ProgramPoint::at(&(intern_memory(memory))),
            Box::new(pointer),
            LoadKind::Int32,
        );
        let fact = ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(load.clone()),
            right: Box::new(term(50)),
        };
        let context = PureFactContext::new()
            .assume_condition(fact.clone(), true)
            .assume_condition(order(40, 41), true)
            .assume_condition(order(70, 71), true)
            .assume_condition(order(90, 91), true);
        let goal = Proposition::condition_is(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(load),
                right: Box::new(term(60)),
            },
            true,
        );
        let selected = connected_condition_premises(&context, &goal, false).unwrap();
        assert_eq!(selected, scanned_component(&context, &goal).0);
        assert_eq!(selected.len(), 3);
    }

    #[test]
    fn condition_selection_tracks_restriction_contradiction_and_exclusion() {
        let (context, goal) = chain(8, 20);
        let selected = connected_condition_premises(&context, &goal, false).unwrap();
        let restricted = context.restricted_to_facts(&selected, &[]);
        assert_eq!(
            connected_condition_premises(&restricted, &goal, false).unwrap(),
            selected
        );
        let condition = chain_fact(1);
        let replaced = context.clone().assume_condition(condition.clone(), false);
        assert!(replaced.is_inconsistent());
        assert!(
            connected_condition_premises(&replaced, &goal, false)
                .unwrap()
                .contains(&(condition, true))
        );
        let stated = context.assume_proposition(goal.clone());
        assert_eq!(
            connected_condition_premises(&stated, &goal, true).unwrap(),
            selected
        );
        let constant = Proposition::condition_is(ConditionTerm::Constant(true), true);
        let context = PureFactContext::new().assume_proposition(constant.clone());
        assert_eq!(
            connected_condition_premises(&context, &constant, false)
                .unwrap()
                .len(),
            1
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/search/proposition_search/condition_premise_tests.rs");
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
/// equalities and algebraic `==` facts alike. `solve` offers them to its
/// rewrite chain.
pub(crate) fn connected_equalities(
    context: &PureFactContext,
    goal: &Proposition,
) -> Option<Vec<Proposition>> {
    let (conditions, propositions, _, _) =
        connected_atomic_premises(context, goal, &[], true, true, true)?;
    let mut equalities = Vec::new();
    for (condition, value) in conditions {
        let fact = Proposition::condition_is(condition, value);
        // A registered read's defining equation is kernel metadata, not a
        // source equality. It cannot supply a new rewrite or source spelling.
        if crate::kernel::is_verified_load_variable_defining_fact(&fact) {
            continue;
        }
        // `σ(x) == x` is `x == x` under rule K6: true of every word and no
        // rewrite (`MachineTerm::is_sign_cast32_of`).
        if let Some((
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left,
                right,
            },
            true,
        )) = fact.condition_native()
            && left.is_sign_cast32_of(right)
        {
            continue;
        }
        if matches!(&fact, condition_source @ Proposition::ConditionIs(_, true)
        if matches!(condition_source.condition_native(), Some((
            // An 8- or 16-bit equality is the same fact as the int32
            // equality of its widenings (rule K8), and rewrites at its own width.
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32 | MachineIntegerType::Int8
                    | MachineIntegerType::UInt8 | MachineIntegerType::Int16 | MachineIntegerType::UInt16,
                relation: CompareRelation::Equal, ..
            } | ConditionTerm::Compare { format: MachineIntegerType::Int64, relation: CompareRelation::Equal, .. }
                | ConditionTerm::PointerEqual(..) | ConditionTerm::AddressEqual(..) | ConditionTerm::AddressOffsetEqual(..)
                | ConditionTerm::IntegerEqual(..) | ConditionTerm::AlgebraicEqual(..) | ConditionTerm::BoolEqual(..), _))))
        // A Bool application's claim is its equality with a literal (Stage 5).
        || matches!(&fact, condition_source @ Proposition::ConditionIs(_, _)
            if matches!(condition_source.condition_native(), Some((ConditionTerm::BoolApplication(_), _))))
        {
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

/// Every fact connected to `goal` through shared atoms, of any shape: a
/// disjunctive postcondition `result == f(..) or result < 0` among them.
/// `solve`'s evaluation of a recursive call over constants reads the calls
/// these facts name.
pub(crate) fn connected_facts(
    context: &PureFactContext,
    goal: &Proposition,
) -> Option<Vec<Proposition>> {
    let (conditions, propositions, _, _) =
        connected_atomic_premises(context, goal, &[], true, true, true)?;
    Some(
        conditions
            .into_iter()
            .map(|(condition, value)| Proposition::condition_is(condition, value))
            .filter(|fact| !crate::kernel::is_verified_load_variable_defining_fact(fact))
            .chain(propositions)
            .collect(),
    )
}

/// Walk syntax adjacency, never rebuilding an index of the ambient context.
/// A wider smart fallback follows recent havoc bounds and general facts;
/// its result still has to pass the restricted kernel query.
/// The condition facts connected to `goal` through shared atoms, the same
/// component `solve` selects. `solve`'s selected-premise arithmetic reads its premises
/// from this component; it never scans facts unconnected to the goal.
pub(crate) fn arithmetic_connected_premises(
    context: &PureFactContext,
    goal: &Proposition,
) -> Option<Vec<Proposition>> {
    let (conditions, _, _, _) = connected_atomic_premises(context, goal, &[], false, true, true)?;
    Some(
        conditions
            .into_iter()
            .map(|(condition, value)| Proposition::condition_is(condition, value))
            .filter(|fact| !crate::kernel::is_verified_load_variable_defining_fact(fact))
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
        for fact in context.atomic_general_facts(SearchPermission::new()) {
            if solve_reasoning_interrupted() {
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
        if solve_reasoning_interrupted() {
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
            if solve_reasoning_interrupted() {
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
            Proposition::ConditionIs(condition, value) => {
                conditions.push((condition.native_compat().clone(), value))
            }
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
    for fact in context.atomic_general_facts(SearchPermission::new()) {
        if solve_reasoning_interrupted() || !selected.contains_assumed_exact(fact) {
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

/// Select only the exact order edges covering a native view's prefix. The
/// ordinary restricted kernel query still decides state transport and
/// retirement; a prefix that needs other dependencies uses the usual planner.
fn native_view_prefix_premises(
    context: &PureFactContext,
    goal: &Proposition,
    source: &Proposition,
) -> Option<Vec<Proposition>> {
    let (
        Proposition::MemoryLoadable {
            base,
            bytes,
            wide: true,
            ..
        },
        Proposition::MemoryLoadable {
            base: source_base,
            bytes: source_bytes,
            wide: true,
            ..
        },
    ) = (goal, source)
    else {
        return None;
    };
    if base != source_base {
        return None;
    }
    let coverage = Proposition::condition_is(
        ConditionTerm::uint64_less_equal(
            bytes.native_compat().clone(),
            source_bytes.native_compat().clone(),
        ),
        true,
    );
    let mut premises = vec![source.clone()];
    if context.proves_exact(&coverage) {
        premises.push(coverage);
    } else {
        let (evidence, _) =
            crate::kernel::SelectedFacts::for_search(context, SearchPermission::new())
                .proves_atomic_for_derivation_with_id(&coverage, true);
        let Some(AtomicPropositionDerivationEvidence::WideOrderPath {
            format: crate::kernel::MachineIntegerType::UInt64,
            path,
        }) = evidence
        else {
            return None;
        };
        premises.extend(path.into_iter().map(|step| step.premise().clone()));
    }
    Some(premises)
}

#[cfg(test)]
mod disjunction_work_tests {
    use super::*;

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/search/proposition_search/disjunction_work_tests.rs");
    }
}

/// A compatibility atomic decision can retain a connected component rather
/// than the facts it consumed. Before solve spells historical source forms,
/// discard chunks that the same kernel query proves unnecessary. Each trial
/// holds only the remaining selected facts; no ambient fact participates.
/// Typed evidence already records its dependencies and needs no such search.
///
/// This is bounded smart planning, not certificate validation: at most 128
/// facts and 255 restricted queries. A missed reduction keeps the checked
/// selection, and the final evidence is rebuilt against the retained context.
fn reduce_solve_atomic_premises(
    proposition: &Proposition,
    extended_rules: bool,
    selected: (PureFactContext, u64, AtomicPropositionDerivationEvidence),
) -> Option<(PureFactContext, u64, AtomicPropositionDerivationEvidence)> {
    let (mut context, mut context_id, mut evidence) = selected;
    if extended_rules
        && let Some((retained, retained_id)) = context.retained_atomic_equality_context(&evidence)
    {
        return Some((retained, retained_id, evidence));
    }
    if !extended_rules || !matches!(evidence, AtomicPropositionDerivationEvidence::Legacy) {
        return Some((context, context_id, evidence));
    }
    let query = match proposition {
        condition_source_0 @ Proposition::ConditionIs(_, true)
            if let Some((
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                },
                _,
            )) = condition_source_0.condition_native() =>
        {
            match (left.as_ref(), right.as_ref()) {
                (MachineTerm::Variable(left), MachineTerm::Variable(right)) => {
                    Some(AtomicReductionQuery::VariableEquality32(*left, *right))
                }
                _ => None,
            }
        }
        condition_source_0 @ Proposition::ConditionIs(_, true)
            if let Some((
                ConditionTerm::Compare {
                    format: MachineIntegerType::UInt64,
                    relation: CompareRelation::LessThan,
                    left,
                    right,
                },
                _,
            )) = condition_source_0.condition_native() =>
        {
            match (left.as_ref(), right.as_ref()) {
                (
                    MachineTerm::Binary {
                        format: MachineIntegerType::UInt64,
                        op: MachineBinaryOp::Subtract,
                        left: base,
                        right: amount,
                    },
                    MachineTerm::Variable(upper),
                ) => match (base.as_ref(), amount.as_ref()) {
                    (MachineTerm::Variable(base), uint64_constant!(amount)) => {
                        Some(AtomicReductionQuery::UnsignedSubtractionLessThan(
                            *base,
                            constant_u64(*amount),
                            *upper,
                        ))
                    }
                    _ => None,
                },
                _ => None,
            }
        }
        condition_source_0 @ Proposition::ConditionIs(_, true)
            if let Some((ConditionTerm::IntegerLessEqual(left, right), _)) =
                condition_source_0.condition_native() =>
        {
            Some(AtomicReductionQuery::IntegerLessEqual(
                left.id(),
                right.id(),
            ))
        }
        condition_source_0 @ Proposition::ConditionIs(_, true)
            if let Some((ConditionTerm::IntegerEqual(left, right), _)) =
                condition_source_0.condition_native() =>
        {
            Some(AtomicReductionQuery::IntegerEqual(left.id(), right.id()))
        }
        _ => None,
    };
    let cache_key = query.map(|query| (context_id, atomic_derivation_modes(), query));
    if let Some(key) = cache_key
        && let Some(reduced) = SOLVE_ATOMIC_REDUCTIONS.with(|cache| {
            crate::instrumentation::record_deterministic_work(1);
            cache
                .borrow()
                .as_ref()
                .and_then(|cache| cache.get(&key).cloned())
        })
    {
        return Some(reduced);
    }
    let premises = RetainedPremises::from_context(&context);
    let premises = premises.named();
    if !(8..=128).contains(&premises.len()) {
        return Some((context, context_id, evidence));
    }
    let _timing = crate::instrumentation::OperationTiming::new(
        "surface",
        "solve closure",
        "solve selected premise reduction",
    );
    let mut retained = vec![true; premises.len()];
    let mut pending = vec![(0, premises.len())];
    while let Some((start, end)) = pending.pop() {
        crate::instrumentation::record_deterministic_work(premises.len() + 1);
        if solve_reasoning_interrupted() {
            return None;
        }
        let mut conditions = Vec::new();
        let mut propositions = Vec::new();
        for (index, premise) in premises.iter().enumerate() {
            if !retained[index] || (start..end).contains(&index) {
                continue;
            }
            match premise {
                Proposition::ConditionIs(condition, value) => {
                    conditions.push((condition.native_compat().clone(), *value));
                }
                _ => propositions.push(premise.clone()),
            }
        }
        let trial = context.restricted_to_facts(&conditions, &propositions);
        let (trial_evidence, trial_id) =
            crate::kernel::SelectedFacts::for_search(&trial, SearchPermission::new())
                .proves_atomic_for_derivation_with_id(proposition, extended_rules);
        if let Some(trial_evidence) = trial_evidence {
            retained[start..end].fill(false);
            context = trial;
            context_id = trial_id;
            evidence = trial_evidence;
        } else if end - start > 1 {
            let middle = start + (end - start) / 2;
            // Conditions precede propositions in the retained selection.
            // Try dropping the later chunk first, so irrelevant frame
            // propositions do not accompany every trial on an exact scalar
            // equality's condition sources.
            pending.push((start, middle));
            pending.push((middle, end));
        }
    }
    let reduced = (!solve_reasoning_interrupted()).then_some((context, context_id, evidence))?;
    if let Some(key) = cache_key {
        SOLVE_ATOMIC_REDUCTIONS.with(|cache| {
            if let Some(cache) = cache.borrow_mut().as_mut() {
                crate::instrumentation::record_deterministic_work(1);
                cache.insert(key, reduced.clone());
            }
        });
    }
    Some(reduced)
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
                arguments: vec![Term::Bitvector32(
                    MachineTerm::Variable(Variable(800_000 + index)).into(),
                )],
            };
            let mut body = predicate(0);
            for index in 1..size {
                body = Proposition::And(Box::new(body), Box::new(predicate(index)));
            }
            let source = crate::kernel::quantifiers::test_forall(
                Default::default(),
                Variable(900_000),
                Sort::ProgramInt32,
                body,
            );
            let (context, clones) = crate::kernel::count_proposition_clone_nodes(|| {
                let context = PureFactContext::new().assume_proposition(source.clone());
                let (_, selected, _, _) =
                    connected_atomic_premises(&context, &predicate(0), &[], true, false, false)
                        .expect("all variable buckets must lead to the same wide premise");
                assert_eq!(selected, vec![source.clone()]);
                let proof = crate::kernel::search::ProofSearch::derive_atomic_proposition(
                    &(context),
                    &source,
                )
                .expect("the stated premise is available");
                assert!(proof.check(&context));
                assert!(!proof.check(&PureFactContext::new()));
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

    #[cfg(test)]
    mod scaling_tests {
        include!(
            "../../scaling_tests/kernel/search/proposition_search/shared_atomic_premise_tests.rs"
        );
    }
}

#[cfg(test)]
mod atomic_reduction_tests {
    use super::*;

    fn selection(size: usize, middle: Variable) -> (PureFactContext, Proposition, u64) {
        let left = MachineTerm::Variable(Variable(785_001));
        let right = MachineTerm::Variable(Variable(785_002));
        let middle = MachineTerm::Variable(middle);
        let equal = |left, right| ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(left),
            right: Box::new(right),
        };
        let goal = Proposition::condition_is(equal(left.clone(), right.clone()), true);
        let mut context = PureFactContext::new()
            .assume_condition(equal(left.clone(), middle.clone()), true)
            .assume_condition(equal(middle, right), true);
        for index in 0..size {
            context = context.assume_proposition(Proposition::Predicate {
                name: format!("connected_{index}"),
                arguments: vec![Term::Bitvector32(left.clone().into())],
            });
        }
        let (evidence, id) =
            crate::kernel::SelectedFacts::for_search(&context, SearchPermission::new())
                .proves_atomic_for_derivation_with_id(&goal, true);
        assert!(evidence.is_some());
        (context, goal, id)
    }

    fn reduce(context: &PureFactContext, goal: &Proposition, id: u64) -> ReducedAtomicPremises {
        // Exercise the compatibility producer's selection: it has established
        // the equality but retained the connected context without a typed path.
        reduce_solve_atomic_premises(
            goal,
            true,
            (
                context.clone(),
                id,
                AtomicPropositionDerivationEvidence::Legacy,
            ),
        )
        .unwrap()
    }

    #[test]
    fn cached_reductions_keep_their_selected_contexts_separate() {
        let (first, goal, first_id) = selection(8, Variable(785_003));
        let (second, same_goal, second_id) = selection(8, Variable(785_004));
        assert_eq!(goal, same_goal);
        assert_ne!(first_id, second_id);
        with_solve_atomic_reduction_cache(|| {
            let a = reduce(&first, &goal, first_id);
            let b = reduce(&second, &goal, second_id);
            for (selected, original) in [(&a.0, &first), (&b.0, &second)] {
                assert!(
                    crate::kernel::SelectedFacts::for_search(selected, SearchPermission::new())
                        .proves_atomic_for_derivation_with_id(&goal, true)
                        .0
                        .is_some()
                );
                assert!(
                    selected
                        .pure_facts()
                        .iter()
                        .all(|fact| original.pure_facts().contains(fact))
                );
            }
            assert_ne!(a.0.pure_facts(), b.0.pure_facts());
            assert_eq!(
                reduce(&first, &goal, first_id).0.pure_facts(),
                a.0.pure_facts()
            );
        });
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/search/proposition_search/atomic_reduction_tests.rs");
    }
}

#[cfg(test)]
mod loadability_view_scaling_tests {
    use super::*;
    include!("../../scaling_tests/kernel/search/proposition_search/loadability_view_tests.rs");
}
