//! Certificate and equality-rewrite planning for `solve`.

use crate::kernel::proof::equality_rewrite::rewrite_proposition_by_exact_equality;
use crate::kernel::{CompareRelation, MachineIntegerType};
use crate::surface::*;

pub(in crate::surface) fn computes_with_known(goal: &Proposition) -> bool {
    match goal {
        Proposition::And(left, right) => computes_with_known(left) && computes_with_known(right),
        Proposition::Or(left, right) => computes_with_known(left) || computes_with_known(right),
        _ => crate::kernel::proof::fact_reasoning::computes_leaf(goal),
    }
}

/// Choose a computational closer. Other goals need an explicit derivation;
/// search must never retain the broad plain-normalization fallback.
pub(in crate::surface) fn plan_context_free_closer(goal: &Proposition) -> Option<ProofTactic> {
    if computes_with_known(goal) {
        Some(ProofTactic::Known)
    } else {
        None
    }
}

/// The single explicit-certificate search shared by every smart-simplification
/// construction path. Both the fixed-state proof `solve() using` chain and the
/// post-execution outcome planner must call through here, so a named simple
/// rule available to one is available to the other. `is_available` is the
/// caller's judgment of when the current goal closes by `known`.
pub(in crate::surface) fn plan_explicit_equality_rewrites_from(
    goal: &Proposition,
    premises: &[(Proposition, ClickProposition)],
    available: &[Proposition],
    is_available: &impl Fn(&Proposition) -> bool,
    closer: &impl Fn(&Proposition) -> Option<Vec<ProofTactic>>,
) -> Option<Vec<ProofTactic>> {
    fn reverse_equality(
        kernel: &Proposition,
        surface: &ClickProposition,
    ) -> Option<(Proposition, ClickProposition)> {
        let kernel = match kernel {
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: format @ (MachineIntegerType::Int32 | MachineIntegerType::UInt32),
                    relation: CompareRelation::Equal,
                    left,
                    right,
                },
                true,
            ) => Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: *format,
                    relation: CompareRelation::Equal,
                    left: right.clone(),
                    right: left.clone(),
                },
                true,
            ),
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int64,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                },
                true,
            ) => Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int64,
                    relation: CompareRelation::Equal,
                    left: right.clone(),
                    right: left.clone(),
                },
                true,
            ),
            Proposition::ConditionIs(ConditionTerm::PointerValueEqual(left, right), true) => {
                Proposition::ConditionIs(
                    ConditionTerm::PointerValueEqual(right.clone(), left.clone()),
                    true,
                )
            }
            Proposition::ConditionIs(ConditionTerm::PointerEqual(left, right), true) => {
                Proposition::ConditionIs(
                    ConditionTerm::PointerEqual(right.clone(), left.clone()),
                    true,
                )
            }
            Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(left, right), true) => {
                Proposition::ConditionIs(
                    ConditionTerm::PointerOffsetEqual(right.clone(), left.clone()),
                    true,
                )
            }
            Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) => {
                Proposition::Equal(
                    Term::Algebraic(right.clone()),
                    Term::Algebraic(left.clone()),
                )
            }
            _ => return None,
        };
        let ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::Equal,
            right,
        } = surface
        else {
            return None;
        };
        Some((
            kernel,
            ClickProposition::Comparison {
                left: right.clone(),
                operator: ComparisonOperator::Equal,
                right: left.clone(),
            },
        ))
    }

    fn search(
        current: Proposition,
        premises: &[(Proposition, ClickProposition)],
        available: &[Proposition],
        used: &mut [bool],
        tactics: &mut Vec<ProofTactic>,
        is_available: &impl Fn(&Proposition) -> bool,
        closer: &impl Fn(&Proposition) -> Option<Vec<ProofTactic>>,
    ) -> bool {
        // The search tries premise orders depth first, so its node count is
        // factorial in the equalities it may use. Each node observes the
        // enclosing tactic's deadline and work budget, so a search that
        // cannot close fails when its tactic's bound runs out rather than
        // running on to finish.
        if crate::instrumentation::deadline_exceeded() {
            return false;
        }
        if is_available(&current) {
            tactics.push(ProofTactic::Known);
            return true;
        }
        if let Some(closer) = plan_context_free_closer(&current) {
            tactics.push(closer);
            return true;
        }
        if let Some(suffix) = closer(&current) {
            tactics.extend(suffix);
            return true;
        }
        // A disjunction closes the way `known` closes it: one
        // disjunct must be the same total boolean condition as an
        // available fact up to polarity (`x > 0` from `not (x <= 0)`).
        // Construction mirrors exactly that rule, and commits only
        // when a disjunct closes, so nothing beyond the two children is
        // examined.
        if let Proposition::Or(left_child, right_child) = &current {
            for child in [left_child.as_ref(), right_child.as_ref()] {
                if available
                    .iter()
                    .any(|fact| condition_polarity_equivalent(fact, child))
                {
                    tactics.push(ProofTactic::Known);
                    return true;
                }
            }
        }
        for (index, (kernel, surface)) in premises.iter().enumerate() {
            if used[index] {
                continue;
            }
            let mut orientations = vec![(kernel.clone(), surface.clone())];
            if let Some(reverse) = reverse_equality(kernel, surface) {
                orientations.push(reverse);
            }
            for (oriented_kernel, oriented_surface) in orientations {
                let Ok(rewritten) =
                    rewrite_proposition_by_exact_equality(&current, &oriented_kernel, available)
                else {
                    continue;
                };
                used[index] = true;
                tactics.push(ProofTactic::Rewrite(oriented_surface));
                if search(
                    rewritten,
                    premises,
                    available,
                    used,
                    tactics,
                    is_available,
                    closer,
                ) {
                    return true;
                }
                tactics.pop();
                used[index] = false;
            }
        }
        false
    }

    let mut used = vec![false; premises.len()];
    let mut tactics = Vec::new();
    search(
        goal.clone(),
        premises,
        available,
        &mut used,
        &mut tactics,
        is_available,
        closer,
    )
    .then_some(tactics)
}

/// The checked kernel evidence behind one successful smart simplification.
/// Search produces this at the moment it succeeds and immediately writes it
/// as explicit surface tactics; it is never stored, ordered into a plan, or
/// checked as a private operation program. A derivation the surface
/// vocabulary cannot write is a search failure, not a lowering error.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::surface) enum SolveEvidence {
    /// The goal closes by the fact-free computational rules of `known`.
    Known,
    /// A kernel derivation of the goal from its context premises.
    Derivation(PropositionDerivation),
}

pub(in crate::surface) fn plan_solve_certificate(
    proposition: &Proposition,
    assumptions: &PureFactContext,
) -> Option<SolveEvidence> {
    if computes_with_known(proposition) {
        Some(SolveEvidence::Known)
    } else {
        Some(SolveEvidence::Derivation(
            crate::kernel::search::ProofSearch::derive_solve_proposition(assumptions, proposition)?,
        ))
    }
}
