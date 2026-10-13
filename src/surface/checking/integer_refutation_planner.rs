//! Plan a mathematical `Integer` bound by refuting its negation.
//!
//! The goal's integer negation and the selected premises become linear
//! constraints for the simplex (`simplex.rs`). An infeasible system yields
//! Farkas multipliers, which become an ordinary `Integer` certificate:
//! premise and `negated_goal` nodes, scaled and added up to a constant
//! contradiction. The kernel checks that certificate; nothing here is
//! trusted.

use super::simplex::{self, Constraint, FarkasTerm, Rational, Relation, SimplexOutcome};
use crate::kernel::Proposition;
use crate::kernel::proof::integer_arithmetic::{
    IntegerAffineAtom, IntegerAffineClaim, IntegerAffineRelation, IntegerArithmeticCertificate,
    IntegerArithmeticNode, add_claim, integer_affine_claim, negate_claim, scale_claim,
};
use num_bigint::BigInt;
use num_traits::{One, Signed};
use std::collections::BTreeMap;

/// The result of a refutation attempt.
#[derive(Debug)]
pub(crate) enum IntegerRefutation {
    /// A certificate for the goal. Its premise nodes index `premises`, the
    /// premises the refutation used, in the order the caller passed them.
    Proved {
        certificate: IntegerArithmeticCertificate,
        premises: Vec<Proposition>,
    },
    /// The premises and the negated goal have a rational solution, given as
    /// atom values. The goal does not follow from these premises by linear
    /// arithmetic. The `auto` diagnostics (stage-1 milestone 5) will report
    /// it; until then only the tests read the values.
    #[cfg_attr(not(test), allow(dead_code))]
    Counterexample(Vec<(IntegerAffineAtom, Rational)>),
    /// The goal is not a mathematical `Integer` bound this planner refutes.
    Outside,
    /// The work budget ran out.
    Exhausted,
}

/// Refute the integer negation of `goal` from `premises`. Premises that are
/// not linear `Integer` claims are ignored. Work is charged to the active
/// deterministic budget.
pub(crate) fn plan_integer_refutation(
    goal: &Proposition,
    premises: &[Proposition],
) -> IntegerRefutation {
    let Some(goal_claim) = integer_affine_claim(goal) else {
        return IntegerRefutation::Outside;
    };
    if goal_claim.relation != IntegerAffineRelation::LessEqual {
        return IntegerRefutation::Outside;
    }
    let mut negated = negate_claim(&goal_claim, IntegerAffineRelation::LessEqual);
    negated.constant += BigInt::one();

    // Constraint 0 is the negated goal; constraint i + 1 is the i-th usable
    // premise.
    let mut sources: Vec<Option<usize>> = vec![None];
    let mut claims: Vec<IntegerAffineClaim> = vec![negated.clone()];
    for (index, premise) in premises.iter().enumerate() {
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return IntegerRefutation::Exhausted;
        }
        if let Some(claim) = integer_affine_claim(premise) {
            sources.push(Some(index));
            claims.push(claim);
        }
    }

    let mut atoms: BTreeMap<IntegerAffineAtom, usize> = BTreeMap::new();
    let constraints: Vec<Constraint> = claims
        .iter()
        .map(|claim| Constraint {
            terms: claim
                .terms
                .iter()
                .map(|(atom, coefficient)| {
                    let next = atoms.len();
                    (
                        *atoms.entry(atom.clone()).or_insert(next),
                        coefficient.clone(),
                    )
                })
                .collect(),
            constant: claim.constant.clone(),
            relation: match claim.relation {
                IntegerAffineRelation::LessEqual => Relation::LessEqual,
                IntegerAffineRelation::Equal => Relation::Equal,
            },
        })
        .collect();

    let outcome = simplex::solve(atoms.len(), &constraints, |units| {
        !crate::instrumentation::deadline_exceeded_with_work(units)
    });
    let terms = match outcome {
        SimplexOutcome::Infeasible(terms) => terms,
        SimplexOutcome::Feasible(model) => {
            let mut by_index: Vec<Option<IntegerAffineAtom>> = vec![None; atoms.len()];
            for (atom, index) in atoms {
                by_index[index] = Some(atom);
            }
            return IntegerRefutation::Counterexample(
                model
                    .into_iter()
                    .filter_map(|(index, value)| Some((by_index[index].clone()?, value)))
                    .collect(),
            );
        }
        SimplexOutcome::Exhausted => return IntegerRefutation::Exhausted,
    };
    match certificate_from_farkas(&terms, &claims, &sources, premises) {
        Some(proved) => proved,
        None => IntegerRefutation::Outside,
    }
}

/// Build the certificate: one premise or `negated_goal` node per used
/// constraint, an equality turned into the direction its multiplier's sign
/// selects, each scaled by its multiplier's magnitude, and all of them added.
fn certificate_from_farkas(
    terms: &[FarkasTerm],
    claims: &[IntegerAffineClaim],
    sources: &[Option<usize>],
    premises: &[Proposition],
) -> Option<IntegerRefutation> {
    let mut nodes: Vec<IntegerArithmeticNode> = Vec::new();
    let mut used_premises: Vec<Proposition> = Vec::new();
    let mut premise_slots: BTreeMap<usize, usize> = BTreeMap::new();
    let mut addends: Vec<(usize, IntegerAffineClaim)> = Vec::new();
    for term in terms {
        let claim = claims.get(term.constraint)?;
        let base = nodes.len();
        match sources.get(term.constraint)? {
            None => nodes.push(IntegerArithmeticNode::NegatedGoal {
                result: claim.clone(),
            }),
            Some(index) => {
                let next = used_premises.len();
                let slot = *premise_slots.entry(*index).or_insert_with(|| {
                    used_premises.push(premises[*index].clone());
                    next
                });
                nodes.push(IntegerArithmeticNode::Premise {
                    index: slot,
                    result: claim.clone(),
                });
            }
        }
        let (mut source, mut current) = (base, claim.clone());
        if claim.relation == IntegerAffineRelation::Equal {
            let reverse = term.multiplier.is_negative();
            let bound = if reverse {
                negate_claim(claim, IntegerAffineRelation::LessEqual)
            } else {
                IntegerAffineClaim {
                    relation: IntegerAffineRelation::LessEqual,
                    terms: claim.terms.clone(),
                    constant: claim.constant.clone(),
                }
            };
            nodes.push(IntegerArithmeticNode::EqualityToLessEqual {
                source,
                reverse,
                result: bound.clone(),
            });
            source = nodes.len() - 1;
            current = bound;
        }
        let magnitude = term.multiplier.abs();
        if !magnitude.is_one() {
            let scaled = scale_claim(&current, &magnitude)?;
            nodes.push(IntegerArithmeticNode::Scale {
                source,
                coefficient: magnitude,
                result: scaled.clone(),
            });
            source = nodes.len() - 1;
            current = scaled;
        }
        addends.push((source, current));
    }
    let mut addends = addends.into_iter();
    let (mut sum_node, mut sum) = addends.next()?;
    for (node, claim) in addends {
        let total = add_claim(&sum, &claim);
        nodes.push(IntegerArithmeticNode::Add {
            left: sum_node,
            right: node,
            result: total.clone(),
        });
        sum_node = nodes.len() - 1;
        sum = total;
    }
    Some(IntegerRefutation::Proved {
        certificate: IntegerArithmeticCertificate {
            nodes,
            conclusion: sum_node,
        },
        premises: used_premises,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{ConditionTerm, IntegerTerm, Variable};

    fn x(id: u64) -> IntegerTerm {
        IntegerTerm::Variable(Variable(id))
    }

    fn le(left: IntegerTerm, right: IntegerTerm) -> Proposition {
        Proposition::ConditionIs(ConditionTerm::integer_less_equal(left, right), true)
    }

    fn lt(left: IntegerTerm, right: IntegerTerm) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::IntegerLessThan(left.into(), right.into()),
            true,
        )
    }

    fn eq(left: IntegerTerm, right: IntegerTerm) -> Proposition {
        Proposition::ConditionIs(ConditionTerm::integer_equal(left, right), true)
    }

    fn c(value: i64) -> IntegerTerm {
        IntegerTerm::constant_i64(value)
    }

    fn proves(goal: &Proposition, premises: &[Proposition]) -> Vec<Proposition> {
        match plan_integer_refutation(goal, premises) {
            IntegerRefutation::Proved {
                certificate,
                premises,
            } => {
                assert_eq!(
                    certificate.check(goal, &premises),
                    Ok(()),
                    "{certificate:?}"
                );
                premises
            }
            other => panic!("expected a proof, got {other:?}"),
        }
    }

    #[test]
    fn chains_bounds_and_cites_only_what_it_uses() {
        // i < n, n <= 1000, total <= 255 * i  ⊢  total <= 255000.
        let (i, n, total, unrelated) = (x(1), x(2), x(3), x(4));
        let premises = vec![
            lt(i.clone(), n.clone()),
            le(n, c(1000)),
            le(unrelated, c(7)),
            le(total.clone(), IntegerTerm::multiply(c(255), i)),
        ];
        let goal = le(total, c(255000));
        let used = proves(&goal, &premises);
        assert_eq!(used.len(), 3);
        assert!(!used.contains(&premises[2]));
    }

    #[test]
    fn uses_equalities_in_either_direction() {
        // a == b + c, b == 2, c == 3  ⊢  a <= 5 and 5 <= a.
        let (a, b, cc) = (x(11), x(12), x(13));
        let premises = vec![
            eq(a.clone(), IntegerTerm::add(b.clone(), cc.clone())),
            eq(b, c(2)),
            eq(cc, c(3)),
        ];
        proves(&le(a.clone(), c(5)), &premises);
        proves(&le(c(5), a), &premises);
    }

    #[test]
    fn reports_a_counterexample_when_the_goal_does_not_follow() {
        let (i, n) = (x(21), x(22));
        let premises = vec![le(i.clone(), n.clone()), le(n, c(10))];
        let goal = le(i.clone(), c(9));
        let IntegerRefutation::Counterexample(model) = plan_integer_refutation(&goal, &premises)
        else {
            panic!("expected a counterexample");
        };
        let value = model
            .iter()
            .find(|(atom, _)| *atom == IntegerAffineAtom::Variable(Variable(21)))
            .map(|(_, value)| value.clone())
            .expect("i has a value");
        assert!(value > Rational::integer(BigInt::from(9)));
    }

    #[test]
    fn equality_and_machine_goals_are_outside_this_planner() {
        let goal = eq(x(31), c(1));
        assert!(matches!(
            plan_integer_refutation(&goal, &[]),
            IntegerRefutation::Outside
        ));
    }

    #[test]
    fn a_strict_goal_uses_integer_tightening() {
        // 2x <= 7 does not give x < 3 rationally (x = 3.5), but x <= 3 is
        // integral reasoning the planner does not do yet; x < 4 follows
        // rationally.
        let goal = lt(x(41), c(4));
        proves(&goal, &[le(IntegerTerm::multiply(c(2), x(41)), c(7))]);
    }

    #[test]
    fn work_grows_linearly_with_independent_unused_premises() {
        let mut samples = Vec::new();
        for size in [8u64, 16, 32, 64] {
            let mut premises = vec![le(x(50), x(51)), le(x(51), c(3))];
            for extra in 0..size {
                premises.push(le(x(1000 + extra), c(extra as i64)));
            }
            let goal = le(x(50), c(3));
            let (outcome, work) = crate::instrumentation::measure_deterministic_work(|| {
                plan_integer_refutation(&goal, &premises)
            });
            assert!(matches!(outcome, IntegerRefutation::Proved { .. }));
            samples.push(work);
        }
        for pair in samples.windows(2) {
            assert!(pair[1] <= 3 * pair[0], "{samples:?}");
        }
    }
}
