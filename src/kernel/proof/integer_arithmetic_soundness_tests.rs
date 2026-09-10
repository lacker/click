//! Independent small-model checks of accepted Integer certificates.
//!
//! The oracle evaluates source arithmetic directly over a finite collection
//! of assignments; it does not reuse the checker's affine normalization.

use super::integer_arithmetic::{
    IntegerArithmeticCertificate, IntegerArithmeticNode, integer_affine_claim,
};
use crate::kernel::{ConditionTerm, IntegerTerm, Proposition, Variable};
use num_bigint::BigInt;

#[derive(Clone)]
enum Expression {
    X,
    Y,
    Constant(i64),
    Add(Box<Self>, Box<Self>),
    Subtract(Box<Self>, Box<Self>),
    Negate(Box<Self>),
    Twice(Box<Self>),
}

impl Expression {
    fn term(&self) -> IntegerTerm {
        match self {
            Self::X => IntegerTerm::Variable(Variable(710)),
            Self::Y => IntegerTerm::Variable(Variable(711)),
            Self::Constant(value) => IntegerTerm::constant_i64(*value),
            Self::Add(left, right) => IntegerTerm::Add(
                crate::kernel::SharedIntegerTerm::from(left.term()),
                crate::kernel::SharedIntegerTerm::from(right.term()),
            ),
            Self::Subtract(left, right) => IntegerTerm::Subtract(
                crate::kernel::SharedIntegerTerm::from(left.term()),
                crate::kernel::SharedIntegerTerm::from(right.term()),
            ),
            Self::Negate(value) => {
                IntegerTerm::Negate(crate::kernel::SharedIntegerTerm::from(value.term()))
            }
            Self::Twice(value) => IntegerTerm::Multiply(
                crate::kernel::SharedIntegerTerm::from(IntegerTerm::constant_i64(2)),
                crate::kernel::SharedIntegerTerm::from(value.term()),
            ),
        }
    }

    fn evaluate(&self, x: i64, y: i64) -> i64 {
        match self {
            Self::X => x,
            Self::Y => y,
            Self::Constant(value) => *value,
            Self::Add(left, right) => left.evaluate(x, y) + right.evaluate(x, y),
            Self::Subtract(left, right) => left.evaluate(x, y) - right.evaluate(x, y),
            Self::Negate(value) => -value.evaluate(x, y),
            Self::Twice(value) => 2 * value.evaluate(x, y),
        }
    }
}

struct Case {
    proposition: Proposition,
    satisfying_assignments: u64,
}

fn cases() -> Vec<Case> {
    use Expression::{Add, Constant, Negate, Subtract, Twice, X, Y};
    let pairs = [
        (X, Y),
        (Add(Box::new(X), Box::new(Constant(1))), Y),
        (Constant(0), X),
        (Subtract(Box::new(X), Box::new(X)), Constant(0)),
        (Negate(Box::new(X)), Y),
        (Twice(Box::new(X)), X),
        (
            Subtract(Box::new(Constant(1)), Box::new(X)),
            Add(Box::new(Y), Box::new(Constant(1))),
        ),
    ];
    let mut result = Vec::new();
    for (left, right) in pairs {
        for comparison in 0..6 {
            for expected in [false, true] {
                let terms = (left.term().into(), right.term().into());
                let condition = match comparison {
                    0 => ConditionTerm::IntegerLessThan(terms.0, terms.1),
                    1 => ConditionTerm::IntegerLessEqual(terms.0, terms.1),
                    2 => ConditionTerm::IntegerGreaterThan(terms.0, terms.1),
                    3 => ConditionTerm::IntegerGreaterEqual(terms.0, terms.1),
                    4 => ConditionTerm::IntegerEqual(terms.0, terms.1),
                    5 => ConditionTerm::IntegerNotEqual(terms.0, terms.1),
                    _ => unreachable!(),
                };
                let mut satisfying_assignments = 0;
                let mut bit = 1;
                for x in -3..=3 {
                    for y in -3..=3 {
                        let left = left.evaluate(x, y);
                        let right = right.evaluate(x, y);
                        let actual = match comparison {
                            0 => left < right,
                            1 => left <= right,
                            2 => left > right,
                            3 => left >= right,
                            4 => left == right,
                            5 => left != right,
                            _ => unreachable!(),
                        };
                        if actual == expected {
                            satisfying_assignments |= bit;
                        }
                        bit <<= 1;
                    }
                }
                result.push(Case {
                    proposition: Proposition::ConditionIs(condition, expected),
                    satisfying_assignments,
                });
            }
        }
    }
    result
}

#[test]
fn integer_certificate_comparison_normalization_preserves_small_models() {
    let cases = cases();
    let all_assignments = (1u64 << 49) - 1;
    let mut accepted = 0;
    for goal in &cases {
        let Some(goal_claim) = integer_affine_claim(&goal.proposition) else {
            continue;
        };
        let trivial = IntegerArithmeticCertificate {
            nodes: vec![IntegerArithmeticNode::Trivial {
                result: goal_claim.clone(),
            }],
            conclusion: 0,
        };
        if trivial.check(&goal.proposition, &[]).is_ok() {
            accepted += 1;
            assert_eq!(
                goal.satisfying_assignments, all_assignments,
                "a context-free certificate accepted a false comparison: {:?}",
                goal.proposition,
            );
        }
        for premise in &cases {
            let Some(premise_claim) = integer_affine_claim(&premise.proposition) else {
                continue;
            };
            for scale in -2..=2 {
                let certificate = IntegerArithmeticCertificate {
                    nodes: vec![
                        IntegerArithmeticNode::Premise {
                            index: 0,
                            result: premise_claim.clone(),
                        },
                        IntegerArithmeticNode::Scale {
                            source: 0,
                            coefficient: BigInt::from(scale),
                            result: goal_claim.clone(),
                        },
                    ],
                    conclusion: 1,
                };
                if certificate
                    .check(
                        &goal.proposition,
                        std::slice::from_ref(&premise.proposition),
                    )
                    .is_ok()
                {
                    accepted += 1;
                    assert_eq!(
                        premise.satisfying_assignments & !goal.satisfying_assignments,
                        0,
                        "accepted scale {scale} has a counterexample: premise {:?}, goal {:?}",
                        premise.proposition,
                        goal.proposition,
                    );
                }
            }
        }
    }
    assert!(
        accepted > 100,
        "the matrix must exercise successful certificates"
    );
}

// Partition the exhaustive matrix by left-expression family and rule. Every
// supported premise pair and goal is still checked against the independent oracle.
fn check_binary_rule_family(family: usize, rule_index: usize) {
    let cases = cases();
    assert_eq!(
        cases.len(),
        7 * 12,
        "update partitions when the case matrix changes"
    );
    let supported: Vec<_> = cases
        .iter()
        .filter_map(|case| integer_affine_claim(&case.proposition).map(|claim| (case, claim)))
        .collect();
    let mut accepted = [0usize; 2];
    for (left, left_claim) in supported.iter().filter(|(case, _)| {
        cases[family * 12..(family + 1) * 12]
            .iter()
            .any(|candidate| std::ptr::eq(*case, candidate))
    }) {
        for (right, right_claim) in &supported {
            let premises = [left.proposition.clone(), right.proposition.clone()];
            let premise_models = left.satisfying_assignments & right.satisfying_assignments;
            for (goal, goal_claim) in &supported {
                let rules = [
                    IntegerArithmeticNode::Add {
                        left: 0,
                        right: 1,
                        result: goal_claim.clone(),
                    },
                    IntegerArithmeticNode::EqualityFromBounds {
                        lower: 0,
                        upper: 1,
                        result: goal_claim.clone(),
                    },
                ];
                for (rule_index, rule) in rules
                    .into_iter()
                    .enumerate()
                    .filter(|(index, _)| *index == rule_index)
                {
                    let certificate = IntegerArithmeticCertificate {
                        nodes: vec![
                            IntegerArithmeticNode::Premise {
                                index: 0,
                                result: left_claim.clone(),
                            },
                            IntegerArithmeticNode::Premise {
                                index: 1,
                                result: right_claim.clone(),
                            },
                            rule,
                        ],
                        conclusion: 2,
                    };
                    if certificate.check(&goal.proposition, &premises).is_ok() {
                        accepted[rule_index] += 1;
                        assert_eq!(
                            premise_models & !goal.satisfying_assignments,
                            0,
                            "binary rule {rule_index} admitted a counterexample: {:?}, {:?} -> {:?}",
                            left.proposition,
                            right.proposition,
                            goal.proposition,
                        );
                    }
                }
            }
        }
    }
    assert!(
        accepted[rule_index] > 0,
        "each partition must exercise successful certificates: {}",
        accepted[rule_index]
    );
}

macro_rules! binary_rule_family_tests {
    ($add:ident, $bounds:ident, $family:expr) => {
        #[test]
        fn $add() {
            check_binary_rule_family($family, 0);
        }
        #[test]
        fn $bounds() {
            check_binary_rule_family($family, 1);
        }
    };
}
binary_rule_family_tests!(
    integer_certificate_add_variables,
    integer_certificate_bounds_variables,
    0
);
binary_rule_family_tests!(
    integer_certificate_add_successor,
    integer_certificate_bounds_successor,
    1
);
binary_rule_family_tests!(
    integer_certificate_add_zero,
    integer_certificate_bounds_zero,
    2
);
binary_rule_family_tests!(
    integer_certificate_add_cancellation,
    integer_certificate_bounds_cancellation,
    3
);
binary_rule_family_tests!(
    integer_certificate_add_negation,
    integer_certificate_bounds_negation,
    4
);
binary_rule_family_tests!(
    integer_certificate_add_doubling,
    integer_certificate_bounds_doubling,
    5
);
binary_rule_family_tests!(
    integer_certificate_add_subtraction,
    integer_certificate_bounds_subtraction,
    6
);
