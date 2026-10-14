//! Locally checked truncating quotient/remainder bounds from four explicit
//! constant endpoints. Divisor intervals must exclude zero. No native
//! definedness, observer range, or ambient premise search is inferred.

use super::arithmetic_special::SpecialArithmeticCheckError as Error;
use super::integer_product_bounds::order;
use crate::kernel::{IntegerTerm, Proposition};
use num_bigint::BigInt;
use num_traits::{Signed, Zero};

pub(super) fn check(
    node: usize,
    bounds: &[usize],
    premises: &[Proposition],
    result: &Proposition,
) -> Result<(), Error> {
    if crate::instrumentation::deadline_exceeded_with_work(5) {
        return Err(Error::WorkLimitExceeded);
    }
    if bounds.len() != 4 {
        return Err(Error::InvalidIntegerDivisionBounds(node));
    }
    let (goal_left, goal_right) = order(result).ok_or(Error::InvalidOperator(node))?;
    let (expression, target, lower) = if let Some(target) = goal_left.as_const() {
        (goal_right, target, true)
    } else if let Some(target) = goal_right.as_const() {
        (goal_left, target, false)
    } else {
        return Err(Error::InvalidOperator(node));
    };
    let (left, right, remainder) = match expression.as_ref() {
        IntegerTerm::TruncatingQuotient(a, b) => (a, b, false),
        IntegerTerm::TruncatingRemainder(a, b) => (a, b, true),
        _ => return Err(Error::InvalidOperator(node)),
    };
    let mut endpoints = Vec::with_capacity(4);
    for (position, index) in bounds.iter().enumerate() {
        let premise = premises.get(*index).ok_or(Error::InvalidPremise(*index))?;
        let (first, second) = order(premise).ok_or(Error::InvalidIntegerDivisionBounds(node))?;
        let operand = if position < 2 { left } else { right };
        let endpoint = if position % 2 == 0 && second == operand {
            first.as_const()
        } else if position % 2 == 1 && first == operand {
            second.as_const()
        } else {
            None
        }
        .ok_or(Error::InvalidIntegerDivisionBounds(node))?;
        endpoints.push(endpoint);
    }
    let bits = |value: &BigInt| {
        usize::try_from(value.bits())
            .unwrap_or(usize::MAX)
            .saturating_add(1)
    };
    // Charge magnitude-dependent division and comparisons before doing
    // any BigInt arithmetic. No source-expression subtree needs to be walked:
    // the four operand identities are shared Integer DAG node identities.
    let mut work = bits(target);
    for a in &endpoints[..2] {
        for b in &endpoints[2..] {
            work =
                work.saturating_add(bits(a).saturating_mul(bits(b)))
                    .saturating_add(8usize.saturating_mul(
                        bits(a).saturating_add(bits(b)).saturating_add(bits(target)),
                    ));
        }
    }
    if crate::instrumentation::deadline_exceeded_with_work(work) {
        return Err(Error::WorkLimitExceeded);
    }
    if endpoints[0] > endpoints[1] || endpoints[2] > endpoints[3] {
        return Err(Error::InvalidIntegerDivisionBounds(node));
    }
    if endpoints[2] <= &BigInt::zero() && endpoints[3] >= &BigInt::zero() {
        return Err(Error::InvalidIntegerDivisionBounds(node));
    }
    let (minimum, maximum) = if remainder {
        let modulus: BigInt = endpoints[2].abs().max(endpoints[3].abs()) - 1;
        let numerator_magnitude = endpoints[0].abs().max(endpoints[1].abs());
        let minimum_divisor = endpoints[2].abs().min(endpoints[3].abs());
        if numerator_magnitude < minimum_divisor {
            (endpoints[0].clone(), endpoints[1].clone())
        } else {
            let lo = if endpoints[0].is_negative() {
                -endpoints[0].abs().min(modulus.clone())
            } else {
                BigInt::zero()
            };
            let hi = if endpoints[1].is_positive() {
                endpoints[1].clone().min(modulus)
            } else {
                BigInt::zero()
            };
            (lo, hi)
        }
    } else {
        let quotients = [
            endpoints[0] / endpoints[2],
            endpoints[0] / endpoints[3],
            endpoints[1] / endpoints[2],
            endpoints[1] / endpoints[3],
        ];
        (
            quotients.iter().min().unwrap().clone(),
            quotients.iter().max().unwrap().clone(),
        )
    };
    let follows = if lower {
        target <= &minimum
    } else {
        &maximum <= target
    };
    follows.then_some(()).ok_or(Error::NodeResultMismatch(node))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::ConditionTerm;
    use crate::kernel::{
        Variable,
        proof::arithmetic_special::{SpecialArithmeticCertificate, SpecialArithmeticNode},
    };

    fn le(a: IntegerTerm, b: IntegerTerm) -> Proposition {
        Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(a.into(), b.into()), true)
    }
    fn inputs(ends: [i64; 4]) -> (Vec<Proposition>, IntegerTerm, IntegerTerm) {
        let a = IntegerTerm::var(Variable(181_001));
        let b = IntegerTerm::var(Variable(181_002));
        (
            vec![
                le(IntegerTerm::constant(ends[0].into()), a.clone()),
                le(a.clone(), IntegerTerm::constant(ends[1].into())),
                le(IntegerTerm::constant(ends[2].into()), b.clone()),
                le(b.clone(), IntegerTerm::constant(ends[3].into())),
            ],
            a,
            b,
        )
    }
    fn goal(
        a: &IntegerTerm,
        b: &IntegerTerm,
        remainder: bool,
        target: i64,
        lower: bool,
    ) -> Proposition {
        let expression = if remainder {
            IntegerTerm::truncating_remainder(a.clone(), b.clone())
        } else {
            IntegerTerm::truncating_quotient(a.clone(), b.clone())
        };
        if lower {
            le(IntegerTerm::constant(target.into()), expression)
        } else {
            le(expression, IntegerTerm::constant(target.into()))
        }
    }
    #[test]
    #[ignore = "nightly: 0.5s in the parallel gate"]
    fn division_bounds_match_independent_small_signed_oracles() {
        for lo in -3..=3 {
            for hi in lo..=3 {
                for dlo in -3..=3 {
                    for dhi in dlo..=3 {
                        let (premises, a, b) = inputs([lo, hi, dlo, dhi]);
                        for remainder in [false, true] {
                            for target in -4..=4 {
                                for lower in [false, true] {
                                    let accepted = check(
                                        0,
                                        &[0, 1, 2, 3],
                                        &premises,
                                        &goal(&a, &b, remainder, target, lower),
                                    )
                                    .is_ok();
                                    if dlo <= 0 && dhi >= 0 {
                                        assert!(!accepted);
                                        continue;
                                    }
                                    let valid = (lo..=hi).all(|n| {
                                        (dlo..=dhi).all(|d| {
                                            let value = if remainder { n % d } else { n / d };
                                            if lower {
                                                target <= value
                                            } else {
                                                value <= target
                                            }
                                        })
                                    });
                                    assert!(
                                        !accepted || valid,
                                        "{lo}..{hi} / {dlo}..{dhi}, rem={remainder}, target={target}, lower={lower}"
                                    );
                                    if !remainder {
                                        assert_eq!(accepted, valid);
                                    }
                                    if target == -4 && lower || target == 4 && !lower {
                                        assert!(accepted);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    #[test]
    fn division_bounds_reject_forged_premises_polarity_and_operator() {
        let (premises, a, b) = inputs([-100, 100, 1, 10]);
        let valid = goal(&a, &b, false, 100, false);
        for bounds in [
            vec![],
            vec![0, 1, 2],
            vec![0, 1, 2, 4],
            vec![1, 0, 2, 3],
            vec![0, 1, 3, 2],
            vec![0, 0, 2, 3],
        ] {
            assert!(check(0, &bounds, &premises, &valid).is_err());
        }
        let mut altered = premises.clone();
        altered[2] = le(IntegerTerm::constant(1.into()), a.clone());
        assert!(check(0, &[0, 1, 2, 3], &altered, &valid).is_err());
        let mut opposite = valid.clone();
        if let Proposition::ConditionIs(_, truth) = &mut opposite {
            *truth = false;
        }
        assert!(check(0, &[0, 1, 2, 3], &premises, &opposite).is_err());
        assert!(
            check(
                0,
                &[0, 1, 2, 3],
                &premises,
                &le(
                    IntegerTerm::multiply(a, b),
                    IntegerTerm::constant(100.into())
                )
            )
            .is_err()
        );
        let cert = SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::IntegerDivisionBounds {
                bounds: vec![0, 1, 2, 3],
                result: valid.clone(),
            }],
            conclusion: 0,
        };
        assert!(cert.check(&valid, &premises).is_ok());
        let wrong = SpecialArithmeticCertificate {
            conclusion: 1,
            ..cert
        };
        assert!(wrong.check(&valid, &premises).is_err());
        for ends in [
            [10, -10, 1, 10],
            [-10, 10, 10, 1],
            [-10, 10, 0, 1],
            [-10, 10, -1, 0],
        ] {
            let (p, a, b) = inputs(ends);
            assert!(check(0, &[0, 1, 2, 3], &p, &goal(&a, &b, false, 100, false)).is_err());
        }
    }
    #[test]
    fn division_bounds_support_large_values_and_remainder_signs() {
        let (_, a, b) = inputs([0, 0, 1, 1]);
        let maximum: BigInt = (BigInt::from(1) << 127u32) - 1;
        let p = vec![
            le(IntegerTerm::constant(-&maximum), a.clone()),
            le(a.clone(), IntegerTerm::constant(maximum.clone())),
            le(IntegerTerm::constant(1.into()), b.clone()),
            le(b.clone(), IntegerTerm::constant(2147483647.into())),
        ];
        for remainder in [false, true] {
            let term = if remainder {
                IntegerTerm::truncating_remainder(a.clone(), b.clone())
            } else {
                IntegerTerm::truncating_quotient(a.clone(), b.clone())
            };
            let bound = if remainder {
                BigInt::from(2147483646)
            } else {
                maximum.clone()
            };
            assert!(
                check(
                    0,
                    &[0, 1, 2, 3],
                    &p,
                    &le(term.clone(), IntegerTerm::constant(bound.clone()))
                )
                .is_ok()
            );
            assert!(
                check(
                    0,
                    &[0, 1, 2, 3],
                    &p,
                    &le(IntegerTerm::constant(-bound), term)
                )
                .is_ok()
            );
        }
        let (p, a, b) = inputs([-2, -1, 10, 20]);
        assert!(check(0, &[0, 1, 2, 3], &p, &goal(&a, &b, true, -1, false)).is_ok());
        assert!(check(0, &[0, 1, 2, 3], &p, &goal(&a, &b, true, -2, true)).is_ok());
    }
    #[test]
    fn division_bounds_work_is_independent_of_unused_facts_and_linear_in_nodes() {
        let (mut p, a, b) = inputs([-100, 100, 1, 10]);
        let result = goal(&a, &b, true, 9, false);
        let mut baseline = None;
        for size in [4usize, 16, 64, 256] {
            while p.len() < size {
                p.push(le(
                    IntegerTerm::constant(0.into()),
                    IntegerTerm::constant(1.into()),
                ));
            }
            let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
                check(0, &[0, 1, 2, 3], &p, &result)
            });
            checked.unwrap();
            assert_eq!(*baseline.get_or_insert(work), work);
            let cert = SpecialArithmeticCertificate {
                nodes: vec![
                    SpecialArithmeticNode::IntegerDivisionBounds {
                        bounds: vec![0, 1, 2, 3],
                        result: result.clone()
                    };
                    size
                ],
                conclusion: size - 1,
            };
            let (checked, work) =
                crate::instrumentation::measure_deterministic_work(|| cert.check(&result, &p));
            checked.unwrap();
            assert_eq!(work, size * baseline.unwrap() + 1);
        }
    }
    #[test]
    fn division_bounds_precharge_magnitude_work_and_enforce_its_budget() {
        let (_, a, b) = inputs([0, 0, 1, 1]);
        let mut previous = 0;
        for bits in [64usize, 128, 256, 512, 1024] {
            let maximum = BigInt::from(1) << bits;
            let p = vec![
                le(IntegerTerm::constant(-&maximum), a.clone()),
                le(a.clone(), IntegerTerm::constant(maximum.clone())),
                le(IntegerTerm::constant(BigInt::from(1)), b.clone()),
                le(b.clone(), IntegerTerm::constant(maximum.clone())),
            ];
            let result = le(
                IntegerTerm::truncating_quotient(a.clone(), b.clone()),
                IntegerTerm::constant(maximum),
            );
            let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
                check(0, &[0, 1, 2, 3], &p, &result)
            });
            checked.unwrap();
            assert!(work > previous);
            if previous > 0 {
                assert!(work <= previous * 4);
            }
            previous = work;
            crate::instrumentation::with_run_work_limit(work - 1, || {
                assert_eq!(
                    check(0, &[0, 1, 2, 3], &p, &result),
                    Err(Error::WorkLimitExceeded)
                )
            });
            crate::instrumentation::with_run_work_limit(work, || {
                assert_eq!(check(0, &[0, 1, 2, 3], &p, &result), Ok(()))
            });
        }
    }
}
