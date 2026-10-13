//! One local, exact Integer product bound. There is no ambient premise search
//! and no machine-width interpretation: callers must separately establish the
//! meaning and definedness of any machine operation they relate to this product.

use super::arithmetic_special::SpecialArithmeticCheckError as Error;
use crate::kernel::{ConditionTerm, IntegerTerm, Proposition, SharedIntegerTerm};
use num_bigint::BigInt;

/// The two sides of an Integer `<=` fact.
pub(super) fn order(proposition: &Proposition) -> Option<(&SharedIntegerTerm, &SharedIntegerTerm)> {
    match proposition {
        Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(left, right), true) => {
            Some((left, right))
        }
        _ => None,
    }
}

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
        return Err(Error::InvalidIntegerProductBounds(node));
    }
    let (goal_left, goal_right) = order(result).ok_or(Error::InvalidOperator(node))?;
    let (product, target, lower) = if let Some(target) = goal_left.as_const() {
        (goal_right, target, true)
    } else if let Some(target) = goal_right.as_const() {
        (goal_left, target, false)
    } else {
        return Err(Error::InvalidOperator(node));
    };
    let IntegerTerm::Multiply(left, right) = product.as_ref() else {
        return Err(Error::InvalidOperator(node));
    };
    let mut endpoints = Vec::with_capacity(4);
    for (position, index) in bounds.iter().enumerate() {
        let premise = premises.get(*index).ok_or(Error::InvalidPremise(*index))?;
        let (first, second) = order(premise).ok_or(Error::InvalidIntegerProductBounds(node))?;
        let operand = if position < 2 { left } else { right };
        let endpoint = if position % 2 == 0 && second == operand {
            first.as_const()
        } else if position % 2 == 1 && first == operand {
            second.as_const()
        } else {
            None
        }
        .ok_or(Error::InvalidIntegerProductBounds(node))?;
        endpoints.push(endpoint);
    }
    let bits = |value: &BigInt| {
        usize::try_from(value.bits())
            .unwrap_or(usize::MAX)
            .saturating_add(1)
    };
    // Charge magnitude-dependent multiplication and comparisons before doing
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
        return Err(Error::InvalidIntegerProductBounds(node));
    }
    let products = [
        endpoints[0] * endpoints[2],
        endpoints[0] * endpoints[3],
        endpoints[1] * endpoints[2],
        endpoints[1] * endpoints[3],
    ];
    let follows = if lower {
        products.iter().all(|product| target <= product)
    } else {
        products.iter().all(|product| product <= target)
    };
    follows.then_some(()).ok_or(Error::NodeResultMismatch(node))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::Variable;
    use crate::kernel::proof::arithmetic_special::{
        SpecialArithmeticCertificate, SpecialArithmeticNode,
    };

    fn le(left: IntegerTerm, right: IntegerTerm) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::IntegerLessEqual(left.into(), right.into()),
            true,
        )
    }

    fn inputs(x: &IntegerTerm, y: &IntegerTerm, ends: &[BigInt; 4]) -> Vec<Proposition> {
        vec![
            le(IntegerTerm::constant(ends[0].clone()), x.clone()),
            le(x.clone(), IntegerTerm::constant(ends[1].clone())),
            le(IntegerTerm::constant(ends[2].clone()), y.clone()),
            le(y.clone(), IntegerTerm::constant(ends[3].clone())),
        ]
    }

    fn goal(x: &IntegerTerm, y: &IntegerTerm, bound: BigInt, lower: bool) -> Proposition {
        let product = IntegerTerm::multiply(x.clone(), y.clone());
        let bound = IntegerTerm::constant(bound);
        if lower {
            le(bound, product)
        } else {
            le(product, bound)
        }
    }

    fn variables() -> (IntegerTerm, IntegerTerm) {
        (
            IntegerTerm::var(Variable(700)),
            IntegerTerm::var(Variable(701)),
        )
    }

    #[test]
    fn product_bounds_match_an_exhaustive_small_integer_oracle() {
        let (x, y) = variables();
        // Include every sign quadrant, singleton zero, and crossing intervals.
        for a in -3i64..=3 {
            for b in a..=3 {
                for c in -3i64..=3 {
                    for d in c..=3 {
                        let values: Vec<_> =
                            (a..=b).flat_map(|i| (c..=d).map(move |j| i * j)).collect();
                        let lo = *values.iter().min().unwrap();
                        let hi = *values.iter().max().unwrap();
                        let premises = inputs(&x, &y, &[a.into(), b.into(), c.into(), d.into()]);
                        for (bound, lower, valid) in [
                            (lo, true, true),
                            (lo - 1, true, true),
                            (lo + 1, true, false),
                            (hi, false, true),
                            (hi + 1, false, true),
                            (hi - 1, false, false),
                        ] {
                            assert_eq!(
                                check(
                                    0,
                                    &[0, 1, 2, 3],
                                    &premises,
                                    &goal(&x, &y, bound.into(), lower)
                                )
                                .is_ok(),
                                valid,
                                "[{a}, {b}] * [{c}, {d}], bound {bound}, lower {lower}"
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn product_bounds_establish_wide_signed_ranges_without_host_width_arithmetic() {
        let (x, y) = variables();
        let ends = [
            -(BigInt::from(1) << 63usize),
            (BigInt::from(1) << 63usize) - 1,
            -(BigInt::from(1) << 31usize),
            (BigInt::from(1) << 31usize) - 1,
        ];
        let premises = inputs(&x, &y, &ends);
        for width in [96usize, 128, 256] {
            let limit = BigInt::from(1) << (width - 1usize);
            for (bound, lower) in [(-&limit, true), (&limit - 1, false)] {
                assert_eq!(
                    check(0, &[0, 1, 2, 3], &premises, &goal(&x, &y, bound, lower)),
                    Ok(())
                );
            }
        }
        // Both signed minima multiply to +2^94, outside signed 95 bits.
        let too_small = (BigInt::from(1) << 94usize) - 1;
        assert_eq!(
            check(0, &[0, 1, 2, 3], &premises, &goal(&x, &y, too_small, false)),
            Err(Error::NodeResultMismatch(0))
        );
        let large = BigInt::from(1) << 127usize;
        let premises = inputs(&x, &y, &[-&large, &large - 1, -&large, &large - 1]);
        assert_eq!(
            check(
                0,
                &[0, 1, 2, 3],
                &premises,
                &goal(&x, &y, &large - 1, false)
            ),
            Err(Error::NodeResultMismatch(0))
        );
        assert_eq!(
            check(
                0,
                &[0, 1, 2, 3],
                &premises,
                &goal(&x, &y, &large * &large, false)
            ),
            Ok(())
        );
    }

    #[test]
    fn product_bounds_reject_hostile_shape_references_and_conclusions() {
        let (x, y) = variables();
        let premises = inputs(&x, &y, &[(-2).into(), 3.into(), (-4).into(), 5.into()]);
        let result = goal(&x, &y, 15.into(), false);
        for bounds in [
            &[0, 1, 2][..],
            &[0, 1, 2, 3, 3],
            &[1, 0, 2, 3],
            &[2, 3, 0, 1],
            &[0, 1, 0, 1],
        ] {
            assert!(check(0, bounds, &premises, &result).is_err());
        }
        assert_eq!(
            check(0, &[0, 1, 2, 99], &premises, &result),
            Err(Error::InvalidPremise(99))
        );
        let mut false_fact = premises.clone();
        if let Proposition::ConditionIs(_, expected) = &mut false_fact[0] {
            *expected = false;
        }
        assert!(check(0, &[0, 1, 2, 3], &false_fact, &result).is_err());
        let mut strict = premises.clone();
        strict[0] = Proposition::ConditionIs(
            ConditionTerm::IntegerLessThan(IntegerTerm::constant_i64(-2).into(), x.clone().into()),
            true,
        );
        assert!(check(0, &[0, 1, 2, 3], &strict, &result).is_err());
        let inverted = inputs(&x, &y, &[3.into(), 2.into(), (-4).into(), 5.into()]);
        assert!(check(0, &[0, 1, 2, 3], &inverted, &result).is_err());
        let mut symbolic = premises.clone();
        symbolic[0] = le(y.clone(), x.clone());
        assert!(check(0, &[0, 1, 2, 3], &symbolic, &result).is_err());
        let unrelated = goal(&x, &IntegerTerm::var(Variable(702)), 15.into(), false);
        assert!(check(0, &[0, 1, 2, 3], &premises, &unrelated).is_err());
        assert!(check(0, &[0, 1, 2, 3], &premises, &le(x.clone(), y.clone())).is_err());
        let certificate = SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::IntegerProductBounds {
                bounds: vec![0, 1, 2, 3],
                result: result.clone(),
            }],
            conclusion: 0,
        };
        assert_eq!(certificate.check(&result, &premises), Ok(()));
        assert_eq!(
            certificate.check(&goal(&x, &y, 14.into(), false), &premises),
            Err(Error::DoesNotFollow)
        );
        let mut invalid_tail = certificate.clone();
        invalid_tail
            .nodes
            .push(SpecialArithmeticNode::IntegerProductBounds {
                bounds: vec![],
                result: result.clone(),
            });
        assert!(invalid_tail.check(&result, &premises).is_err());
    }

    #[test]
    fn product_bounds_work_is_linear_in_nodes_and_independent_of_unused_facts_and_operand_depth() {
        let (mut x, y) = variables();
        let mut last = None;
        for size in [4, 16, 64, 256, 1024] {
            for _ in 0..size {
                x = IntegerTerm::multiply(x, y.clone());
            }
            let mut premises = inputs(&x, &y, &[(-2).into(), 3.into(), (-4).into(), 5.into()]);
            premises.extend((0..size).map(|_| le(y.clone(), IntegerTerm::constant_i64(100))));
            let result = goal(&x, &y, 15.into(), false);
            let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
                check(0, &[0, 1, 2, 3], &premises, &result)
            });
            assert_eq!(checked, Ok(()));
            if let Some(last) = last {
                assert_eq!(work, last);
            }
            last = Some(work);
            let certificate = SpecialArithmeticCertificate {
                nodes: (0..size)
                    .map(|_| SpecialArithmeticNode::IntegerProductBounds {
                        bounds: vec![0, 1, 2, 3],
                        result: result.clone(),
                    })
                    .collect(),
                conclusion: 0,
            };
            let (checked, total) = crate::instrumentation::measure_deterministic_work(|| {
                certificate.check(&result, &premises)
            });
            assert_eq!(checked, Ok(()));
            assert_eq!(total, size * work + 1);
        }
    }

    #[test]
    fn product_bounds_precharge_big_integer_work_and_stop_before_arithmetic() {
        let (x, y) = variables();
        let mut previous = 0;
        for bits in [64usize, 128, 256, 512, 1024] {
            let limit = BigInt::from(1) << bits;
            let premises = inputs(&x, &y, &[-&limit, limit.clone(), -&limit, limit.clone()]);
            let result = goal(&x, &y, &limit * &limit, false);
            let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
                check(0, &[0, 1, 2, 3], &premises, &result)
            });
            assert_eq!(checked, Ok(()));
            assert!(work > previous);
            if previous != 0 {
                assert!(work <= previous * 4);
            }
            previous = work;
            crate::instrumentation::with_run_work_limit(work - 1, || {
                assert_eq!(
                    check(0, &[0, 1, 2, 3], &premises, &result),
                    Err(Error::WorkLimitExceeded)
                );
            });
            crate::instrumentation::with_run_work_limit(work, || {
                assert_eq!(check(0, &[0, 1, 2, 3], &premises, &result), Ok(()));
            });
        }
    }
}
