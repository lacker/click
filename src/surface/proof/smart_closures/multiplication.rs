//! Explicit multiplication order from the stated order and factor sign.
use super::*;

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    pub(in crate::surface::proof) fn try_multiply_order_using(
        input: &Proof<'a>,
        premises: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_multiply_order_using");
        use crate::kernel::IntegerTerm as I;
        let Some((
            OldConditionTerm::IntegerLessEqual(gl, gr)
            | OldConditionTerm::IntegerGreaterEqual(gl, gr),
            _,
        )) = input.goal().and_then(Proposition::old_condition)
        else {
            return Ok(None);
        };
        if !matches!(gl.as_ref(), I::Multiply(..)) && !matches!(gr.as_ref(), I::Multiply(..)) {
            return Ok(None);
        }
        let Some(surface) = input
            .surface_goal()
            .and_then(integer_composition::canonical_surface)
        else {
            return Ok(None);
        };
        let Some((_, ComparisonOperator::LessEqual, _)) = integer_surface_ordered_parts(&surface)
        else {
            return Ok(None);
        };
        let goal = input.lower_integer_surface_proposition(&surface, "multiplication order")?;
        let Some((OldConditionTerm::IntegerLessEqual(left, right), true)) = goal.old_condition()
        else {
            return Ok(None);
        };
        if !matches!(left.as_ref(), I::Multiply(..)) && !matches!(right.as_ref(), I::Multiply(..)) {
            return Ok(None);
        }
        let mut orders = Vec::new();
        for source in premises {
            let Some(canonical) = integer_composition::canonical_surface(source) else {
                continue;
            };
            let Some((a, ComparisonOperator::LessEqual, b)) =
                integer_surface_ordered_parts(&canonical)
            else {
                continue;
            };
            let kernel =
                input.lower_integer_surface_proposition(&canonical, "multiplication premise")?;
            let readings = if matches!(&kernel, condition_source_0 @ Proposition::ConditionIs(_, _) if matches!(condition_source_0.old_condition(), Some((OldConditionTerm::Compare { .. }, _))))
            {
                crate::kernel::machine_integer::comparison::integer_readings_with_promotions(
                    &kernel,
                )
            } else {
                vec![kernel]
            };
            for kernel in readings {
                if let Some((OldConditionTerm::IntegerLessEqual(x, y), true)) =
                    (kernel).old_condition()
                {
                    orders.push((source, a.clone(), b.clone(), x.clone(), y.clone()));
                }
            }
        }
        for (sign, sa, sb, x, y) in &orders {
            let (factor, written, negative) = if x.as_const().is_some_and(Zero::is_zero) {
                (y, sb, false)
            } else if y.as_const().is_some_and(Zero::is_zero) {
                (x, sa, true)
            } else {
                continue;
            };
            for (order, a, b, ka, kb) in &orders {
                check_verification_deadline()?;
                let (first, second) = if negative { (kb, ka) } else { (ka, kb) };
                let product = |a: &crate::kernel::SharedIntegerTerm,
                               b: &crate::kernel::SharedIntegerTerm|
                 -> crate::kernel::SharedIntegerTerm {
                    I::multiply(a.as_ref().clone(), b.as_ref().clone()).into()
                };
                let l = product(first, factor);
                let r = product(second, factor);
                if (left != &l && left != &product(factor, first))
                    || (right != &r && right != &product(factor, second))
                {
                    continue;
                }
                let mut proof = input.clone();
                for (source, actual, canonical) in [
                    (if negative { b } else { a }, left, &l),
                    (if negative { a } else { b }, right, &r),
                ] {
                    if actual == canonical {
                        continue;
                    }
                    let equality = SyntaxProposition::Comparison {
                        left: SyntaxTerm::Multiply(
                            Box::new(source.clone()),
                            Box::new(written.clone()),
                        ),
                        operator: ComparisonOperator::Equal,
                        right: SyntaxTerm::Multiply(
                            Box::new(written.clone()),
                            Box::new(source.clone()),
                        ),
                    };
                    let scope = proof.driver().open_have(equality)?;
                    let closed =
                        scope
                            .driver()
                            .apply_step_then_close(ProofStep::ApplyPlannedTheorem {
                                application: TheoremApplication {
                                    name: "click::integer::multiply_commutative".into(),
                                    arguments: vec![source.clone(), written.clone()],
                                },
                                premises: vec![],
                            })?;
                    proof = closed.join()?;
                }
                let proof = proof.driver().apply_step(ProofStep::ApplyPlannedTheorem {
                    application: TheoremApplication {
                        name: format!(
                            "click::integer::multiply_order_{}",
                            if negative {
                                "nonpositive"
                            } else {
                                "nonnegative"
                            }
                        ),
                        arguments: vec![a.clone(), b.clone(), written.clone()],
                    },
                    premises: vec![(*order).clone(), (*sign).clone()],
                })?;
                return Ok(Some(if proof.focused_discharged() {
                    proof
                } else {
                    proof.driver().apply_step(ProofStep::Known)?
                }));
            }
        }
        Ok(None)
    }
}
