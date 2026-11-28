//! Ordinary proofs of products and quotients from selected floating-point bounds.
use super::super::surface_certificates::surface_strict_parts;
use super::*;
use crate::kernel::proof::arithmetic_special::{
    FloatBoundWeakening, float_corner_bound_weakening, float_positive_product_bound,
    float_square_bound, float_zero_product_from_bounds, tighter_float_interval_bound,
};
use crate::kernel::{FloatBinaryOperator, KernelFloatType};

fn literal(format: KernelFloatType, bits: u64) -> SyntaxTerm {
    SyntaxTerm::ProgramExpression(match format {
        KernelFloatType::Float32 => crate::kernel::program_expression::float32_literal(bits as u32),
        KernelFloatType::Float64 => crate::kernel::program_expression::float64_literal(bits),
    })
}

fn finite(expression: &SyntaxTerm) -> SyntaxProposition {
    SyntaxProposition::FloatClassification {
        expression: expression.clone(),
        classification: syntax::CFloatClassification::Finite,
    }
}

fn less(left: SyntaxTerm, right: SyntaxTerm) -> SyntaxProposition {
    SyntaxProposition::Comparison {
        left,
        operator: ComparisonOperator::LessThan,
        right,
    }
}

fn at_most(left: SyntaxTerm, right: SyntaxTerm) -> SyntaxProposition {
    SyntaxProposition::Comparison {
        left,
        operator: ComparisonOperator::LessEqual,
        right,
    }
}

fn corner_order(
    operator: FloatBinaryOperator,
    plan: &FloatBoundWeakening,
    left: &SyntaxTerm,
    right: &SyntaxTerm,
) -> SyntaxProposition {
    let (left, right) = (Box::new(left.clone()), Box::new(right.clone()));
    let corner = match operator {
        FloatBinaryOperator::Multiply => SyntaxTerm::Multiply(left, right),
        FloatBinaryOperator::Divide => SyntaxTerm::Divide(left, right),
        _ => unreachable!("finite product or quotient"),
    };
    let bound = literal(plan.format, plan.actual_endpoint);
    let (left, right) = if plan.lower {
        (bound, corner)
    } else {
        (corner, bound)
    };
    at_most(left, right)
}

type ResolvedIntervalBound = (SyntaxProposition, (SyntaxTerm, SyntaxTerm));

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    fn resolve_float_interval_bound(
        input: &Proof<'a>,
        bound: &Proposition,
        introduced_surfaces: &[SyntaxProposition],
    ) -> Option<SyntaxProposition> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("resolve_float_interval_bound");
        Self::resolve_solve_premises_unmeasured(
            input,
            std::slice::from_ref(bound),
            introduced_surfaces,
        )
        .and_then(|mut pairs| pairs.pop().map(|(_, surface)| surface))
        .or_else(|| input.structural_proposition_candidate(bound))
    }

    fn prepare_float_interval_bounds<const N: usize>(
        input: &Proof<'a>,
        format: KernelFloatType,
        bounds: &[Proposition; N],
        introduced_surfaces: &[SyntaxProposition],
    ) -> Result<Option<(Proof<'a>, [ResolvedIntervalBound; N])>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("prepare_float_interval_bounds");
        let mut proof = input.clone();
        let mut resolved = Vec::with_capacity(N);
        for bound in bounds {
            let surface = if let Some(tighter) = tighter_float_interval_bound(bound) {
                let Some((retained, surface)) =
                    Self::retain_float_adjacent_bound(&proof, &tighter)?
                else {
                    return Ok(None);
                };
                proof = retained;
                surface
            } else {
                let Some(surface) =
                    Self::resolve_float_interval_bound(&proof, bound, introduced_surfaces)
                else {
                    return Ok(None);
                };
                surface
            };
            let Some((retained, premise, left, right)) =
                Self::prepare_float_bound(&proof, format, surface)?
            else {
                return Ok(None);
            };
            proof = retained;
            resolved.push((premise, (left, right)));
        }
        Ok(Some((
            proof,
            resolved.try_into().expect("one proof per interval bound"),
        )))
    }

    fn try_apply_float_interval_bound(
        input: &Proof<'a>,
        plan: &FloatBoundWeakening,
        name: &str,
        arguments: Vec<SyntaxTerm>,
        premises: Vec<SyntaxProposition>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_apply_float_interval_bound");
        let Some(intermediate) = input.structural_proposition_candidate(&plan.intermediate) else {
            return Ok(None);
        };
        let Some(proof) =
            Self::try_retain_float_interval_fact(input, &intermediate, name, arguments, premises)?
        else {
            return Ok(None);
        };
        Self::try_float_bound_weakening(&proof, plan, intermediate)
    }

    fn try_retain_float_interval_fact(
        input: &Proof<'a>,
        intermediate: &SyntaxProposition,
        name: &str,
        arguments: Vec<SyntaxTerm>,
        premises: Vec<SyntaxProposition>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_retain_float_interval_fact");
        let application = ProofStep::ApplyPlannedTheorem {
            application: TheoremApplication {
                name: format!("click::float_order::{name}"),
                arguments,
            },
            premises,
        };
        attempt::candidate_outcome(
            input
                .driver()
                .apply_step(super::super::wide_arithmetic::have(
                    intermediate.clone(),
                    vec![application, ProofStep::Known],
                )),
        )
    }

    pub(in crate::surface::proof) fn try_rounded_int32_to_float32_bound(
        input: &Proof<'a>,
        source: &Proposition,
        goal: &Proposition,
        source_surface: &SyntaxProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_rounded_int32_to_float32_bound");
        use crate::kernel::proof::arithmetic_special::rounded_int32_to_float32_bound;
        let Some((plan, endpoint, strict)) = rounded_int32_to_float32_bound(source, goal) else {
            return Ok(None);
        };
        let comparison = surface_comparison_with_anchored_operands(source_surface);
        let parts = if strict {
            surface_strict_parts(&comparison)
        } else {
            surface_nonstrict_parts(&comparison)
        };
        let Some((left, right)) = parts else {
            return Ok(None);
        };
        let value = if plan.lower { right } else { left };
        let observation = super::super::wide_arithmetic::to_integer(&value);
        let integer_literal = |n: i64| surface_signed_integer_literal(&BigInt::from(n));
        let endpoint = i64::from(endpoint);
        let ordered = |endpoint: SyntaxTerm| {
            if plan.lower {
                [endpoint, observation.clone()]
            } else {
                [observation.clone(), endpoint]
            }
        };
        let [left, right] = ordered(integer_literal(endpoint));
        let inclusive = at_most(left, right);
        let proof_steps = if strict {
            let (original, law) = if plan.lower {
                (endpoint - 1, "lt_step_le")
            } else {
                (endpoint + 1, "lt_le_predecessor")
            };
            let [left, right] = ordered(integer_literal(original));
            let strict = less(left.clone(), right.clone());
            vec![
                super::super::wide_arithmetic::have(strict.clone(), vec![ProofStep::Known]),
                ProofStep::ApplyPlannedTheorem {
                    application: TheoremApplication {
                        name: format!("click::integer::{law}"),
                        arguments: vec![left, right],
                    },
                    premises: vec![strict],
                },
                ProofStep::Known,
            ]
        } else {
            vec![ProofStep::Known]
        };
        let Some(proof) = attempt::candidate_outcome(input.driver().apply_step(
            super::super::wide_arithmetic::have(inclusive.clone(), proof_steps),
        ))?
        else {
            return Ok(None);
        };
        let endpoint = integer_literal(endpoint);
        let arguments = if plan.lower {
            vec![endpoint, value]
        } else {
            vec![value, endpoint]
        };
        Self::try_apply_float_interval_bound(
            &proof,
            &plan,
            "int32_to_float32_le",
            arguments,
            vec![inclusive],
        )
    }

    pub(super) fn try_float_finite_interval(
        input: &Proof<'a>,
        goal: &Proposition,
        introduced_surfaces: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_float_finite_interval");
        let Some((format, bounds)) =
            crate::kernel::proof::arithmetic_special::float_finite_interval(goal)
        else {
            return Ok(None);
        };
        let Some((proof, premises)) =
            Self::establish_arithmetic_bounds(input, &bounds, introduced_surfaces)?
        else {
            return Ok(None);
        };
        let [lower, upper] = premises.as_slice() else {
            unreachable!("both finite endpoints were established");
        };
        let (Some((lo, x)), Some((_, hi))) = (
            surface_nonstrict_parts(&surface_comparison_with_anchored_operands(lower)),
            surface_nonstrict_parts(&surface_comparison_with_anchored_operands(upper)),
        ) else {
            return Ok(None);
        };
        let name = match format {
            KernelFloatType::Float32 => "click::float_order::float32_finite_between",
            KernelFloatType::Float64 => "click::float_order::float64_finite_between",
        };
        let step = ProofStep::ApplyPlannedTheorem {
            application: TheoremApplication {
                name: name.into(),
                arguments: vec![x, lo.clone(), hi.clone()],
            },
            premises: vec![lower.clone(), upper.clone(), finite(&lo), finite(&hi)],
        };
        attempt::candidate_outcome(proof.driver().apply_step_then_close(step))
    }

    pub(in crate::surface::proof) fn try_float_zero_product_bound(
        input: &Proof<'a>,
        goal: &Proposition,
        bounds: &[Proposition; 2],
        introduced_surfaces: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_float_zero_product_bound");
        let Some((format, classification)) = float_zero_product_from_bounds(goal, bounds) else {
            return Ok(None);
        };
        let Some((proof, [(first, (lo, x)), (second, (_, hi))])) =
            Self::prepare_float_interval_bounds(input, format, bounds, introduced_surfaces)?
        else {
            return Ok(None);
        };
        let Some(finite_x) = input.structural_proposition_candidate(&classification) else {
            return Ok(None);
        };
        let premises = vec![first, second, finite(&lo), finite(&hi)];
        let name = match format {
            KernelFloatType::Float32 => "float32_finite_between",
            KernelFloatType::Float64 => "float64_finite_between",
        };
        let Some(proof) = Self::try_retain_float_interval_fact(
            &proof,
            &finite_x,
            name,
            vec![x, lo, hi],
            premises,
        )?
        else {
            return Ok(None);
        };
        attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Known))
    }

    pub(in crate::surface::proof) fn try_float_square_bound(
        input: &Proof<'a>,
        goal: &Proposition,
        bounds: &[Proposition; 2],
        introduced_surfaces: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_float_square_bound");
        let Some((plan, upper)) = float_square_bound(goal, bounds) else {
            return Ok(None);
        };
        let Some((proof, [(first, (lo, x)), (second, (_, hi))])) =
            Self::prepare_float_interval_bounds(input, plan.format, bounds, introduced_surfaces)?
        else {
            return Ok(None);
        };
        let upper = literal(plan.format, upper);
        let square_bound = |endpoint: &SyntaxTerm| SyntaxProposition::Comparison {
            left: SyntaxTerm::Multiply(Box::new(endpoint.clone()), Box::new(endpoint.clone())),
            operator: ComparisonOperator::LessEqual,
            right: upper.clone(),
        };
        let premises = vec![
            first,
            second,
            finite(&lo),
            finite(&hi),
            square_bound(&lo),
            square_bound(&hi),
        ];
        let name = match plan.format {
            KernelFloatType::Float32 => "float32_square_interval",
            KernelFloatType::Float64 => "float64_square_interval",
        };
        Self::try_apply_float_interval_bound(&proof, &plan, name, vec![x, lo, hi, upper], premises)
    }

    pub(in crate::surface::proof) fn try_positive_float_product_bound(
        input: &Proof<'a>,
        goal: &Proposition,
        bounds: &[Proposition; 2],
        introduced_surfaces: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_positive_float_product_bound");
        let Some(plan) = float_positive_product_bound(goal, bounds) else {
            return Ok(None);
        };
        let Some((proof, [(first, (a, x)), (second, (b, y))])) =
            Self::prepare_float_interval_bounds(input, plan.format, bounds, introduced_surfaces)?
        else {
            return Ok(None);
        };
        let zero = literal(plan.format, 0);
        let premises = vec![
            first,
            second,
            finite(&a),
            finite(&b),
            less(zero.clone(), a.clone()),
            less(zero, b.clone()),
        ];
        let name = match plan.format {
            KernelFloatType::Float32 => "float32_positive_product_lower",
            KernelFloatType::Float64 => "float64_positive_product_lower",
        };
        Self::try_apply_float_interval_bound(&proof, &plan, name, vec![x, y, a, b], premises)
    }

    pub(in crate::surface::proof) fn try_float_corner_bound(
        input: &Proof<'a>,
        goal: &Proposition,
        bounds: &[Proposition; 4],
        introduced_surfaces: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_float_corner_bound");
        let Some((plan, operator)) = float_corner_bound_weakening(goal, bounds) else {
            return Ok(None);
        };
        let Some((
            proof,
            [
                (first, (a, x)),
                (second, (b, y)),
                (third, (_, c)),
                (fourth, (_, d)),
            ],
        )) = Self::prepare_float_interval_bounds(input, plan.format, bounds, introduced_surfaces)?
        else {
            return Ok(None);
        };
        let mut premises = vec![
            first,
            second,
            third,
            fourth,
            finite(&a),
            finite(&b),
            finite(&c),
            finite(&d),
        ];
        use FloatBinaryOperator::{Divide, Multiply};
        let advanced = if operator == Divide {
            let zero = literal(plan.format, 0);
            let sign = SyntaxProposition::Or(
                Box::new(less(zero.clone(), b.clone())),
                Box::new(less(d.clone(), zero)),
            );
            // Selected applications cite the disjunction itself. Retain it
            // even when the two literal comparisons decide its truth.
            let Some(proof) = attempt::candidate_outcome(proof.driver().apply_step(
                super::super::wide_arithmetic::have(sign.clone(), vec![ProofStep::Known]),
            ))?
            else {
                return Ok(None);
            };
            premises.push(sign);
            Some(proof)
        } else {
            None
        };
        for (left, right) in [(&a, &b), (&a, &d), (&c, &b), (&c, &d)] {
            premises.push(corner_order(operator, &plan, left, right));
        }
        let name = match (operator, plan.format, plan.lower) {
            (Multiply, KernelFloatType::Float32, true) => "float32_product_lower",
            (Multiply, KernelFloatType::Float32, false) => "float32_product_upper",
            (Multiply, KernelFloatType::Float64, true) => "float64_product_lower",
            (Multiply, KernelFloatType::Float64, false) => "float64_product_upper",
            (Divide, KernelFloatType::Float32, true) => "float32_quotient_lower",
            (Divide, KernelFloatType::Float32, false) => "float32_quotient_upper",
            (Divide, KernelFloatType::Float64, true) => "float64_quotient_lower",
            (Divide, KernelFloatType::Float64, false) => "float64_quotient_upper",
            _ => unreachable!("finite product or quotient"),
        };
        let bound = literal(plan.format, plan.actual_endpoint);
        Self::try_apply_float_interval_bound(
            advanced.as_ref().unwrap_or(&proof),
            &plan,
            name,
            vec![x, y, a, b, c, d, bound],
            premises,
        )
    }

    pub(in crate::surface::proof) fn try_float_reciprocal_bound(
        input: &Proof<'a>,
        source: &Proposition,
        goal: &Proposition,
        source_surface: &SyntaxProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_float_reciprocal_bound");
        use crate::kernel::proof::arithmetic_special::float_reciprocal_bound_weakening;
        let Some(reciprocal) = float_reciprocal_bound_weakening(source, goal) else {
            return Ok(None);
        };
        let plan = &reciprocal.weakening;
        let comparison = surface_comparison_with_anchored_operands(source_surface);
        let parts = if reciprocal.strict_source {
            surface_strict_parts(&comparison)
        } else {
            surface_nonstrict_parts(&comparison)
        };
        let Some((left, right)) = parts else {
            return Ok(None);
        };
        let (source_bound, divisor) = if reciprocal.divisor_lower_bound {
            (left.clone(), right.clone())
        } else {
            (right.clone(), left.clone())
        };
        let bound = reciprocal.minimum_positive_endpoint.map_or_else(
            || source_bound.clone(),
            |endpoint| literal(plan.format, endpoint),
        );
        let float = match plan.format {
            KernelFloatType::Float32 => "float32",
            KernelFloatType::Float64 => "float64",
        };
        let zero = literal(plan.format, 0);
        let mut proof = input.clone();
        let premise = if reciprocal.strict_source {
            let (nonstrict, law, arguments, premises) =
                if reciprocal.minimum_positive_endpoint.is_some() {
                    (
                        at_most(bound.clone(), divisor.clone()),
                        "strictly_positive_minimum",
                        vec![source_bound.clone(), divisor.clone()],
                        vec![
                            SyntaxProposition::Comparison {
                                left: source_bound,
                                operator: ComparisonOperator::Equal,
                                right: zero.clone(),
                            },
                            source_surface.clone(),
                        ],
                    )
                } else {
                    (
                        at_most(left.clone(), right.clone()),
                        "lt_to_le",
                        vec![left, right],
                        vec![source_surface.clone()],
                    )
                };
            let application = ProofStep::ApplyPlannedTheorem {
                application: TheoremApplication {
                    name: format!("click::float_order::{float}_{law}"),
                    arguments,
                },
                premises,
            };
            let Some(next) = attempt::candidate_outcome(proof.driver().apply_step(
                super::super::wide_arithmetic::have(
                    nonstrict.clone(),
                    vec![application, ProofStep::Known],
                ),
            ))?
            else {
                return Ok(None);
            };
            proof = next;
            nonstrict
        } else {
            source_surface.clone()
        };
        let numerator = literal(plan.format, reciprocal.numerator);
        let direction = if plan.lower { "lower" } else { "upper" };
        if reciprocal.uses_positive_law {
            let premises = vec![
                finite(&numerator),
                less(zero.clone(), numerator.clone()),
                less(zero, bound.clone()),
                premise,
            ];
            return Self::try_apply_float_interval_bound(
                &proof,
                plan,
                &format!("{float}_reciprocal_{direction}"),
                vec![numerator, divisor, bound],
                premises,
            );
        }

        let sign = SyntaxProposition::Or(
            Box::new(SyntaxProposition::And(
                Box::new(less(zero.clone(), bound.clone())),
                Box::new(at_most(bound.clone(), divisor.clone())),
            )),
            Box::new(SyntaxProposition::And(
                Box::new(less(bound.clone(), zero.clone())),
                Box::new(at_most(divisor.clone(), bound.clone())),
            )),
        );
        let Some(proof) = attempt::candidate_outcome(proof.driver().apply_step(
            super::super::wide_arithmetic::have(sign.clone(), vec![ProofStep::Known]),
        ))?
        else {
            return Ok(None);
        };
        let endpoint = literal(plan.format, plan.actual_endpoint);
        let zero_bound = if plan.lower {
            at_most(endpoint.clone(), zero)
        } else {
            at_most(zero, endpoint.clone())
        };
        let premises = vec![
            finite(&numerator),
            sign,
            zero_bound,
            corner_order(FloatBinaryOperator::Divide, plan, &numerator, &bound),
        ];
        Self::try_apply_float_interval_bound(
            &proof,
            plan,
            &format!("{float}_bounded_reciprocal_{direction}"),
            vec![numerator, divisor, bound, endpoint],
            premises,
        )
    }
}
