//! Ordinary observation and conditional bridges from explicitly selected facts.
use super::*;

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    /// Decide only whether this local rule can consume the selected context.
    /// Discovery does not borrow omitted bounds or guards from ambient facts.
    pub(in crate::surface::proof) fn known_bridge_using(
        input: &Proof<'a>,
        premises: &[ClickProposition],
    ) -> Result<bool, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("known_bridge_using");
        let Some(goal) = input.goal() else {
            return Ok(false);
        };
        let readings =
            crate::kernel::machine_integer::comparison::integer_readings_with_promotions(goal);
        let check = |available: &dyn Fn(&Proposition) -> bool| {
            crate::kernel::proof::fact_reasoning::known_bridge_leaf(goal, &available)
                || readings.iter().any(|reading| {
                    crate::kernel::proof::fact_reasoning::known_bridge_leaf(reading, &available)
                })
        };
        let mut selected = Vec::with_capacity(premises.len());
        for premise in premises {
            let kernel =
                input.lower_cited_surface_proposition(premise, "observation bridge premise")?;
            if !input.facts().listed_premise_available(&kernel, &[], false) {
                return Ok(false);
            }
            selected.push(kernel);
        }
        let facts = crate::kernel::proof::PureFactStore::from_ordered(&selected);
        // The mirrored spelling is already an exact indexed lookup in
        // `close()`. Keep restricted search tied to the selected facts.
        let mirrored =
            crate::kernel::mirrored_equality(goal).is_some_and(|premise| facts.contains(&premise));
        Ok(mirrored || check(&|p| facts.pure_known_available(p)))
    }
}

fn integer_parts(
    proposition: &Proposition,
) -> Option<(
    &crate::kernel::SharedIntegerTerm,
    &crate::kernel::SharedIntegerTerm,
)> {
    match proposition {
        condition_source_0 @ Proposition::ConditionIs(_, true)
            if let Some((
                ConditionTerm::IntegerLessEqual(a, b)
                | ConditionTerm::IntegerLessThan(a, b)
                | ConditionTerm::IntegerEqual(a, b),
                _,
            )) = condition_source_0.condition_native() =>
        {
            Some((a, b))
        }
        condition_source_0 @ Proposition::ConditionIs(_, true)
            if let Some((
                ConditionTerm::IntegerGreaterEqual(a, b) | ConditionTerm::IntegerGreaterThan(a, b),
                _,
            )) = condition_source_0.condition_native() =>
        {
            Some((b, a))
        }
        _ => None,
    }
}

fn number(value: impl Into<BigInt>) -> ContractExpression {
    super::super::surface_synthesis::integer_typed_expression(surface_signed_integer_literal(
        &value.into(),
    ))
}
fn observe(value: ContractExpression) -> ContractExpression {
    ContractExpression::Call {
        name: "to_integer".into(),
        arguments: vec![value],
    }
}
fn compare(
    left: ContractExpression,
    operator: ComparisonOperator,
    right: ContractExpression,
) -> ClickProposition {
    ClickProposition::Comparison {
        left,
        operator,
        right,
    }
}
fn le(left: ContractExpression, right: ContractExpression) -> ClickProposition {
    compare(left, ComparisonOperator::LessEqual, right)
}
fn eq(left: ContractExpression, right: ContractExpression) -> ClickProposition {
    compare(left, ComparisonOperator::Equal, right)
}
fn mul(left: ContractExpression, right: ContractExpression) -> ContractExpression {
    ContractExpression::Multiply(Box::new(left), Box::new(right))
}
fn add(left: ContractExpression, right: ContractExpression) -> ContractExpression {
    ContractExpression::Add(Box::new(left), Box::new(right))
}
fn neg(value: ContractExpression) -> ContractExpression {
    ContractExpression::Negate(Box::new(value))
}
fn application(
    name: &str,
    arguments: Vec<ContractExpression>,
    premises: Vec<ClickProposition>,
) -> ProofStep {
    ProofStep::ApplyPlannedTheorem {
        application: TheoremApplication {
            name: format!("click::integer::{name}"),
            arguments,
        },
        premises,
    }
}

// Follow only the value explicitly named by this expression. Retained point
// wrappers are put on its operand, never replaced by a different point.
fn written_operands(
    input: &Proof<'_>,
    expression: &ContractExpression,
) -> Option<(ContractExpression, ContractExpression)> {
    written_operands_inner(input, expression, &mut std::collections::HashSet::new())
}
fn written_operands_inner(
    input: &Proof<'_>,
    expression: &ContractExpression,
    aliases: &mut std::collections::HashSet<String>,
) -> Option<(ContractExpression, ContractExpression)> {
    match expression {
        ContractExpression::Call { name, arguments } if name == "to_integer" => {
            written_operands_inner(input, arguments.first()?, aliases)
        }
        ContractExpression::Binding(name) => {
            if !aliases.insert(name.clone()) {
                return None;
            }
            written_operands_inner(input, input.local_binding(name)?, aliases)
        }
        ContractExpression::CUnary { operand, .. }
        | ContractExpression::MemoryLoad {
            pointer: operand, ..
        } => written_operands_inner(input, operand, aliases),
        ContractExpression::ShiftLeft(left, right)
        | ContractExpression::ShiftRight(left, right)
        | ContractExpression::BitwiseAnd(left, right) => {
            Some((left.as_ref().clone(), right.as_ref().clone()))
        }
        ContractExpression::At {
            selector,
            expression,
        } => {
            let (left, right) = written_operands_inner(input, expression, aliases)?;
            Some((
                ContractExpression::At {
                    selector: selector.clone(),
                    expression: Box::new(left),
                },
                ContractExpression::At {
                    selector: selector.clone(),
                    expression: Box::new(right),
                },
            ))
        }
        ContractExpression::Old(expression) => {
            let (left, right) = written_operands_inner(input, expression, aliases)?;
            Some((
                ContractExpression::Old(Box::new(left)),
                ContractExpression::Old(Box::new(right)),
            ))
        }
        _ => None,
    }
}

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    /// Compose two intrinsic operand bounds without selecting ambient facts.
    /// The generated proof checks each operand at the observation in the goal.
    pub(in crate::surface::proof) fn try_intrinsic_sum_bound(
        input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_intrinsic_sum_bound");
        use crate::kernel::IntegerTerm;
        use crate::kernel::machine_integer::range::observation_range;

        let Some((condition, true)) = input.goal().and_then(Proposition::condition_native) else {
            return Ok(None);
        };
        let (left, right) = match condition {
            ConditionTerm::IntegerLessEqual(left, right) => (left.as_ref(), right.as_ref()),
            ConditionTerm::IntegerGreaterEqual(left, right) => (right.as_ref(), left.as_ref()),
            _ => return Ok(None),
        };
        let (upper, a, b, target) = match (left, right) {
            (IntegerTerm::Add(a, b), IntegerTerm::Constant(target)) => (true, a, b, target),
            (IntegerTerm::Constant(target), IntegerTerm::Add(a, b)) => (false, a, b, target),
            _ => return Ok(None),
        };
        let endpoint = |term: &IntegerTerm| match term {
            IntegerTerm::Machine(value) => {
                let (min, max) = observation_range(value);
                Some(if upper { max } else { min })
            }
            IntegerTerm::Constant(value) => Some(value.clone()),
            _ => None,
        };
        let (Some(a_bound), Some(b_bound)) = (endpoint(a), endpoint(b)) else {
            return Ok(None);
        };
        let sum = &a_bound + &b_bound;
        if (upper && &sum > target) || (!upper && &sum < target) {
            return Ok(None);
        }

        let Some(ClickProposition::Comparison { left, right, .. }) = input
            .surface_goal()
            .and_then(integer_composition::canonical_surface)
        else {
            return Ok(None);
        };
        let mut source = if upper { left } else { right };
        while let ContractExpression::IntegerContext(inner) = source {
            source = *inner;
        }
        let ContractExpression::Add(a_source, b_source) = source else {
            return Ok(None);
        };
        let spelling = |term: &IntegerTerm, source: ContractExpression| {
            term.as_const()
                .map_or(source, |value| number(value.clone()))
        };
        let a_source = spelling(a, *a_source);
        let b_source = spelling(b, *b_source);
        let orient = |value, bound| {
            if upper {
                (value, bound)
            } else {
                (bound, value)
            }
        };
        let (a_left, a_right) = orient(a_source, number(a_bound));
        let (b_left, b_right) = orient(b_source, number(b_bound));
        let operands = [
            le(a_left.clone(), a_right.clone()),
            le(b_left.clone(), b_right.clone()),
        ];
        let mut proof = input.clone();
        for operand in &operands {
            proof = proof
                .driver()
                .apply_step(super::super::wide_arithmetic::have(
                    operand.clone(),
                    vec![ProofStep::Known],
                ))?;
        }

        let left = add(a_left.clone(), b_left.clone());
        let right = add(a_right.clone(), b_right.clone());
        let composition = application(
            "add_le",
            vec![a_left, a_right, b_left, b_right],
            operands.to_vec(),
        );
        if &sum == target {
            let closed = proof.driver().apply_step(composition)?;
            return Ok(closed.focused_discharged().then_some(closed));
        }
        let combined = le(left.clone(), right.clone());
        proof = proof
            .driver()
            .apply_step(super::super::wide_arithmetic::have(
                combined.clone(),
                vec![composition],
            ))?;

        let target = number(target.clone());
        let (a, b, c, premises) = if upper {
            let weakening = le(right.clone(), target.clone());
            (left, right, target, [combined, weakening])
        } else {
            let weakening = le(target.clone(), left.clone());
            (target, left, right, [weakening, combined])
        };
        let weakening = &premises[usize::from(upper)];
        proof = proof
            .driver()
            .apply_step(super::super::wide_arithmetic::have(
                weakening.clone(),
                vec![ProofStep::Known],
            ))?;
        let proof = proof.driver().apply_step(application(
            "le_transitive",
            vec![a, b, c],
            premises.to_vec(),
        ))?;
        Ok(proof.focused_discharged().then_some(proof))
    }

    /// Replace the widened uint32-sum shortcut with its ordinary observation
    /// identity and selected Integer proof. Native widening is value preserving;
    /// the sum's int64 range follows from its operands' uint32 type ranges.
    pub(in crate::surface::proof) fn try_widened_unsigned_sum_using(
        input: &Proof<'a>,
        premises: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_widened_unsigned_sum_using");
        let (Some(goal), Some(surface)) = (input.goal(), input.surface_goal()) else {
            return Ok(None);
        };
        let Proposition::ConditionIs(condition, _) = goal else {
            return Ok(None);
        };
        if crate::kernel::PureFactContext::new()
            .widened_unsigned_sum_bound_premises(condition.native_compat())
            .is_none()
            || signed_intervals::has_retained_read_source(surface)
            || premises
                .iter()
                .any(signed_intervals::has_retained_read_source)
        {
            return Ok(None);
        }
        for source in premises {
            let kernel = input.lower_cited_surface_proposition(source, "widened sum premise")?;
            if !input.facts().listed_premise_available(&kernel, &[], false) {
                return Ok(None);
            }
        }
        // Only the goal's operations need identities; unrelated cited
        // expressions must not introduce extra overflow obligations.
        let identities = operation_identities(machine_observations(goal, &[]));
        let observed = observed_native_surface_comparison(goal, surface);
        let mut written =
            written_integer_observations(premises.iter().chain(std::iter::once(&observed)));
        // A returned scalar can name the entire sum without writing either
        // widening. Raise its two operands from the retained program state.
        // No read identities, program points, or version points are changed.
        if let Some(view) = input.premise_fixed_state_view() {
            let _recorded = super::super::surface_synthesis::SynthesisRecordedPointsScope::enter(
                view.fixed_state.recorded_states,
            );
            let query = crate::kernel::machine_integer::comparison::comparison_view(
                condition.native_compat(),
                true,
            )
            .expect("recognized widened sum comparison");
            let (_, _, operands) = query.operands[0]
                .operand_view()
                .binary()
                .expect("recognized widened sum operation");
            for operand in operands {
                let operand = operand.retain(MachineIntegerType::Int64);
                let root = operand.shared_operand().ok_or_else(|| {
                    input.step_error("widened unsigned sum operand has no shared term")
                })?;
                let source = super::super::surface_synthesis::raise_kernel_term(
                    root,
                    view.parameter_binding,
                    view.fixed_state.state,
                    &BTreeMap::new(),
                )
                .ok_or_else(|| {
                    input.step_error(
                        "cannot raise a widened unsigned sum operand from its retained source",
                    )
                })?;
                written.push(observe(source));
            }
        }
        let identities = identities.iter().collect::<Vec<_>>();
        let Ok((proof, established)) =
            Self::prove_operation_identities(input, &identities, &written, Some(premises))?
        else {
            return Ok(None);
        };
        let mut sources = premises.to_vec();
        sources.extend(established.into_iter().map(|(_, source)| source));
        Self::try_integer_composition_using(&proof, &sources)
    }

    /// Prove one explicitly bounded shift or mask through local observation
    /// facts. The arithmetic in this route uses only the ordinary emitter.
    pub(in crate::surface::proof) fn try_machine_bridge_using(
        input: &Proof<'a>,
        premises: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_machine_bridge_using");
        use crate::kernel::IntegerTerm as I;
        let Some(goal) = input.goal() else {
            return Ok(None);
        };
        let has_root = |value: &crate::kernel::SharedIntegerTerm| matches!(value.as_ref(), I::Machine(machine) if machine.operand_view().binary().is_some_and(|(_, op, _)| matches!(op, MachineBinaryOp::ShiftLeft | MachineBinaryOp::ShiftRight | MachineBinaryOp::BitwiseAnd)));
        let mut roots =
            crate::kernel::machine_integer::comparison::integer_readings_with_promotions(goal);
        if roots.is_empty() {
            roots.push(goal.clone());
        }
        if !roots
            .iter()
            .any(|root| integer_parts(root).is_some_and(|(a, b)| has_root(a) || has_root(b)))
        {
            return Ok(None);
        }
        let Some(written_goal) = input.surface_goal() else {
            return Ok(None);
        };
        let observed_goal = observed_native_surface_comparison(goal, written_goal);
        let Some(canonical) = integer_composition::canonical_surface(&observed_goal) else {
            return Ok(None);
        };
        let ClickProposition::Comparison {
            left,
            operator,
            right,
        } = canonical
        else {
            return Ok(None);
        };
        let lowered = input.lower_integer_surface_proposition(
            &compare(left.clone(), operator, right.clone()),
            "machine bridge goal",
        )?;
        let mut readings =
            crate::kernel::machine_integer::comparison::integer_readings_with_promotions(&lowered);
        if readings.is_empty() {
            readings.push(lowered);
        }
        let Some((ka, kb)) = readings
            .iter()
            .filter_map(integer_parts)
            .find(|(a, b)| has_root(a) || has_root(b))
        else {
            return Ok(None);
        };
        for source in premises {
            let kernel = input.lower_cited_surface_proposition(source, "machine bridge premise")?;
            if !input.facts().listed_premise_available(&kernel, &[], false) {
                return Ok(None);
            }
        }
        for (term, surface) in [(ka, &left), (kb, &right)] {
            let I::Machine(machine) = term.as_ref() else {
                continue;
            };
            let Some((format, op, [lhs, rhs])) = machine.operand_view().binary() else {
                continue;
            };
            if format.format().bits() != machine.ty().format().bits() {
                continue;
            }
            let format = machine.ty();
            let mut commuted = false;
            let mut amount =
                if matches!(op, MachineBinaryOp::ShiftLeft | MachineBinaryOp::ShiftRight) {
                    crate::kernel::machine_integer::bounds::constant_shift_count(rhs)
                        .map(BigInt::from)
                } else {
                    rhs.literal()
                        .and_then(|n| format.constant_from_term(&n))
                        .map(|n| n.to_integer())
                };
            if amount.is_none() && op == MachineBinaryOp::BitwiseAnd {
                commuted = true;
                amount = lhs
                    .literal()
                    .and_then(|n| format.constant_from_term(&n))
                    .map(|n| n.to_integer());
            }
            let Some(amount) = amount else {
                continue;
            };
            let Some((left, right)) = written_operands(input, surface) else {
                continue;
            };
            let source = if commuted { right } else { left };
            let source = observe(ContractExpression::CUnary {
                operand: Box::new(source),
                lowered: ProgramExpression::Cast {
                    expression: Box::new(ProgramExpression::Value(int32(0))),
                    target_type: format.program_type(),
                    integer_mode: crate::kernel::IntegerCastMode::CConversion,
                    pointee_struct: None,
                    pointee_struct_size: None,
                    pointee_volatile: false,
                    pointee_constant: false,
                    explicit_qualification: false,
                },
            });
            let observed = surface.clone();
            let mut proof = input.clone();
            let mut cited = premises.to_vec();
            // Every new fact is retained by the ordinary have driver.
            let known = |proof: &mut Proof<'a>,
                         cited: &mut Vec<ClickProposition>,
                         claim: ClickProposition|
             -> Result<(), ClickError> {
                *proof = proof
                    .driver()
                    .apply_step(super::super::wide_arithmetic::have(
                        claim.clone(),
                        vec![ProofStep::Known],
                    ))?;
                cited.push(claim);
                Ok(())
            };
            match op {
                MachineBinaryOp::BitwiseAnd if amount >= BigInt::zero() => {
                    known(&mut proof, &mut cited, le(number(0), observed.clone()))?;
                    known(&mut proof, &mut cited, le(observed.clone(), number(amount)))?;
                    let nonnegative = le(number(0), source.clone());
                    let scope = proof.driver().open_have(nonnegative.clone())?;
                    if let Some(closed) = scope.driver().try_integer_composition_using(&cited)? {
                        proof = closed.join()?;
                        cited.push(nonnegative);
                        known(&mut proof, &mut cited, le(observed.clone(), source))?;
                    }
                }
                MachineBinaryOp::ShiftLeft | MachineBinaryOp::ShiftRight => {
                    let Some(count) = amount.to_u32().filter(|n| *n < format.format().bits())
                    else {
                        continue;
                    };
                    let scale = BigInt::one() << count;
                    if op == MachineBinaryOp::ShiftLeft {
                        let (source_min, source_max) = format.format().bounds();
                        known(
                            &mut proof,
                            &mut cited,
                            le(number(source_min), source.clone()),
                        )?;
                        known(
                            &mut proof,
                            &mut cited,
                            le(source.clone(), number(source_max)),
                        )?;
                        let factor_bound = le(number(scale.clone()), number(scale.clone()));
                        known(&mut proof, &mut cited, factor_bound)?;
                        let exact = mul(number(scale.clone()), source.clone());
                        let (min, max) = format.format().bounds();
                        let mut bounds = Vec::new();
                        if format.format().is_signed() {
                            bounds.push(le(number(0), source.clone()));
                            bounds.push(le(
                                source.clone(),
                                number(format.format().bounds().1 >> count),
                            ));
                        }
                        bounds.extend([
                            le(number(min), exact.clone()),
                            le(exact.clone(), number(max)),
                        ]);
                        for bound in bounds {
                            let scope = proof.driver().open_have(bound.clone())?;
                            let closed = if matches!(bound, ClickProposition::Comparison { ref left, ref right, .. } if matches!(left,ContractExpression::Multiply(..)) || matches!(right, ContractExpression::Multiply(..)))
                            {
                                scope.driver().try_product_bound_using(&cited)?
                            } else {
                                scope.driver().try_integer_composition_using(&cited)?
                            };
                            let Some(closed) = closed else {
                                return Ok(None);
                            };
                            proof = closed.join()?;
                            cited.push(bound);
                        }
                        let identity = eq(observed.clone(), exact.clone());
                        proof = proof
                            .driver()
                            .apply_step(super::super::wide_arithmetic::have(
                                identity.clone(),
                                vec![ProofStep::Known],
                            ))?;
                        let lower = term == kb;
                        let endpoint = if lower { ka.as_const() } else { kb.as_const() };
                        if let Some(endpoint) = endpoint {
                            let endpoint = if operator == ComparisonOperator::LessThan {
                                if lower {
                                    endpoint + BigInt::one()
                                } else {
                                    endpoint - BigInt::one()
                                }
                            } else {
                                endpoint.clone()
                            };
                            let product_bound = if lower {
                                le(number(endpoint), exact.clone())
                            } else {
                                le(exact.clone(), number(endpoint))
                            };
                            let scope = proof.driver().open_have(product_bound.clone())?;
                            let Some(closed) = scope.driver().try_product_bound_using(&cited)?
                            else {
                                return Ok(None);
                            };
                            proof = closed.join()?;
                            proof = proof.driver().apply_step(ProofStep::Rewrite(identity))?;
                            if proof.focused_discharged() {
                                return Ok(Some(proof));
                            }
                            if let Ok(closed) = proof.driver().apply_step(ProofStep::Known) {
                                return Ok(Some(closed));
                            }
                            cited = vec![product_bound];
                        } else {
                            cited.push(identity);
                        }
                    } else {
                        let slack: BigInt = &scale - 1;
                        let scaled = mul(number(scale.clone()), observed.clone());
                        known(&mut proof, &mut cited, le(scaled.clone(), source.clone()))?;
                        known(
                            &mut proof,
                            &mut cited,
                            le(source, add(scaled, number(slack.clone()))),
                        )?;
                        // Integer rounding is explicit. For a lower bound,
                        // negate the quotient and the requested endpoint.
                        let lower = term == kb;
                        let endpoint = if lower { ka.as_const() } else { kb.as_const() };
                        let Some(endpoint) = endpoint else {
                            return Ok(None);
                        };
                        let endpoint = if operator == ComparisonOperator::LessThan {
                            if lower {
                                endpoint + BigInt::one()
                            } else {
                                endpoint - BigInt::one()
                            }
                        } else {
                            endpoint.clone()
                        };
                        let q = if lower {
                            neg(observed.clone())
                        } else {
                            observed.clone()
                        };
                        let bound = if lower { -&endpoint } else { endpoint.clone() };
                        let threshold = add(
                            mul(number(bound.clone()), number(scale.clone())),
                            number(slack.clone()),
                        );
                        let raw_scaled = if lower {
                            neg(mul(number(scale.clone()), observed.clone()))
                        } else {
                            mul(number(scale.clone()), observed.clone())
                        };
                        if crate::instrumentation::deadline_exceeded_with_work(
                            (bound.bits() as usize + 1).saturating_mul(scale.bits() as usize + 1),
                        ) {
                            return Ok(None);
                        }
                        let threshold_value = number(&bound * &scale + &slack);
                        let threshold_equality = eq(threshold.clone(), threshold_value.clone());
                        proof = proof
                            .driver()
                            .apply_step(super::super::wide_arithmetic::have(
                                threshold_equality.clone(),
                                vec![ProofStep::Known],
                            ))?;
                        let raw_bound = le(raw_scaled.clone(), threshold_value);
                        let scope = proof.driver().open_have(raw_bound.clone())?;
                        let Some(closed) = scope.driver().try_integer_composition_using(&cited)?
                        else {
                            return Ok(None);
                        };
                        proof = closed.join()?;
                        let commuted = eq(
                            mul(q.clone(), number(scale.clone())),
                            mul(number(scale.clone()), q.clone()),
                        );
                        proof = proof
                            .driver()
                            .apply_step(super::super::wide_arithmetic::have(
                                commuted.clone(),
                                vec![application(
                                    "multiply_commutative",
                                    vec![q.clone(), number(scale.clone())],
                                    vec![],
                                )],
                            ))?;
                        if lower {
                            let negated =
                                eq(mul(number(scale.clone()), q.clone()), raw_scaled.clone());
                            proof =
                                proof
                                    .driver()
                                    .apply_step(super::super::wide_arithmetic::have(
                                        negated,
                                        vec![application(
                                            "multiply_negate",
                                            vec![number(scale.clone()), observed],
                                            vec![],
                                        )],
                                    ))?;
                        }
                        let scaled_bound = le(mul(q.clone(), number(scale.clone())), threshold);
                        // Congruence combines the two named equations when the
                        // quotient was negated; then one rewrite exposes raw_bound.
                        let equality = eq(mul(q.clone(), number(scale.clone())), raw_scaled);
                        proof = proof
                            .driver()
                            .apply_step(super::super::wide_arithmetic::have(
                                equality.clone(),
                                vec![ProofStep::Known],
                            ))?;
                        proof = proof
                            .driver()
                            .apply_step(super::super::wide_arithmetic::have(
                                scaled_bound.clone(),
                                vec![
                                    ProofStep::Rewrite(equality),
                                    ProofStep::Rewrite(threshold_equality),
                                    ProofStep::Known,
                                ],
                            ))?;
                        let rounded = le(q.clone(), number(bound.clone()));
                        proof = proof
                            .driver()
                            .apply_step(super::super::wide_arithmetic::have(
                                rounded.clone(),
                                vec![application(
                                    "round_down_le",
                                    vec![
                                        q,
                                        number(bound),
                                        number(scale.clone()),
                                        number(slack.clone()),
                                    ],
                                    vec![
                                        compare(
                                            number(0),
                                            ComparisonOperator::LessThan,
                                            number(scale.clone()),
                                        ),
                                        compare(
                                            number(slack),
                                            ComparisonOperator::LessThan,
                                            number(scale),
                                        ),
                                        scaled_bound,
                                    ],
                                )],
                            ))?;
                        cited.push(rounded);
                    }
                }
                _ => continue,
            }
            if proof.focused_discharged() {
                return Ok(Some(proof));
            }
            if let Some(closed) = Self::try_integer_composition_using(&proof, &cited)? {
                return Ok(Some(closed));
            }
        }
        Ok(None)
    }
}

// Do not detach a conditional from a binder or a program point. The
// mathematical/native context is retained so a native arm equation does not
// accidentally become an Integer conditional with different branch types.
pub(super) fn conditional_candidates<'s>(
    left: &'s ContractExpression,
    right: &'s ContractExpression,
    mathematical: bool,
    remaining: &mut usize,
) -> Result<Vec<(&'s ContractExpression, bool)>, &'static str> {
    use ContractExpression as E;
    let mut pending = vec![(right, mathematical, 0), (left, mathematical, 0)];
    let mut result = Vec::new();
    while let Some((expression, mathematical, depth)) = pending.pop() {
        if *remaining == 0 || crate::instrumentation::deadline_exceeded_with_work(1) {
            return Err("conditional expansion reached its work or 4096-node bound");
        }
        *remaining -= 1;
        if depth >= 256 {
            return Err("conditional expansion reached its source depth bound");
        }
        match expression {
            // Visit only the selected arm, after the outer equation has been
            // rewritten. An inactive arm may not have an evaluable domain.
            E::If { .. } => result.push((expression, mathematical)),
            E::IntegerContext(inner) => pending.push((inner, true, depth + 1)),
            E::CUnary { operand, .. } => pending.push((operand, false, depth + 1)),
            E::Negate(inner) | E::BitwiseNot(inner) => {
                pending.push((inner, mathematical, depth + 1));
            }
            E::Add(a, b)
            | E::Subtract(a, b)
            | E::Multiply(a, b)
            | E::Divide(a, b)
            | E::Remainder(a, b)
            | E::ShiftLeft(a, b)
            | E::ShiftRight(a, b)
            | E::RustShiftLeft(a, b)
            | E::RustShiftRight(a, b)
            | E::BitwiseAnd(a, b)
            | E::BitwiseOr(a, b)
            | E::BitwiseXor(a, b) => {
                pending.push((b, mathematical, depth + 1));
                pending.push((a, mathematical, depth + 1));
            }
            E::AlgebraicConstructor { arguments, .. } => {
                pending.extend(arguments.iter().rev().map(|arg| (arg, false, depth + 1)));
            }
            E::Call { name, arguments } => {
                let mathematical = matches!(
                    name.rsplit("::").next(),
                    Some("truncating_quotient" | "truncating_remainder")
                );
                pending.extend(
                    arguments
                        .iter()
                        .rev()
                        .map(|argument| (argument, mathematical, depth + 1)),
                );
            }
            _ => {}
        }
    }
    Ok(result)
}

pub(super) fn non_numeric_conditional_goal(goal: &Proposition) -> bool {
    let goal = match goal {
        Proposition::Not(body) => body.as_ref(),
        _ => goal,
    };
    matches!(&goal, condition_source @ Proposition::ConditionIs(_, _)
        if matches!(condition_source.condition_native(), Some((ConditionTerm::BoolEqual(..) | ConditionTerm::BoolIf { .. } | ConditionTerm::AlgebraicEqual(..), _))))
        || matches!(
            goal,
            Proposition::Equal(Term::Algebraic(_), Term::Algebraic(_))
        )
}

// Branch selection emits local equations and rewrites. Arithmetic after
// those rewrites remains in the existing ordinary proof emitters.
impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    pub(in crate::surface::proof) fn rewrite_conditional_arms_using(
        input: &Proof<'a>,
        premises: &[ClickProposition],
    ) -> Result<Option<(Proof<'a>, Vec<ClickProposition>)>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("rewrite_conditional_arms_using");
        let Some(goal) = input.goal() else {
            return Ok(None);
        };
        let mathematical = integer_affine_claim(goal).is_some();
        let narrow_native = matches!(goal, Proposition::ConditionIs(condition, _)
            if condition.operand_view().comparison().is_some_and(|(format, _, _)| format.format().bits() < 32));
        if !mathematical
            && !narrow_native
            && !non_numeric_conditional_goal(goal)
            && !crate::kernel::machine_integer::comparison::integer_readings_with_promotions(goal)
                .iter()
                .any(|reading| integer_affine_claim(reading).is_some())
        {
            return Ok(None);
        }
        let Some(ClickProposition::Comparison { left, right, .. }) = input
            .surface_goal()
            .and_then(integer_composition::canonical_surface)
        else {
            return Ok(None);
        };
        let mut remaining = 4096;
        // Ordinary arithmetic goals should not construct a selected fact
        // context when their written expression contains no conditional.
        if conditional_candidates(&left, &right, mathematical, &mut remaining)
            .map_err(|message| input.step_error(message))?
            .is_empty()
        {
            return Ok(None);
        }
        let mut selected = Vec::new();
        for source in premises {
            let kernel =
                input.lower_cited_surface_proposition(source, "conditional bridge premise")?;
            if !input.facts().listed_premise_available(&kernel, &[], false) {
                return Ok(None);
            }
            selected.push(kernel);
        }
        let facts = crate::kernel::proof::PureFactStore::from_ordered(&selected);
        let mut proof = input.clone();
        let mut sources = premises.to_vec();
        let mut changed = false;
        for _ in 0..64 {
            let Some(ClickProposition::Comparison { left, right, .. }) = proof
                .surface_goal()
                .and_then(integer_composition::canonical_surface)
            else {
                break;
            };
            let candidates = conditional_candidates(&left, &right, mathematical, &mut remaining)
                .map_err(|message| proof.step_error(message))?;
            let mut next = None;
            'candidate: for (expression, mathematical) in candidates {
                let ContractExpression::If {
                    condition,
                    then_branch,
                    else_branch,
                } = expression
                else {
                    unreachable!("conditional candidate");
                };
                for (guard, arm) in [
                    (condition.as_ref().clone(), then_branch),
                    (ClickProposition::Not(condition.clone()), else_branch),
                ] {
                    let lowered = proof
                        .lower_cited_surface_proposition(&guard, "conditional bridge guard")?;
                    if !facts.pure_known_available(&lowered)
                        && !crate::surface::planning::solve::computes_with_known(&lowered)
                    {
                        continue;
                    }
                    let left = if mathematical {
                        super::super::surface_synthesis::integer_typed_expression(
                            expression.clone(),
                        )
                    } else {
                        expression.clone()
                    };
                    let equality = compare(left, ComparisonOperator::Equal, arm.as_ref().clone());
                    let Ok(equation) =
                        proof
                            .driver()
                            .apply_step(super::super::wide_arithmetic::have(
                                equality.clone(),
                                vec![ProofStep::Known],
                            ))
                    else {
                        continue;
                    };
                    let rewritten = equation
                        .driver()
                        .apply_step(ProofStep::Rewrite(equality.clone()))?;
                    if rewritten.goal() == proof.goal() {
                        continue;
                    }
                    next = Some((rewritten, equality));
                    break 'candidate;
                }
            }
            let Some((rewritten, equality)) = next else {
                break;
            };
            proof = rewritten;
            sources.push(equality);
            changed = true;
            if proof.focused_discharged() {
                return Ok(Some((proof, sources)));
            }
        }
        if !changed {
            return Ok(None);
        }
        Ok(Some((proof, sources)))
    }

    pub(in crate::surface::proof) fn try_conditional_bridge_using(
        input: &Proof<'a>,
        premises: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_conditional_bridge_using");
        let Some((proof, sources)) = Self::rewrite_conditional_arms_using(input, premises)? else {
            return attempt::candidate_outcome(Self::try_conditional_bound_using(input, premises))
                .map(Option::flatten);
        };
        if proof.focused_discharged() {
            return Ok(Some(proof));
        }
        let selected_goal = proof.goal().is_some_and(|goal| {
            sources.iter().any(|source| {
                proof
                    .lower_cited_surface_proposition(source, "conditional arm premise")
                    .is_ok_and(|premise| selected_premise_contains_goal(&premise, goal))
            })
        });
        if selected_goal
            || Self::known_bridge_using(&proof, &sources)?
            || proof
                .goal()
                .is_some_and(crate::kernel::proof::fact_reasoning::computes_leaf)
        {
            return proof.driver().apply_step(ProofStep::Known).map(Some);
        }
        if let Some(closed) = Self::try_integer_composition_using(&proof, &sources)? {
            return Ok(Some(closed));
        }
        if let Some(closed) = Self::try_widened_unsigned_sum_using(&proof, &sources)? {
            return Ok(Some(closed));
        }
        Self::try_signed_interval_using(&proof, &sources)
    }

    /// Prove an order bound by checking its two selected arms. Try one
    /// written guard and close each branch from its explicit evidence.
    pub(super) fn try_conditional_bound_using(
        input: &Proof<'a>,
        premises: &[ClickProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_conditional_bound_using");
        let Some(ClickProposition::Comparison {
            left,
            operator:
                ComparisonOperator::LessEqual
                | ComparisonOperator::LessThan
                | ComparisonOperator::GreaterEqual
                | ComparisonOperator::GreaterThan,
            right,
        }) = input
            .surface_goal()
            .and_then(integer_composition::canonical_surface)
        else {
            return Ok(None);
        };
        // An order may compare exact observations of native operands.
        // Preserve the conditional's lexical Integer context, if any.
        let mut remaining = 4096;
        let candidates = conditional_candidates(&left, &right, false, &mut remaining)
            .map_err(|message| input.step_error(message))?;
        let Some((
            expression @ ContractExpression::If {
                condition,
                then_branch,
                else_branch,
            },
            mathematical,
        )) = candidates.first().copied()
        else {
            return Ok(None);
        };
        let condition = condition.as_ref().clone();
        let Some((mut proof, split, ids)) =
            attempt::candidate_outcome(input.split_focused_if(condition.clone()))?
        else {
            return Ok(None);
        };
        let marker = proof.checkpoint();
        let operand = if mathematical {
            super::super::surface_synthesis::integer_typed_expression(expression.clone())
        } else {
            expression.clone()
        };
        let mut sources = premises.to_vec();
        for (id, (guard, arm)) in ids.into_iter().zip([
            (condition.clone(), then_branch),
            (
                ClickProposition::Not(Box::new(condition.clone())),
                else_branch,
            ),
        ]) {
            let branch = proof.focus_branch(id)?;
            let equality = eq(operand.clone(), arm.as_ref().clone());
            let stated = branch
                .driver()
                .apply_step(super::super::wide_arithmetic::have(
                    equality.clone(),
                    vec![ProofStep::Known],
                ))?;
            let rewritten = stated
                .driver()
                .apply_step(ProofStep::Rewrite(equality.clone()))?;
            sources.extend([guard, equality]);
            proof = if let Some(goal) = rewritten.goal() {
                let listed = || {
                    sources.iter().any(|source| {
                        rewritten
                            .lower_cited_surface_proposition(source, "conditional arm bound")
                            .is_ok_and(|premise| {
                                selected_premise_contains_goal(&premise, goal)
                                    && rewritten.facts().listed_premise_available(
                                        &premise,
                                        &[],
                                        false,
                                    )
                            })
                    })
                };
                if !crate::surface::planning::solve::computes_with_known(goal)
                    && !listed()
                    && !Self::known_bridge_using(&rewritten, &sources)?
                {
                    return Ok(None);
                }
                rewritten.driver().apply_step(ProofStep::Known)?
            } else {
                rewritten
            };
            sources.truncate(premises.len());
        }
        attempt::candidate_outcome(proof.join_focused_if(&marker, split, ids, condition))
    }
}

#[cfg(test)]
mod widened_sum_tests {
    use crate::surface::{
        expand_c_claim_source_by_label, verify_c_sources, without_implicit_solve,
    };

    fn replay(source: &str, c: &[(&str, &str)], label: &str) {
        let expanded = expand_c_claim_source_by_label(source, c, label)
            .unwrap_or_else(|error| panic!("{}\n{source}", error.message()));
        assert!(!expanded.contains("normalize("), "{expanded}");
        assert!(!expanded.contains("solve("), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, c))
            .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: widened unsigned sums with strict expansion replay"]
    fn widened_unsigned_sums_expand_without_normalize() {
        for (parameters, bounds, goal) in [
            (
                "a: uint32, b: uint32",
                "a <= 10u32; b <= 20u32;",
                "a as int64 + b as int64 <= 30i64",
            ),
            (
                "a: uint32, b: uint32",
                "",
                "a as int64 + b as int64 <= 8589934590i64",
            ),
            (
                "a: uint32, b: uint8",
                "a <= 4294967040u32;",
                "a as int64 + b as int64 <= 4294967295i64",
            ),
            (
                "a: uint8, b: uint8",
                "",
                "a as int64 + b as int64 <= 510i64",
            ),
            (
                "a: uint16, b: uint16",
                "",
                "a as int64 + b as int64 <= 131070i64",
            ),
            ("a: uint32", "a <= 10u32;", "a as int64 + 7i64 <= 17i64"),
            (
                "a: uint32, b: uint32",
                "a <= 10u32; b <= 20u32;",
                "to_integer(a as int64 + b as int64) <= 30",
            ),
            (
                "a: uint32, b: uint32",
                "31u32 <= a;",
                "not (a as int64 + b as int64 <= 30i64)",
            ),
        ] {
            let requires = bounds
                .split(';')
                .filter(|p| !p.trim().is_empty())
                .map(|p| format!("requires {p};"))
                .collect::<String>();
            for tactic in [format!("close() using {{ {bounds} }};"), "close();".into()] {
                let source = format!(
                    "theorem widened({parameters}) {{ {requires} ensures {goal} by {{ {tactic} }} }}"
                );
                replay(&source, &[], "widened.ensures_0");
            }
        }
        let c = "long add_byte(unsigned sum, unsigned char byte) { unsigned word = (unsigned)byte; long wide = (long)sum + (long)word; return wide; }";
        let source = r#"verifying "wide.c";
            int64 add_byte(uint32 sum, uint8 byte) {
                requires sum <= 4294967040u32;
                ensures result <= 4294967295i64 by {
                    step_until(function.exit);
                    close() using { (byte as uint32) <= 255u32; sum <= 4294967040u32; };
                }
            }"#;
        replay(source, &[("wide.c", c)], "add_byte.ensures_0");
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: widened unsigned sum refusal controls"]
    fn widened_unsigned_sums_require_the_selected_bounds() {
        for (bounds, goal, selected) in [
            (
                "requires a <= 10u32; requires b <= 20u32;",
                "a as int64 + b as int64 <= 30i64",
                "a <= 10u32;",
            ),
            (
                "requires a <= 10u32; requires b <= 20u32;",
                "a as int64 + b as int64 <= 29i64",
                "a <= 10u32; b <= 20u32;",
            ),
            ("", "a as int64 + b as int64 <= 8589934589i64", ""),
        ] {
            let source = format!(
                "theorem bad(a: uint32,b: uint32) {{ {bounds} ensures {goal} by {{ close() using {{ {selected} }}; }} }}"
            );
            assert!(verify_c_sources(&source, &[]).is_err(), "{source}");
        }
    }
}

#[cfg(test)]
mod nested_conditional_tests {
    #[cfg(not(feature = "fast-gate"))]
    use crate::surface::{
        expand_c_claim_source_by_label, verify_c_sources, without_implicit_solve,
    };

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: nested conditional expansion and strict replay"]
    fn nested_conditionals_expand_without_normalize() {
        let mut failures = Vec::new();
        for (parameters, bounds, goal) in [
            (
                "flag: Bool, x: Integer, y: Integer",
                "flag; x <= 5;",
                "(if flag {x} else {y}) + 3 <= 8",
            ),
            (
                "flag: Bool, x: Integer, y: Integer",
                "not flag; y <= 5;",
                "3 * (if flag {x} else {y}) <= 15",
            ),
            (
                "flag: Bool, x: int32, y: int32",
                "flag; x <= 5;",
                "to_integer(if flag {x} else {y}) + 3 <= 8",
            ),
            (
                "flag: Bool, x: int32, y: int32",
                "flag;",
                "to_integer((if flag {x} else {y}) as int64) == to_integer(x)",
            ),
            (
                "flag: Bool, x: int32, y: int32",
                "flag; 0 <= x; x <= 5; defined((if flag {x} else {y}) + 1);",
                "to_integer((if flag {x} else {y}) + 1) <= 6",
            ),
            (
                "flag: Bool, inner: Bool, x: Integer, y: Integer",
                "flag; not inner; y <= 5;",
                "(if flag {if inner {x} else {y}} else {0}) + 3 <= 8",
            ),
            (
                "flag: Bool, inner: Bool, x: Integer, y: Integer",
                "flag; inner; x <= 5; y <= 5;",
                "(if flag {x} else {0}) + (if inner {y} else {0}) <= 10",
            ),
            (
                "flag: Bool, inner: Bool, x: Integer",
                "flag; inner; x <= 5;",
                "3 + (if flag {x} else {0}) <= ((if inner {8} else {0}) : Integer)",
            ),
            (
                "flag: Bool, x: uint32, y: uint32",
                "flag; x <= 10u32;",
                "(if flag {x} else {y}) as int64 + 1i64 <= 11i64",
            ),
            (
                "flag: Bool",
                "flag;",
                "truncating_quotient(if flag {7} else {9}, 2) == 3",
            ),
            (
                "flag: Bool",
                "flag;",
                "3 + (if flag {4} else {truncating_quotient(1, 0)}) == 7",
            ),
            (
                "flag: Bool, x: Integer",
                "flag; x <= 5;",
                "not ((if flag {x} else {0}) + 3 > 8)",
            ),
        ] {
            let requirements = bounds
                .split(';')
                .filter(|p| !p.trim().is_empty())
                .map(|p| format!("requires {p};"))
                .collect::<String>();
            for tactic in [format!("close() using {{ {bounds} }};"), "close();".into()] {
                let source = format!(
                    "theorem nested({parameters}) {{ {requirements} ensures {goal} by {{ {tactic} }} }}"
                );
                if std::panic::catch_unwind(|| {
                    let expanded = expand_c_claim_source_by_label(&source, &[], "nested.ensures_0")
                        .unwrap_or_else(|e| panic!("{}\n{source}", e.message()));
                    assert!(!expanded.contains("normalize("), "{source}\n{expanded}");
                    assert!(!expanded.contains("solve("), "{expanded}");
                    without_implicit_solve(|| verify_c_sources(&expanded, &[]))
                        .unwrap_or_else(|e| panic!("{}\n{expanded}", e.message()));
                })
                .is_err()
                {
                    failures.push(source);
                }
            }
        }
        assert!(failures.is_empty(), "{}", failures.join("\n"));
    }

    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: nested conditional guard and type refusal controls"]
    fn nested_conditionals_preserve_selected_guards_and_arm_domains() {
        for source in [
            "theorem bad(flag: Bool,x: Integer,y: Integer) {requires flag; requires x<=5; ensures (if flag{x}else{y})+3<=8 by {close() using {x<=5;};}}",
            "theorem bad(flag: Bool,inner: Bool,x: Integer,y: Integer) {requires flag; requires inner; requires x<=5; ensures (if flag{if inner{x}else{y}}else{0})+3<=8 by {close() using {flag;x<=5;};}}",
            "theorem bad(flag: Bool) {requires flag; ensures to_integer((if flag{4294967295u32}else{0u32}) as int64)==-1 by {close() using {flag;};}}",
            "theorem bad(flag: Bool) {requires flag; ensures (if flag{1}else{3})+3==6 by {close() using {flag;};}}",
        ] {
            crate::surface::parse(source).unwrap();
            assert!(verify_c_sources(source, &[]).is_err(), "{source}");
        }
        let source = r#"theorem bad(flag: Bool, a: uint64, d: uint64) {
            requires flag; requires d == 64u64;
            ensures to_integer(if flag {a << d} else {0u64}) == 0 by {
                close() using {flag; d == 64u64;};
            }
        }"#;
        crate::surface::parse(source).unwrap();
        assert!(verify_c_sources(source, &[]).is_err());
    }
}

#[cfg(test)]
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: Boolean and constructor conditional expansion and strict replay"]
fn non_numeric_conditional_arms_expand_without_normalize() {
    use crate::surface::{
        expand_c_claim_source_by_label, verify_c_sources, without_implicit_solve,
    };

    let prelude =
        "spec enum Choice { Missing, Present(int32), } spec enum Wrapper { Wrap(Choice), }";
    for (parameters, premises, goal) in [
        (
            "g: Bool, a: Bool, b: Bool",
            "g == true;",
            "(if g { a } else { b }) == a",
        ),
        (
            "g: Bool",
            "g == false;",
            "(if g { true } else { false }) == false",
        ),
        (
            "g: Bool, a: Bool",
            "g == true; a == true;",
            "(if g { a } else { false }) == true",
        ),
        (
            "g: Bool, h: Bool, a: Bool, b: Bool, c: Bool",
            "g == true; h == false;",
            "(if g { if h { a } else { b } } else { c }) == b",
        ),
        (
            "g: Bool, x: int32",
            "g == true;",
            "(if g { Choice::Present(x) } else { Choice::Missing }) == Choice::Present(x)",
        ),
        (
            "g: Bool, x: int32",
            "g == false;",
            "Choice::Missing == (if g { Choice::Present(x) } else { Choice::Missing })",
        ),
        (
            "g: Bool, h: Bool, x: int32, y: int32",
            "g == true; h == false;",
            "(if g { if h { Choice::Present(x) } else { Choice::Present(y) } } else { Choice::Missing }) == Choice::Present(y)",
        ),
        (
            "g: Bool, x: int32",
            "g == true;",
            "Wrapper::Wrap(if g { Choice::Present(x) } else { Choice::Missing }) == Wrapper::Wrap(Choice::Present(x))",
        ),
    ] {
        let requirements = premises
            .split(';')
            .filter(|p| !p.trim().is_empty())
            .map(|p| format!("requires {};", p.trim()))
            .collect::<String>();
        for tactic in [
            format!("close() using {{ {premises} }};"),
            "close();".into(),
        ] {
            let source = format!(
                "{prelude} theorem selected({parameters}) {{ {requirements} ensures {goal} by {{ {tactic} }} }}"
            );
            let expanded = expand_c_claim_source_by_label(&source, &[], "selected.ensures_0")
                .unwrap_or_else(|error| panic!("{}\n{source}", error.message()));
            assert!(!expanded.contains("normalize("), "{expanded}");
            assert!(!expanded.contains("solve("), "{expanded}");
            without_implicit_solve(|| verify_c_sources(&expanded, &[]))
                .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
        }
    }

    for claim in [
        "theorem omitted(g: Bool, a: Bool, b: Bool) { requires g == true; ensures (if g { a } else { b }) == a by { close() using {}; } }",
        "theorem omitted(g: Bool, x: int32) { requires g == true; ensures (if g { Choice::Present(x) } else { Choice::Missing }) == Choice::Present(x) by { close() using {}; } }",
        "theorem wrong(g: Bool, x: int32) { requires g == true; ensures (if g { Choice::Present(x) } else { Choice::Missing }) == Choice::Missing by close(); }",
    ] {
        let source = format!("{prelude} {claim}");
        crate::surface::parse(&source).expect("conditional refusal should parse");
        assert!(verify_c_sources(&source, &[]).is_err(), "{source}");
    }
}
