//! Discovery over Surface proof presentations; semantic state remains in ProofObject.
use super::*;
use crate::kernel::{OffsetTree, OffsetView};

thread_local! {
    static PREDICATE_SEARCH_PATH: std::cell::RefCell<BTreeSet<String>> = const { std::cell::RefCell::new(BTreeSet::new()) };
}
// Search cycle prevention belongs to the active search, never proof state.
struct PredicateSearchGuard(String);
impl PredicateSearchGuard {
    fn enter(name: &str) -> Option<Self> {
        PREDICATE_SEARCH_PATH
            .with(|path| path.borrow_mut().insert(name.to_string()))
            .then(|| Self(name.to_string()))
    }
}
impl Drop for PredicateSearchGuard {
    fn drop(&mut self) {
        PREDICATE_SEARCH_PATH.with(|path| path.borrow_mut().remove(&self.0));
    }
}

/// Premise citations must already be evaluable; a proposed `have` may
/// carry evaluation requirements that its ordinary driver still must prove.
#[derive(Clone, Copy)]
enum SurfaceRaisingPurpose {
    AvailablePremise,
    ProposedGoal,
}

/// After stored reads resolve, the same indicators can occur in a different
/// order. At most three 0-or-1 terms fit in int32 regardless of their guards.
/// Observe the uncast sums with `to_integer` so the checked arithmetic leaf
/// can compute the equality without treating the outer native casts as atoms.
fn observed_reordered_indicator_sum(surface: &SyntaxProposition) -> Option<SyntaxProposition> {
    fn indicator_count(mut value: &SyntaxTerm) -> Option<usize> {
        fn literal(expression: &SyntaxTerm, value: u32) -> bool {
            match expression {
                SyntaxTerm::ProgramExpression(ProgramExpression::Value(actual)) => {
                    actual == &int32(value)
                }
                SyntaxTerm::IntegerLiteral(actual) => *actual == value.to_string(),
                _ => false,
            }
        }

        let mut count = 0;
        while let SyntaxTerm::Add(prefix, term) = value {
            let SyntaxTerm::If {
                then_branch,
                else_branch,
                ..
            } = term.as_ref()
            else {
                return None;
            };
            if count == 3 || !literal(then_branch, 1) || !literal(else_branch, 0) {
                return None;
            }
            count += 1;
            value = prefix;
        }
        (count >= 2 && literal(value, 0)).then_some(count)
    }

    let uncast = |expression: &SyntaxTerm| match expression {
        SyntaxTerm::CUnary {
            operand,
            lowered:
                ProgramExpression::Cast {
                    target_type: crate::kernel::ProgramType::Int32,
                    ..
                },
        } => Some(operand.clone()),
        _ => None,
    };
    let SyntaxProposition::Comparison {
        left,
        operator: ComparisonOperator::Equal,
        right,
    } = surface
    else {
        return None;
    };
    let left = uncast(left)?;
    let right = uncast(right)?;
    if indicator_count(&left)? != indicator_count(&right)? {
        return None;
    }

    let observe = |expression: Box<SyntaxTerm>| SyntaxTerm::Call {
        name: "to_integer".into(),
        arguments: vec![*expression],
    };
    Some(SyntaxProposition::Comparison {
        left: observe(left),
        operator: ComparisonOperator::Equal,
        right: observe(right),
    })
}

fn is_field_observation(term: &SyntaxTerm) -> bool {
    match term {
        SyntaxTerm::Field { .. } => true,
        SyntaxTerm::At { expression, .. } => {
            matches!(expression.as_ref(), SyntaxTerm::Field { .. })
        }
        _ => false,
    }
}

fn field_at_two_points<'a>(
    left: &'a SyntaxTerm,
    right: &'a SyntaxTerm,
) -> Option<(&'a SyntaxTerm, &'a SyntaxTerm)> {
    fn anchor(term: &SyntaxTerm) -> (Option<&ProgramPointSelector>, &SyntaxTerm) {
        match term {
            SyntaxTerm::At {
                selector:
                    selector @ ProgramPointSelector::ProgramPoint(ProgramPointRef {
                        region: CodeRegionRef::Region(_) | CodeRegionRef::Path(_),
                        kind: ProgramPointKind::Entry | ProgramPointKind::Exit,
                    }),
                expression,
            } => (Some(selector), expression),
            _ => (None, term),
        }
    }
    for (earlier, current) in [(left, right), (right, left)] {
        let (earlier_point, earlier_read) = anchor(earlier);
        let (current_point, current_read) = anchor(current);
        let across_entry = earlier_point.is_some()
            && earlier_point == current_point
            && matches!(earlier_read, SyntaxTerm::Old(read) if read.as_ref() == current_read);
        let across_named_points = earlier_point.is_some()
            && current_point.is_some()
            && earlier_point != current_point
            && earlier_read == current_read;
        if matches!(current_read, SyntaxTerm::Field { .. }) && (across_entry || across_named_points)
        {
            return Some((earlier, current_read));
        }
    }
    None
}

impl<'a> crate::kernel::search::ProofSearch<Proof<'a>> {
    /// Try a goal-local computation or a checked derivation over selected
    /// premises. A missing list permits only goal-local computation.
    pub(in crate::surface::proof) fn try_local_checked_closure(
        search_input: &Proof<'a>,
        premises: Option<Vec<SyntaxProposition>>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_local_checked_closure");
        if search_input
            .goal()
            .is_some_and(crate::surface::planning::solve::computes_with_known)
            || Self::known_bridge_using(search_input, premises.as_deref().unwrap_or(&[]))?
        {
            return search_input.driver().apply_step(ProofStep::Known).map(Some);
        }
        if let Some(closed) =
            attempt::candidate_outcome(Self::try_intrinsic_sum_bound(search_input))?.flatten()
        {
            return Ok(Some(closed));
        }
        if let Some(premises) = &premises
            && let Some(closed) = attempt::candidate_outcome(
                Self::try_bounded_observation_identity_using(search_input, premises),
            )?
            .flatten()
        {
            return Ok(Some(closed));
        }
        if let Some(closed) =
            Self::try_pointer_translation_using(search_input, premises.as_deref().unwrap_or(&[]))?
        {
            return Ok(Some(closed));
        }
        if let Some(closed) =
            Self::try_widened_unsigned_sum_using(search_input, premises.as_deref().unwrap_or(&[]))?
        {
            return Ok(Some(closed));
        }
        if let Some(premises) = &premises
            && let Some(closed) = Self::try_address_words_using(search_input, premises)?
        {
            return Ok(Some(closed));
        }
        if let Some(premises) = &premises
            && let Some(closed) = Self::try_quotient_shift_using(search_input, premises)?
        {
            return Ok(Some(closed));
        }
        if let Some(closed) = Self::try_integer_algebra(search_input)? {
            return Ok(Some(closed));
        }
        if let Some(premises) = &premises
            && let Some(closed) = Self::try_conditional_bridge_using(search_input, premises)?
        {
            return Ok(Some(closed));
        }
        if let Some(premises) = &premises
            && let Some(closed) = Self::try_machine_bridge_using(search_input, premises)?
        {
            return Ok(Some(closed));
        }
        if let Some(premises) = &premises
            && let Some(closed) = Self::try_division_bound_using(search_input, premises)?
        {
            return Ok(Some(closed));
        }
        if let Some(premises) = &premises
            && let Some(closed) = Self::try_multiply_order_using(search_input, premises)?
        {
            return Ok(Some(closed));
        }
        if let Some(premises) = &premises
            && let Some(closed) = Self::try_product_bound_using(search_input, premises)?
        {
            return Ok(Some(closed));
        }
        if let Some(guard) = search_input
            .goal()
            .and_then(uint64_increment_upper_bound_guard)
            && let Some(sources) = &premises
            && let Some(step) = sources.iter().find_map(|source| {
                search_input
                    .lower_cited_surface_proposition(source, "uint64 increment guard")
                    .ok()
                    .filter(|premise| *premise == guard)
                    .and_then(|_| uint64_increment_upper_bound_application(source))
            })
            && let Some(applied) =
                attempt::candidate_outcome(search_input.driver().apply_step(step))?
        {
            if applied.focused_discharged() {
                return Ok(Some(applied));
            }
            if let Some(closed) =
                attempt::candidate_outcome(applied.driver().apply_step(ProofStep::Known))?
            {
                return Ok(Some(closed));
            }
        }
        // A cited literal result of a completed call can replace the wide
        // operand of a returning conversion before direct computation.
        if let Some(
            [
                equality @ SyntaxProposition::Comparison {
                    left: SyntaxTerm::RegionResult(_),
                    operator: ComparisonOperator::Equal,
                    right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(_)),
                },
            ],
        ) = premises.as_deref()
            && let Some(rewritten) = attempt::candidate_outcome(
                search_input
                    .driver()
                    .apply_step(ProofStep::Rewrite(equality.clone())),
            )?
        {
            if rewritten.focused_discharged() {
                return Ok(Some(rewritten));
            }
            if rewritten
                .goal()
                .is_some_and(crate::surface::planning::solve::computes_with_known)
                && let Some(closed) =
                    attempt::candidate_outcome(rewritten.driver().apply_step(ProofStep::Known))?
            {
                return Ok(Some(closed));
            }
        }
        Ok(None)
    }

    /// Construct an interval-product proof over the explicitly selected facts.
    /// Selection is slow work; replay names the four bounds and four corners.
    pub(in crate::surface::proof) fn try_product_bound_using(
        search_input: &Proof<'a>,
        premises: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_product_bound_using");
        use crate::kernel::IntegerTerm;
        fn has_product(goal: &Proposition) -> bool {
            match goal {
                Proposition::Not(inner) => has_product(inner),
                condition_source_0 @ Proposition::ConditionIs(_, _)
                    if let Some((
                        OldConditionTerm::IntegerLessEqual(a, b)
                        | OldConditionTerm::IntegerGreaterEqual(a, b)
                        | OldConditionTerm::IntegerLessThan(a, b)
                        | OldConditionTerm::IntegerGreaterThan(a, b),
                        _,
                    )) = condition_source_0.old_condition() =>
                {
                    matches!(a.as_ref(), IntegerTerm::Multiply(..))
                        || matches!(b.as_ref(), IntegerTerm::Multiply(..))
                }
                _ => false,
            }
        }
        if !search_input.goal().is_some_and(has_product) {
            return Ok(None);
        }
        let Some(surface) = search_input.surface_goal() else {
            return Ok(None);
        };
        let Some(canonical) = super::integer_composition::canonical_surface(surface) else {
            return Ok(None);
        };
        let Some((_, ComparisonOperator::LessEqual, _)) = integer_surface_ordered_parts(&canonical)
        else {
            return Ok(None);
        };
        let kernel = search_input.lower_integer_surface_proposition(&canonical, "product bound")?;
        let Some((OldConditionTerm::IntegerLessEqual(a, b), true)) = kernel.old_condition() else {
            return Ok(None);
        };
        let (product, target, lower) = if let Some(target) = a.as_const() {
            (b, target, true)
        } else if let Some(target) = b.as_const() {
            (a, target, false)
        } else {
            return Ok(None);
        };
        let IntegerTerm::Multiply(x, y) = product.as_ref() else {
            return Ok(None);
        };
        // The cited bound supplies its operand's exact spelling, even when
        // the goal names the complete product through an Integer let binding.
        let mut selected: [Option<(BigInt, SyntaxProposition, SyntaxTerm)>; 4] =
            std::array::from_fn(|_| None);
        for (i, operand) in [x, y].into_iter().enumerate() {
            if let Some(value) = operand.as_const() {
                let written = super::super::surface_synthesis::integer_typed_expression(
                    surface_signed_integer_literal(value),
                );
                let bound = SyntaxProposition::Comparison {
                    left: written.clone(),
                    operator: ComparisonOperator::LessEqual,
                    right: written.clone(),
                };
                selected[2 * i] = Some((value.clone(), bound.clone(), written.clone()));
                selected[2 * i + 1] = Some((value.clone(), bound, written));
            }
        }
        for surface in premises {
            let written = super::integer_composition::canonical_surface(surface)
                .unwrap_or_else(|| surface.clone());
            let Some((written_left, _, written_right)) = integer_surface_ordered_parts(&written)
            else {
                continue;
            };
            let premise =
                search_input.lower_integer_surface_proposition(&written, "product interval")?;
            let readings = if matches!(&premise, condition_source_0 @ Proposition::ConditionIs(_, _) if matches!(condition_source_0.old_condition(), Some((OldConditionTerm::Compare { .. }, _))))
            {
                crate::kernel::machine_integer::comparison::integer_readings_with_promotions(
                    &premise,
                )
            } else {
                vec![premise]
            };
            for premise in readings {
                let Some((OldConditionTerm::IntegerLessEqual(a, b), true)) =
                    premise.old_condition()
                else {
                    continue;
                };
                for (i, operand) in [x, y].into_iter().enumerate() {
                    for (upper, bounded, endpoint) in [(false, &b, &a), (true, &a, &b)] {
                        if bounded.value_read() != operand.value_read() {
                            continue;
                        }
                        let Some(value) = endpoint.as_const() else {
                            continue;
                        };
                        let index = i * 2 + usize::from(upper);
                        if selected[index]
                            .as_ref()
                            .is_none_or(|(old, _, _)| if upper { value < old } else { value > old })
                        {
                            selected[index] = Some((value.clone(), surface.clone(), {
                                let written = if upper {
                                    written_left.clone()
                                } else {
                                    written_right.clone()
                                };
                                // Native bounds supply a machine spelling; theorem
                                // arguments denote its mathematical observation.
                                if matches!(operand.value_read(), IntegerTerm::Machine(_))
                                    && super::integer_composition::observed_argument(&written)
                                        .is_none()
                                {
                                    SyntaxTerm::Call {
                                        name: "to_integer".into(),
                                        arguments: vec![written],
                                    }
                                } else {
                                    written
                                }
                            }));
                        }
                    }
                }
            }
        }
        let [
            Some((lo_x, p0, written_x)),
            Some((hi_x, p1, _)),
            Some((lo_y, p2, written_y)),
            Some((hi_y, p3, _)),
        ] = selected
        else {
            return Ok(None);
        };
        if lo_x > hi_x || lo_y > hi_y {
            return Ok(None);
        }
        let mut corners = Vec::with_capacity(4);
        for x in [&lo_x, &hi_x] {
            for y in [&lo_y, &hi_y] {
                let work = (x.bits() as usize + 1)
                    .saturating_mul(y.bits() as usize + 1)
                    .saturating_add(target.bits() as usize + 1);
                if crate::instrumentation::deadline_exceeded_with_work(work) {
                    return Ok(None);
                }
                let value = x * y;
                if if lower {
                    target > &value
                } else {
                    &value > target
                } {
                    return Ok(None);
                }
                let product = SyntaxTerm::Multiply(
                    Box::new(surface_signed_integer_literal(x)),
                    Box::new(surface_signed_integer_literal(y)),
                );
                let (left, right) = if lower {
                    (surface_signed_integer_literal(target), product)
                } else {
                    (product, surface_signed_integer_literal(target))
                };
                corners.push(SyntaxProposition::Comparison {
                    left: super::super::surface_synthesis::integer_typed_expression(left),
                    operator: ComparisonOperator::LessEqual,
                    right,
                });
            }
        }
        let mut proof = search_input.clone();
        for corner in &corners {
            let scope = proof.driver().open_have(corner.clone())?;
            let closed = scope.driver().apply_step(ProofStep::Known)?;
            proof = closed.join()?;
        }
        let mut cited = vec![p0, p1, p2, p3];
        cited.extend(corners);
        let arguments = vec![
            written_x,
            written_y,
            surface_signed_integer_literal(&lo_x),
            surface_signed_integer_literal(&hi_x),
            surface_signed_integer_literal(&lo_y),
            surface_signed_integer_literal(&hi_y),
            surface_signed_integer_literal(target),
        ];
        Ok(Some(proof.driver().apply_step(
            ProofStep::ApplyPlannedTheorem {
                application: TheoremApplication {
                    name: format!(
                        "click::integer::product_{}_bound",
                        if lower { "lower" } else { "upper" }
                    ),
                    arguments,
                },
                premises: cited,
            },
        )?))
    }

    /// Strategy dispatch for the smart arithmetic step. Keep the same selected
    /// premise order, explicit certificates, and refusal precedence as solve.
    pub(in crate::surface::proof) fn apply_arithmetic_using(
        search_input: &Proof<'a>,
        premises: &[SyntaxProposition],
    ) -> Result<Proof<'a>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("apply_arithmetic_using");
        if crate::surface::proof::implicit_solve_scope::checked_only() {
            return Err(search_input.step_error("checked-only verification forbids arithmetic search; write its proof steps explicitly"));
        }
        if let Some(closed) = Self::try_quotient_shift_using(search_input, premises)? {
            return Ok(closed);
        }
        if let Some(closed) = Self::try_conditional_bridge_using(search_input, premises)? {
            return Ok(closed);
        }
        if let Some(closed) = Self::try_machine_bridge_using(search_input, premises)? {
            return Ok(closed);
        }
        if let Some(proof) = Self::try_integer_composition_using(search_input, premises)? {
            return Ok(proof);
        }
        if let Some(closed) = Self::try_signed_interval_using(search_input, premises)? {
            return Ok(closed);
        }
        if search_input.goal().is_some_and(|goal| {
            crate::kernel::proof::arithmetic_special::signed_definedness_query(goal).is_some()
        }) {
            let pairs = premises
                .iter()
                .map(|p| {
                    search_input
                        .lower_cited_surface_proposition(p, "definedness premise")
                        .map(|k| (k, p.clone()))
                })
                .collect::<Result<Vec<_>, _>>()?;
            if pairs.iter().all(|(kernel, _)| {
                search_input
                    .facts()
                    .listed_premise_available(kernel, &[], false)
            }) && let Some(closed) =
                Self::try_restricted_signed_definedness_closure(search_input, &pairs)?
            {
                return Ok(closed);
            }
        }
        if let Some(proof) = Self::try_unsigned_order_step_using(search_input, premises) {
            return Ok(proof);
        }
        let ordinary = search_input.arithmetic_refusal(premises);
        if let Some(refuted) = Self::disequality_by_refutation(search_input, premises) {
            return refuted;
        }
        match Self::try_wide_arithmetic_using(search_input, premises) {
            Ok(proof) => Ok(proof),
            Err(Some(reason)) => Err(search_input.step_error(format!(
                "arithmetic read the current goal as a 64-bit comparison: {reason}"
            ))),
            Err(None) => ordinary,
        }
    }

    pub(in crate::surface::proof) fn try_signed_interval_using(
        search_input: &Proof<'a>,
        premises: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_signed_interval_using");
        let (Some(goal), Some(surface_goal)) = (search_input.goal(), search_input.surface_goal())
        else {
            return Ok(None);
        };
        let pairs = premises
            .iter()
            .map(|p| {
                search_input
                    .lower_cited_surface_proposition(p, "signed interval premise")
                    .map(|k| (k, p.clone()))
            })
            .collect::<Result<Vec<_>, _>>()?;
        if pairs
            .iter()
            .any(|(k, _)| !search_input.facts().listed_premise_available(k, &[], false))
        {
            return Ok(None);
        }
        let kernels = pairs.iter().map(|(k, _)| k.clone()).collect::<Vec<_>>();
        let retained = signed_intervals::has_retained_read_source(surface_goal);
        let add_sub = retained && signed_intervals::is_int32_add_sub_obligation(goal);
        if add_sub
            && let Some(closed) =
                attempt::candidate_outcome(Self::try_int32_add_sub_using(search_input, premises))?
                    .flatten()
        {
            return Ok(Some(closed));
        }
        if retained {
            for source in &kernels {
                if let Some(closed) = Self::try_native_integer_bound(search_input, source)?
                    && closed.is_complete()
                {
                    return Ok(Some(closed));
                }
            }
            if kernels.contains(goal) || crate::surface::planning::solve::computes_with_known(goal)
            {
                return search_input.driver().apply_step(ProofStep::Known).map(Some);
            }
        }
        if let Some(closed) = Self::try_interval_fact_using(search_input, premises)? {
            return Ok(Some(closed));
        }
        let Some(plan) =
            plan_arithmetic(ArithmeticEngine::SignedInt32WithWeakening, goal, &kernels)
                .and_then(ArithmeticPlan::signed_int32)
        else {
            return Ok(None);
        };
        let Some(certificate) = search_input.signed_plan_to_surface(&plan, &pairs, surface_goal)
        else {
            return Ok(None);
        };
        Self::apply_signed_interval_composition(search_input, &certificate)
    }

    /// Construct ordinary proofs of the selected Integer composition plan.
    /// Unsupported rule families retain their existing arithmetic routes.
    pub(in crate::surface::proof) fn try_integer_composition_using(
        search_input: &Proof<'a>,
        premises: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_integer_composition_using");
        let (Some(goal), Some(surface_goal)) = (search_input.goal(), search_input.surface_goal())
        else {
            return Ok(None);
        };
        // Plan the same Integer observation that the ordinary emitter checks.
        // A native operation goal and its observed source can have distinct
        // representations even though the observation is their exact reading.
        let observed = observed_native_surface_comparison(goal, surface_goal);
        let observed_goal = if matches!(
            surface_comparison_with_anchored_operands(&observed),
            SyntaxProposition::Comparison { .. }
        ) {
            search_input.lower_cited_surface_proposition(&observed, "Integer composition goal")?
        } else {
            goal.clone()
        };
        let goal = &observed_goal;
        if integer_affine_claim(goal).is_none() {
            return Ok(None);
        }
        let mut pairs = Vec::with_capacity(premises.len());
        for surface in premises {
            let kernel = search_input
                .lower_cited_surface_proposition(surface, "Integer arithmetic premise")?;
            // A declined route leaves the original tactic's diagnostic and
            // native definedness/observation handling authoritative.
            if !search_input
                .facts()
                .listed_premise_available(&kernel, &[], false)
            {
                #[cfg(test)]
                integer_composition::note_refusal(format!(
                    "unavailable Integer source: {surface:?} => {kernel:?}"
                ));
                return Ok(None);
            }
            if integer_affine_claim(&kernel).is_none()
                && crate::kernel::proof::integer_arithmetic::integer_disequality_claims(&kernel)
                    .is_empty()
            {
                // All written citations were checked for availability above.
                // Other selected fragments can accompany the scalar bounds;
                // they do not prevent an Integer plan from using those bounds.
                continue;
            }
            pairs.push((kernel, surface.clone()));
        }
        let kernels = pairs
            .iter()
            .map(|(kernel, _)| kernel.clone())
            .collect::<Vec<_>>();
        for engine in [
            ArithmeticEngine::IntegerAffine,
            ArithmeticEngine::IntegerRefutation,
        ] {
            let Some(plan) =
                plan_arithmetic(engine, goal, &kernels).and_then(ArithmeticPlan::integer_affine)
            else {
                continue;
            };
            let candidate =
                Self::apply_integer_composition(search_input, &plan, &pairs, surface_goal, &[]);
            #[cfg(test)]
            if let Err(error) = &candidate {
                integer_composition::note_refusal(format!(
                    "construction error: {}",
                    error.raw_summary()
                ));
            }
            if let Some(closed) = attempt::candidate_outcome(candidate)?.flatten() {
                return Ok(Some(closed));
            }
        }
        if matches!(&goal, condition_source_0 @ Proposition::ConditionIs(_, true) if matches!(condition_source_0.old_condition(), Some((OldConditionTerm::IntegerEqual(..), _))))
            && specialized::needs_distribution(&observed)
        {
            let plan = SpecializedCompositionPlan {
                premises: Vec::new(),
                nodes: vec![SpecialArithmeticNode::IntegerPolynomialIdentity {
                    bounds: Vec::new(),
                    result: observed,
                }],
                conclusion: 0,
            };
            return Ok(
                attempt::candidate_outcome(Self::apply_specialized_composition(
                    search_input,
                    &plan,
                ))?
                .flatten(),
            );
        }
        Ok(None)
    }

    /// The fact `lower <u upper` as a proof that has it in that spelling,
    /// with the fact's surface and its two operands. The fact may be held
    /// as `upper >u lower`; it is then first restated the other way round by
    /// Integer arithmetic. Both lookups are exact: no fact is scanned.
    fn try_unsigned_strict_fact(
        search_input: &Proof<'a>,
        lower: &OldMachineTerm,
        upper: &OldMachineTerm,
        surface_fact: &dyn Fn(&Proposition) -> Option<SyntaxProposition>,
    ) -> Option<(Proof<'a>, SyntaxProposition, SyntaxTerm, SyntaxTerm)> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_unsigned_strict_fact");
        let less = Proposition::condition_is(
            OldConditionTerm::unsigned_less_than(lower.clone(), upper.clone()),
            true,
        );
        if let Some(surface) = surface_fact(&less) {
            let (lower, upper) = surface_strict_parts(&surface)?;
            return Some((search_input.clone(), surface, lower, upper));
        }
        let greater = Proposition::condition_is(
            OldConditionTerm::unsigned_greater_than(upper.clone(), lower.clone()),
            true,
        );
        let surface = surface_fact(&greater)?;
        let (lower, upper) = surface_strict_parts(&surface)?;
        let reversed = SyntaxProposition::Comparison {
            left: lower.clone(),
            operator: ComparisonOperator::LessThan,
            right: upper.clone(),
        };
        let proof = search_input
            .driver()
            .have_by_integer_arithmetic(reversed.clone(), vec![surface])
            .ok()?;
        Some((proof, reversed, lower, upper))
    }

    fn try_direct_logical_leaf(
        input: &Proof<'a>,
        budget: &mut attempt::AttemptBudget,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_direct_logical_leaf");
        let mut candidates = direct_logical_candidates(input.goal()).into_iter();
        if let Some(closed) = attempt::try_steps(input, budget, candidates.by_ref().take(1))? {
            return Ok(Some(closed));
        }
        if let Some(closed) =
            attempt::candidate_outcome(Self::try_intrinsic_sum_bound(input))?.flatten()
        {
            return Ok(Some(closed));
        }
        if let Some(closed) =
            attempt::candidate_outcome(Self::try_conditional_bound_using(input, &[]))?.flatten()
        {
            return Ok(Some(closed));
        }
        if let Some(proof) = Self::try_linked_pointer_viewability(input)? {
            return Ok(Some(proof));
        }
        if let Some(target) = input.surface_goal()
            && let Some(proof) = Self::try_indexed_read_preservation(
                input,
                target,
                MAX_TRANSPORT_SOURCE_POINTS,
                false,
            )?
        {
            return Ok(Some(proof));
        }
        attempt::try_steps(input, budget, candidates)
    }

    /// A small shared search combinator for structural proposition closure.
    /// Every candidate is accepted only through `apply_step`; `intro` is the
    /// binder move; disjunctions open a `have` for a smaller disjunct.
    ///
    /// A miss is `Ok(None)` and leaves `self` the unchanged authority. An
    /// error is a tooling failure such as an exceeded deadline; it must abort
    /// the enclosing search rather than read as one more rejection.
    pub(in crate::surface::proof) fn try_direct_logical_closure(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_direct_logical_closure");
        if crate::surface::proof::implicit_solve_scope::checked_only() {
            return attempt::candidate_outcome(search_input.driver().apply_step(ProofStep::Known));
        }
        let mut scope = attempt::search_scope("direct logical closure");
        let mut budget = attempt::AttemptBudget::unbounded();
        let mut proof = search_input.clone();
        let mut openings = Vec::new();
        let mut closed = 'close: loop {
            if let Some(closed) = Self::try_direct_logical_leaf(&proof, &mut budget)? {
                break 'close closed;
            }
            // A disjunct that closes directly needs no search through the
            // other side's connected facts. Retain its ordinary `have` proof
            // and inject it with `known`, just as the general structural
            // search does. Recursion only visits smaller goal disjuncts; a
            // miss never invokes general solve.
            if matches!(proof.goal(), Some(Proposition::Or(_, _)))
                && let Some((left, right)) = proof
                    .surface_goal()
                    .and_then(|goal| surface_logical_children(goal, false))
            {
                for disjunct in [left, right] {
                    let Some(disjunct_scope) =
                        attempt::candidate_outcome(proof.driver().open_have(disjunct))?
                    else {
                        continue;
                    };
                    let Some(closed) = disjunct_scope.driver().try_direct_logical_closure()? else {
                        continue;
                    };
                    let Some(joined) = attempt::candidate_outcome(closed.join())? else {
                        continue;
                    };
                    if let Some(closed) =
                        attempt::candidate_outcome(joined.driver().apply_step(ProofStep::Known))?
                    {
                        break 'close closed;
                    }
                }
            }
            if let Some(closed) =
                crate::kernel::search::ProofSearch::try_discharged_consequent_closure(&(proof))?
            {
                break 'close closed;
            }
            if let Some(closed) =
                crate::kernel::search::ProofSearch::try_quantified_conjunct_projection_closure(
                    &(proof),
                )?
            {
                break 'close closed;
            }
            // The kernel introduces only these outer connectives. An
            // atomic goal cannot take this step; constructing its rejection
            // would also capture an unused memory-history diagnostic.
            if !matches!(
                proof.goal(),
                Some(Proposition::Implies(..) | Proposition::ForAll { .. })
            ) {
                return Ok(None);
            }
            // An antecedent that context-free normalization refutes, such as
            // `to_integer(i) == to_integer(i) + 1`, closes the implication
            // once introduced and its negation has been proved.
            let refuted = match (proof.goal(), proof.surface_goal()) {
                (
                    Some(Proposition::Implies(antecedent, _)),
                    Some(SyntaxProposition::Implies(surface, _)),
                ) if normalization_refutes(antecedent) => Some(surface.as_ref().clone()),
                _ => None,
            };
            match attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Intro))? {
                Some(introduced) => {
                    openings.push((proof, introduced.clone()));
                    proof = introduced;
                }
                None => return Ok(None),
            }
            if let Some(antecedent) = refuted
                && let Some(closed) =
                    attempt::candidate_outcome(Self::close_refuted_fact(&proof, &antecedent))?
            {
                break 'close closed;
            }
        };
        for (parent, introduced) in openings.into_iter().rev() {
            closed = parent.finish_generated_intro(&introduced, closed)?;
        }
        scope.succeed();
        Ok(Some(closed))
    }

    /// Modus ponens as a direct logical step: the goal is the consequent of
    /// an available implication (or chain) whose antecedents are exactly
    /// available, such as a call guarantee `left_result == 0 implies X`
    /// inside the branch whose path condition is `left_result == 0`. The
    /// consequent index selects the source implication. For an order
    /// comparison, search also tries its mirrored spelling with one additional
    /// probe. Expansion prints a `have` with explicit fact application and
    /// closes the goal with `known`.
    pub(in crate::surface::proof) fn try_discharged_consequent_closure(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_discharged_consequent_closure");
        let (Some(goal), Some(surface)) = (search_input.goal(), search_input.surface_goal()) else {
            return Ok(None);
        };
        if !search_input
            .facts()
            .contains_discharged_implication_consequent(goal)
        {
            // Implication extraction deliberately requires the consequent as
            // written. Select its mirrored order spelling in search, then
            // let the checked extraction and ordinary `known` close it.
            if let SyntaxProposition::Comparison {
                left,
                operator,
                right,
            } = surface
            {
                let mirrored_operator = match operator {
                    ComparisonOperator::LessThan => Some(ComparisonOperator::GreaterThan),
                    ComparisonOperator::LessEqual => Some(ComparisonOperator::GreaterEqual),
                    ComparisonOperator::GreaterThan => Some(ComparisonOperator::LessThan),
                    ComparisonOperator::GreaterEqual => Some(ComparisonOperator::LessEqual),
                    _ => None,
                };
                if let Some(operator) = mirrored_operator
                    && let Some(kernel) = mirrored_order_goal(goal)
                {
                    let mirrored = SyntaxProposition::Comparison {
                        left: right.clone(),
                        operator,
                        right: left.clone(),
                    };
                    if search_input
                        .facts()
                        .contains_discharged_implication_consequent(&kernel)
                        && let Some(extracted) = attempt::candidate_outcome(
                            Self::publish_selected_fact(search_input, &(mirrored)),
                        )?
                    {
                        if extracted.focused_discharged() {
                            return Ok(Some(extracted));
                        }
                        return Ok(attempt::candidate_outcome(
                            extracted.driver().apply_step(ProofStep::Known),
                        )?
                        .filter(Proof::focused_discharged));
                    }
                }
            }
            return crate::kernel::search::ProofSearch::try_discharged_consequent_conjunct_closure(
                search_input,
                goal,
                surface,
            );
        }
        Ok(attempt::candidate_outcome(Self::publish_selected_fact(
            search_input,
            &(surface.clone()),
        ))?
        .filter(Proof::focused_discharged))
    }

    /// A goal that is one conjunct of a discharged implication's
    /// consequent, `c` from `a` and `a implies (b and c)`: apply the
    /// implication to publish the whole consequent, spelled as the implication fact is written, and
    /// then the goal, now a proper conjunct of an available fact. The
    /// implication is selected by one probe of the conjunct index
    /// (`PureFactStore::discharged_implication_containing`); both steps are
    /// checked as written, and expansion prints them.
    pub(in crate::surface::proof) fn try_discharged_consequent_conjunct_closure(
        search_input: &Proof<'a>,
        goal: &Proposition,
        surface: &SyntaxProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_discharged_consequent_conjunct_closure");
        let Some((fact, whole)) = search_input.facts().discharged_implication_containing(goal)
        else {
            return Ok(None);
        };
        let Some(mut spelled) = search_input.spelled_goal_for_search(&fact) else {
            return Ok(None);
        };
        // A fact recorded at a state is spelled `at(selector, ...)`; its
        // consequent is read at the same state.
        let selector = match spelled {
            SyntaxProposition::At {
                selector,
                proposition,
            } => {
                spelled = *proposition;
                Some(selector)
            }
            _ => None,
        };
        let mut kernel = &fact;
        while let Proposition::Implies(_, consequent) = kernel {
            let SyntaxProposition::Implies(_, rest) = spelled else {
                return Ok(None);
            };
            spelled = *rest;
            kernel = consequent;
            if kernel == &whole {
                break;
            }
        }
        let spelled = match selector {
            Some(selector) => SyntaxProposition::At {
                selector,
                proposition: Box::new(spelled),
            },
            None => spelled,
        };
        let Some(extracted) =
            attempt::candidate_outcome(Self::publish_selected_fact(search_input, &(spelled)))?
        else {
            return Ok(None);
        };
        if extracted.is_complete() || extracted.focused_discharged() {
            return Ok(Some(extracted));
        }
        Ok(
            attempt::candidate_outcome(Self::publish_selected_fact(
                &extracted,
                &(surface.clone()),
            ))?
            .filter(Proof::focused_discharged),
        )
    }

    /// Weakening a guarded universal by dropping conjuncts of its conclusion:
    /// the goal `forall k { G implies A }` follows from an available
    /// `forall k { G implies A and B }` with the same binder and guards.
    /// The source is selected by one probe of the indexed conjunct
    /// projections (`PureFactStore::quantified_conjunct_projection_source`), so
    /// a universal goal no such fact concludes costs one lookup and no
    /// unrelated fact is visited. The proof is the explicit sequence
    /// `intro()` for the binder and each guard, `instantiate(F, k)` at the
    /// introduced binder, and `close()`; each step is checked as written
    /// and expansion prints it.
    pub(in crate::surface::proof) fn try_quantified_conjunct_projection_closure(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_quantified_conjunct_projection_closure");
        let Some(goal @ Proposition::ForAll { body, .. }) = search_input.goal() else {
            return Ok(None);
        };
        let Some(source) = search_input
            .facts()
            .quantified_conjunct_projection_source(goal)
        else {
            return Ok(None);
        };
        let binder = match search_input.surface_goal() {
            Some(SyntaxProposition::ForAll { name, .. }) => name.clone(),
            Some(SyntaxProposition::RangeAll { item, .. }) => item.clone(),
            _ => return Ok(None),
        };
        let source = source.clone();
        let mut guards = 0usize;
        let mut conclusion = body.as_ref();
        while let Proposition::Implies(_, consequent) = conclusion {
            guards += 1;
            conclusion = consequent;
        }
        let Some(quantified) = crate::kernel::search::ProofSearch::resolve_solve_premises(
            search_input,
            std::slice::from_ref(&source),
            &[],
        )
        .and_then(|pairs| pairs.into_iter().next())
        .map(|(_, surface)| surface) else {
            return Ok(None);
        };
        let mut scope = attempt::search_scope("quantified conjunct projection");
        let Some(introduced) =
            attempt::candidate_outcome(search_input.driver().apply_step(ProofStep::Intro))?
        else {
            return Ok(None);
        };
        let steps = std::iter::repeat_n(ProofStep::Intro, guards).chain([ProofStep::Instantiate {
            quantified,
            arguments: vec![SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                binder.into(),
            ))],
        }]);
        let mut proof = introduced.clone();
        let mut openings = Vec::new();
        for (index, step) in steps.enumerate() {
            let Some(next) = attempt::candidate_outcome(proof.driver().apply_step(step))? else {
                return Ok(None);
            };
            if index < guards {
                openings.push((proof, next.clone()));
            }
            proof = next;
        }
        if !proof.focused_discharged() {
            let Some(closed) =
                attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Known))?
            else {
                return Ok(None);
            };
            proof = closed;
        }
        if !proof.focused_discharged() {
            return Ok(None);
        }
        for (parent, opening) in openings.into_iter().rev() {
            proof = parent.finish_generated_intro(&opening, proof)?;
        }
        let proof = search_input.finish_generated_intro(&introduced, proof)?;
        scope.succeed();
        Ok(Some(proof))
    }

    /// Extends [`Self::try_direct_logical_closure`] through the goal's
    /// logical structure: a conjunction the direct candidates miss is split
    /// with the checked `both` operation and each conjunct is closed by this
    /// same closer, and `intro` may expose a conjunction to split. Only
    /// direct logical candidates close a leaf, so the search never selects
    /// premises, rewrites the goal, or instantiates ambient facts.
    ///
    /// Every move strictly removes one outer connective of the focused goal
    /// (`both` splits one conjunction, `intro` removes one binder), so the
    /// number of attempted candidates is linear in the goal's size. A miss
    /// anywhere declines the whole candidate and leaves `self` unchanged; a
    /// success is the explicit `both`/`intro`/direct-step sequence that
    /// expansion prints.
    pub(in crate::surface::proof) fn try_direct_structural_closure(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_direct_structural_closure");
        let mut scope = attempt::search_scope("direct structural closure");
        let result = crate::kernel::search::ProofSearch::try_direct_structural_closure_inner(
            search_input,
            &mut |_| Ok(None),
        )?;
        if result.is_some() {
            scope.succeed();
        }
        Ok(result)
    }

    /// A conjunction under implications or universals, every leaf of which
    /// the direct candidates close, is closed before any premise-selecting,
    /// rewriting, or instantiating strategy runs over the whole goal. Those
    /// strategies scale with the ambient facts rather than with the goal,
    /// and the implication closure that would eventually introduce the
    /// binders first searches for a refutation of each antecedent. A bare
    /// conjunction needs no such pass: it is split before those strategies
    /// run, and each conjunct is offered to the direct candidates first.
    pub(in crate::surface::proof) fn try_direct_structural_closure_under_binders(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_direct_structural_closure_under_binders");
        if !conjunction_under_binders(search_input.goal()) {
            return Ok(None);
        }
        crate::instrumentation::measure_operation(
            "surface",
            "solve closure",
            "solve closure: direct structural",
            || crate::kernel::search::ProofSearch::try_direct_structural_closure(search_input),
        )
    }

    /// [`Self::try_direct_structural_closure`] with one more closer at a
    /// universal node the direct candidates miss: `quantified` is offered
    /// the universal whole before `intro` descends into it. The walk is
    /// otherwise the same goal-sized descent, so the extra work is one
    /// `quantified` attempt per universal node of the goal.
    pub(in crate::surface::proof) fn try_direct_structural_closure_with_quantified(
        search_input: &Proof<'a>,
        quantified: &mut dyn FnMut(&Proof<'a>) -> Result<Option<Proof<'a>>, ClickError>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_direct_structural_closure_with_quantified");
        let mut scope = attempt::search_scope("direct structural closure");
        let result = crate::kernel::search::ProofSearch::try_direct_structural_closure_inner(
            search_input,
            quantified,
        )?;
        if result.is_some() {
            scope.succeed();
        }
        Ok(result)
    }

    pub(in crate::surface::proof) fn try_direct_structural_closure_inner(
        search_input: &Proof<'a>,
        quantified: &mut dyn FnMut(&Proof<'a>) -> Result<Option<Proof<'a>>, ClickError>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_direct_structural_closure_inner");
        crate::kernel::search::ProofSearch::try_direct_structural_closure_inner_impl(
            search_input,
            quantified,
        )
        .map_err(|error| search_input.attach_step_diagnostic(error))
    }

    pub(in crate::surface::proof) fn try_direct_structural_closure_inner_impl(
        search_input: &Proof<'a>,
        quantified: &mut dyn FnMut(&Proof<'a>) -> Result<Option<Proof<'a>>, ClickError>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_direct_structural_closure_inner_impl");
        check_verification_deadline()?;
        let mut budget = attempt::AttemptBudget::unbounded();
        if let Some(closed) = Self::try_direct_logical_leaf(search_input, &mut budget)? {
            return Ok(Some(closed));
        }
        if let Some(closed) =
            crate::kernel::search::ProofSearch::try_discharged_consequent_closure(search_input)?
        {
            return Ok(Some(closed));
        }
        if let Some(surfaces) = search_input.wide_conjunction_surfaces() {
            let mut proof = search_input.clone();
            for surface in surfaces {
                let scope = proof.driver().open_have(surface)?;
                let Some(closed) = (scope)
                    .driver()
                    .try_direct_structural_closure_with_quantified(quantified)?
                else {
                    return Ok(None);
                };
                proof = closed.join()?;
            }
            return attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Known));
        }
        if search_input.has_conjunctive_goal() {
            let Some((split_proof, split, ids)) =
                attempt::candidate_outcome(search_input.split_focused_both())?
            else {
                return Ok(None);
            };
            let marker = split_proof.conjunction_checkpoint(ids)?;
            let Some(left) =
                crate::kernel::search::ProofSearch::try_direct_structural_closure_inner(
                    &(split_proof.focus_branch(ids[0])?),
                    quantified,
                )?
            else {
                return Ok(None);
            };
            let Some(right) =
                crate::kernel::search::ProofSearch::try_direct_structural_closure_inner(
                    &(left.focus_branch(ids[1])?),
                    quantified,
                )?
            else {
                return Ok(None);
            };
            return attempt::candidate_outcome(right.join_focused_both(&marker, split, ids));
        }
        if matches!(search_input.goal(), Some(Proposition::ForAll { .. }))
            && let Some(closed) = quantified(search_input)?
        {
            return Ok(Some(closed));
        }
        if matches!(search_input.goal(), Some(Proposition::Implies(_, _))) {
            let mut frontier = search_input.clone();
            let mut openings = Vec::new();
            while matches!(frontier.goal(), Some(Proposition::Implies(_, _))) {
                let Some(introduced) =
                    attempt::candidate_outcome(frontier.driver().apply_step(ProofStep::Intro))?
                else {
                    return Ok(None);
                };
                openings.push((frontier, introduced.clone()));
                frontier = introduced;
            }
            let Some(mut closed) =
                Self::try_direct_structural_closure_inner(&frontier, quantified)?
            else {
                return Ok(None);
            };
            for (parent, introduced) in openings.into_iter().rev() {
                closed = parent.finish_generated_intro(&introduced, closed)?;
            }
            return Ok(Some(closed));
        }
        match attempt::candidate_outcome(search_input.driver().apply_step(ProofStep::Intro))? {
            Some(introduced) => {
                let closed =
                    crate::kernel::search::ProofSearch::try_direct_structural_closure_inner(
                        &introduced,
                        quantified,
                    )?;
                closed
                    .map(|closed| search_input.finish_generated_intro(&introduced, closed))
                    .transpose()
            }
            None => Ok(None),
        }
    }

    /// Searches the currently migrated `solve` vocabulary against this proof.
    ///
    /// Direct logical closers remain the cheap first choice. For a pure or
    /// fixed-state signed-order/equality derivation, the kernel-selected edge path
    /// is translated into a candidate made only of checked theorem
    /// applications, rewrites, and nested `have` scopes. The candidate
    /// advances this same `Proof`; no semantic result is produced before
    /// those proof steps have been accepted.
    pub(in crate::surface::proof) fn try_solve_closure(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_solve_closure");
        if crate::surface::proof::implicit_solve_scope::checked_only() {
            return Err(search_input.step_error(
                "checked-only verification forbids close(); write its proof steps explicitly",
            ));
        }
        // solve reaches the same failing frame question through several of
        // its strategies and candidates; one closure attempt answers each
        // exact failed question once (`with_closure_failure_memo`).
        crate::kernel::search::proposition_search::with_solve_atomic_reduction_cache(|| {
            crate::kernel::with_closure_failure_memo(|| {
                crate::kernel::search::ProofSearch::try_solve_closure_strategies(search_input)
            })
        })
        .map_err(|error| search_input.attach_step_diagnostic(error))
    }

    /// Close a mathematical `Integer` bound goal with selected-premise arithmetic behind
    /// `solve`: refute the goal's negation from the facts connected to it and
    /// apply the resulting certificate as one ordinary checked step. Any
    /// miss leaves the proof unchanged.
    /// `solve` on an arithmetic goal: `arithmetic` from premises it selects
    /// itself, the facts connected to the goal and the type ranges of the
    /// machine values they observe, then the same with a machine order or
    /// equality carried to `Integer`, an equality proved from its two
    /// bounds, and `defined(a + b)` proved from the bounds of the exact
    /// result. Each returns at once on a goal it does not apply to.
    /// A subgoal of the arithmetic below, such as one bound of an equality
    /// or the definedness of an operand: a direct logical closure, else
    /// the same arithmetic, else the rest of `solve` with no arithmetic of
    /// its own, so a subgoal does not open subgoals again.
    pub(in crate::surface::proof) fn try_arithmetic_fact_closure(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_arithmetic_fact_closure");
        if let Some(closed) =
            crate::kernel::search::ProofSearch::try_direct_logical_closure(search_input)?
        {
            return Ok(Some(closed));
        }
        if let Some(closed) =
            crate::kernel::search::ProofSearch::try_arithmetic_with_selected_premises(search_input)?
        {
            return Ok(Some(closed));
        }
        let Some(_scope) = SolveFallbackScope::enter(SolveFallback::ArithmeticSubgoal) else {
            return Ok(None);
        };
        crate::kernel::search::ProofSearch::try_solve_closure(search_input)
    }

    /// Arithmetic subgoals do not recursively select the same premises.
    /// Connected rewrites only retry arithmetic when the original comparison
    /// has a scalar match operand: selecting its arm exposes new arithmetic.
    pub(in crate::surface::proof) fn try_arithmetic_with_selected_premises(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_arithmetic_with_selected_premises");
        if (SolveFallbackScope::active(SolveFallback::ConnectedFacts)
            && !SolveFallbackScope::active(SolveFallback::MatchArithmetic))
            || SolveFallbackScope::active(SolveFallback::ArithmeticSubgoal)
        {
            return Ok(None);
        }
        if let Some(closed) =
            crate::kernel::search::ProofSearch::try_selected_arithmetic(search_input)?
        {
            return Ok(Some(closed));
        }
        if let Some(closed) =
            crate::kernel::search::ProofSearch::try_bridged_selected_arithmetic(search_input)?
        {
            return Ok(Some(closed));
        }
        if let Some(closed) =
            crate::kernel::search::ProofSearch::try_machine_goal_through_integer(search_input)?
        {
            return Ok(Some(closed));
        }
        if let Some(closed) =
            crate::kernel::search::ProofSearch::try_equality_by_bounds_early(search_input)?
        {
            return Ok(Some(closed));
        }
        if let Some(closed) =
            crate::kernel::search::ProofSearch::try_disequality_by_selected_refutation(
                search_input,
            )?
        {
            return Ok(Some(closed));
        }
        crate::kernel::search::ProofSearch::try_definedness_by_bounds(search_input)
    }

    /// The arithmetic `solve` tries last, once every other strategy has
    /// missed: a 64-bit equality through its `Integer` reading, whose type
    /// is known only after the reading is proved, and a native comparison
    /// through its `Integer` reading.
    pub(in crate::surface::proof) fn try_late_arithmetic_with_selected_premises(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_late_arithmetic_with_selected_premises");
        if (SolveFallbackScope::active(SolveFallback::ConnectedFacts)
            && !SolveFallbackScope::active(SolveFallback::MatchArithmetic))
            || SolveFallbackScope::active(SolveFallback::ArithmeticSubgoal)
        {
            return Ok(None);
        }
        if let Some(closed) =
            crate::kernel::search::ProofSearch::try_wide_equality_through_integer(search_input)?
        {
            return Ok(Some(closed));
        }
        crate::kernel::search::ProofSearch::try_native_goal_by_integer_reading(search_input)
    }

    /// A known different scalar value or a nonzero mathematical offset
    /// cannot satisfy this equality. Avoid spelling historical equalities
    /// and unfolding functions for that miss. An inconsistent context stays
    /// eligible for ordinary contradiction closure; this is not proof evidence.
    pub(in crate::surface::proof) fn scalar_offset_goal_is_refuted(
        search_input: &Proof<'a>,
    ) -> bool {
        #[cfg(test)]
        crate::kernel::search::record_discovery("scalar_offset_goal_is_refuted");
        let Some(Proposition::ConditionIs(condition, wanted)) = search_input.goal() else {
            return false;
        };
        let assumptions = search_input.facts().assumptions();
        if let OldConditionTerm::IntegerEqual(left, right) = condition.old_form() {
            if !*wanted {
                return false;
            }
            fn offset_base(
                term: &crate::kernel::SharedIntegerTerm,
            ) -> Option<&crate::kernel::SharedIntegerTerm> {
                use crate::kernel::IntegerTerm;
                match term.as_ref() {
                    IntegerTerm::Add(base, delta) | IntegerTerm::Subtract(base, delta) if matches!(delta.as_ref(), IntegerTerm::Constant(value) if !value.is_zero()) => {
                        Some(base)
                    }
                    IntegerTerm::Add(delta, base) if matches!(delta.as_ref(), IntegerTerm::Constant(value) if !value.is_zero()) => {
                        Some(base)
                    }
                    _ => None,
                }
            }
            let same_value =
                |left: &crate::kernel::SharedIntegerTerm,
                 right: &crate::kernel::SharedIntegerTerm| {
                    left == right
                        || search_input.facts().contains(&Proposition::condition_is(
                            OldConditionTerm::IntegerEqual(left.clone(), right.clone()),
                            true,
                        ))
                        || search_input.facts().contains(&Proposition::condition_is(
                            OldConditionTerm::IntegerEqual(right.clone(), left.clone()),
                            true,
                        ))
                };
            // Cancel ordinary Integer terms before asking about a single
            // remaining machine observation. A contract parameter pinned to
            // two cannot satisfy `to_integer(x) + 3 == to_integer(x) + to_integer(parameter)`.
            let affine_refuted = integer_affine_claim(
                search_input.goal().expect("an equality goal"),
            )
            .is_some_and(|claim| {
                if claim.terms.is_empty() {
                    return !claim.constant.is_zero();
                }
                let mut terms = claim.terms.iter();
                let Some((
                    crate::kernel::proof::integer_arithmetic::IntegerAffineAtom::Machine(machine),
                    coefficient,
                )) = terms.next()
                else {
                    return false;
                };
                if terms.next().is_some() || coefficient.abs() != BigInt::one() {
                    return false;
                }
                let required = -claim.constant / coefficient;
                let Some(constant) =
                    crate::kernel::machine_integer::range::constant_word(machine.ty(), &required)
                else {
                    return true;
                };
                assumptions.decide(&OldConditionTerm::machine_compare(
                    machine.ty(),
                    CompareRelation::Equal,
                    machine.value().clone(),
                    constant,
                )) == Some(false)
            });
            let refuted = affine_refuted
                || incompatible_machine_offsets(left, right)
                || offset_base(right).is_some_and(|base| same_value(left, base))
                || offset_base(left).is_some_and(|base| same_value(right, base));
            if !refuted {
                return false;
            }
            let _scope = crate::kernel::assumptions::PureFactContextIdScope::enter(assumptions);
            return !assumptions.is_inconsistent();
        }
        let (left, right) = match condition.old_form() {
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
            } => (left, right),
            _ => return false,
        };
        if *wanted
            && matches!(
                condition.old_form(),
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    relation: CompareRelation::Equal,
                    ..
                }
            )
        {
            // Adding or subtracting a nonzero word has no fixed point,
            // including at unsigned wraparound. A retained equality names
            // the same base without spelling unrelated historical premises.
            fn offset_base(term: &OldMachineTerm) -> Option<&OldMachineTerm> {
                match term {
                    binary_term!(Int32, Add, base, delta)
                    | binary_term!(Int32, Subtract, base, delta)
                        if matches!(delta.as_ref(), bits32_constant!(value) if constant_u32(*value) != 0) =>
                    {
                        Some(base)
                    }
                    _ => None,
                }
            }
            let same_value = |left: &OldMachineTerm, right: &OldMachineTerm| {
                left == right
                    || search_input.facts().contains(&Proposition::condition_is(
                        OldConditionTerm::Compare {
                            format: MachineIntegerType::Int32,
                            relation: CompareRelation::Equal,
                            left: Box::new(left.clone()),
                            right: Box::new(right.clone()),
                        },
                        true,
                    ))
                    || search_input.facts().contains(&Proposition::condition_is(
                        OldConditionTerm::Compare {
                            format: MachineIntegerType::Int32,
                            relation: CompareRelation::Equal,
                            left: Box::new(right.clone()),
                            right: Box::new(left.clone()),
                        },
                        true,
                    ))
            };
            if offset_base(right).is_some_and(|base| same_value(left, base))
                || offset_base(left).is_some_and(|base| same_value(right, base))
            {
                return !assumptions.is_inconsistent();
            }
        }
        false
    }

    pub(in crate::surface::proof) fn scalar_equality_goal_is_refuted(
        search_input: &Proof<'a>,
    ) -> bool {
        #[cfg(test)]
        crate::kernel::search::record_discovery("scalar_equality_goal_is_refuted");
        if crate::kernel::search::ProofSearch::scalar_offset_goal_is_refuted(search_input) {
            return true;
        }
        let Some(Proposition::ConditionIs(condition, wanted)) = search_input.goal() else {
            return false;
        };
        let (left, right) = match condition.old_form() {
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
            } => (left, right),
            _ => return false,
        };
        let assumptions = search_input.facts().assumptions();
        let literal =
            |term: &OldMachineTerm| matches!(term, bits32_constant!(_) | int64_constant!(_));
        // A closed comparison, which lowering retains, is false whatever the
        // facts: like the goal `false`, only a refutation of the context
        // proves it, which the strategies after this one search for.
        if !literal(left) && !literal(right)
            || crate::kernel::machine_integer::comparison::closed_condition_value(
                condition.operand_view(),
            )
            .is_some()
        {
            return false;
        }
        !assumptions.is_inconsistent()
            && assumptions
                .decide(condition.old_form())
                .is_some_and(|known| known != *wanted)
    }

    pub(in crate::surface::proof) fn try_selected_arithmetic(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_selected_arithmetic");
        // Generated loop and execution obligations may have no written goal.
        // Prove their Integer spelling in an ordinary have, then use that
        // established fact to close the original obligation. Native carrier
        // representations need not be alpha-identical to their source reading.
        if search_input.surface_goal().is_none()
            && let Some(goal) = search_input.goal()
            && integer_affine_claim(goal).is_some()
        {
            let reading = crate::kernel::machine_integer::comparison::integer_observations_of_native_comparison(goal)
                .into_iter()
                .next();
            let Some(surface) =
                search_input.spell_integer_comparison(reading.as_ref().unwrap_or(goal), &[])
            else {
                return Ok(None);
            };
            let Some(scope) = attempt::candidate_outcome(search_input.driver().open_have(surface))?
            else {
                return Ok(None);
            };
            if let Some(closed) =
                attempt::candidate_outcome(scope.driver().try_selected_arithmetic())?.flatten()
            {
                return attempt::candidate_outcome(
                    closed.join()?.driver().apply_step(ProofStep::Known),
                );
            }
            return Ok(None);
        }
        crate::kernel::search::ProofSearch::selected_arithmetic(search_input, true, &[])
    }

    /// Close a native comparison of exact observations, such as `a < 100`
    /// for an `int`, by proving its Integer reading `to_integer(a) < 100`
    /// with selected-premise arithmetic. The Integer fact files its native comparison, so
    /// the goal is then an available fact.
    pub(in crate::surface::proof) fn try_native_goal_by_integer_reading(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_native_goal_by_integer_reading");
        let (Some(goal), Some(surface_goal)) = (search_input.goal(), search_input.surface_goal())
        else {
            return Ok(None);
        };
        // A plain 32-bit equality reads as an Integer equality, which
        // simplex proves only from its two bounds; its Integer spelling would
        // be filed as the same native goal.
        if matches!(&goal, condition_source_0 @ Proposition::ConditionIs(
                _,
                true
            ) if matches!(condition_source_0.old_condition(), Some((OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    relation: CompareRelation::Equal,
                    ..
                }, _))))
        {
            return crate::kernel::search::ProofSearch::equality_by_bounds(search_input, true);
        }
        let readings =
            crate::kernel::machine_integer::comparison::integer_observations_of_native_comparison(
                goal,
            );
        if readings.is_empty() {
            return Ok(None);
        }
        let written = written_integer_observations(std::iter::once(surface_goal));
        for reading in readings {
            let Some(spelled) = search_input.spell_integer_comparison(&reading, &written) else {
                continue;
            };
            let Ok(scope) = search_input.driver().open_have(spelled) else {
                continue;
            };
            let Some(closed) = (scope).driver().try_selected_arithmetic()? else {
                continue;
            };
            let Ok(proof) = closed.join() else {
                continue;
            };
            if let Some(closed) =
                attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Known))?
            {
                return Ok(Some(closed));
            }
        }
        Ok(None)
    }

    /// An operation identity has a direct certificate from its ordinary
    /// domain. Try it in the written read names before exploring a stored-
    /// value comparison form, whose inner operations may have older names.
    pub(in crate::surface::proof) fn try_direct_operation_identity(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_direct_operation_identity");
        let (Some(goal), Some(surface)) = (search_input.goal(), search_input.surface_goal()) else {
            return Ok(None);
        };
        if !matches!(&goal, condition_source @ Proposition::ConditionIs(_, true)
            if matches!(condition_source.old_condition(), Some((OldConditionTerm::IntegerEqual(..), _))))
        {
            return Ok(None);
        }
        let direct = operation_identities(machine_observations(goal, &[]));
        let equivalent = |identity: &Proposition| {
            let (
                Some((OldConditionTerm::IntegerEqual(a, b), true)),
                Some((OldConditionTerm::IntegerEqual(c, d), true)),
            ) = (identity.old_condition(), goal.old_condition())
            else {
                return false;
            };
            let same = |left: &crate::kernel::SharedIntegerTerm,
                        right: &crate::kernel::SharedIntegerTerm| {
                left == right
                    || search_input
                        .facts()
                        .assumptions()
                        .decide(&OldConditionTerm::IntegerEqual(left.clone(), right.clone()))
                        == Some(true)
            };
            (same(a, c) && same(b, d)) || (same(a, d) && same(b, c))
        };
        if !direct.iter().any(|(_, _, identity)| equivalent(identity)) {
            return Ok(None);
        }
        let written = written_integer_observations(std::iter::once(surface));
        let identities = direct.iter().collect::<Vec<_>>();
        if let Ok((proof, _)) = crate::kernel::search::ProofSearch::prove_operation_identities(
            search_input,
            &identities,
            &written,
            None,
        )? {
            return attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Known));
        }
        Ok(None)
    }

    /// Refute the goal's negation from the connected facts, then from them
    /// and the type ranges of their machine observations, then, when
    /// `identities`, also from in-range machine `+` and `-` identities.
    ///
    /// `spelled` gives the source spelling of facts the caller just
    /// established, which a cited premise uses before its resolved one.
    pub(in crate::surface::proof) fn selected_arithmetic(
        search_input: &Proof<'a>,
        identities: bool,
        spelled: &[(Proposition, SyntaxProposition)],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("selected_arithmetic");
        let (Some(goal), Some(surface_goal)) = (search_input.goal(), search_input.surface_goal())
        else {
            return Ok(None);
        };
        // A native goal is refuted as its Integer reading, so the certificate
        // spells it observed: `r <= 5` as `to_integer(r) <= 5`.
        let observed_goal = observed_native_surface_comparison(goal, surface_goal);
        let surface_goal = &observed_goal;
        if identities
            && let Some(closed) =
                crate::kernel::search::ProofSearch::try_direct_operation_identity(search_input)?
        {
            return Ok(Some(closed));
        }
        if crate::kernel::proof::integer_arithmetic::integer_affine_claim(goal).is_none() {
            return Ok(None);
        }
        let Some(candidates) =
            crate::kernel::search::proposition_search::arithmetic_connected_premises(
                search_input.facts().assumptions(),
                goal,
            )
        else {
            return Ok(None);
        };
        check_verification_deadline()?;
        let plan = |premises: &[Proposition], ranges: &[crate::kernel::IntegerTerm]| {
            crate::instrumentation::measure_operation(
                "surface",
                "solve arithmetic",
                "solve arithmetic: integer refutation",
                || refute_integer_goal(goal, premises, ranges),
            )
        };
        // Native comparisons read as Integer comparisons, and machine type
        // ranges, are added only when the Integer facts alone leave a
        // counterexample, so a proof that needs neither keeps its
        // certificate.
        // A native candidate reads as an Integer fact, so the first plan may
        // cite one with no source spelling (a derived low-word bound); the
        // extended search below then drops it and plans again.
        // The planner reads a native comparison as an Integer one, but it
        // cites native facts only through their Integer readings,
        // which it spells by the native fact's own written operands; the
        // native candidates themselves stay out.
        let native = |premise: &Proposition| {
            !crate::kernel::machine_integer::comparison::integer_observations_of_native_comparison(
                premise,
            )
            .is_empty()
        };
        // The first plan reads only the native facts that observe a value
        // the goal does; the extended search below reads the rest.
        let generated_scalar_goal = !matches!(
            surface_comparison_with_anchored_operands(surface_goal),
            SyntaxProposition::Comparison { .. }
        );
        let goal_values =
            crate::kernel::proof::integer_arithmetic::integer_affine_machine_values(goal)
                .into_iter()
                .map(|value| value.id())
                .collect::<std::collections::HashSet<_>>();
        let observes_goal = |premise: &Proposition| {
            crate::kernel::proof::integer_arithmetic::integer_affine_machine_values(premise)
                .iter()
                .any(|value| goal_values.contains(&value.id()))
        };
        let near = candidates
            .iter()
            .filter(|premise| generated_scalar_goal || !native(premise) || observes_goal(premise))
            .cloned()
            .collect::<Vec<_>>();
        let mut integer_candidates = with_native_comparisons_as_integer(&near);
        integer_candidates.retain(|premise| !native(premise));

        let spellings = SpellingCache::default();
        // Prefer a direct composition before introducing a negated goal.
        // Refutation remains the fallback for strictness, ranges, and the
        // other rules outside the ordinary composition fragment.
        // Refutation proves only `<=` goals, so an Integer equality, such as
        // a 128-bit `a == b` from `a <= b` and `b <= a`, is composed directly
        // from its two bounds or not at all.
        let equality_goal = crate::kernel::proof::integer_arithmetic::integer_affine_claim(goal)
            .is_some_and(|claim| {
                claim.relation
                    == crate::kernel::proof::integer_arithmetic::IntegerAffineRelation::Equal
            });
        if (generated_scalar_goal
            || equality_goal
            || (goal_values.is_empty()
                && integer_composition::parts(goal).is_some()
                && candidates
                    .iter()
                    .all(|premise| integer_composition::parts(premise).is_some())))
            && let Some(direct) =
                plan_arithmetic(ArithmeticEngine::IntegerAffine, goal, &integer_candidates)
                    .and_then(ArithmeticPlan::integer_affine)
            && let Spelling::Spelled(pairs, _) = search_input.spell_refutation(
                &direct,
                &integer_candidates,
                &candidates,
                spelled,
                surface_goal,
                &spellings,
            )
            && let Some(proof) = attempt::candidate_outcome(Self::apply_integer_composition(
                search_input,
                &direct,
                &pairs,
                surface_goal,
                &[],
            ))?
            .flatten()
        {
            return Ok(Some(proof));
        }
        let first = match plan(&integer_candidates, &[]) {
            IntegerRefutation::Proved {
                certificate,
                premises,
            } => match search_input.spell_refutation(
                &certificate,
                &premises,
                &candidates,
                spelled,
                surface_goal,
                &spellings,
            ) {
                Spelling::Spelled(pairs, ranges) => Some((certificate, pairs, ranges)),
                Spelling::UnspelledReading(_) => None,
                _ => return Ok(None),
            },
            IntegerRefutation::Counterexample(_) => None,
            _ => return Ok(None),
        };
        let (certificate, pairs, ranges) = match first {
            Some(spelled) => spelled,
            None => {
                let mut extended = with_native_comparisons_as_integer(&candidates);
                extended.retain(|premise| !native(premise));
                let mut ranges = machine_observations(goal, &extended);
                // A reading or a range with no source spelling cannot be
                // cited; drop it and plan again, a bounded number of times.
                let mut attempts = 0;
                loop {
                    match plan(&extended, &ranges) {
                        IntegerRefutation::Proved {
                            certificate,
                            premises,
                        } if !ranges.is_empty() || extended.len() > integer_candidates.len() => {
                            let outcome = search_input.spell_refutation(
                                &certificate,
                                &premises,
                                &candidates,
                                spelled,
                                surface_goal,
                                &spellings,
                            );
                            match outcome {
                                Spelling::Spelled(pairs, spelled_ranges) => {
                                    break (certificate, pairs, spelled_ranges);
                                }
                                Spelling::UnspelledReading(reading) if attempts < 8 => {
                                    extended.retain(|premise| premise != &reading);
                                }
                                Spelling::UnspelledRange(value) if attempts < 8 => {
                                    ranges.retain(|range| range != &value);
                                }
                                Spelling::UnspelledBound => return Ok(None),
                                _ => return Ok(None),
                            }
                            attempts += 1;
                        }
                        IntegerRefutation::Counterexample(_) if identities => {
                            return crate::kernel::search::ProofSearch::try_operation_identity_closure(search_input,
                                goal,
                                surface_goal,
                                &extended,
                                &candidates,
                            );
                        }
                        _ => return Ok(None),
                    }
                }
            }
        };
        if let Some(closed) = attempt::candidate_outcome(Self::apply_integer_composition(
            search_input,
            &certificate,
            &pairs,
            surface_goal,
            &ranges,
        ))?
        .flatten()
        {
            return Ok(Some(closed));
        }
        Ok(None)
    }

    /// Close the goal with in-range machine `+` and `-` identities. A
    /// refutation that may assume `to_integer(a op b) == to_integer(a) op
    /// to_integer(b)` for the operations among the facts' and goal's
    /// machine observations selects the identities it needs. Each is then
    /// proved: its two type-range bounds by selected-premise arithmetic, the identity by
    /// `integer_operation_identity`, and the goal by selected-premise arithmetic from the
    /// facts and identities. An operand's identity is proved before its
    /// operation's, so the bounds of `a + b + c` read the established
    /// `to_integer(a + b) == to_integer(a) + to_integer(b)`.
    pub(in crate::surface::proof) fn try_operation_identity_closure(
        search_input: &Proof<'a>,
        goal: &Proposition,
        surface_goal: &SyntaxProposition,
        candidates: &[Proposition],
        written_facts: &[Proposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_operation_identity_closure");
        let mut identities = operation_identities(machine_observations(goal, candidates));
        // A refutation may cite an identity that nothing written spells, or
        // one whose spelling proves a different identity, such as the signed
        // reading of an unsigned narrowing's word, which spells as the
        // unsigned cast. That identity is dropped and the refutation planned
        // again, so each identity costs at most one more plan.
        loop {
            if identities.is_empty() {
                return Ok(None);
            }
            check_verification_deadline()?;
            let mut assumed = candidates.to_vec();
            assumed.extend(identities.iter().map(|(_, _, identity)| identity.clone()));
            let ranges = machine_observations(goal, &assumed);
            let IntegerRefutation::Proved { premises, .. } =
                crate::instrumentation::measure_operation(
                    "surface",
                    "solve arithmetic",
                    "solve arithmetic: integer refutation with operation identities",
                    || refute_integer_goal(goal, &assumed, &ranges),
                )
            else {
                return Ok(None);
            };
            let used: Vec<_> = identities
                .iter()
                .filter(|(_, _, identity)| premises.contains(identity))
                .collect();
            if used.is_empty() {
                return Ok(None);
            }
            // Spell each identity from the goal and the facts the refutation
            // cited.
            let mut surfaces = vec![surface_goal.clone()];
            for premise in &premises {
                if identities
                    .iter()
                    .any(|(_, _, identity)| identity == premise)
                {
                    continue;
                }
                // A native comparison read as an Integer one has no spelling
                // of its own; the goal and the other facts spell the
                // identities.
                if let Some((_, surface)) =
                    crate::kernel::search::ProofSearch::resolve_solve_premises(
                        search_input,
                        std::slice::from_ref(premise),
                        &[],
                    )
                    .and_then(|mut spelled| spelled.pop())
                {
                    surfaces.push(surface);
                }
            }
            let mut written = written_integer_observations(surfaces.iter());
            // An operand the cited facts do not spell, such as a capacity the
            // refutation bounds only through a native comparison, may still
            // be spelled by another connected fact as written, such as the
            // native `capacity == used + available` behind a cited Integer
            // reading. Look there only on a miss.
            let spells = |written: &[SyntaxTerm], (observed, value, _): &OperationIdentity| {
                let Some(operands) = identity_operands(value) else {
                    return false;
                };
                std::iter::once(observed).chain(operands).all(|term| {
                    search_input
                        .spell_integer_observation(term, written)
                        .is_some()
                })
            };
            if !used.iter().all(|identity| spells(&written, identity)) {
                for premise in written_facts.iter().take(MAX_SOLVER_SPELLING_FACTS) {
                    if let Some((_, surface)) =
                        crate::kernel::search::ProofSearch::resolve_solve_premises(
                            search_input,
                            std::slice::from_ref(premise),
                            &[],
                        )
                        .and_then(|mut spelled| spelled.pop())
                    {
                        surfaces.push(surface);
                    }
                }
                written = written_integer_observations(surfaces.iter());
            }
            if let Some(unspelled) = used.iter().find(|identity| !spells(&written, identity)) {
                let unspelled = unspelled.2.clone();
                identities.retain(|(_, _, identity)| identity != &unspelled);
                continue;
            }
            match crate::kernel::search::ProofSearch::prove_operation_identities(
                search_input,
                &used,
                &written,
                None,
            )? {
                Ok((proof, established)) => {
                    // A cited product whose bounds missed is left out; plan
                    // again without it, as for any identity that missed.
                    if let Some((_, _, skipped)) = used.iter().find(|(_, _, identity)| {
                        !established.iter().any(|(fact, _)| fact == identity)
                    }) {
                        let skipped = skipped.clone();
                        identities.retain(|(_, _, identity)| identity != &skipped);
                        continue;
                    }
                    return crate::kernel::search::ProofSearch::selected_arithmetic(
                        &(proof),
                        false,
                        &established,
                    );
                }
                Err(failed) => identities.retain(|(_, _, identity)| identity != &failed),
            }
        }
    }

    /// Prove each of `identities`, `to_integer(a op b) == to_integer(a) op
    /// to_integer(b)` or `to_integer((T)x) == to_integer(x)`, spelled from
    /// `written`: its two type-range bounds by selected-premise arithmetic, then the identity
    /// by `known` for written operators, retaining selected normalization for
    /// identities that require the read-over-write adapter. Each
    /// operand was found after its operation, so the reverse order proves
    /// the innermost identity first. Returns the proof with the identities
    /// established and their spellings, or the identity that missed.
    pub(in crate::surface::proof) fn prove_operation_identities(
        search_input: &Proof<'a>,
        identities: &[&OperationIdentity],
        written: &[SyntaxTerm],
        listed: Option<&[SyntaxProposition]>,
    ) -> Result<Result<(Proof<'a>, Vec<(Proposition, SyntaxProposition)>), Proposition>, ClickError>
    {
        #[cfg(test)]
        crate::kernel::search::record_discovery("prove_operation_identities");
        use crate::kernel::IntegerTerm;
        let mut proof = search_input.clone();
        let mut written = written.to_vec();
        // Keep the names supplied for observations, including narrow carriers.
        // Only newly introduced intermediate operations allocate an expression
        // from their operands; an existing source name retains its exact type.
        let mut sources = std::collections::HashMap::new();
        for source in &written {
            let probe = SyntaxProposition::Comparison {
                left: source.clone(),
                operator: ComparisonOperator::LessEqual,
                right: SyntaxTerm::IntegerLiteral("0".into()),
            };
            let Ok(lowered) =
                search_input.lower_integer_surface_proposition(&probe, "operation source")
            else {
                continue;
            };
            let mut readings = crate::kernel::machine_integer::comparison::integer_observations_of_native_comparison(&lowered);
            if readings.is_empty() {
                readings.push(lowered);
            }
            for reading in readings {
                if let Some((OldConditionTerm::IntegerLessEqual(value, _), true)) =
                    (reading).old_condition()
                {
                    sources
                        .entry(value.value_read().clone())
                        .or_insert_with(|| source.clone());
                }
            }
        }

        let mut established: Vec<(Proposition, SyntaxProposition)> = Vec::new();
        'identities: for (observed, value, failed) in identities.iter().rev().copied() {
            let IntegerTerm::Machine(machine) = observed else {
                return Ok(Err(failed.clone()));
            };
            // A product whose bounds miss is left out rather than failing the
            // others: before products were planned its identity was never
            // proved, and an identity over it still needs its own bounds.
            // A caller that cited it sees it missing from `established`.
            let product = matches!(value, IntegerTerm::Multiply(left, right)
                if left.as_const().is_none() && right.as_const().is_none());
            let before_product = proof.clone();
            let conversion =
                crate::kernel::machine_integer::conversion::integer_conversion(observed).is_some();
            let mut unsigned_sum = None;
            let (spelled_observed, spelled_value, signed_operation) = match value {
                // The conversion's operand as the observation itself writes
                // it, `E` of `to_integer(to_T(E))`: lowering is fact-stable,
                // so `E` lowers to the operand `z`, and the kernel checks it.
                _ if conversion => {
                    let Some(spelled_observed) =
                        search_input.spell_integer_observation(observed, &written)
                    else {
                        return Ok(Err(failed.clone()));
                    };
                    let SyntaxTerm::Call { name, arguments } = &spelled_observed else {
                        return Ok(Err(failed.clone()));
                    };
                    let [
                        SyntaxTerm::Call {
                            arguments: converted,
                            ..
                        },
                    ] = arguments.as_slice()
                    else {
                        return Ok(Err(failed.clone()));
                    };
                    let [operand] = converted.as_slice() else {
                        return Ok(Err(failed.clone()));
                    };
                    if name != "to_integer" {
                        return Ok(Err(failed.clone()));
                    }
                    (spelled_observed.clone(), operand.clone(), None)
                }
                IntegerTerm::Add(left, right)
                | IntegerTerm::Subtract(left, right)
                | IntegerTerm::Multiply(left, right) => {
                    let (Some(spelled_left), Some(spelled_right)) = (
                        search_input.spell_integer_observation(left, &written),
                        search_input.spell_integer_observation(right, &written),
                    ) else {
                        return Ok(Err(failed.clone()));
                    };
                    // Introduce each intermediate operation with a source expression
                    // built from its operands. A returned value may name only the
                    // outer operation; its inner operations still need explicit names.
                    let native = |source: &SyntaxTerm| SyntaxTerm::CUnary {
                        operand: Box::new(
                            integer_composition::observed_argument(source)
                                .unwrap_or_else(|| source.clone()),
                        ),
                        lowered: ProgramExpression::Cast {
                            expression: Box::new(ProgramExpression::Value(int32(0))),
                            target_type: machine.ty().program_type(),
                            integer_mode: crate::kernel::IntegerCastMode::CConversion,
                            pointee_struct: None,
                            pointee_struct_size: None,
                            pointee_volatile: false,
                            pointee_constant: false,
                            explicit_qualification: false,
                        },
                    };
                    if machine.ty() == MachineIntegerType::UInt64
                        && matches!(value, IntegerTerm::Add(..))
                    {
                        unsigned_sum = Some(vec![native(&spelled_left), native(&spelled_right)]);
                    }
                    let operation = match value {
                        IntegerTerm::Subtract(..) => SyntaxTerm::Subtract(
                            Box::new(native(&spelled_left)),
                            Box::new(native(&spelled_right)),
                        ),
                        IntegerTerm::Multiply(..) => SyntaxTerm::Multiply(
                            Box::new(native(&spelled_left)),
                            Box::new(native(&spelled_right)),
                        ),
                        _ => SyntaxTerm::Add(
                            Box::new(native(&spelled_left)),
                            Box::new(native(&spelled_right)),
                        ),
                    };
                    let operation = SyntaxTerm::Call {
                        name: "to_integer".into(),
                        arguments: vec![native(&operation)],
                    };
                    let observed = sources
                        .entry(observed.value_read().clone())
                        .or_insert_with(|| operation.clone())
                        .clone();
                    let signed_operation = (machine.ty() == MachineIntegerType::Int32
                        && matches!(value, IntegerTerm::Add(..) | IntegerTerm::Subtract(..))
                        && observed != operation)
                        .then_some(operation);
                    let (left, right) = (Box::new(spelled_left), Box::new(spelled_right));
                    let value = match value {
                        IntegerTerm::Subtract(..) => SyntaxTerm::Subtract(left, right),
                        IntegerTerm::Multiply(..) => SyntaxTerm::Multiply(left, right),
                        _ => SyntaxTerm::Add(left, right),
                    };
                    (observed, value, signed_operation)
                }
                IntegerTerm::Machine(_) => {
                    let Some(spelled) = search_input.spell_integer_observation(value, &written)
                    else {
                        return Ok(Err(failed.clone()));
                    };
                    let Some(observed) = search_input.spell_integer_observation(observed, &written)
                    else {
                        return Ok(Err(failed.clone()));
                    };
                    (observed, spelled, None)
                }
                _ => return Ok(Err(failed.clone())),
            };
            written.push(spelled_observed.clone());
            let identity = SyntaxProposition::Comparison {
                left: spelled_observed.clone(),
                operator: ComparisonOperator::Equal,
                right: spelled_value.clone(),
            };
            // The identity is checked at the format of the observation's
            // value reading (rule W).
            let (min, max) = match observed.value_read() {
                IntegerTerm::Machine(read) => read.ty().format().bounds(),
                _ => machine.ty().format().bounds(),
            };
            let (lower, upper) = (
                SyntaxProposition::Comparison {
                    left: surface_signed_integer_literal(&min),
                    operator: ComparisonOperator::LessEqual,
                    right: spelled_value.clone(),
                },
                SyntaxProposition::Comparison {
                    left: spelled_value.clone(),
                    operator: ComparisonOperator::LessEqual,
                    right: surface_signed_integer_literal(&max),
                },
            );
            // For a narrowing of a previously proved machine sum, cite
            // that exact identity before composing the operand ranges.
            let sum_identity = if matches!(value, IntegerTerm::Machine(_)) {
                established
                    .iter()
                    .find_map(|(kernel, surface)| match kernel.old_condition() {
                        Some((OldConditionTerm::IntegerEqual(observed, exact), true))
                            if observed.as_ref() == value
                                && matches!(exact.as_ref(), IntegerTerm::Add(..)) =>
                        {
                            Some(surface.clone())
                        }
                        _ => None,
                    })
            } else {
                None
            };
            for bound in [&lower, &upper] {
                let scope = proof.driver().open_have(bound.clone())?;
                let intrinsic = if let Some(identity) = &sum_identity {
                    attempt::candidate_outcome((|| {
                        let rewritten = scope
                            .driver()
                            .apply_step(ProofStep::Rewrite(identity.clone()))?;
                        if rewritten.is_complete() {
                            return Ok(Some(rewritten));
                        }
                        rewritten.driver().try_intrinsic_sum_bound()
                    })())?
                    .flatten()
                } else {
                    None
                };
                let closed = if intrinsic.is_some() {
                    intrinsic
                } else if let Some(listed) = listed {
                    let mut premises = listed.to_vec();
                    premises.extend(established.iter().map(|(_, surface)| surface.clone()));
                    scope
                        .driver()
                        .apply_step(ProofStep::ArithmeticUsing(premises))
                        .ok()
                } else if let Some(closed) = (scope).driver().try_direct_logical_closure()? {
                    // A complete arithmetic domain already contains these
                    // ordinary bounds. Use the available fact before a
                    // refutation search, which excludes the exact goal.
                    Some(closed)
                } else {
                    scope
                        .driver()
                        .try_selected_arithmetic_without_identities()?
                };
                let closed = match closed {
                    Some(closed) => Some(closed.join()?),
                    None if product => {
                        let IntegerTerm::Multiply(left, right) = value else {
                            unreachable!("a product identity's value is a product")
                        };
                        let SyntaxTerm::Multiply(spelled_left, spelled_right) = &spelled_value
                        else {
                            unreachable!("a product is spelled as one")
                        };
                        let (target, lower) = if std::ptr::eq(bound, &lower) {
                            (&min, true)
                        } else {
                            (&max, false)
                        };
                        crate::kernel::search::ProofSearch::prove_product_bound_from_ranges(
                            &proof,
                            [(left, spelled_left), (right, spelled_right)],
                            bound,
                            target,
                            lower,
                        )?
                    }
                    None => None,
                };
                let Some(closed) = closed else {
                    if product {
                        proof = before_product;
                        continue 'identities;
                    }
                    return Ok(Err(failed.clone()));
                };
                proof = closed;
                established.extend(
                    proof
                        .added_facts()
                        .iter()
                        .map(|fact| (fact.clone(), bound.clone())),
                );
            }
            // The observation identity consumes only the exact outer range,
            // which is `defined(native-expression)` over total operands.
            // Native theorem arguments establish their operands' domains where
            // they are actually applied.
            if !conversion
                && let Some(expression) = integer_composition::observed_argument(&spelled_observed)
            {
                let domain = SyntaxProposition::Defined { expression };
                // Over total operands this is precisely the range pair. Keep
                // its native spelling available to subsequent theorem arguments.
                // An operand that is itself an operation or a read owes its own
                // domain, which is established only when an argument requires it.
                if !integer_composition::domain_has_compound_operand(&domain)
                    && proof
                        .lower_cited_surface_proposition(&domain, "native argument domain")
                        .is_ok_and(|kernel| {
                            crate::kernel::machine_integer::definedness::range_domain_query(&kernel)
                                .is_some()
                        })
                {
                    let scope = proof.driver().open_have(domain)?;
                    proof = scope.driver().apply_step(ProofStep::Known)?.join()?;
                }
            }
            let identity_surface = identity.clone();
            let scope = proof.driver().open_have(identity.clone())?;
            // Prove the operation observation from the established range.
            // A retained read of the stored result can then use the checked
            // fact through its read-over-write comparison form.
            let closed = if let Some(closed) =
                attempt::candidate_outcome(scope.driver().apply_step(ProofStep::Known))?
            {
                closed
            } else if let Some(closed) = attempt::candidate_outcome((|| {
                let step = if let Some(arguments) = unsigned_sum {
                    ProofStep::ApplyPlannedTheorem {
                        application: TheoremApplication {
                            name: "click::integer::uint64_add_to_integer".into(),
                            arguments,
                        },
                        premises: vec![upper.clone()],
                    }
                } else if let Some(operation) = signed_operation
                    && scope
                        .body()
                        .goal()
                        .and_then(crate::kernel::comparison_form)
                        .is_some()
                {
                    let operation = SyntaxProposition::Comparison {
                        left: operation,
                        operator: ComparisonOperator::Equal,
                        right: spelled_value,
                    };
                    super::super::wide_arithmetic::have(operation, vec![ProofStep::Known])
                } else {
                    return Ok(None);
                };
                let applied = scope.driver().apply_step(step)?;
                if applied.is_complete() {
                    return Ok(Some(applied));
                }
                applied.driver().apply_step(ProofStep::Known).map(Some)
            })())?
            .flatten()
                && closed.is_complete()
            {
                closed
            } else {
                return Ok(Err(failed.clone()));
            };
            proof = closed.join()?;
            established.extend(
                proof
                    .added_facts()
                    .iter()
                    .map(|fact| (fact.clone(), identity_surface.clone())),
            );
        }
        Ok(Ok((proof, established)))
    }

    /// A bound `target <= a * b` (`lower`) or `a * b <= target` on a product
    /// of two machine observations, from the operands' type ranges:
    /// each operand's two range bounds as a `have`, then the product bound
    /// by explicit library application using those four premises,
    /// the shape `click expand` writes. The four corner products of the
    /// ranges are compared with `target` first, so a range that cannot give
    /// the bound costs no step. Reads no fact and no other premise: the work
    /// is the two operands' formats and four constant products.
    pub(in crate::surface::proof) fn prove_product_bound_from_ranges(
        search_input: &Proof<'a>,
        operands: [(&crate::kernel::SharedIntegerTerm, &SyntaxTerm); 2],
        bound: &SyntaxProposition,
        target: &num_bigint::BigInt,
        lower: bool,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("prove_product_bound_from_ranges");
        use crate::kernel::IntegerTerm;
        let mut ranges = Vec::with_capacity(2);
        for (operand, _) in &operands {
            let IntegerTerm::Machine(read) = operand.value_read() else {
                return Ok(None);
            };
            ranges.push(read.ty().format().bounds());
        }
        let follows = [&ranges[0].0, &ranges[0].1].into_iter().all(|left| {
            [&ranges[1].0, &ranges[1].1].into_iter().all(|right| {
                let corner = left * right;
                if lower {
                    target <= &corner
                } else {
                    &corner <= target
                }
            })
        });
        if !follows {
            return Ok(None);
        }
        let mut proof = search_input.clone();
        let mut premises = Vec::with_capacity(4);
        for ((_, spelled), (min, max)) in operands.iter().zip(&ranges) {
            for range_bound in [
                SyntaxProposition::Comparison {
                    left: surface_signed_integer_literal(min),
                    operator: ComparisonOperator::LessEqual,
                    right: (**spelled).clone(),
                },
                SyntaxProposition::Comparison {
                    left: (**spelled).clone(),
                    operator: ComparisonOperator::LessEqual,
                    right: surface_signed_integer_literal(max),
                },
            ] {
                let scope = proof.driver().open_have(range_bound.clone())?;
                let closed = match scope.driver().try_direct_logical_closure()? {
                    Some(closed) => Some(closed),
                    None => scope
                        .driver()
                        .try_selected_arithmetic_without_identities()?,
                };
                let Some(closed) = closed else {
                    return Ok(None);
                };
                proof = closed.join()?;
                premises.push(range_bound);
            }
        }
        let scope = proof.driver().open_have(bound.clone())?;
        let closed = scope.driver().try_product_bound_using(&premises)?;
        let Some(closed) = closed else {
            return Ok(None);
        };
        Ok(Some(closed.join()?))
    }

    /// Establish the in-range machine `+` and `-` identities of the
    /// operations this goal observes, and those of their operands, before
    /// an equality is split into its two bounds, so both bounds read them
    /// rather than each proving them inside its own `have`. Only the goal's
    /// own spelling is read; an identity it cannot spell, or a bound the
    /// arithmetic misses, leaves the proof unchanged.
    pub(in crate::surface::proof) fn with_goal_operation_identities(
        search_input: &Proof<'a>,
        surface_goal: &SyntaxProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("with_goal_operation_identities");
        let Some(goal) = search_input.goal() else {
            return Ok(None);
        };
        let identities = operation_identities(machine_observations(goal, &[]))
            .into_iter()
            .filter(|(_, _, identity)| !search_input.facts().contains(identity))
            .collect::<Vec<_>>();
        if identities.is_empty() {
            return Ok(None);
        }
        check_verification_deadline()?;
        let written = written_integer_observations(std::iter::once(surface_goal));
        let identities = identities.iter().collect::<Vec<_>>();
        Ok(
            crate::kernel::search::ProofSearch::prove_operation_identities(
                search_input,
                &identities,
                &written,
                None,
            )?
            .ok()
            .map(|(proof, _)| proof),
        )
    }

    pub(in crate::surface::proof) fn try_flat_solve_conjunction(
        search_input: &Proof<'a>,
        introduced_surfaces: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_flat_solve_conjunction");
        let Some(surfaces) = search_input.wide_conjunction_surfaces() else {
            return Ok(None);
        };
        let mut proof = search_input.clone();
        for surface in surfaces {
            let scope = proof.driver().open_have(surface)?;
            let Some(closed) = (scope)
                .driver()
                .try_solve_closure_with_surfaces(introduced_surfaces)?
            else {
                return Ok(None);
            };
            proof = closed.join()?;
        }
        attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Known))
    }

    /// Try the explicit zero witness for a machine-integer existential.
    /// The recursive solve sees its instantiated body, not the existential.
    pub(in crate::surface::proof) fn try_zero_witness_closure(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_zero_witness_closure");
        let Some(SyntaxProposition::Exists {
            click_type: ClickType::Program(crate::languages::interface::InterfaceType::Int32),
            ..
        }) = search_input.surface_goal()
        else {
            return Ok(None);
        };
        let Some(witnessed) = attempt::candidate_outcome(search_input.driver().apply_step(
            ProofStep::Witness(ProofWitness::single(SyntaxTerm::ProgramExpression(
                ProgramExpression::Value(ProgramValue::Int32(OldMachineTerm::constant(0))),
            ))),
        ))?
        else {
            return Ok(None);
        };
        crate::kernel::search::ProofSearch::try_solve_closure(&witnessed)
    }

    /// Reuse a witness from a function-entry existential, then preserve its
    /// leaves through the effect-free prefix. This is an ordinary solve
    /// strategy; it receives no call-site obligation or private premise list.
    pub(in crate::surface::proof) fn try_entry_existential_closure(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_entry_existential_closure");
        if !matches!(
            search_input.surface_goal(),
            Some(SyntaxProposition::Exists { .. })
        ) {
            return Ok(None);
        }
        let ProofContext::Execution(context) = search_input.context.as_ref() else {
            return Ok(None);
        };
        let Some(execution) = search_input.execution() else {
            return Ok(None);
        };
        if !execution.core.effect_facts.is_empty() {
            return Ok(None);
        }
        let Some(owner) = &context.constants.caller_source_owner else {
            return Ok(None);
        };
        for outer_ordinal in 0..context.function_block.requires().len() {
            check_verification_deadline()?;
            let source_id = RequirementSourceId {
                owner: owner.clone(),
                outer_ordinal,
            };
            let Some(selection) = context
                .constants
                .caller_requirement_index
                .lookup_source_requirement(&source_id)
            else {
                continue;
            };
            let SyntaxProposition::PredicateCall { .. } = &selection.source_proposition else {
                continue;
            };
            let Some(proof) = attempt::candidate_outcome(search_input.driver().apply_step(
                ProofStep::UnfoldProposition(SyntaxProposition::At {
                    selector: ProgramPointSelector::ProgramPoint(ProgramPointRef {
                        region: CodeRegionRef::Function,
                        kind: ProgramPointKind::Entry,
                    }),
                    proposition: Box::new(selection.source_proposition.clone()),
                }),
            ))?
            else {
                continue;
            };
            if let Some(closed) =
                crate::kernel::search::ProofSearch::try_selected_entry_existential_closure(
                    &proof, &selection,
                )?
            {
                return Ok(Some(closed));
            }
        }
        Ok(None)
    }

    pub(in crate::surface::proof) fn try_selected_entry_existential_closure(
        search_input: &Proof<'a>,
        selection: &CallerRequirementSelection,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_selected_entry_existential_closure");
        let ProofContext::Execution(context) = search_input.context.as_ref() else {
            return Ok(None);
        };
        let unfolded = unfold_surface_predicates(
            context.spec_definitions.predicates,
            &selection.source_proposition,
            &[match &selection.source_proposition {
                SyntaxProposition::PredicateCall { name, .. } => name,
                _ => return Ok(None),
            }
            .to_string()],
        )
        .map_err(|message| search_input.step_error(message))?;
        let SyntaxProposition::Exists {
            click_type,
            name: source_name,
            body,
            ..
        } = unfolded
        else {
            return Ok(None);
        };
        let source_name = source_name.written().unwrap_or("value");
        let candidate_names =
            std::iter::once(source_name.to_owned()).chain((0..4096).map(|suffix| {
                format!(
                    "{}_witness_{}_{suffix}",
                    source_name, selection.source_id.outer_ordinal
                )
            }));
        let Some(choice_name) = candidate_names.into_iter().find(|candidate| {
            search_input.local_binding(candidate).is_none()
                && !context
                    .parsed_function
                    .parameters()
                    .iter()
                    .any(|parameter| parameter.name() == candidate)
                && search_input
                    .execution()
                    .is_none_or(|execution| !execution.core.state.locals().contains_name(candidate))
        }) else {
            return Ok(None);
        };
        let replacement = match &click_type {
            ClickType::Proposition | ClickType::Function { .. } | ClickType::Resource => {
                return Ok(None);
            }
            ClickType::Integer | ClickType::Algebraic(_) => {
                SyntaxTerm::Binding(choice_name.clone())
            }
            ClickType::Program(_) | ClickType::CObjectPointer { .. } => {
                SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                    (choice_name.clone()).into(),
                ))
            }
            ClickType::Parameter(_) => return Ok(None),
        };
        let body =
            substitute_click_proposition(&body, &BTreeMap::from([(source_name, replacement)]))
                .map_err(|message| search_input.step_error(message))?;
        let source = SyntaxProposition::At {
            selector: ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Function,
                kind: ProgramPointKind::Entry,
            }),
            proposition: Box::new(SyntaxProposition::Exists {
                click_type: click_type.clone(),
                name: choice_name.clone().into(),
                written_name: None,
                body: Box::new(body),
            }),
        };
        let Some(chosen) = attempt::candidate_outcome(search_input.driver().apply_step(
            ProofStep::LetSatisfy(ProofLetSatisfy {
                bindings: vec![(choice_name.clone(), Some(click_type))],
                proposition: source,
            }),
        ))?
        else {
            return Ok(None);
        };
        let Some(projection) = chosen
            .execution()
            .and_then(|execution| execution.presentation.existential_projection.as_ref())
        else {
            return Ok(None);
        };
        if chosen.focused_discharged() {
            return Ok(Some(chosen));
        }
        let source_leaves = projection
            .leaves
            .iter()
            .map(|leaf| leaf.surface.clone())
            .collect::<Vec<_>>();
        let Some(SyntaxProposition::Exists { .. }) = chosen.surface_goal() else {
            return Ok(None);
        };
        let Some(witnessed) = attempt::candidate_outcome(chosen.driver().apply_step(
            ProofStep::Witness(ProofWitness::single(SyntaxTerm::ProgramExpression(
                ProgramExpression::Variable((choice_name).into()),
            ))),
        ))?
        else {
            return Ok(None);
        };
        let mut proof = witnessed;
        for source in &source_leaves {
            // At the entry state the leaves already close the goal.
            if proof.focused_discharged() {
                return Ok(Some(proof));
            }
            let Some(extracted) =
                attempt::candidate_outcome(Self::publish_selected_fact(&proof, &(source.clone())))?
            else {
                return Ok(None);
            };
            proof = extracted;
        }
        if proof.focused_discharged() {
            return Ok(Some(proof));
        }
        // The leaves hold at function entry. Establish the conjuncts that
        // still need a proof at this frontier before closing the whole goal.
        let Some(goal) = proof.surface_goal().cloned() else {
            return Ok(None);
        };
        let mut conjuncts = Vec::new();
        let mut pending = vec![goal];
        while let Some(proposition) = pending.pop() {
            match proposition {
                SyntaxProposition::And(left, right) => {
                    pending.push(*right);
                    pending.push(*left);
                }
                conjunct => conjuncts.push(conjunct),
            }
        }
        for conjunct in conjuncts {
            check_verification_deadline()?;
            let Ok(lowered) =
                proof.lower_surface_proposition(&conjunct, "caller requirement conjunct")
            else {
                return Ok(None);
            };
            if proof.facts().pure_known_available(&lowered) {
                continue;
            }
            let Some(carried) =
                crate::kernel::search::ProofSearch::try_carry_entry_conjunct(&(proof), &conjunct)?
            else {
                return Ok(None);
            };
            proof = carried;
        }
        crate::kernel::search::ProofSearch::try_solve_closure_with_surfaces(
            &(proof),
            &source_leaves,
        )
    }

    /// Reuse an entry conjunct with ordinary facts and footprint preservation.
    /// Specialize a guarded universal before proving its conclusion.
    pub(in crate::surface::proof) fn try_carry_entry_conjunct(
        search_input: &Proof<'a>,
        conjunct: &SyntaxProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_carry_entry_conjunct");
        let entry = |proposition: &SyntaxProposition| SyntaxProposition::At {
            selector: ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Function,
                kind: ProgramPointKind::Entry,
            }),
            proposition: Box::new(proposition.clone()),
        };
        let Some(mut scope) =
            attempt::candidate_outcome(search_input.driver().open_have(conjunct.clone()))?
        else {
            return Ok(None);
        };
        let mut openings = Vec::new();
        let conclusion = if let SyntaxProposition::ForAll { name, body, .. } = conjunct {
            let SyntaxProposition::Implies(_, consequent) = body.as_ref() else {
                return Ok(None);
            };
            for step in [
                ProofStep::IntroBinder(name.clone()),
                ProofStep::Intro,
                ProofStep::Instantiate {
                    quantified: entry(conjunct),
                    arguments: vec![SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                        (name.clone()).into(),
                    ))],
                },
            ] {
                let introduces = matches!(&step, ProofStep::Intro | ProofStep::IntroBinder(_));
                let Some(next) = attempt::candidate_outcome(scope.driver().apply_step(step))?
                else {
                    return Ok(None);
                };
                if introduces {
                    openings.push((scope.body().clone(), next.body().clone()));
                }
                scope = next;
            }
            consequent.as_ref()
        } else {
            conjunct
        };
        if !scope.is_complete() {
            if let Some(closed) =
                attempt::candidate_outcome(scope.driver().apply_step(ProofStep::Known))?
            {
                scope = closed;
            } else if let Some(closed) = scope
                .driver()
                .try_preserve_selected_fact(conclusion, entry(conclusion))?
            {
                scope = closed;
            } else {
                return Ok(None);
            }
        }
        for (parent, introduced) in openings.into_iter().rev() {
            scope = scope.finish_generated_intro(&parent, &introduced)?;
        }
        attempt::candidate_outcome(scope.join())
    }

    pub(in crate::surface::proof) fn try_preserve_selected_fact(
        body: &Proof<'a>,
        conclusion: &SyntaxProposition,
        source: SyntaxProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_preserve_selected_fact");
        if let Some(goal @ Proposition::MemoryLoadable { .. }) = body.goal() {
            let Some(kernel) = attempt::candidate_outcome(
                body.lower_cited_surface_proposition(&source, "preserved source fact"),
            )?
            else {
                return Ok(None);
            };
            return Ok(Self::try_local_viewability_preservation(
                body,
                goal,
                &[(kernel, source)],
            ));
        }
        if let Some(proof) = Self::try_indexed_read_preservation(
            body,
            conclusion,
            MAX_TRANSPORT_SOURCE_POINTS,
            true,
        )? {
            return Ok(Some(proof));
        }
        Self::try_store_read_rewrite(body, conclusion)
    }

    pub(in crate::surface::proof) fn try_solve_closure_strategies(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_solve_closure_strategies");
        let mut scope = attempt::search_scope("solve closure");
        // Prefer the whole `known` closure, including computation, before
        // decomposing the goal or searching for another derivation.
        if let Some(proof) =
            attempt::candidate_outcome(search_input.driver().apply_step(ProofStep::Known))?
        {
            scope.succeed();
            return Ok(Some(proof));
        }
        if let Some(proof) = Self::try_struct_field_equalities(search_input)? {
            scope.succeed();
            return Ok(Some(proof));
        }
        if let Some(proof) = attempt::candidate_outcome(
            Self::try_bounded_observation_identity_closure(search_input),
        )?
        .flatten()
        {
            scope.succeed();
            return Ok(Some(proof));
        }
        if let Some(proof) = Self::try_pointer_translation_closure(search_input)? {
            scope.succeed();
            return Ok(Some(proof));
        }
        if let Some(goal) = search_input.surface_goal() {
            for premises in quotient_shifts::guard_candidates(goal) {
                if let Some(proof) = Self::try_quotient_shift_using(search_input, &premises)? {
                    scope.succeed();
                    return Ok(Some(proof));
                }
            }
        }
        if let Some(proof) = Self::try_integer_algebra(search_input)? {
            scope.succeed();
            return Ok(Some(proof));
        }
        if let Some(proof) = super::super::program_termination::try_closure(search_input)? {
            scope.succeed();
            return Ok(Some(proof));
        }
        if let Some(proof) = Self::try_bounded_arithmetic_closure(search_input, &[])? {
            scope.succeed();
            return Ok(Some(proof));
        }
        if let Some(proof) =
            crate::kernel::search::ProofSearch::try_flat_solve_conjunction(search_input, &[])?
        {
            scope.succeed();
            return Ok(Some(proof));
        }
        if let Some(proof) =
            crate::kernel::search::ProofSearch::try_direct_logical_closure(search_input)?
        {
            scope.succeed();
            return Ok(Some(proof));
        }
        if let Some(proof) =
            crate::kernel::search::ProofSearch::try_zero_witness_closure(search_input)?
        {
            scope.succeed();
            return Ok(Some(proof));
        }
        if let Some(proof) =
            crate::kernel::search::ProofSearch::try_entry_existential_closure(search_input)?
        {
            scope.succeed();
            return Ok(Some(proof));
        }
        if crate::kernel::search::ProofSearch::scalar_equality_goal_is_refuted(search_input) {
            // The facts decide the goal false, so only an undetected
            // contradiction proves it; a rewrite chain may expose one.
            let result =
                crate::kernel::search::ProofSearch::try_connected_fact_closure(search_input)?;
            if result.is_some() {
                scope.succeed();
            }
            return Ok(result);
        }
        if let Some(proof) =
            crate::kernel::search::ProofSearch::try_direct_structural_closure_under_binders(
                search_input,
            )?
        {
            scope.succeed();
            return Ok(Some(proof));
        }
        if matches!(search_input.context.as_ref(), ProofContext::Pure(_))
            && let Some(surface) = search_input.surface_goal()
            && let Ok(proof) = Self::publish_selected_fact(search_input, &(surface.clone()))
            && proof.focused_discharged()
        {
            scope.succeed();
            return Ok(Some(proof));
        }
        if let Some(execution) = search_input.execution()
            && let Some(anchor) = frontier_premise_anchor(execution)
            && let Some(surface_goal) = search_input.surface_goal()
            && let Ok(source) =
                surface_at_program_point(surface_goal, &ProgramPointSelector::ProgramPoint(anchor))
            && let Ok(proof) = Self::publish_selected_fact(search_input, &(source))
            && proof.is_complete()
        {
            scope.succeed();
            return Ok(Some(proof));
        }
        if let Some(proof) =
            crate::kernel::search::ProofSearch::try_direct_operation_identity(search_input)?
        {
            scope.succeed();
            return Ok(Some(proof));
        }
        let result = match crate::kernel::search::ProofSearch::try_solve_closure_after_direct(search_input, false)? {
            Some(proof) => Some(proof),
            None => match crate::kernel::search::ProofSearch::try_restated_constant_upper_bound(search_input)? {
                Some(proof) => Some(proof),
                None => match crate::kernel::search::ProofSearch::try_connected_fact_closure(search_input)? {
                    Some(proof) => Some(proof),
                    None => match crate::kernel::search::ProofSearch::try_late_arithmetic_with_selected_premises(search_input)? {
                        Some(proof) => Some(proof),
                        None => match crate::kernel::search::ProofSearch::try_disequality_by_refuted_equality(search_input)? {
                            Some(proof) => Some(proof),
                            None => crate::kernel::search::ProofSearch::try_element_address_disequality(search_input)?,
                        },
                    },
                },
            },
        };
        if result.is_some() {
            scope.succeed();
        }
        Ok(result)
    }

    /// Proves a disequality `a != b` from an available disequality `p != q`
    /// that `a == b` contradicts, such as the `int32` word fact
    /// `((m - 1) as int32) != 0` from the Integer fact `m - 1 != 0` where the
    /// facts keep `m - 1` in range, or the converse. Arithmetic reads no
    /// disequality premise, so the proof is by cases on `a == b`: that arm
    /// states `p == q`, which `solve` proves from `a == b`, and `known`
    /// closes it on the contradictory pair; the other arm holds the goal. The
    /// certificate is an ordinary proof `if`.
    ///
    /// It runs only after every other strategy has missed, on a disequality
    /// goal, over at most [`MAX_REFUTED_EQUALITY_PREMISES`] disequalities
    /// connected to the goal. The goals it states are equalities, and the
    /// strategy does not nest inside itself.
    pub(in crate::surface::proof) fn try_disequality_by_refuted_equality(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_disequality_by_refuted_equality");
        /// The equality a kernel disequality denies.
        fn denied(proposition: &Proposition) -> Option<Proposition> {
            match proposition {
                condition_source_0 @ Proposition::ConditionIs(_, true)
                    if let Some((OldConditionTerm::IntegerNotEqual(left, right), _)) =
                        condition_source_0.old_condition() =>
                {
                    Some(Proposition::condition_is(
                        OldConditionTerm::IntegerEqual(left.clone(), right.clone()),
                        true,
                    ))
                }
                condition_source_0 @ Proposition::ConditionIs(_, false)
                    if let Some((
                        condition @ (OldConditionTerm::IntegerEqual(..)
                        | OldConditionTerm::Compare {
                            relation: CompareRelation::Equal,
                            ..
                        }),
                        _,
                    )) = condition_source_0.old_condition() =>
                {
                    Some(Proposition::condition_is(condition.clone(), true))
                }
                _ => None,
            }
        }
        /// The equality a written disequality denies, under its state.
        fn denied_surface(surface: &SyntaxProposition) -> Option<SyntaxProposition> {
            match surface {
                SyntaxProposition::At {
                    selector,
                    proposition,
                } => Some(SyntaxProposition::At {
                    selector: selector.clone(),
                    proposition: Box::new(denied_surface(proposition)?),
                }),
                SyntaxProposition::Comparison {
                    operator: ComparisonOperator::NotEqual,
                    ..
                } => Some(negate_click_proposition(surface)),
                SyntaxProposition::Not(body)
                    if matches!(
                        body.as_ref(),
                        SyntaxProposition::Comparison {
                            operator: ComparisonOperator::Equal,
                            ..
                        }
                    ) =>
                {
                    Some(body.as_ref().clone())
                }
                _ => None,
            }
        }
        let (Some(goal), Some(surface_goal)) = (search_input.goal(), search_input.surface_goal())
        else {
            return Ok(None);
        };
        if denied(goal).is_none() {
            return Ok(None);
        }
        let Some(equal) = denied_surface(surface_goal) else {
            return Ok(None);
        };
        let Some(_scope) = SolveFallbackScope::enter(SolveFallback::RefutedEquality) else {
            return Ok(None);
        };
        let Some(connected) =
            crate::kernel::search::proposition_search::arithmetic_connected_premises(
                search_input.facts().assumptions(),
                goal,
            )
        else {
            return Ok(None);
        };
        check_verification_deadline()?;
        let premises = connected
            .into_iter()
            .filter(|fact| fact != goal)
            .filter_map(|fact| denied(&fact))
            .take(MAX_REFUTED_EQUALITY_PREMISES)
            .collect::<Vec<_>>();
        if premises.is_empty() {
            return Ok(None);
        }
        let Some((split_proof, split, ids)) =
            attempt::candidate_outcome(search_input.split_focused_if(equal.clone()))?
        else {
            return Ok(None);
        };
        let marker = split_proof.checkpoint();
        let equal_arm = split_proof.focus_branch(ids[0])?;
        let introduced = [equal.clone()];
        for contradicted in premises {
            // The denied equality is spelled by construction at this state,
            // as a requirement is; a missing spelling is the candidate's miss.
            let requirement = UnresolvedRequirement {
                proposition: contradicted,
                context: None,
                introductions: Default::default(),
                call_site: None,
                assertion_condition: None,
                theorem_source: None,
                statement_safety: false,
                surface: None,
            };
            let Some(Some(spelling)) = attempt::candidate_outcome(
                equal_arm.requirement_surface(&requirement, &ProofStep::Step),
            )?
            else {
                continue;
            };
            let Some(scope) =
                attempt::candidate_outcome(equal_arm.driver().open_have(spelling.surface))?
            else {
                continue;
            };
            let Some(stated) = scope
                .driver()
                .try_solve_closure_with_surfaces(&introduced)?
            else {
                continue;
            };
            let Some(refuted) = attempt::candidate_outcome(stated.join())? else {
                continue;
            };
            let Some(equal_done) =
                attempt::candidate_outcome(refuted.driver().apply_step(ProofStep::Known))?
            else {
                continue;
            };
            let other_arm = equal_done.focus_branch(ids[1])?;
            let Some(other_done) =
                attempt::candidate_outcome(other_arm.driver().apply_step(ProofStep::Known))?
            else {
                return Ok(None);
            };
            return other_done
                .join_focused_if(&marker, split, ids, equal)
                .map(Some);
        }
        Ok(None)
    }

    /// Proves `&p[i] != &p[j]` from `i != j`: states the index disequality
    /// with `have i != j`, proved by `solve`, then closes the goal with
    /// `apply(click::separation::distinct_elements(p, i, j))`.
    /// `p` is the written goal's base; `i` and `j` are spelled from the
    /// kernel's two index words as the store search spells its index
    /// disequality (`((m - 1) as int32)`, `n - 1u64`, `0u64`), so the steps
    /// are spelled by construction and expansion writes them; the expanded
    /// proof searches nothing. It runs after every other strategy has missed, on a
    /// goal the kernel reads as two element addresses of one common base
    /// with indices of one width and format (`int32`, or 64-bit of one
    /// signedness), once (it does not nest inside itself), and its one
    /// search is the nested `solve` of the index disequality.
    pub(in crate::surface::proof) fn try_element_address_disequality(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_element_address_disequality");
        /// The base of a written element address `&p[i]`.
        fn element_address_base(expression: &SyntaxTerm) -> Option<&ProgramExpression> {
            let SyntaxTerm::ProgramExpression(ProgramExpression::AddressOf(target)) = expression
            else {
                return None;
            };
            let ProgramExpression::Index(base, _) = target.as_ref() else {
                return None;
            };
            Some(base)
        }
        let (Some(goal), Some(surface_goal)) = (search_input.goal(), search_input.surface_goal())
        else {
            return Ok(None);
        };
        let Some((left, right, format)) =
            crate::kernel::search::store_separation::element_address_disequality_indices(goal)
        else {
            return Ok(None);
        };
        let SyntaxProposition::Comparison {
            left: left_address,
            operator: ComparisonOperator::NotEqual,
            right: right_address,
        } = surface_goal
        else {
            return Ok(None);
        };
        let (Some(base), Some(other_base)) = (
            element_address_base(left_address),
            element_address_base(right_address),
        ) else {
            return Ok(None);
        };
        if base != other_base {
            return Ok(None);
        }
        let Some(_scope) = SolveFallbackScope::enter(SolveFallback::ElementAddress) else {
            return Ok(None);
        };
        check_verification_deadline()?;
        // The two indices are spelled from the kernel's index words, as the
        // store search spells its disequality, and are the law's arguments.
        let Some(indices_differ) = search_input.index_disequality_surface(&left, &right, format)
        else {
            return Ok(None);
        };
        let SyntaxProposition::Comparison {
            left: i, right: j, ..
        } = &indices_differ
        else {
            return Ok(None);
        };
        let arguments = vec![
            SyntaxTerm::ProgramExpression(base.clone()),
            i.clone(),
            j.clone(),
        ];
        let Some(scope) =
            attempt::candidate_outcome(search_input.driver().open_have(indices_differ.clone()))?
        else {
            return Ok(None);
        };
        let Some(closed) = scope.driver().try_solve_closure()? else {
            return Ok(None);
        };
        let Some(proof) = attempt::candidate_outcome(closed.join())? else {
            return Ok(None);
        };
        Ok(proof.driver().close_with_unsigned_lemma(
            "click::separation::distinct_elements",
            arguments,
            indices_differ,
        ))
    }

    /// A goal that reads stored cells, proved over the values stored there:
    /// `have` the goal's read-over-write form (`kernel::comparison_form`)
    /// by `solve`, then close the goal by `known`, which matches a read
    /// through the value its cell holds. The stored-value form is the goal
    /// `solve` would have seen had the reads been folded, so this recovers
    /// what its rules prove about the stored values. One level: the inner
    /// `solve` does not take this route again.
    pub(in crate::surface::proof) fn try_stored_value_goal(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_stored_value_goal");
        let Some(goal) = search_input.goal() else {
            return Ok(None);
        };
        let Some(resolved) = crate::kernel::comparison_form(goal) else {
            return Ok(None);
        };
        let Some(_scope) = SolveFallbackScope::enter(SolveFallback::StoredValue) else {
            return Ok(None);
        };
        let surface = search_input.premise_surface_facts().and_then(|recorded| {
            Self::proposed_surface_goal(search_input, recorded, &resolved).or_else(|| {
                Self::proposed_surface_goal(
                    search_input,
                    search_input.local_surface_facts(),
                    &resolved,
                )
            })
        });
        let Some(surface) = surface else {
            return Ok(None);
        };
        let observed = observed_reordered_indicator_sum(&surface);
        let Some(scope) = attempt::candidate_outcome(search_input.driver().open_have(surface))?
        else {
            return Ok(None);
        };
        let observed_closure = if let Some(observed) = observed
            && let Some(established) = attempt::candidate_outcome(scope.driver().apply_step(
                super::super::wide_arithmetic::have(observed, vec![ProofStep::Known]),
            ))? {
            attempt::candidate_outcome(established.driver().apply_step(ProofStep::Known))?
        } else {
            None
        };
        let closed = match observed_closure {
            Some(closed) => closed,
            None => {
                let Some(closed) = scope.driver().try_solve_closure()? else {
                    return Ok(None);
                };
                closed
            }
        };
        let Some(proof) = attempt::candidate_outcome(closed.join())? else {
            return Ok(None);
        };
        attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Known))
    }

    /// `solve`'s strategy over the facts connected to the goal: read
    /// the goal out of a function fact's definition; rewrite the goal by a
    /// connected equality once and then `known`, then as a bounded
    /// chain whose rewritten goals the cheap closers and a nested `solve`
    /// try; and join two constructor equations of one value. A nested
    /// `solve` inside these does not start them again.
    pub(in crate::surface::proof) fn try_connected_fact_closure(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_connected_fact_closure");
        let Some(_scope) = SolveFallbackScope::enter(SolveFallback::ConnectedFacts) else {
            return Ok(None);
        };
        // A scalar match was opaque to arithmetic before its constructor
        // rewrite. Only that shape permits arithmetic to restart inside the
        // connected search; general equality chains must not repeat all its
        // failed planners at every rewritten goal.
        let scalar_match = match search_input.goal() {
            Some(condition_source_0 @ Proposition::ConditionIs(_, _))
                if let Some((OldConditionTerm::IntegerEqual(left, right), _)) =
                    condition_source_0.old_condition() =>
            {
                matches!(
                    left.as_ref(),
                    crate::kernel::IntegerTerm::AlgebraicMatch { .. }
                ) || matches!(
                    right.as_ref(),
                    crate::kernel::IntegerTerm::AlgebraicMatch { .. }
                )
            }
            _ => false,
        };
        let _match_arithmetic = scalar_match
            .then(|| SolveFallbackScope::enter(SolveFallback::MatchArithmetic))
            .flatten();
        // First: it costs little when it does not apply.
        if let Some(closed) =
            crate::kernel::search::ProofSearch::try_definition_condition_closure(search_input)?
        {
            return Ok(Some(closed));
        }
        if let Some(closed) =
            crate::kernel::search::ProofSearch::try_single_rewrite_closure(search_input)?
        {
            return Ok(Some(closed));
        }
        if let Some(closed) =
            crate::kernel::search::ProofSearch::try_connected_equality_chain_closure(
                search_input,
                RewriteClosers::Ambient,
            )?
        {
            return Ok(Some(closed));
        }
        crate::kernel::search::ProofSearch::try_constructor_join_closure(search_input)
    }

    /// Closes `value <= c` over a constant by proving the same bound
    /// written `value < c + 1`. The two are one claim, but an order chain
    /// that ends at `c + 1` concludes the strict form, and the derivation
    /// asked for the non-strict form finds no chain ending at `c`.
    ///
    /// It runs only after every other strategy has missed, on a goal of
    /// exactly this shape, and the restated goal is strict, so it does not
    /// recur.
    pub(in crate::surface::proof) fn try_restated_constant_upper_bound(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_restated_constant_upper_bound");
        let Some((
            OldConditionTerm::Compare {
                format: format @ (MachineIntegerType::Int32 | MachineIntegerType::UInt32),
                relation: CompareRelation::LessEqual,
                left: _,
                right: bound,
            },
            true,
        )) = search_input.goal().and_then(Proposition::old_condition)
        else {
            return Ok(None);
        };
        let unsigned = *format == MachineIntegerType::UInt32;
        // `c + 1` must not wrap in the order the comparison is made in.
        let Some(bound) = bound.as_const().filter(|bound| {
            if unsigned {
                *bound != u32::MAX
            } else {
                *bound as i32 != i32::MAX
            }
        }) else {
            return Ok(None);
        };
        let Some(SyntaxProposition::Comparison {
            left,
            operator: ComparisonOperator::LessEqual,
            right,
        }) = search_input.surface_goal().cloned()
        else {
            return Ok(None);
        };
        // The source bound is the kernel bound; the successor is spelled in
        // the operand's own type.
        let successor = match &right {
            SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::UInt32(
                bits32_constant!(value),
            ))) if unsigned && constant_u32(*value) == bound => {
                SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::UInt32(
                    OldMachineTerm::uint32_constant(constant_u32(*value) + 1),
                )))
            }
            SyntaxTerm::IntegerLiteral(literal)
                if !unsigned && literal.parse::<i32>().ok() == Some(bound as i32) =>
            {
                SyntaxTerm::IntegerLiteral((i64::from(bound as i32) + 1).to_string())
            }
            _ => return Ok(None),
        };
        let strict = SyntaxProposition::Comparison {
            left,
            operator: ComparisonOperator::LessThan,
            right: successor,
        };
        let Ok(scope) = search_input.driver().open_have(strict.clone()) else {
            return Ok(None);
        };
        let Some(proved) = (scope).driver().try_solve_closure()? else {
            return Ok(None);
        };
        let Ok(joined) = proved.join() else {
            return Ok(None);
        };
        Ok(joined
            .driver()
            .apply_step(ProofStep::ArithmeticUsing(vec![strict]))
            .ok()
            .filter(|proof| proof.is_complete() || proof.goal() != search_input.goal()))
    }

    /// Exclude two distinct constants for the same signed word. This closes
    /// the overflow guard of `x / x` and `x % x` with one explicit proof split.
    fn try_distinct_constant_exclusion(
        search_input: &Proof<'a>,
        left: &Proposition,
        right: &Proposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_distinct_constant_exclusion");
        let (
            Some((
                left_equality @ OldConditionTerm::Compare {
                    format: format @ (MachineIntegerType::Int32 | MachineIntegerType::Int64),
                    relation: CompareRelation::Equal,
                    left: left_word,
                    right: left_literal,
                },
                false,
            )),
            Some((
                OldConditionTerm::Compare {
                    format: right_format,
                    relation: CompareRelation::Equal,
                    left: right_word,
                    right: right_literal,
                },
                false,
            )),
        ) = (left.old_condition(), right.old_condition())
        else {
            return Ok(None);
        };
        if format != right_format
            || left_word != right_word
            || !format
                .constant_from_term(left_literal)
                .zip(format.constant_from_term(right_literal))
                .is_some_and(|(left, right)| left != right)
        {
            return Ok(None);
        }
        let equality = Proposition::condition_is(left_equality.clone(), true);
        let (Some(condition), Some(other_exclusion)) = (
            search_input.structural_proposition_candidate(&equality),
            search_input.structural_proposition_candidate(right),
        ) else {
            return Ok(None);
        };
        let Some((proof, split, ids)) =
            attempt::candidate_outcome(search_input.split_focused_if(condition.clone()))?
        else {
            return Ok(None);
        };
        let marker = proof.checkpoint();
        let then_arm = proof.focus_branch(ids[0])?;
        let Some(scope) = attempt::candidate_outcome(then_arm.driver().open_have(other_exclusion))?
        else {
            return Ok(None);
        };
        let Some(rewritten) = attempt::candidate_outcome(
            scope
                .driver()
                .apply_step(ProofStep::Rewrite(condition.clone())),
        )?
        else {
            return Ok(None);
        };
        let Some(proved) =
            attempt::candidate_outcome(rewritten.driver().apply_step(ProofStep::Known))?
        else {
            return Ok(None);
        };
        let Some(then_done) =
            attempt::candidate_outcome(proved.join()?.driver().apply_step(ProofStep::Known))?
        else {
            return Ok(None);
        };
        let else_arm = then_done.focus_branch(ids[1])?;
        let Some(done) =
            attempt::candidate_outcome(else_arm.driver().apply_step(ProofStep::Known))?
        else {
            return Ok(None);
        };
        done.join_focused_if(&marker, split, ids, condition)
            .map(Some)
    }

    /// A computed count must be in range before the written nonzero
    /// comparison itself can be opened as a goal.
    pub(in crate::surface::proof) fn retain_computed_shift_divisor_bound(
        input: &Proof<'a>,
        goal: &Proposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("retain_computed_shift_divisor_bound");
        let Some(bound) =
            crate::kernel::proof::arithmetic_special::computed_shift_divisor_bound(goal)
        else {
            return Ok(None);
        };
        if input.facts().listed_premise_available(&bound, &[], false) {
            return Ok(None);
        }
        let Some(surface) = input.structural_proposition_candidate(&bound) else {
            return Ok(None);
        };
        let Some(scope) = attempt::candidate_outcome(input.driver().open_have(surface))? else {
            return Ok(None);
        };
        let Some(closed) = scope.driver().try_solve_closure_with_surfaces(&[])? else {
            return Ok(None);
        };
        closed.join().map(Some)
    }

    /// Prove and cite the fixed premises of a local arithmetic rule.
    /// Each recursive goal is a bound on an operand of the original goal.
    fn try_close_after_arithmetic_bounds(
        input: &Proof<'a>,
        requirements: &[Proposition],
        introduced_surfaces: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_close_after_arithmetic_bounds");
        let Some((proof, surfaces)) =
            Self::establish_arithmetic_bounds(input, requirements, introduced_surfaces)?
        else {
            return Ok(None);
        };
        attempt::candidate_outcome(proof.driver().apply_step(ProofStep::CloseBounds(surfaces)))
    }

    pub(super) fn establish_arithmetic_bounds(
        input: &Proof<'a>,
        requirements: &[Proposition],
        introduced_surfaces: &[SyntaxProposition],
    ) -> Result<Option<(Proof<'a>, Vec<SyntaxProposition>)>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("establish_arithmetic_bounds");
        let mut proof = input.clone();
        let mut surfaces = Vec::with_capacity(requirements.len());
        for required in requirements {
            check_verification_deadline()?;
            let Some(surface) = Self::resolve_solve_premises_unmeasured(
                &proof,
                std::slice::from_ref(required),
                introduced_surfaces,
            )
            .and_then(|mut pairs| pairs.pop().map(|(_, surface)| surface))
            .or_else(|| proof.structural_proposition_candidate(required)) else {
                return Ok(None);
            };
            if !proof.facts().listed_premise_available(required, &[], false) {
                let Some(scope) =
                    attempt::candidate_outcome(proof.driver().open_have(surface.clone()))?
                else {
                    return Ok(None);
                };
                let Some(closed) = scope
                    .driver()
                    .try_solve_closure_with_surfaces(introduced_surfaces)?
                else {
                    return Ok(None);
                };
                proof = closed.join()?;
            }
            surfaces.push(surface);
        }
        Ok(Some((proof, surfaces)))
    }

    fn try_signed_max_shift_bound(
        input: &Proof<'a>,
        bound: &Proposition,
        count: &Proposition,
        introduced_surfaces: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_signed_max_shift_bound");
        use crate::kernel::proof::arithmetic_special::{
            signed_max_shift_bound_identity, signed_max_shift_signed_identity,
        };
        let Some(goal) = input.goal() else {
            return Ok(None);
        };
        let Some((proof, surfaces)) = Self::establish_arithmetic_bounds(
            input,
            &[bound.clone(), count.clone()],
            introduced_surfaces,
        )?
        else {
            return Ok(None);
        };
        if let Some(closed) =
            attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Known))?
        {
            return Ok(Some(closed));
        }
        // The execution checker can know the count via its range index
        // before that exact bound has been published as an available fact.
        let Some(count_surface) = surfaces.last() else {
            return Ok(None);
        };
        let Some(proof) = attempt::candidate_outcome(proof.driver().apply_step(
            super::super::wide_arithmetic::have(count_surface.clone(), vec![ProofStep::Known]),
        ))?
        else {
            return Ok(None);
        };
        let identities = signed_max_shift_bound_identity(bound, goal)
            .into_iter()
            .chain(std::iter::once_with(|| signed_max_shift_signed_identity(goal)).flatten());
        for identity in identities {
            if let Some(equality) = proof.structural_proposition_candidate(&identity)
                && let Some(with_identity) = attempt::candidate_outcome(proof.driver().apply_step(
                    super::super::wide_arithmetic::have(equality.clone(), vec![ProofStep::Known]),
                ))?
                && let Some(rewritten) = attempt::candidate_outcome(
                    with_identity
                        .driver()
                        .apply_step(ProofStep::Rewrite(equality)),
                )?
                && let Some(closed) =
                    attempt::candidate_outcome(rewritten.driver().apply_step(ProofStep::Known))?
            {
                return Ok(Some(closed));
            }
        }
        Ok(None)
    }

    fn try_same_float_bound_weakening(
        input: &Proof<'a>,
        source: &Proposition,
        goal: &Proposition,
        source_surface: &SyntaxProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_same_float_bound_weakening");
        use crate::kernel::KernelFloatType;
        use crate::kernel::proof::arithmetic_special::same_float_bound_weakening;

        let Some((plan, source_strict)) = same_float_bound_weakening(source, goal) else {
            return Ok(None);
        };
        let Some(intermediate) = input.structural_proposition_candidate(&plan.intermediate) else {
            return Ok(None);
        };
        let step = if source_strict && !plan.intermediate_strict {
            let comparison = surface_comparison_with_anchored_operands(source_surface);
            let Some((left, right)) =
                super::super::surface_certificates::surface_strict_parts(&comparison)
            else {
                return Ok(None);
            };
            let name = match plan.format {
                KernelFloatType::Float32 => "click::float_order::float32_lt_to_le",
                KernelFloatType::Float64 => "click::float_order::float64_lt_to_le",
            };
            ProofStep::ApplyPlannedTheorem {
                application: TheoremApplication {
                    name: name.into(),
                    arguments: vec![left, right],
                },
                premises: vec![source_surface.clone()],
            }
        } else {
            ProofStep::Known
        };
        let Some(scope) =
            attempt::candidate_outcome(input.driver().open_have(intermediate.clone()))?
        else {
            return Ok(None);
        };
        let Some(mut proof) = attempt::candidate_outcome(scope.driver().apply_step(step))? else {
            return Ok(None);
        };
        if !proof.is_complete() {
            let Some(closed) =
                attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Known))?
            else {
                return Ok(None);
            };
            proof = closed;
        }
        Self::try_float_bound_weakening(&proof.join()?, &plan, intermediate)
    }

    fn try_exact_float_bound_transfer(
        input: &Proof<'a>,
        source: &Proposition,
        goal: &Proposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_exact_float_bound_transfer");
        use crate::kernel::proof::arithmetic_special::exact_float_bound_transfer;
        let Some(plan) = exact_float_bound_transfer(source, goal) else {
            return Ok(None);
        };
        let Some(intermediate) = input.structural_proposition_candidate(&plan.intermediate) else {
            return Ok(None);
        };
        let Some(proof) = attempt::candidate_outcome(input.driver().apply_step(
            super::super::wide_arithmetic::have(intermediate.clone(), vec![ProofStep::Known]),
        ))?
        else {
            return Ok(None);
        };
        Self::try_float_bound_weakening(&proof, &plan, intermediate)
    }

    pub(in crate::surface::proof) fn try_float_bound_weakening(
        proof: &Proof<'a>,
        plan: &crate::kernel::proof::arithmetic_special::FloatBoundWeakening,
        intermediate: SyntaxProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_float_bound_weakening");
        use crate::kernel::KernelFloatType;
        if let Some(closed) =
            attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Known))?
        {
            return Ok(Some(closed));
        }
        let SyntaxProposition::Comparison { left: operand, .. } =
            surface_comparison_with_anchored_operands(&intermediate)
        else {
            return Ok(None);
        };
        let literal = |bits| {
            SyntaxTerm::ProgramExpression(match plan.format {
                KernelFloatType::Float32 => {
                    crate::kernel::program_expression::float32_literal(bits as u32)
                }
                KernelFloatType::Float64 => {
                    crate::kernel::program_expression::float64_literal(bits)
                }
            })
        };
        let actual = literal(plan.actual_endpoint);
        let requested = literal(plan.requested_endpoint);
        let (left, right, arguments) = if plan.lower {
            (
                requested.clone(),
                actual.clone(),
                vec![requested, actual, operand],
            )
        } else {
            (
                actual.clone(),
                requested.clone(),
                vec![operand, actual, requested],
            )
        };
        let endpoint_order = SyntaxProposition::Comparison {
            left,
            operator: if plan.endpoint_strict {
                ComparisonOperator::LessThan
            } else {
                ComparisonOperator::LessEqual
            },
            right,
        };
        let strict_left = if plan.lower {
            plan.endpoint_strict
        } else {
            plan.intermediate_strict
        };
        let strict_right = if plan.lower {
            plan.intermediate_strict
        } else {
            plan.endpoint_strict
        };
        let name = match (plan.format, strict_left, strict_right) {
            (KernelFloatType::Float32, false, false) => "float32_le_le",
            (KernelFloatType::Float32, false, true) => "float32_le_lt",
            (KernelFloatType::Float32, true, false) => "float32_lt_le",
            (KernelFloatType::Float64, false, false) => "float64_le_le",
            (KernelFloatType::Float64, false, true) => "float64_le_lt",
            (KernelFloatType::Float64, true, false) => "float64_lt_le",
            (_, true, true) => unreachable!("only one comparison needs to be strict"),
        };
        let Some(proof) = attempt::candidate_outcome(proof.driver().apply_step(
            ProofStep::ApplyPlannedTheorem {
                application: TheoremApplication {
                    name: format!("click::float_order::{name}"),
                    arguments,
                },
                premises: vec![intermediate, endpoint_order],
            },
        ))?
        else {
            return Ok(None);
        };
        if proof.focused_discharged() {
            return Ok(Some(proof));
        }
        attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Known))
    }

    fn try_float_pair_bound(
        input: &Proof<'a>,
        goal: &Proposition,
        bounds: &[Proposition; 2],
        introduced_surfaces: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_float_pair_bound");
        use crate::kernel::proof::arithmetic_special::float_pair_bound_weakening;
        let Some((plan, subtract, tightened)) = float_pair_bound_weakening(goal, bounds) else {
            return Ok(None);
        };
        let resolve = |bound| {
            Self::resolve_solve_premises_unmeasured(
                input,
                std::slice::from_ref(bound),
                introduced_surfaces,
            )
            .and_then(|mut pairs| pairs.pop().map(|(_, surface)| surface))
            .or_else(|| input.structural_proposition_candidate(bound))
        };
        let [Some(first), Some(second)] = bounds.each_ref().map(resolve) else {
            return Ok(None);
        };
        let mut premises = [first, second];
        let mut proof = input.clone();
        for (premise, tighter) in premises.iter_mut().zip(tightened) {
            let Some(tighter) = tighter else {
                continue;
            };
            let Some((retained, surface)) = Self::retain_float_adjacent_bound(&proof, &tighter)?
            else {
                return Ok(None);
            };
            *premise = surface;
            proof = retained;
        }
        Self::try_apply_float_pair_bound(&proof, &plan, subtract, premises)
    }

    fn try_float_literal_sum_or_difference_bound(
        input: &Proof<'a>,
        source: &Proposition,
        goal: &Proposition,
        source_surface: &SyntaxProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_float_literal_sum_or_difference_bound");
        use crate::kernel::KernelFloatType;
        use crate::kernel::proof::arithmetic_special::{
            FloatLiteralSumOperation::{AddAtInfinity, Subtract, SubtractAtInfinity},
            float_literal_sum_or_difference_bound,
        };
        let Some((plan, bits, literal_on_left, operation)) =
            float_literal_sum_or_difference_bound(source, goal)
        else {
            return Ok(None);
        };
        let literal = SyntaxTerm::ProgramExpression(match plan.format {
            KernelFloatType::Float32 => {
                crate::kernel::program_expression::float32_literal(bits as u32)
            }
            KernelFloatType::Float64 => crate::kernel::program_expression::float64_literal(bits),
        });
        if matches!(operation, AddAtInfinity | SubtractAtInfinity) {
            return Self::try_float_sum_or_difference_at_infinite_bound(
                input,
                &plan,
                matches!(operation, SubtractAtInfinity),
                literal,
                source_surface,
            );
        }
        let reflexive = SyntaxProposition::Comparison {
            left: literal.clone(),
            operator: ComparisonOperator::LessEqual,
            right: literal.clone(),
        };
        let premises = if literal_on_left {
            [reflexive, source_surface.clone()]
        } else {
            [source_surface.clone(), reflexive]
        };
        Self::try_apply_float_pair_bound(input, &plan, matches!(operation, Subtract), premises)
    }

    fn try_float_sum_or_difference_at_infinite_bound(
        input: &Proof<'a>,
        plan: &crate::kernel::proof::arithmetic_special::FloatBoundWeakening,
        subtract: bool,
        literal: SyntaxTerm,
        source: &SyntaxProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_float_sum_or_difference_at_infinite_bound");
        use crate::kernel::KernelFloatType;
        let Some(intermediate) = input.structural_proposition_candidate(&plan.intermediate) else {
            return Ok(None);
        };
        let Some((proof, ordered, left, right)) =
            Self::prepare_float_bound(input, plan.format, source.clone())?
        else {
            return Ok(None);
        };
        let less_equal = SyntaxProposition::Comparison {
            left: left.clone(),
            operator: ComparisonOperator::LessEqual,
            right: right.clone(),
        };
        let proof = if ordered == less_equal {
            proof
        } else {
            let step =
                super::super::wide_arithmetic::have(less_equal.clone(), vec![ProofStep::Known]);
            let Some(retained) = attempt::candidate_outcome(proof.driver().apply_step(step))?
            else {
                return Ok(None);
            };
            retained
        };
        let finite = SyntaxProposition::FloatClassification {
            expression: literal.clone(),
            classification: syntax::CFloatClassification::Finite,
        };
        let name = match (plan.format, subtract) {
            (KernelFloatType::Float32, false) => "click::float_order::float32_add_finite_monotone",
            (KernelFloatType::Float64, false) => "click::float_order::float64_add_finite_monotone",
            (KernelFloatType::Float32, true) => {
                "click::float_order::float32_subtract_finite_monotone"
            }
            (KernelFloatType::Float64, true) => {
                "click::float_order::float64_subtract_finite_monotone"
            }
        };
        let application = ProofStep::ApplyPlannedTheorem {
            application: TheoremApplication {
                name: name.into(),
                arguments: vec![literal, left, right],
            },
            premises: vec![less_equal, finite],
        };
        let Some(scope) =
            attempt::candidate_outcome(proof.driver().open_have(intermediate.clone()))?
        else {
            return Ok(None);
        };
        let Some(mut scope) = attempt::candidate_outcome(scope.driver().apply_step(application))?
        else {
            return Ok(None);
        };
        if !scope.is_complete() {
            // The theorem gives both operand orders. Close the focused one.
            let Some(closed) =
                attempt::candidate_outcome(scope.driver().apply_step(ProofStep::Known))?
            else {
                return Ok(None);
            };
            scope = closed;
        }
        Self::try_float_bound_weakening(&scope.join()?, plan, intermediate)
    }

    pub(super) fn retain_float_adjacent_bound(
        input: &Proof<'a>,
        tighter: &Proposition,
    ) -> Result<Option<(Proof<'a>, SyntaxProposition)>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("retain_float_adjacent_bound");
        let Some(surface) = input.structural_proposition_candidate(tighter) else {
            return Ok(None);
        };
        let step = super::super::wide_arithmetic::have(surface.clone(), vec![ProofStep::Known]);
        Ok(attempt::candidate_outcome(input.driver().apply_step(step))?
            .map(|retained| (retained, surface)))
    }

    /// Rounding can merge distinct operands. Turn a strict input comparison
    /// into the explicitly checked non-strict premise used by the rounded laws.
    pub(super) fn prepare_float_bound(
        input: &Proof<'a>,
        format: crate::kernel::KernelFloatType,
        source: SyntaxProposition,
    ) -> Result<Option<(Proof<'a>, SyntaxProposition, SyntaxTerm, SyntaxTerm)>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("prepare_float_bound");
        let comparison = surface_comparison_with_anchored_operands(&source);
        if let Some((left, right)) = surface_nonstrict_parts(&comparison) {
            return Ok(Some((input.clone(), source, left, right)));
        }
        let Some((left, right)) =
            super::super::surface_certificates::surface_strict_parts(&comparison)
        else {
            return Ok(None);
        };
        let bound = SyntaxProposition::Comparison {
            left: left.clone(),
            operator: ComparisonOperator::LessEqual,
            right: right.clone(),
        };
        let name = match format {
            crate::kernel::KernelFloatType::Float32 => "click::float_order::float32_lt_to_le",
            crate::kernel::KernelFloatType::Float64 => "click::float_order::float64_lt_to_le",
        };
        let weakening = ProofStep::ApplyPlannedTheorem {
            application: TheoremApplication {
                name: name.into(),
                arguments: vec![left.clone(), right.clone()],
            },
            premises: vec![source],
        };
        let Some(proof) = attempt::candidate_outcome(input.driver().apply_step(
            super::super::wide_arithmetic::have(bound.clone(), vec![weakening]),
        ))?
        else {
            return Ok(None);
        };
        Ok(Some((proof, bound, left, right)))
    }

    fn try_apply_float_pair_bound(
        input: &Proof<'a>,
        plan: &crate::kernel::proof::arithmetic_special::FloatBoundWeakening,
        subtract: bool,
        [first, second]: [SyntaxProposition; 2],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_apply_float_pair_bound");
        use crate::kernel::KernelFloatType;
        let Some(intermediate) = input.structural_proposition_candidate(&plan.intermediate) else {
            return Ok(None);
        };
        let name = match (plan.format, subtract, plan.lower) {
            (KernelFloatType::Float32, false, true) => "float32_add_lower",
            (KernelFloatType::Float32, false, false) => "float32_add_upper",
            (KernelFloatType::Float64, false, true) => "float64_add_lower",
            (KernelFloatType::Float64, false, false) => "float64_add_upper",
            (KernelFloatType::Float32, true, true) => "float32_sub_lower",
            (KernelFloatType::Float32, true, false) => "float32_sub_upper",
            (KernelFloatType::Float64, true, true) => "float64_sub_lower",
            (KernelFloatType::Float64, true, false) => "float64_sub_upper",
        };
        let Some((proof, first, left, right)) =
            Self::prepare_float_bound(input, plan.format, first)?
        else {
            return Ok(None);
        };
        let (x, a) = if plan.lower {
            (right, left)
        } else {
            (left, right)
        };
        let Some((proof, second, left, right)) =
            Self::prepare_float_bound(&proof, plan.format, second)?
        else {
            return Ok(None);
        };
        let (y, b) = if plan.lower != subtract {
            (right, left)
        } else {
            (left, right)
        };
        let finite = |expression| SyntaxProposition::FloatClassification {
            expression,
            classification: syntax::CFloatClassification::Finite,
        };
        let application = ProofStep::ApplyPlannedTheorem {
            application: TheoremApplication {
                name: format!("click::float_order::{name}"),
                arguments: vec![x, y, a.clone(), b.clone()],
            },
            premises: vec![first, second, finite(a), finite(b)],
        };
        let Some(proof) = attempt::candidate_outcome(proof.driver().apply_step(
            super::super::wide_arithmetic::have(intermediate.clone(), vec![application]),
        ))?
        else {
            return Ok(None);
        };
        Self::try_float_bound_weakening(&proof, plan, intermediate)
    }

    fn try_float_scale_bound(
        input: &Proof<'a>,
        source: &Proposition,
        goal: &Proposition,
        source_surface: &SyntaxProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_float_scale_bound");
        use crate::kernel::KernelFloatType;
        use crate::kernel::proof::arithmetic_special::{
            FloatScaleOperation::{
                DivideNegative, DividePositive, MultiplyLeft, MultiplyNegativeLeft,
                MultiplyNegativeRight, MultiplyRight,
            },
            float_scale_bound_weakening,
        };
        let Some((plan, factor, scale)) = float_scale_bound_weakening(source, goal) else {
            return Ok(None);
        };
        let reverse = matches!(
            scale,
            DivideNegative | MultiplyNegativeLeft | MultiplyNegativeRight
        );
        let Some(intermediate) = input.structural_proposition_candidate(&plan.intermediate) else {
            return Ok(None);
        };
        let literal = |bits| {
            SyntaxTerm::ProgramExpression(match plan.format {
                KernelFloatType::Float32 => {
                    crate::kernel::program_expression::float32_literal(bits as u32)
                }
                KernelFloatType::Float64 => {
                    crate::kernel::program_expression::float64_literal(bits)
                }
            })
        };
        let factor = literal(factor);
        let finite = SyntaxProposition::FloatClassification {
            expression: factor.clone(),
            classification: syntax::CFloatClassification::Finite,
        };
        let (sign_left, sign_right) = if reverse {
            (factor.clone(), literal(0))
        } else {
            (literal(0), factor.clone())
        };
        let sign = SyntaxProposition::Comparison {
            left: sign_left,
            operator: ComparisonOperator::LessThan,
            right: sign_right,
        };
        let name = match (scale, plan.lower) {
            (MultiplyLeft, true) => "scale_lower",
            (MultiplyLeft, false) => "scale_upper",
            (MultiplyRight, true) => "scale_right_lower",
            (MultiplyRight, false) => "scale_right_upper",
            (MultiplyNegativeLeft, true) => "scale_negative_lower",
            (MultiplyNegativeLeft, false) => "scale_negative_upper",
            (MultiplyNegativeRight, true) => "scale_negative_right_lower",
            (MultiplyNegativeRight, false) => "scale_negative_right_upper",
            (DividePositive, true) => "divide_positive_lower",
            (DividePositive, false) => "divide_positive_upper",
            (DivideNegative, true) => "divide_negative_lower",
            (DivideNegative, false) => "divide_negative_upper",
        };
        let module_width = match plan.format {
            KernelFloatType::Float32 => "float32",
            KernelFloatType::Float64 => "float64",
        };
        let Some((proof, source_bound, left, right)) =
            Self::prepare_float_bound(input, plan.format, source_surface.clone())?
        else {
            return Ok(None);
        };
        let (x, endpoint) = if plan.lower != reverse {
            (right, left)
        } else {
            (left, right)
        };
        let application = ProofStep::ApplyPlannedTheorem {
            application: TheoremApplication {
                name: format!("click::float_order::{module_width}_{name}"),
                arguments: vec![factor, x, endpoint],
            },
            premises: vec![source_bound, finite, sign],
        };
        let Some(proof) = attempt::candidate_outcome(proof.driver().apply_step(
            super::super::wide_arithmetic::have(intermediate.clone(), vec![application]),
        ))?
        else {
            return Ok(None);
        };
        Self::try_float_bound_weakening(&proof, &plan, intermediate)
    }

    fn try_float_narrow_bound(
        input: &Proof<'a>,
        source: &Proposition,
        goal: &Proposition,
        source_surface: &SyntaxProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_float_narrow_bound");
        use crate::kernel::proof::arithmetic_special::float_narrow_bound_weakening;
        let Some((plan, strict)) = float_narrow_bound_weakening(source, goal) else {
            return Ok(None);
        };
        let comparison = surface_comparison_with_anchored_operands(source_surface);
        let (parts, name) = if strict {
            (
                super::super::surface_certificates::surface_strict_parts(&comparison),
                "click::float_order::float64_narrow_lt",
            )
        } else {
            (
                surface_nonstrict_parts(&comparison),
                "click::float_order::float64_narrow_le",
            )
        };
        let Some((left, right)) = parts else {
            return Ok(None);
        };
        let Some(intermediate) = input.structural_proposition_candidate(&plan.intermediate) else {
            return Ok(None);
        };
        let application = ProofStep::ApplyPlannedTheorem {
            application: TheoremApplication {
                name: name.into(),
                arguments: vec![left, right],
            },
            premises: vec![source_surface.clone()],
        };
        let Some(scope) =
            attempt::candidate_outcome(input.driver().open_have(intermediate.clone()))?
        else {
            return Ok(None);
        };
        let Some(mut scope) = attempt::candidate_outcome(scope.driver().apply_step(application))?
        else {
            return Ok(None);
        };
        if !scope.is_complete() {
            let Some(closed) =
                attempt::candidate_outcome(scope.driver().apply_step(ProofStep::Known))?
            else {
                return Ok(None);
            };
            scope = closed;
        }
        Self::try_float_bound_weakening(&scope.join()?, &plan, intermediate)
    }

    pub(in crate::surface::proof) fn try_float_bound_link(
        input: &Proof<'a>,
        source: &Proposition,
        goal: &Proposition,
        source_surface: &SyntaxProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_float_bound_link");
        if let Some(closed) =
            Self::try_same_float_bound_weakening(input, source, goal, source_surface)?
        {
            return Ok(Some(closed));
        }
        if let Some(closed) = Self::try_exact_float_bound_transfer(input, source, goal)? {
            return Ok(Some(closed));
        }
        if let Some(closed) = Self::try_float_narrow_bound(input, source, goal, source_surface)? {
            return Ok(Some(closed));
        }
        if let Some(closed) =
            Self::try_float_literal_sum_or_difference_bound(input, source, goal, source_surface)?
        {
            return Ok(Some(closed));
        }
        if let Some(closed) = Self::try_float_reciprocal_bound(input, source, goal, source_surface)?
        {
            return Ok(Some(closed));
        }
        if let Some(closed) =
            Self::try_rounded_int32_to_float32_bound(input, source, goal, source_surface)?
        {
            return Ok(Some(closed));
        }
        Self::try_float_scale_bound(input, source, goal, source_surface)
    }

    /// Materialize each link of a selected bound chain. Each have cites the
    /// previous bound, with its own endpoint.
    fn try_float_bound_chain(
        input: &Proof<'a>,
        bounds: &[Proposition],
        introduced_surfaces: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_float_bound_chain");
        let [source, intermediate @ ..] = bounds else {
            return Ok(None);
        };
        let Some((_, mut previous)) = Self::resolve_solve_premises_unmeasured(
            input,
            std::slice::from_ref(source),
            introduced_surfaces,
        )
        .and_then(|mut pairs| pairs.pop()) else {
            return Ok(None);
        };
        let mut proof = input.clone();
        let mut previous_bound = source;
        for bound in intermediate {
            check_verification_deadline()?;
            let Some(surface) = proof.structural_proposition_candidate(bound) else {
                return Ok(None);
            };
            let Some(scope) =
                attempt::candidate_outcome(proof.driver().open_have(surface.clone()))?
            else {
                return Ok(None);
            };
            if let Some(closed) =
                scope
                    .driver()
                    .try_float_bound_link(previous_bound, bound, &previous)?
            {
                proof = closed.join()?;
                previous = surface;
                previous_bound = bound;
                continue;
            }
            let step = ProofStep::CloseBounds(vec![previous]);
            let Some(closed) = attempt::candidate_outcome(scope.driver().apply_step(step))? else {
                return Ok(None);
            };
            proof = closed.join()?;
            previous = surface;
            previous_bound = bound;
        }
        if let Some(goal) = proof.goal()
            && let Some(closed) =
                Self::try_float_bound_link(&proof, previous_bound, goal, &previous)?
        {
            return Ok(Some(closed));
        }
        let step = ProofStep::CloseBounds(vec![previous]);
        attempt::candidate_outcome(proof.driver().apply_step(step))
    }

    /// Close the small domain conjunction as ordinary checked `have` steps.
    /// In particular, `defined(cast)` is written as one term even though
    /// its lowered goal has two ordered bounds.
    fn try_bounded_arithmetic_closure(
        search_input: &Proof<'a>,
        introduced_surfaces: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_bounded_arithmetic_closure");
        use crate::kernel::proof::arithmetic_special::{
            float_compound_bound_operand, float_finiteness_source, float_zero_product_premise,
            is_float_bound, positive_divisor_product_guards, promoted_right_shift_bound,
            shift_count_mask_requirements, shifted_one_bounds, signed_max_shift_count_bound,
            signed_product_guard_candidates, signed_quotient_bridge_requirement,
            signed_shift_bound_mask_identity,
        };
        let Some(goal) = search_input.goal() else {
            return Ok(None);
        };
        if let Proposition::Or(left, right) = goal {
            return Self::try_distinct_constant_exclusion(search_input, left, right);
        }
        if let Some(requirements) = shift_count_mask_requirements(goal)
            && let Some((proof, _)) =
                Self::establish_arithmetic_bounds(search_input, &requirements, introduced_surfaces)?
        {
            return attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Known));
        }
        if let Some(identity) = signed_shift_bound_mask_identity(goal)
            && let Some(equality) = search_input.structural_proposition_candidate(&identity)
            && let Some(scope) =
                attempt::candidate_outcome(search_input.driver().open_have(equality.clone()))?
            && let Some(closed) = scope
                .driver()
                .try_solve_closure_with_surfaces(introduced_surfaces)?
            && let Some(rewritten) = attempt::candidate_outcome(
                closed
                    .join()?
                    .driver()
                    .apply_step(ProofStep::Rewrite(equality)),
            )?
        {
            if let Some(closed) =
                attempt::candidate_outcome(rewritten.driver().apply_step(ProofStep::Known))?
            {
                return Ok(Some(closed));
            }
            if rewritten
                .goal()
                .is_some_and(|goal| signed_max_shift_count_bound(goal).is_some())
            {
                return Self::try_solve_closure_with_surfaces(&rewritten, introduced_surfaces);
            }
            return Ok(None);
        }
        if let Proposition::And(left, right) = goal
            && [left.as_ref(), right.as_ref()].iter().all(|leaf| {
                is_float_bound(leaf)
                    || promoted_right_shift_bound(leaf) == Some(true)
                    || signed_product_guard_candidates(leaf).next().is_some()
            })
        {
            let mut proof = search_input.clone();
            for leaf in [left, right] {
                let Some(surface) = proof.structural_proposition_candidate(leaf) else {
                    return Ok(None);
                };
                let Some(scope) = attempt::candidate_outcome(proof.driver().open_have(surface))?
                else {
                    return Ok(None);
                };
                let Some(closed) = scope
                    .driver()
                    .try_solve_closure_with_surfaces(introduced_surfaces)?
                else {
                    return Ok(None);
                };
                proof = closed.join()?;
            }
            return attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Known));
        }

        let mut candidates = signed_product_guard_candidates(goal).collect::<Vec<_>>();
        if let Some(guard) = signed_quotient_bridge_requirement(goal) {
            candidates.push(vec![guard]);
        }
        'counts: for signed in [false, true] {
            let Some(bounds) = shifted_one_bounds(goal, signed) else {
                continue;
            };
            let Some((mut proof, _)) =
                Self::establish_arithmetic_bounds(search_input, &bounds, introduced_surfaces)?
            else {
                continue;
            };
            for bound in &bounds {
                if proof.facts().contains(bound) {
                    continue;
                }
                // Publish this exact count reading even if the execution
                // checker could already prove it through a different fact.
                let Some(surface) = proof.structural_proposition_candidate(bound) else {
                    continue 'counts;
                };
                let Some(materialized) = attempt::candidate_outcome(proof.driver().apply_step(
                    super::super::wide_arithmetic::have(surface, vec![ProofStep::Known]),
                ))?
                else {
                    continue 'counts;
                };
                proof = materialized;
            }
            if let Some(closed) =
                attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Known))?
            {
                return Ok(Some(closed));
            }
        }
        if let Some(bound) = crate::kernel::search::ProofSearch::select_arithmetic_bound(
            search_input.facts().assumptions(),
            goal,
        ) {
            if let Some(count) = signed_max_shift_count_bound(goal) {
                if let Some(closed) = Self::try_signed_max_shift_bound(
                    search_input,
                    &bound,
                    &count,
                    introduced_surfaces,
                )? {
                    return Ok(Some(closed));
                }
                if let Some(closed) = Self::try_close_after_arithmetic_bounds(
                    search_input,
                    &[bound, count],
                    introduced_surfaces,
                )? {
                    return Ok(Some(closed));
                }
            } else {
                let source = Self::resolve_solve_premises_unmeasured(
                    search_input,
                    std::slice::from_ref(&bound),
                    introduced_surfaces,
                )
                .and_then(|mut pairs| pairs.pop().map(|(_, surface)| surface))
                .or_else(|| search_input.structural_proposition_candidate(&bound));
                let closed = if let Some(source) = source {
                    Self::try_float_bound_link(search_input, &bound, goal, &source)?
                } else {
                    Self::try_exact_float_bound_transfer(search_input, &bound, goal)?
                };
                if let Some(closed) = closed {
                    return Ok(Some(closed));
                }
                candidates.push(vec![bound]);
            }
        }
        if let Some(bounds) = crate::kernel::search::ProofSearch::select_float_pair_bounds(
            search_input.facts().assumptions(),
            goal,
        ) {
            if let Ok(pair_bounds) = bounds.as_slice().try_into()
                && let Some(closed) = Self::try_float_pair_bound(
                    search_input,
                    goal,
                    pair_bounds,
                    introduced_surfaces,
                )?
            {
                return Ok(Some(closed));
            }
            if let Ok(pair_bounds) = bounds.as_slice().try_into()
                && let Some(closed) = Self::try_positive_float_product_bound(
                    search_input,
                    goal,
                    pair_bounds,
                    introduced_surfaces,
                )?
            {
                return Ok(Some(closed));
            }
            if let Ok(pair_bounds) = bounds.as_slice().try_into() {
                if let Some(closed) = Self::try_float_zero_product_bound(
                    search_input,
                    goal,
                    pair_bounds,
                    introduced_surfaces,
                )? {
                    return Ok(Some(closed));
                }
                if let Some(closed) = Self::try_float_square_bound(
                    search_input,
                    goal,
                    pair_bounds,
                    introduced_surfaces,
                )? {
                    return Ok(Some(closed));
                }
            }
            if let Ok(corners) = bounds.as_slice().try_into()
                && let Some(closed) =
                    Self::try_float_corner_bound(search_input, goal, corners, introduced_surfaces)?
            {
                return Ok(Some(closed));
            }
            candidates.push(bounds);
        }
        if let Some(bounds) = crate::kernel::search::ProofSearch::select_float_bound_chain(
            search_input.facts().assumptions(),
            goal,
        ) && let Some(closed) =
            Self::try_float_bound_chain(search_input, &bounds, introduced_surfaces)?
        {
            return Ok(Some(closed));
        }
        for premises in candidates {
            check_verification_deadline()?;
            let surfaces = premises
                .iter()
                .map(|premise| {
                    Self::resolve_solve_premises_unmeasured(
                        search_input,
                        std::slice::from_ref(premise),
                        introduced_surfaces,
                    )
                    .and_then(|mut pairs| pairs.pop().map(|(_, surface)| surface))
                    .or_else(|| search_input.structural_proposition_candidate(premise))
                })
                .collect::<Option<Vec<_>>>();
            let Some(surfaces) = surfaces else {
                continue;
            };
            let step = ProofStep::CloseBounds(surfaces);
            if let Some(closed) =
                attempt::candidate_outcome(search_input.driver().apply_step(step))?
            {
                return Ok(Some(closed));
            }
        }
        if let Some(source) =
            float_finiteness_source(goal).or_else(|| float_zero_product_premise(goal))
            && let Some((proof, _)) =
                Self::establish_arithmetic_bounds(search_input, &[source], introduced_surfaces)?
            && let Some(closed) =
                attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Known))?
        {
            return Ok(Some(closed));
        }
        if let Some(closed) =
            Self::try_float_finite_interval(search_input, goal, introduced_surfaces)?
        {
            return Ok(Some(closed));
        }
        let derived_requirements = [false, true]
            .into_iter()
            .filter_map(|swap| positive_divisor_product_guards(goal, swap))
            .chain(float_compound_bound_operand(goal).map(|bound| vec![bound]));
        for requirements in derived_requirements {
            if let Some(closed) = Self::try_close_after_arithmetic_bounds(
                search_input,
                &requirements,
                introduced_surfaces,
            )? {
                return Ok(Some(closed));
            }
        }
        Ok(None)
    }

    /// Continues smart closure after direct logical candidates have either
    /// missed or been deliberately rejected as non-checkable. When
    /// `exclude_exact_goal` is true, the atomic derivation query may not cite
    /// the goal's own ambient fact; every selected theorem step is still
    /// checked against this unchanged Proof.
    pub(in crate::surface::proof) fn try_solve_closure_after_direct(
        search_input: &Proof<'a>,
        exclude_exact_goal: bool,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_solve_closure_after_direct");
        let mut scope = attempt::search_scope("solve closure after direct candidates");
        let result =
            crate::kernel::search::ProofSearch::try_solve_closure_after_direct_with_surfaces(
                search_input,
                exclude_exact_goal,
                &[],
            )?;
        if result.is_some() {
            scope.succeed();
        }
        Ok(result)
    }

    pub(in crate::surface::proof) fn try_solve_closure_with_surfaces(
        search_input: &Proof<'a>,
        introduced_surfaces: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_solve_closure_with_surfaces");
        if crate::surface::proof::implicit_solve_scope::checked_only() {
            return Err(search_input.step_error(
                "checked-only verification forbids close(); write its proof steps explicitly",
            ));
        }
        let mut scope = attempt::search_scope("solve closure with surfaces");
        // Prefer the whole `known` closure, including computation, before
        // decomposing the goal or searching for another derivation.
        if let Some(proof) =
            attempt::candidate_outcome(search_input.driver().apply_step(ProofStep::Known))?
        {
            scope.succeed();
            return Ok(Some(proof));
        }
        if let Some(proof) =
            crate::kernel::search::ProofSearch::try_direct_logical_closure(search_input)?
        {
            scope.succeed();
            return Ok(Some(proof));
        }
        if let Some(proof) =
            crate::kernel::search::ProofSearch::try_direct_structural_closure_under_binders(
                search_input,
            )?
        {
            scope.succeed();
            return Ok(Some(proof));
        }
        let result =
            crate::kernel::search::ProofSearch::try_solve_closure_after_direct_with_surfaces(
                search_input,
                false,
                introduced_surfaces,
            )?;
        if result.is_some() {
            scope.succeed();
        }
        Ok(result)
    }

    pub(in crate::surface::proof) fn try_solve_closure_after_direct_with_surfaces(
        search_input: &Proof<'a>,
        exclude_exact_goal: bool,
        introduced_surfaces: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_solve_closure_after_direct_with_surfaces");
        crate::kernel::search::ProofSearch::try_solve_closure_after_direct_with_surfaces_and_function_unfold(search_input,
            exclude_exact_goal,
            introduced_surfaces,
            true,
        )
    }

    pub(in crate::surface::proof) fn try_solve_closure_after_direct_with_surfaces_and_function_unfold(
        search_input: &Proof<'a>,
        exclude_exact_goal: bool,
        introduced_surfaces: &[SyntaxProposition],
        allow_function_unfold: bool,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery(
            "try_solve_closure_after_direct_with_surfaces_and_function_unfold",
        );
        if crate::surface::proof::implicit_solve_scope::checked_only() {
            return Err(search_input.step_error(
                "checked-only verification forbids implicit solve; write its proof steps explicitly",
            ));
        }
        if let Some(proof) = Self::try_recorded_allocation_alignment(search_input)? {
            return Ok(Some(proof));
        }
        if let Some(proof) =
            Self::try_bounded_arithmetic_closure(search_input, introduced_surfaces)?
        {
            return Ok(Some(proof));
        }
        if let (Some(surface_goal), Some(goal)) = (search_input.surface_goal(), search_input.goal())
        {
            // A stated positive bound refutes equality to zero. Use the
            // same checked split and rewrite as disjunctive word bounds.
            if let SyntaxProposition::Comparison {
                left: written_left,
                operator: ComparisonOperator::NotEqual,
                right: written_right,
            } = surface_goal
                && let Some((
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::Int64 | MachineIntegerType::UInt64,
                        relation: CompareRelation::Equal,
                        left,
                        right,
                    },
                    false,
                )) = goal.old_condition()
                && [left, right]
                    .iter()
                    .any(|operand| operand.bitvector64_as_const() == Some(0))
            {
                for (divisor, zero) in
                    [(written_left, written_right), (written_right, written_left)]
                {
                    for (left, operator, right) in [
                        (divisor, ComparisonOperator::GreaterThan, zero),
                        (zero, ComparisonOperator::LessThan, divisor),
                    ] {
                        let premise = SyntaxProposition::Comparison {
                            left: left.clone(),
                            operator,
                            right: right.clone(),
                        };
                        check_verification_deadline()?;
                        if let Some(bound) = attempt::candidate_outcome(
                            search_input
                                .lower_cited_surface_proposition(&premise, "positive bound"),
                        )? && search_input
                            .facts()
                            .assumptions()
                            .states_required_goal(&bound)
                            && crate::kernel::proof::arithmetic_special::word_order_excludes_literal(
                                goal, &bound,
                            )
                            && let Some(proof) =
                                Self::try_word_order_exclusion_case(search_input, &premise)
                        {
                            return Ok(Some(proof));
                        }
                    }
                }
            }
        }
        if let Some(goal) = search_input.goal()
            && !(exclude_exact_goal && search_input.facts().contains(goal))
            && let Some(chain) = crate::kernel::search::ProofSearch::signed_order_chain_premises(
                search_input.facts().assumptions(),
                goal,
            )
            // Short paths have their own checked rules.
            && chain.len() > 2
            && let Some(pairs) = Self::resolve_solve_premises_unmeasured(
                search_input,
                &chain,
                introduced_surfaces,
            )
        {
            let premises = pairs
                .into_iter()
                .map(|(_, surface)| surface)
                .collect::<Vec<_>>();
            if !matches!(search_input.context.as_ref(), ProofContext::Pure(_))
                && let Some(closed) = Self::close_selected_signed_order(search_input, &premises)
            {
                return Ok(Some(closed));
            }
            if let Some(closed) = attempt::candidate_outcome(Self::try_integer_composition_using(
                search_input,
                &premises,
            ))?
            .flatten()
            {
                return Ok(Some(closed));
            }
        }
        // A separating conjunction already states its structural proof tree.
        // Decompose it before selecting ambient arithmetic/history candidates;
        // each child still runs ordinary solve and emits ordinary library steps.
        if let Some(surface_goal) = search_input.surface_goal()
            && let Some(proof) = Self::try_resource_star_separation_closure(
                search_input,
                surface_goal,
                introduced_surfaces,
            )?
        {
            return Ok(Some(proof));
        }
        // Prefer ordinary equalities between resource descriptors to a
        // historical transport of the whole separation proposition.
        if let Some(proof) = Self::try_resource_descriptor_rewrite_closure(search_input)? {
            return Ok(Some(proof));
        }
        // Restrict a current separation fact before trying historical
        // transport. The library application records both containment
        // premises for replay.
        if let Some(surface_goal) = search_input.surface_goal()
            && let Some(proof) = Self::try_resource_separation_restriction_closure(
                search_input,
                surface_goal,
                introduced_surfaces,
                false,
            )?
        {
            return Ok(Some(proof));
        }
        if let Some(proof) = Self::try_ordinary_viewability_restriction_closure(search_input, None)
        {
            return Ok(Some(proof));
        }
        // Plain solve and recursive logical closure share the same memory
        // strategies. A structural child must not lose read-over-write or
        // explicit frame transport merely because it was reached by `both`.
        if let Some(surface) = search_input.surface_goal()
            && let Some(proof) =
                crate::kernel::search::ProofSearch::try_cell_frame_transport_closure(
                    search_input,
                    surface,
                )?
        {
            return Ok(Some(proof));
        }
        // A goal that reads stored cells is first tried over the stored
        // values, the goal the search saw before reads kept their version
        // names; the full search over the reads follows only when that
        // misses.
        if let Some(proof) =
            crate::kernel::search::ProofSearch::try_stored_value_goal(search_input)?
        {
            return Ok(Some(proof));
        }
        // The uint32 lemmas state the wrapping steps of a `uint32` order, so
        // a goal of one of their shapes is closed by naming the lemma, from
        // the exact premise it requires.
        if let Some(proof) =
            crate::kernel::search::ProofSearch::try_unsigned_order_step(search_input)
        {
            return Ok(Some(proof));
        }
        // Population bounds are arithmetic on the authority's count, even
        // when that count shares a carrier with a C field. Try its indexed
        // bounds before searching memory equalities and recorded states.
        // Compound signed orders likewise select indexed bounds before
        // spelling historical aliases, including terminal outcomes with
        // many earlier clauses. Simple terminal comparisons retain their
        // result-aware rewrites and named-rule routes first.
        let population_count_comparison = matches!(
            search_input.surface_goal(),
            Some(
                SyntaxProposition::Comparison {
                    left: SyntaxTerm::ResourceCount(_),
                    ..
                } | SyntaxProposition::Comparison {
                    right: SyntaxTerm::ResourceCount(_),
                    ..
                }
            )
        );
        let compound_signed_order = matches!(&search_input.goal(), Some(condition_source_0 @ Proposition::ConditionIs(
                _,
                _
            )) if matches!(condition_source_0.old_condition(), Some((OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    relation: CompareRelation::LessThan,
                    ..
                } | OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    relation: CompareRelation::LessEqual,
                    ..
                } | OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    relation: CompareRelation::GreaterThan,
                    ..
                } | OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    relation: CompareRelation::GreaterEqual,
                    ..
                }, _))))
            && matches!(
                search_input.surface_goal(),
                Some(SyntaxProposition::Comparison { left, right, .. })
                    if [left, right].into_iter().any(|term| matches!(
                        term,
                        SyntaxTerm::Add(..)
                            | SyntaxTerm::Subtract(..)
                            | SyntaxTerm::Multiply(..)
                    ))
            );
        let indexed_arithmetic_tried = population_count_comparison
            || compound_signed_order
            || (search_input.focused_outcome_data().is_none()
                && matches!(&search_input.goal(), Some(condition_source_0 @ Proposition::ConditionIs(
                        _,
                        _
                    )) if matches!(condition_source_0.old_condition(), Some((OldConditionTerm::Compare {
                            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                            relation: CompareRelation::LessThan,
                            ..
                        } | OldConditionTerm::Compare {
                            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                            relation: CompareRelation::LessEqual,
                            ..
                        } | OldConditionTerm::Compare {
                            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                            relation: CompareRelation::GreaterThan,
                            ..
                        } | OldConditionTerm::Compare {
                            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                            relation: CompareRelation::GreaterEqual,
                            ..
                        }, _)))));
        if indexed_arithmetic_tried
            && let Some(proof) = crate::instrumentation::measure_operation(
                "surface",
                "solve closure",
                "solve closure: indexed bounds",
                || {
                    crate::kernel::search::ProofSearch::try_execution_signed_arithmetic(
                        search_input,
                    )
                },
            )
        {
            return Ok(Some(proof));
        }
        if let Some(proof) =
            crate::kernel::search::ProofSearch::try_equality_from_opposite_bounds(search_input)
        {
            return Ok(Some(proof));
        }
        // Try direct Integer identities even when an unfold refreshed the goal.
        if search_input.goal().is_some_and(|goal| {
            integer_affine_claim(goal).is_some() && normalizes_context_free(goal)
        }) && let Some(closed) = Self::try_local_checked_closure(search_input, Some(Vec::new()))?
        {
            return Ok(Some(closed));
        }
        if let Some(proof) = Self::try_goal_conditional_closure(search_input) {
            return Ok(Some(proof));
        }
        // Close an indexed equality rewrite before deriving a longer
        // arithmetic proof of the same fact. Connected chains still wait
        // until selected arithmetic has had the goal.
        let direct_rewrite = crate::instrumentation::measure_operation(
            "surface",
            "solve closure",
            "solve closure: goal equality rewrite",
            || {
                Ok::<_, ClickError>(
                    crate::kernel::search::ProofSearch::try_indexed_direct_equality_rewrite(
                        search_input,
                        exclude_exact_goal,
                    ),
                )
            },
        )?;
        let chain_rewrites = match direct_rewrite {
            std::ops::ControlFlow::Break(Some(rewritten)) => return Ok(Some(rewritten)),
            std::ops::ControlFlow::Break(None) => false,
            std::ops::ControlFlow::Continue(()) => true,
        };
        let rewrite_chain = |allow_unfold| {
            crate::instrumentation::measure_operation(
                "surface",
                "solve closure",
                "solve closure: goal equality rewrite",
                || Self::try_connected_goal_equality_chain_closure(search_input, allow_unfold),
            )
        };
        if let Some(surface_goal) = search_input.surface_goal()
            && let Some(proof) =
                crate::kernel::search::ProofSearch::try_selected_unchanged_load_forall_goal(
                    search_input,
                    surface_goal,
                    &[],
                )
        {
            return Ok(Some(proof));
        }
        // A written conjunction is split before any whole-goal derivation,
        // rewrite, transport, or instantiation strategy below runs over it.
        // Each of those costs work in the ambient facts per attempt, and on
        // a conjunction chain the structural recursion would otherwise
        // repeat them on every suffix of the chain before reaching its
        // leaves, which is quadratic in the chain. Each conjunct still gets
        // the complete closure, including these strategies, and the
        // whole-goal strategies still run, unchanged, when the split misses.
        if let Some(flat) = crate::kernel::search::ProofSearch::try_flat_solve_conjunction(
            search_input,
            introduced_surfaces,
        )? {
            return Ok(Some(flat));
        }
        let structural_conjunction_tried = if let Some(surface_goal) = search_input.surface_goal()
            && matches!(search_input.goal(), Some(Proposition::And(_, _)))
            && surface_logical_children(surface_goal, true).is_some()
        {
            if let Some(structural) = crate::instrumentation::measure_operation(
                "surface",
                "solve closure",
                "solve closure: structural",
                || {
                    crate::kernel::search::ProofSearch::try_structural_solve_closure_with_surfaces(
                        search_input,
                        surface_goal,
                        introduced_surfaces,
                    )
                },
            )? {
                return Ok(Some(structural));
            }
            true
        } else {
            false
        };
        // A constructor-disjoint guard needs only its indexed model equation.
        // Refute it before the whole implication's connected memory facts are
        // selected and given historical source spellings.
        if let Some(closed) =
            crate::kernel::search::ProofSearch::try_constructor_guard_refutation(search_input)?
        {
            return Ok(Some(closed));
        }
        // Retain the selected premises for the anchored fallbacks. The proof
        // is unchanged by a declined candidate, so repeating derivation
        // discovery here would perform the same search a second time.
        let mut anchored_pairs = Vec::new();
        let atomic = (|| {
            let (goal, derivation) =
                crate::kernel::search::ProofSearch::selected_solve_derivation_plan(
                    search_input,
                    exclude_exact_goal,
                )?;
            // A derivation that records the exact path it used names its
            // own premises. Spell only those first: the selection it ran in
            // holds every fact connected to the goal's variables, and
            // spelling them all costs work in the path's length for a
            // closer that cites one or two.
            let cited_pairs = derivation.recorded_path_premises().and_then(|cited| {
                crate::kernel::search::ProofSearch::resolve_solve_premises(
                    search_input,
                    &cited,
                    introduced_surfaces,
                )
                .filter(|pairs| pairs.len() == cited.len())
            });
            if let Some(pairs) = &cited_pairs
                && let Some(closed) =
                    crate::kernel::search::ProofSearch::check_typed_atomic_solve_candidate(
                        search_input,
                        &goal,
                        &derivation,
                        pairs,
                    )
            {
                return Some(closed);
            }
            // A derivation that only selects a disjunct proves nothing the
            // atomic closers below can check: its premises belong to that
            // disjunct, which the structural closure proves on its own goal.
            if derivation.disjunction_choice().is_some() {
                return None;
            }
            anchored_pairs = crate::kernel::search::ProofSearch::resolve_solve_premises(
                search_input,
                &derivation.context_premises(),
                introduced_surfaces,
            )?;
            let premise_pairs = &anchored_pairs;
            // This rule constructs its checked nonnegative scope directly.
            // Avoid a speculative generic candidate for this same predecessor
            // goal before constructing that scope.
            if let Some(closed) =
                crate::kernel::search::ProofSearch::try_selected_predecessor_upper_bound(
                    search_input,
                    &goal,
                    premise_pairs,
                )
            {
                return Some(closed);
            }
            // The same derivation already failed to check over the premises
            // it cites; the wider context does not translate it either.
            let typed_atomic =
                match crate::kernel::search::ProofSearch::extract_special_conjunct_premises(
                    search_input,
                    &derivation,
                    premise_pairs,
                ) {
                    Ok(Some(extracted)) if extracted.is_complete() => Some(extracted),
                    _ if cited_pairs.is_some() => None,
                    Ok(Some(extracted)) => {
                        crate::kernel::search::ProofSearch::check_typed_atomic_solve_candidate(
                            &(extracted),
                            &goal,
                            &derivation,
                            premise_pairs,
                        )
                    }
                    Ok(None) | Err(()) => {
                        crate::kernel::search::ProofSearch::check_typed_atomic_solve_candidate(
                            search_input,
                            &goal,
                            &derivation,
                            premise_pairs,
                        )
                    }
                };
            typed_atomic
                .or_else(|| {
                    crate::kernel::search::ProofSearch::try_selected_pointer_inequality_rewrite(
                        search_input,
                        &goal,
                        premise_pairs,
                    )
                })
                .or_else(|| {
                    crate::kernel::search::ProofSearch::try_premise_equality_chain_closure(
                        search_input,
                        premise_pairs,
                        RewriteClosers::Selected,
                    )
                    .ok()
                    .flatten()
                })
                .or_else(|| {
                    crate::kernel::search::ProofSearch::try_selected_constant_bound_weakening(
                        search_input,
                        &goal,
                        &derivation,
                    )
                })
                .or_else(|| {
                    search_input.surface_goal().and_then(|surface_goal| {
                        crate::kernel::search::ProofSearch::try_selected_unchanged_load_forall_goal(
                            search_input,
                            surface_goal,
                            premise_pairs,
                        )
                        .or_else(|| {
                            crate::kernel::search::ProofSearch::try_selected_forall_goal(
                                search_input,
                                &goal,
                                surface_goal,
                                premise_pairs,
                            )
                        })
                    })
                })
                .or_else(|| {
                    crate::kernel::search::ProofSearch::try_selected_forall_instantiation(
                        search_input,
                        &goal,
                        premise_pairs,
                    )
                })
                .or_else(|| {
                    crate::kernel::search::ProofSearch::try_selected_disjunction_cases(
                        search_input,
                        premise_pairs,
                    )
                })
        })();
        check_verification_deadline()?;
        if let Some(atomic) = atomic {
            return Ok(Some(atomic));
        }
        if matches!(search_input.context.as_ref(), ProofContext::Pure(_)) {
            for (kernel, surface) in &anchored_pairs {
                let opposite = match kernel {
                    Proposition::ConditionIs(condition, truth) => {
                        Proposition::condition_is(condition.clone(), !truth)
                    }
                    proposition => Proposition::Not(Box::new(proposition.clone())),
                };
                if (search_input.facts().holds_false()
                    || search_input.facts().contains(&opposite)
                    || order_claim_forms(&opposite)
                        .iter()
                        .any(|form| search_input.facts().contains(form))
                    || normalizes_context_free_leaf(&opposite))
                    && let Some(closed) =
                        attempt::candidate_outcome(Self::close_refuted_fact(search_input, surface))?
                {
                    return Ok(Some(closed));
                }
            }
        }
        if let Some(surface_goal) = search_input.surface_goal()
            && let Some(goal) = search_input.goal()
            && !anchored_pairs.is_empty()
        {
            let kernels = anchored_pairs
                .iter()
                .map(|(kernel, _)| kernel.clone())
                .collect::<Vec<_>>();
            // The bounded affine planner first, then simplex for a bound
            // that needs more of the selected premises than it combines.
            for engine in [
                ArithmeticEngine::IntegerAffine,
                ArithmeticEngine::IntegerRefutation,
            ] {
                let Some(plan) = plan_arithmetic(engine, goal, &kernels)
                    .and_then(ArithmeticPlan::integer_affine)
                else {
                    continue;
                };
                if let Some(proof) = attempt::candidate_outcome(Self::apply_integer_composition(
                    search_input,
                    &plan,
                    &anchored_pairs,
                    surface_goal,
                    &[],
                ))?
                .flatten()
                {
                    return Ok(Some(proof));
                }
            }
            check_verification_deadline()?;
        }
        if let Some(anchored) =
            crate::kernel::search::ProofSearch::try_outcome_anchored_order_transitivity(
                search_input,
                &anchored_pairs,
            )
            .or_else(|| {
                crate::kernel::search::ProofSearch::try_outcome_anchored_increment_order(
                    search_input,
                    &anchored_pairs,
                )
            })
        {
            return Ok(Some(anchored));
        }
        // An arithmetic goal the cheap derivations above missed goes to
        // `arithmetic` from premises it selects, before the rewrite, unfold
        // and transport strategies below spend their work in the context's
        // facts.
        if let Some(proof) =
            crate::kernel::search::ProofSearch::try_arithmetic_with_selected_premises(search_input)?
        {
            return Ok(Some(proof));
        }
        if chain_rewrites && let Some(rewritten) = rewrite_chain(allow_function_unfold)? {
            return Ok(Some(rewritten));
        }
        // Indexed rewrite planning uses Option for an ordinary candidate
        // miss; preserve an exhausted budget before trying another closer.
        check_verification_deadline()?;
        if allow_function_unfold
            && let Some(rewritten) =
                crate::kernel::search::ProofSearch::try_introduced_equality_then_function_unfold_closure(search_input, introduced_surfaces)?
        {
            return Ok(Some(rewritten));
        }
        // A recursive call over constants: evaluate it one level at a time.
        if allow_function_unfold
            && let Some(evaluated) =
                crate::kernel::search::ProofSearch::try_ground_recursion_closure(
                    search_input,
                    introduced_surfaces,
                )?
        {
            return Ok(Some(evaluated));
        }
        // A goal over a value a fact equates to a constructor, as a proof
        // `match` arm's case states it: evaluate from a rewrite.
        if allow_function_unfold
            && search_input
                .facts()
                .assumptions()
                .has_algebraic_constructor_facts()
            && let Some(rewritten) =
                crate::kernel::search::ProofSearch::try_constructor_evaluation_closure(
                    search_input,
                    introduced_surfaces,
                )?
        {
            return Ok(Some(rewritten));
        }
        if !super::selected_arithmetic::machine_equality_bridge_active()
            && let Some(target) = search_input.surface_goal()
            && let Some(proof) = Self::try_store_read_rewrite(search_input, target)?
        {
            return Ok(Some(proof));
        }
        if let Some(proof) =
            Self::try_selected_load_equality_bridge(search_input, introduced_surfaces)?
        {
            return Ok(Some(proof));
        }
        if let Some(surface_goal) = search_input.surface_goal()
            && let Some(proof) = crate::kernel::search::ProofSearch::try_state_transport_closure(
                search_input,
                surface_goal,
            )?
        {
            return Ok(Some(proof));
        }
        if let Some(instantiated) =
            crate::kernel::search::ProofSearch::try_indexed_forall_instantiation_with_surfaces(
                search_input,
                introduced_surfaces,
            )
        {
            return Ok(Some(instantiated));
        }
        if let Some(defined) =
            crate::kernel::search::ProofSearch::try_signed_definedness_closure(search_input)?
        {
            return Ok(Some(defined));
        }
        if let Some(eliminated) =
            crate::kernel::search::ProofSearch::try_disjunctive_syllogism_closure(search_input)
        {
            return Ok(Some(eliminated));
        }
        if let Some(guarded) =
            crate::kernel::search::ProofSearch::try_guarded_consequent_closure(search_input)?
        {
            return Ok(Some(guarded));
        }
        // The atomic helpers still classify their internal candidate misses
        // as `Option`; surface a deadline that fired inside them here rather
        // than continuing into structural search with it exceeded.
        check_verification_deadline()?;
        if search_input.surface_goal().is_none()
            && matches!(search_input.goal(), Some(Proposition::And(_, _)))
        {
            return crate::kernel::search::ProofSearch::try_structural_and_solve_closure(
                search_input,
                introduced_surfaces,
            );
        }
        let Some(surface_goal) = search_input.surface_goal().cloned() else {
            return Ok(None);
        };
        if let Some(enumerated) = crate::kernel::search::ProofSearch::try_finite_forall_enumeration(
            search_input,
            &surface_goal,
        )? {
            return Ok(Some(enumerated));
        }
        // A pure goal that its own signed bounds already decide gets the one
        // checked arithmetic step, not a case split over those same
        // bounds. The certificate reads the goal's own bound buckets and
        // emits a single leaf, while the split searches for a pivot and then
        // owes a proof on each arm — including a dead arm closed only by a
        // contradiction between the pivot and a premise. Keep this ahead of
        // the split so the cheaper, smaller expansion wins whenever it
        // applies; the split still runs for everything the certificate
        // declines.
        if let Some(arithmetic) =
            crate::kernel::search::ProofSearch::try_pure_signed_arithmetic(search_input)
        {
            return Ok(Some(arithmetic));
        }
        if let Some(split) = crate::kernel::search::ProofSearch::try_upper_bound_split_closure(
            search_input,
            introduced_surfaces,
        )? {
            return Ok(Some(split));
        }
        // Enter logical binders before looking for function applications.
        // An application below `forall (x)` cannot be checked until `intro`
        // has associated the surface name `x` with its fresh kernel variable.
        // The recursive structural call retains that checked `Intro` step and
        // then discovers applications in the now-focused body goal.
        // A conjunction already missed the same structural closure above;
        // no proof step has been applied since, so it would miss again.
        if !structural_conjunction_tried
            && let Some(structural) = crate::instrumentation::measure_operation(
                "surface",
                "solve closure",
                "solve closure: structural",
                || {
                    crate::kernel::search::ProofSearch::try_structural_solve_closure_with_surfaces(
                        search_input,
                        &surface_goal,
                        introduced_surfaces,
                    )
                },
            )?
        {
            return Ok(Some(structural));
        }
        if allow_function_unfold
            && let Some(unfolded) =
                crate::kernel::search::ProofSearch::try_function_unfold_solve_closure(
                    search_input,
                    introduced_surfaces,
                )?
        {
            return Ok(Some(unfolded));
        }
        // A Special fact such as `aligned(p + i, 8)` is not generally a
        // solve-derivation: the kernel's pointer rule consumes a matching
        // alignment/relation fact directly. Use the selected pairs when
        // `close() using` supplied them; otherwise recover only typed Special
        // candidates from the recorded Surface map for generic `close()`.
        if let Some(surface_goal) = search_input.surface_goal()
            && let Some(goal) = search_input.goal()
        {
            let special_pairs = if !anchored_pairs.is_empty() {
                anchored_pairs.clone()
            } else {
                let (surface_facts, premise_anchor) = match search_input.context.as_ref() {
                    ProofContext::Pure(context) => {
                        (&context.theorem_context.surface_requirements, None)
                    }
                    ProofContext::FixedState(context) => (
                        context.surface_propositions,
                        context.premise_anchor.as_ref(),
                    ),
                    ProofContext::Execution(_) => {
                        if let Some(data) = search_input.focused_outcome_data() {
                            (&data.surface_propositions, data.premise_anchor.as_ref())
                        } else {
                            let Some(execution) = search_input.execution() else {
                                return Ok(None);
                            };
                            (&execution.presentation.surface_propositions, None)
                        }
                    }
                };
                search_input
                    .facts()
                    .special_candidates_mentioning(goal)
                    .into_iter()
                    .filter(|premise| {
                        matches!(&premise, condition_source_0 @ Proposition::ConditionIs(
                                _,
                                true
                            ) if matches!(condition_source_0.old_condition(), Some((OldConditionTerm::Compare {
                                    format: MachineIntegerType::Int64,
                                    relation: CompareRelation::Equal,
                                    ..
                                } | OldConditionTerm::PointerEqual(..)
                                    | OldConditionTerm::AddressEqual(..)
                                    | OldConditionTerm::AddressOffsetEqual(..)
                                    | OldConditionTerm::Float32(FloatCondition::Classification { .. })
                                    | OldConditionTerm::Float64(FloatCondition::Classification { .. }), _))))
                    })
                    .chain(crate::kernel::search::ProofSearch::select_arithmetic_bound(
                        search_input.facts().assumptions(),
                        goal,
                    ))
                    .filter_map(|premise| {
                        crate::kernel::search::ProofSearch::available_surface_fact(
                            search_input,
                            surface_facts,
                            premise_anchor,
                            &premise,
                        )
                        .map(|surface| (premise.clone(), surface))
                    })
                    .collect::<Vec<_>>()
            };
            let kernels = special_pairs
                .iter()
                .map(|(kernel, _)| kernel.clone())
                .collect::<Vec<_>>();
            let surfaces = special_pairs
                .iter()
                .map(|(_, surface)| surface.clone())
                .collect::<Vec<_>>();
            if let Some(plan) = plan_arithmetic(ArithmeticEngine::Special, goal, &kernels)
                .and_then(ArithmeticPlan::special)
            {
                let certificate = special_plan_to_surface(&plan, &surfaces, surface_goal);
                let signed_width = certificate.nodes.iter().find_map(|n| {
                    if let SpecialArithmeticNode::SignedDefined { width, .. } = n {
                        Some(*width)
                    } else {
                        None
                    }
                });
                if let Some(width) = signed_width {
                    if let Some(proof) =
                        Self::try_signed_definedness_bounds(search_input, width, surfaces)?
                    {
                        return Ok(Some(proof));
                    }
                } else if let Some(proof) =
                    Self::apply_specialized_composition(search_input, &certificate)?
                {
                    return Ok(Some(proof));
                }
            }
        }
        // Signed arithmetic over the selected premises is the final
        // fallback. All established equality, transport, quantifier,
        // structural, and function-unfold routes must get first choice so
        // their selected proof steps remain visible in expansion. Population
        // comparisons already tried indexed bounds before memory rewriting;
        // pure arithmetic ran ahead of the case split it would hide behind.
        if let Some(surface_goal) = search_input.surface_goal()
            && let Some(goal) = search_input.goal()
            && !anchored_pairs.is_empty()
            && let Some(plan) = plan_arithmetic(
                ArithmeticEngine::SignedInt32,
                goal,
                &anchored_pairs
                    .iter()
                    .map(|(kernel, _)| kernel.clone())
                    .collect::<Vec<_>>(),
            )
            .and_then(ArithmeticPlan::signed_int32)
            && let Some(certificate) =
                search_input.signed_plan_to_surface(&plan, &anchored_pairs, surface_goal)
            && let Ok(Some(proof)) =
                Self::apply_signed_interval_composition(search_input, &certificate)
        {
            return Ok(Some(proof));
        }
        if !indexed_arithmetic_tried
            && let Some(arithmetic) = crate::instrumentation::measure_operation(
                "surface",
                "solve closure",
                "solve closure: indexed bounds",
                || {
                    crate::kernel::search::ProofSearch::try_execution_signed_arithmetic(
                        search_input,
                    )
                },
            )
        {
            return Ok(Some(arithmetic));
        }
        // The pure signed certificate already ran above on this same proof
        // state; repeating it here would redo identical work for an
        // identical answer.
        check_verification_deadline()?;
        Ok(None)
    }

    /// Select signed bounds only from the goal variables' persistent buckets.
    /// This is a smart query; the resulting certificate checks every premise.
    pub(in crate::surface::proof) fn try_pure_signed_arithmetic(
        search_input: &Proof<'a>,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_pure_signed_arithmetic");
        let ProofContext::Pure(context) = search_input.context.as_ref() else {
            return None;
        };
        crate::kernel::search::ProofSearch::try_indexed_signed_arithmetic(
            search_input,
            &context.theorem_context.surface_requirements,
            None,
        )
    }

    /// The same indexed bound selection on an execution proof: at function
    /// exit, at a statement frontier, or inside a loop phase, so solve reads a
    /// variable's bounds the same way wherever it runs. A bound can also be
    /// the negation of a branch condition. A goal that is itself an available
    /// fact is left to `known`. Pre-return signed orders and population
    /// bounds run before broad premise raising, preferring named rules on
    /// the selected premises; other goals retain the final fallback.
    pub(in crate::surface::proof) fn try_execution_signed_arithmetic(
        search_input: &Proof<'a>,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_execution_signed_arithmetic");
        let goal = search_input.goal()?;
        if std::iter::once(goal.clone())
            .chain(condition_polarity_forms(goal))
            .any(|form| search_input.facts().contains(&form))
        {
            return None;
        }
        let (surfaces, anchor) = match search_input.context.as_ref() {
            ProofContext::Pure(_) => return None,
            ProofContext::FixedState(context) => {
                (context.surface_propositions, context.premise_anchor.clone())
            }
            ProofContext::Execution(_) => match search_input.focused_outcome_data() {
                Some(data) => (&data.surface_propositions, data.premise_anchor.clone()),
                None => (
                    &search_input.execution()?.surface_propositions,
                    search_input.execution().and_then(frontier_premise_anchor),
                ),
            },
        };
        crate::kernel::search::ProofSearch::try_indexed_signed_arithmetic(
            search_input,
            surfaces,
            anchor.as_ref(),
        )
    }

    /// An equality of two machine integers from the two opposite order facts
    /// on them, `l <= r` and `r <= l` in any spelling: an `arithmetic()
    /// using` step citing just those two facts. The signed `int32` order has
    /// its own named rules; this covers `uint32` and both 64-bit orders, which
    /// the atomic derivation does not combine into an equality. Each
    /// candidate fact is one exact index lookup per spelling, so the route
    /// costs a fixed number of lookups per goal.
    pub(in crate::surface::proof) fn try_equality_from_opposite_bounds(
        search_input: &Proof<'a>,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_equality_from_opposite_bounds");
        // Each candidate is the two opposite orders, each with whether it
        // holds of every value: `0 <= x` in an unsigned order, which no
        // fact states and the step's own range reasoning supplies.
        let zero =
            |term: &OldMachineTerm| term.as_const() == Some(0) || term.uint64_as_const() == Some(0);
        let pairs = match search_input.goal()? {
            condition_source_0 @ Proposition::ConditionIs(_, true)
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
                let (left, right) = (left.as_ref().clone(), right.as_ref().clone());
                vec![(
                    (
                        OldConditionTerm::unsigned_less_equal(left.clone(), right.clone()),
                        zero(&left),
                    ),
                    (
                        OldConditionTerm::unsigned_less_equal(right.clone(), left.clone()),
                        zero(&right),
                    ),
                )]
            }
            condition_source_0 @ Proposition::ConditionIs(_, true)
                if let Some((
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::Int64,
                        relation: CompareRelation::Equal,
                        left,
                        right,
                    },
                    _,
                )) = condition_source_0.old_condition() =>
            {
                let (left, right) = (left.as_ref().clone(), right.as_ref().clone());
                vec![
                    (
                        (
                            OldConditionTerm::int64_signed_less_equal(left.clone(), right.clone()),
                            false,
                        ),
                        (
                            OldConditionTerm::int64_signed_less_equal(right.clone(), left.clone()),
                            false,
                        ),
                    ),
                    (
                        (
                            OldConditionTerm::uint64_less_equal(left.clone(), right.clone()),
                            zero(&left),
                        ),
                        (
                            OldConditionTerm::uint64_less_equal(right.clone(), left.clone()),
                            zero(&right),
                        ),
                    ),
                ]
            }
            _ => return None,
        };
        let available = |condition: OldConditionTerm| {
            let fact = Proposition::condition_is(condition, true);
            std::iter::once(fact.clone())
                .chain(crate::surface::proof::order_claim_forms(&fact))
                .find(|form| search_input.facts().contains(form))
        };
        let (surfaces, anchor) = match search_input.context.as_ref() {
            ProofContext::Pure(_) => (None, None),
            ProofContext::FixedState(context) => (
                Some(context.surface_propositions),
                context.premise_anchor.clone(),
            ),
            ProofContext::Execution(_) => match search_input.focused_outcome_data() {
                Some(data) => (
                    Some(&data.surface_propositions),
                    data.premise_anchor.clone(),
                ),
                None => (
                    Some(&search_input.execution()?.surface_propositions),
                    search_input.execution().and_then(frontier_premise_anchor),
                ),
            },
        };
        for ((lower, lower_total), (upper, upper_total)) in pairs {
            let mut facts = Vec::new();
            let mut missing = false;
            for (condition, total) in [(lower, lower_total), (upper, upper_total)] {
                match available(condition) {
                    Some(fact) => facts.push(fact),
                    None if total => {}
                    None => missing = true,
                }
            }
            if missing || facts.is_empty() {
                continue;
            }
            let spelled = facts
                .iter()
                .map(|fact| match surfaces {
                    Some(surfaces) => crate::kernel::search::ProofSearch::available_surface_fact(
                        search_input,
                        surfaces,
                        anchor.as_ref(),
                        fact,
                    )
                    .or_else(|| search_input.raised_comparison_surface(fact)),
                    None => search_input.raised_comparison_surface(fact),
                })
                .collect::<Option<Vec<_>>>();
            if let Some(spelled) = spelled {
                if search_input.surface_goal().is_none() {
                    // The order law's written operands also name its equality
                    // conclusion, even for a generated outcome obligation.
                    let SyntaxProposition::Comparison { left, right, .. } =
                        surface_comparison_with_anchored_operands(&spelled[0])
                    else {
                        continue;
                    };
                    let equality = SyntaxProposition::Comparison {
                        left,
                        operator: ComparisonOperator::Equal,
                        right,
                    };
                    let Ok(scope) = search_input.driver().open_have(equality) else {
                        continue;
                    };
                    if let Some(closed) = scope.driver().try_restricted_solve_closure(&spelled)
                        && let Ok(joined) = closed.join()
                        && let Ok(closed) = joined.driver().apply_step(ProofStep::Known)
                    {
                        return Some(closed);
                    }
                } else if let Ok(proof) = Self::apply_arithmetic_using(search_input, &spelled) {
                    return Some(proof);
                }
            }
        }
        None
    }

    /// The facts the indexed signed arithmetic route plans over: the bounds
    /// reachable from the goal's variables, and with `with_equalities` the
    /// equalities naming them too, followed to their own variables. Each
    /// visited variable costs its indexed bound entries and, with
    /// equalities, one indexed lookup of the facts that mention it.
    pub(in crate::surface::proof) fn indexed_arithmetic_premises(
        search_input: &Proof<'a>,
        goal: &Proposition,
        with_equalities: bool,
    ) -> (Vec<Proposition>, bool) {
        #[cfg(test)]
        crate::kernel::search::record_discovery("indexed_arithmetic_premises");
        let mut available = BTreeSet::new();
        let mut has_equalities = false;
        let mut visited = BTreeSet::new();
        let unsigned_goal = crate::surface::checking::is_unsigned_order_goal(goal);
        // Count lowering can leave a read expression where the bounds index
        // names its registered load variable. Seed from that canonical value,
        // not from variables in the read's address or memory state.
        let canonical_goal = crate::kernel::canonical_condition_fact(goal);
        let mut pending = crate::kernel::proposition_variables(&canonical_goal)
            .into_iter()
            .collect::<std::collections::VecDeque<_>>();
        while let Some(variable) = pending.pop_front() {
            if visited.len() == MAX_BOUND_VARIABLES {
                break;
            }
            if !visited.insert(variable) {
                continue;
            }
            let assumptions = search_input.facts().assumptions();
            let term = OldMachineTerm::Variable(variable);
            // A `uint32` goal's bounds are `uint32` orders, filed in their
            // own index.
            let entries = assumptions
                .signed_order_bound_entries(&term)
                .map(|entry| (MachineIntegerType::Int32, entry))
                .chain(
                    unsigned_goal
                        .then(|| assumptions.uint32_order_bound_entries(&term))
                        .into_iter()
                        .flatten()
                        .map(|entry| (MachineIntegerType::UInt32, entry)),
                )
                .collect::<Vec<_>>();
            for (format, (endpoint, other, strict, forward)) in entries {
                let (left, right) = if forward {
                    (endpoint, other)
                } else {
                    (other, endpoint)
                };
                let condition = OldConditionTerm::Compare {
                    format,
                    relation: if strict {
                        CompareRelation::LessThan
                    } else {
                        CompareRelation::LessEqual
                    },
                    left: Box::new(left),
                    right: Box::new(right),
                };
                let fact = Proposition::condition_is(condition, true);
                let mut found = false;
                for form in std::iter::once(fact.clone()).chain(condition_polarity_forms(&fact)) {
                    if search_input.facts().contains(&form) {
                        available.insert(form);
                        found = true;
                    }
                }
                if found {
                    pending.extend(
                        crate::kernel::proposition_variables(
                            &crate::kernel::canonical_condition_fact(&fact),
                        )
                        .into_iter()
                        .filter(|next| !visited.contains(next)),
                    );
                }
            }
            // An equality names the variable through another: a call's
            // `o.size == old(o.size) + 1` relates the goal's field to the
            // entry value its bounds name.
            if !with_equalities {
                continue;
            }
            let equalities = search_input
                .facts()
                .assumptions()
                .condition_facts_mentioning_variable(variable)
                .into_iter()
                .flatten()
                .filter(|(condition, value)| {
                    *value
                        && matches!(
                            condition,
                            OldConditionTerm::Compare {
                                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                                relation: CompareRelation::Equal,
                                ..
                            }
                        )
                })
                .map(|(condition, _)| Proposition::condition_is(condition.clone(), true))
                // A load's defining equation only names that same value.
                // It adds no arithmetic relation, and following its memory
                // term would pull unrelated address variables into the search.
                .filter(|fact| !crate::kernel::is_load_variable_defining_fact(fact))
                .collect::<Vec<_>>();
            for fact in equalities {
                if !search_input.facts().contains(&fact) {
                    continue;
                }
                has_equalities = true;
                pending.extend(
                    crate::kernel::proposition_variables(&crate::kernel::canonical_condition_fact(
                        &fact,
                    ))
                    .into_iter()
                    .filter(|next| !visited.contains(next)),
                );
                available.insert(fact);
            }
        }
        (available.into_iter().collect(), has_equalities)
    }

    /// Selects the bounds reachable from the goal's variables: each goal
    /// variable's bounds, then the bounds on the variables those bounds
    /// name (`i < n` leads to `n`'s bounds), breadth-first in variable order,
    /// visiting at most [`MAX_BOUND_VARIABLES`] variables. Each visited
    /// variable costs one O(log n) bucket lookup and one indexed membership
    /// test per bound it lists; a leaf conjunct of a fact is itself an
    /// indexed fact, so a bound written inside a conjunction needs no
    /// `have`. Literal bounds on the goal variables are tried first, so
    /// unrelated relational claims do not crowd out those operands' ranges.
    /// The certificate is planned over the kernel facts before any
    /// of them is spelled, so a goal the bounds do not decide is declined
    /// without surface work.
    pub(in crate::surface::proof) fn try_indexed_signed_arithmetic(
        search_input: &Proof<'a>,
        surfaces: &SurfacePropositionMap,
        anchor: Option<&ProgramPointRef>,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_indexed_signed_arithmetic");
        let goal = search_input.goal()?;
        let surface_goal = search_input.surface_goal()?;
        let is_pure = matches!(search_input.context.as_ref(), ProofContext::Pure(_));
        // A `uint32` order chain is an atomic derivation over the goal
        // variables' `uint32` bounds (`x <u n`, `n <=u 4`): its recorded
        // order path is closed by Integer arithmetic over the path's
        // premises, the bounds selected here and nothing else.
        if !is_pure
            && crate::surface::checking::is_unsigned_order_goal(goal)
            && let Some(closed) =
                crate::kernel::search::ProofSearch::try_indexed_unsigned_order_chain(
                    search_input,
                    surfaces,
                    anchor,
                    goal,
                )
        {
            return Some(closed);
        }
        // A variable's literal bounds can settle the goal without admitting
        // every earlier relational claim on that variable to the planner's
        // bounded premise slice. Keep that slice local even in a contract
        // with hundreds of independently checked outcomes.
        let mut available =
            indexed_constant_arithmetic_premises(search_input.facts().assumptions(), goal);
        let compact_plan = plan_arithmetic(ArithmeticEngine::SignedInt32, goal, &available)
            .and_then(ArithmeticPlan::signed_int32);
        // If the literal bounds miss, retain the existing relational-bound
        // and equality routes.
        if compact_plan.is_none() {
            available = crate::kernel::search::ProofSearch::indexed_arithmetic_premises(
                search_input,
                goal,
                false,
            )
            .0;
        }
        let plan = if let Some(plan) = compact_plan.or_else(|| {
            plan_arithmetic(ArithmeticEngine::SignedInt32, goal, &available)
                .and_then(ArithmeticPlan::signed_int32)
        }) {
            plan
        } else {
            let (expanded, has_equalities) =
                crate::kernel::search::ProofSearch::indexed_arithmetic_premises(
                    search_input,
                    goal,
                    true,
                );
            // Without a selected equality, the second traversal follows the
            // same bounds graph and cannot change the first planning miss.
            if !has_equalities {
                return None;
            }
            available = expanded;
            plan_arithmetic(ArithmeticEngine::SignedInt32, goal, &available)
                .and_then(ArithmeticPlan::signed_int32)?
        };
        let planned_premises = available.len();
        let mut pairs = Vec::new();
        for fact in available {
            let source = crate::kernel::search::ProofSearch::available_surface_fact(
                search_input,
                surfaces,
                anchor,
                &fact,
            )
            .or_else(|| (!is_pure).then(|| search_input.raised_comparison_surface(&fact))?);
            if let Some(source) = source {
                pairs.push((fact, source));
            }
        }
        let kernels = pairs
            .iter()
            .map(|(fact, _)| fact.clone())
            .collect::<Vec<_>>();
        // Preserve the existing named-rule expansion when these selected
        // bounds support it. Searching this compact context avoids spelling
        // the entire ambient atomic component merely to recover that rule.
        if !is_pure
            && let Some(SolveEvidence::Derivation(derivation)) =
                plan_solve_certificate(goal, &assumptions_from_propositions(&kernels))
            && let Some(closed) =
                crate::kernel::search::ProofSearch::check_typed_atomic_solve_candidate(
                    search_input,
                    goal,
                    &derivation,
                    &pairs,
                )
        {
            return Some(closed);
        }
        let plan = if kernels.len() == planned_premises {
            plan
        } else {
            plan_arithmetic(ArithmeticEngine::SignedInt32, goal, &kernels)
                .and_then(ArithmeticPlan::signed_int32)?
        };
        let certificate = search_input.signed_plan_to_surface(&plan, &pairs, surface_goal)?;
        Self::apply_signed_interval_composition(search_input, &certificate)
            .ok()
            .flatten()
    }

    /// [`Self::try_indexed_signed_arithmetic`]'s route for a `uint32` order
    /// goal: the goal variables' `uint32` bounds, spelled, and the named
    /// rule or recorded order path a derivation over exactly those selects.
    pub(in crate::surface::proof) fn try_indexed_unsigned_order_chain(
        search_input: &Proof<'a>,
        surfaces: &SurfacePropositionMap,
        anchor: Option<&ProgramPointRef>,
        goal: &Proposition,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_indexed_unsigned_order_chain");
        let available = crate::kernel::search::ProofSearch::indexed_arithmetic_premises(
            search_input,
            goal,
            false,
        )
        .0;
        let mut pairs = Vec::new();
        for fact in available {
            let source = crate::kernel::search::ProofSearch::available_surface_fact(
                search_input,
                surfaces,
                anchor,
                &fact,
            )
            .or_else(|| search_input.raised_comparison_surface(&fact));
            if let Some(source) = source {
                pairs.push((fact, source));
            }
        }
        let kernels = pairs
            .iter()
            .map(|(fact, _)| fact.clone())
            .collect::<Vec<_>>();
        let Some(SolveEvidence::Derivation(derivation)) =
            plan_solve_certificate(goal, &assumptions_from_propositions(&kernels))
        else {
            return None;
        };
        crate::kernel::search::ProofSearch::check_typed_atomic_solve_candidate(
            search_input,
            goal,
            &derivation,
            &pairs,
        )
    }

    /// Select only guards actually occurring in the goal, through indexed
    /// fact/source lookups. The emitted simple step checks every selection.
    pub(in crate::surface::proof) fn try_goal_conditional_closure(
        search_input: &Proof<'a>,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_goal_conditional_closure");
        // Select guards by exact indexed lookup from the written expression.
        // After ordinary arm rewrites, ambient solve can select the arithmetic
        // bounds of the newly exposed operands. Restricted solve instead keeps
        // its original explicit source list throughout the same rewrite prefix.
        if let Some(SyntaxProposition::Comparison { left, right, .. }) = search_input
            .surface_goal()
            .and_then(integer_composition::canonical_surface)
        {
            let mathematical = search_input
                .goal()
                .is_some_and(|goal| integer_affine_claim(goal).is_some());
            let mut remaining = 4096;
            let candidates = machine_bridges::conditional_candidates(
                &left,
                &right,
                mathematical,
                &mut remaining,
            )
            .ok()?;
            let mut selected = Vec::new();
            for (expression, _) in candidates {
                let SyntaxTerm::If { condition, .. } = expression else {
                    unreachable!("conditional candidate");
                };
                for guard in [
                    condition.as_ref().clone(),
                    SyntaxProposition::Not(condition.clone()),
                ] {
                    let kernel = search_input
                        .lower_cited_surface_proposition(&guard, "conditional goal guard")
                        .ok()?;
                    if search_input.facts().pure_known_available(&kernel)
                        || crate::surface::planning::solve::computes_with_known(&kernel)
                    {
                        selected.push(guard);
                    }
                }
            }
            if !selected.is_empty()
                && let Ok(Some((rewritten, _))) =
                    Self::rewrite_conditional_arms_using(search_input, &selected)
            {
                if rewritten.focused_discharged() {
                    return Some(rewritten);
                }
                if let Some(closed) = Self::try_solve_closure(&rewritten).ok().flatten() {
                    return Some(closed);
                }
            }
        }
        if matches!(&search_input.goal(), Some(condition_source_0 @ Proposition::ConditionIs(
                _,
                true
            )) if matches!(condition_source_0.old_condition(), Some((OldConditionTerm::AddressEqual(..) | OldConditionTerm::PointerEqual(..), _))))
            && let Ok(Some(proof)) = Self::try_local_checked_closure(search_input, Some(Vec::new()))
            && proof.is_complete()
        {
            return Some(proof);
        }
        let guards = crate::kernel::proof::term_rewrite::TermRewrite::conditional_guards(
            search_input.goal()?,
        );
        let frontier_anchor = match search_input.context.as_ref() {
            ProofContext::Execution(_) if search_input.focused_outcome_data().is_none() => {
                search_input.execution().and_then(frontier_premise_anchor)
            }
            _ => None,
        };
        let (surfaces, anchor) = match search_input.context.as_ref() {
            ProofContext::Pure(context) => (&context.theorem_context.surface_requirements, None),
            ProofContext::FixedState(context) => (
                context.surface_propositions,
                context.premise_anchor.as_ref(),
            ),
            ProofContext::Execution(_) => match search_input.focused_outcome_data() {
                Some(data) => (&data.surface_propositions, data.premise_anchor.as_ref()),
                None => (
                    &search_input.execution()?.surface_propositions,
                    frontier_anchor.as_ref(),
                ),
            },
        };
        // The written goal retains nominal field places that the imported
        // scalar execution expression can spell only as a lowered index.
        // Cite its own conditional guards before reconstructing a premise
        // from execution syntax, so printing preserves that field's type.
        let written_guards = match search_input.surface_goal() {
            Some(SyntaxProposition::Comparison { left, right, .. }) => [left, right]
                .into_iter()
                .filter_map(|expression| match expression {
                    SyntaxTerm::If { condition, .. } => Some(condition.as_ref().clone()),
                    _ => None,
                })
                .flat_map(|condition| {
                    [
                        condition.clone(),
                        SyntaxProposition::Not(Box::new(condition)),
                    ]
                })
                .filter_map(|surface| {
                    let lowered = search_input
                        .lower_surface_proposition_direct(&surface, "conditional goal guard")
                        .ok()?;
                    Some((lowered, surface))
                })
                .collect::<Vec<_>>(),
            _ => Vec::new(),
        };
        let mut premises = Vec::new();
        let mut selected = BTreeSet::new();
        for condition in guards {
            for value in [true, false] {
                let fact = Proposition::condition_is(condition.clone(), value);
                if !search_input.facts().contains(&fact)
                    && !condition_polarity_forms(&fact)
                        .iter()
                        .any(|form| search_input.facts().contains(form))
                {
                    continue;
                }
                let surface = written_guards
                    .iter()
                    .find(|(lowered, _)| {
                        *lowered == fact || condition_polarity_equivalent(lowered, &fact)
                    })
                    .map(|(_, surface)| surface.clone())
                    .or_else(|| {
                        crate::kernel::search::ProofSearch::available_surface_fact(
                            search_input,
                            surfaces,
                            anchor,
                            &fact,
                        )
                    })
                    .or_else(|| {
                        condition_polarity_forms(&fact).iter().find_map(|form| {
                            crate::kernel::search::ProofSearch::available_surface_fact(
                                search_input,
                                surfaces,
                                anchor,
                                form,
                            )
                        })
                    });
                if let Some(surface) = surface
                    && selected.insert(fact)
                {
                    premises.push(surface);
                }
            }
        }
        if premises.is_empty() {
            return None;
        }
        // Selecting an arm and proving arithmetic in it are separate simple
        // steps. Check the arm equation from its stated guard, then
        // rewrite the goal before ordinary arithmetic composes its proof.
        let SyntaxProposition::Comparison { left, right, .. } = search_input.surface_goal()? else {
            return None;
        };
        for expression in [left, right] {
            let SyntaxTerm::If {
                condition,
                then_branch,
                else_branch,
            } = expression
            else {
                continue;
            };
            for (guard, branch) in [
                (condition.as_ref().clone(), then_branch),
                (SyntaxProposition::Not(condition.clone()), else_branch),
            ] {
                let kernel = search_input
                    .lower_cited_surface_proposition(&guard, "conditional arm")
                    .ok()?;
                if !search_input.facts().contains(&kernel) {
                    continue;
                }
                let equality = SyntaxProposition::Comparison {
                    left: expression.clone(),
                    operator: ComparisonOperator::Equal,
                    right: branch.as_ref().clone(),
                };
                let Ok(equation) =
                    search_input
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
                    .apply_step(ProofStep::Rewrite(equality))
                    .ok()?;
                if rewritten.goal() == search_input.goal() {
                    continue;
                }
                if let Some(closed) = Self::try_solve_closure(&rewritten).ok().flatten() {
                    return Some(closed);
                }
            }
        }
        Self::try_local_checked_closure(search_input, Some(premises))
            .ok()
            .flatten()
    }

    /// Uses one explicitly supplied equality before unfolding applications in
    /// the rewritten goal. Loop preservation supplies its entry invariants in
    /// this list: rewriting through that checked premise first changes a
    /// function-entry comparison into the smaller loop-entry frame that the
    /// defining equation can expose.
    pub(in crate::surface::proof) fn try_introduced_equality_then_function_unfold_closure(
        search_input: &Proof<'a>,
        introduced_surfaces: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery(
            "try_introduced_equality_then_function_unfold_closure",
        );
        for surface in introduced_surfaces {
            for oriented in
                std::iter::once(surface.clone()).chain(reverse_surface_equality(surface))
            {
                let Some(rewritten) = attempt::candidate_outcome(
                    search_input
                        .driver()
                        .apply_step(ProofStep::Rewrite(oriented)),
                )?
                else {
                    continue;
                };
                if let Some(closed) =
                    crate::kernel::search::ProofSearch::try_direct_logical_closure(&(rewritten))?
                {
                    return Ok(Some(closed));
                }
                if let Some(closed) =
                    crate::kernel::search::ProofSearch::try_function_unfold_solve_closure(
                        &(rewritten),
                        introduced_surfaces,
                    )?
                {
                    return Ok(Some(closed));
                }
            }
        }
        Ok(None)
    }

    /// Tries the finite set of function applications already present in the
    /// current surface goal. Each accepted candidate is a normal checked
    /// `unfold` step. The recursive simplification attempt disables further
    /// function unfolding, so recursive definitions cannot turn this smart
    /// tactic into unbounded evaluation.
    pub(in crate::surface::proof) fn try_function_unfold_solve_closure(
        search_input: &Proof<'a>,
        introduced_surfaces: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_function_unfold_solve_closure");
        // The structural closer introduces these binders and searches their
        // bodies with the guard or fresh variable available. Unfolding the
        // whole binder would repeat that same search for every candidate.
        if matches!(
            search_input.goal(),
            Some(Proposition::Implies(..) | Proposition::ForAll { .. })
        ) {
            return Ok(None);
        }
        let Some(_scope) = SolveFallbackScope::enter(SolveFallback::FunctionUnfold) else {
            return Ok(None);
        };
        let Some(surface_goal) = search_input.surface_goal() else {
            return Ok(None);
        };
        let applications =
            pure_theorems::click_function_applications(surface_goal, introduced_surfaces);
        if applications.is_empty() {
            return Ok(None);
        }
        // A recursion over constants is evaluated one level at a time before
        // anything unfolds in this goal, whose size each unfold would grow.
        if let Some(evaluated) = crate::kernel::search::ProofSearch::try_ground_recursion_closure(
            search_input,
            introduced_surfaces,
        )? {
            return Ok(Some(evaluated));
        }
        let mut unfolded_any = false;
        let mut proof = search_input.clone();
        for application in applications {
            let attempted = proof
                .driver()
                .apply_step(ProofStep::UnfoldFunction(application));
            let Some(unfolded) = attempt::candidate_outcome(attempted)? else {
                continue;
            };
            proof = unfolded;
            unfolded_any = true;
            // The unfold can close the goal itself: the refreshed goal may
            // already be an available fact, which leaves no goal to search.
            if proof.is_complete() {
                return Ok(Some(proof));
            }
            if let Some(closed) =
                crate::kernel::search::ProofSearch::try_direct_logical_closure(&(proof))?
            {
                return Ok(Some(closed));
            }
            // A recursive definition over a known constructor exposes its
            // recursive call on a smaller argument. Evaluate those calls to a
            // fixed fuel before searching.
            if let Some(closed) =
                crate::kernel::search::ProofSearch::try_constructor_evaluation_closure(
                    &(proof),
                    introduced_surfaces,
                )?
            {
                return Ok(Some(closed));
            }
            if let Some(closed) = crate::kernel::search::ProofSearch::try_solve_closure_after_direct_with_surfaces_and_function_unfold(&(proof),
                    false,
                    introduced_surfaces,
                    false,
                )?
            {
                return Ok(Some(closed));
            }
        }
        // No application unfolds as it stands, as when its argument is a
        // variable a fact equates to a constructor: evaluate from a rewrite.
        if !unfolded_any {
            return crate::kernel::search::ProofSearch::try_constructor_evaluation_closure(
                search_input,
                introduced_surfaces,
            );
        }
        Ok(None)
    }

    /// Evaluate a recursive call over constants, such as a byte copy
    /// `output_from(lit, 0u64, 13)` that a fact or the goal names, one level
    /// at a time. Each level is a `have` that the call equals the arm of its
    /// definition that constant guards select, `output_from(lit, 0u64, 13) ==
    /// List::Cons(lit[0u64], output_from(lit, 0u64 + 1u64, 13 - 1))`, proved
    /// by `unfold` and `close()`; the next level is the arm's recursive call
    /// with its constants evaluated. Each `have` has the size of one level,
    /// so the evaluation is linear in its depth, unlike unfolding in the goal,
    /// which lowers the growing goal at each step. After the last level the
    /// goal is closed from the equations, without this strategy. At most
    /// `MAX_GROUND_RECURSION_LEVELS` levels.
    pub(in crate::surface::proof) fn try_ground_recursion_closure(
        search_input: &Proof<'a>,
        introduced_surfaces: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_ground_recursion_closure");
        // Closing the goal after an evaluation runs `solve` again, which must
        // not evaluate again.
        let Some(_scope) = SolveFallbackScope::enter(SolveFallback::GroundRecursion) else {
            return Ok(None);
        };
        let functions = search_input.spec_functions();
        let Some(surface_goal) = search_input.surface_goal() else {
            return Ok(None);
        };
        // The goal and the facts connected to it, where a postcondition names
        // the call: `out.write_history == List::Cons(.. output_from(..) ..)`
        // or `result == f(..) or result < 0`.
        let mut surfaces = vec![surface_goal.clone()];
        if let Some(goal) = search_input.goal()
            && let Some(facts) = crate::kernel::search::proposition_search::connected_facts(
                search_input.facts().assumptions(),
                goal,
            )
        {
            for equality in facts.iter().take(CONSTRUCTOR_EVALUATION_FACTS) {
                // A call under a quantifier is over its bound variable, not
                // constants.
                if matches!(
                    equality,
                    crate::kernel::Proposition::ForAll { .. }
                        | crate::kernel::Proposition::Exists { .. }
                ) {
                    continue;
                }
                if let Some((_, surface)) =
                    crate::kernel::search::ProofSearch::resolve_solve_premises(
                        search_input,
                        std::slice::from_ref(equality),
                        &[],
                    )
                    .and_then(|mut spelled| spelled.pop())
                {
                    surfaces.push(surface);
                }
            }
        }
        // Every distinct call over constants the goal or those facts name,
        // such as both the output and the length a postcondition states.
        // Each is evaluated at the point a fact names it, if any.
        let mut applications = Vec::new();
        for surface in &surfaces {
            for application in pure_theorems::click_function_applications(surface, &[]) {
                if pure_theorems::largest_constant_argument(&application) > 0
                    && !applications
                        .iter()
                        .any(|(_, known): &(_, ClickFunctionApplication)| *known == application)
                {
                    let point = pure_theorems::application_point(surface, &application);
                    applications.push((point, application));
                }
            }
        }
        let mut proof = search_input.clone();
        let mut levels = 0;
        let mut evaluated_any = false;
        for (point, application) in applications {
            let at_point = |expression: SyntaxTerm| match &point {
                Some(selector) => SyntaxTerm::At {
                    selector: selector.clone(),
                    expression: Box::new(expression),
                },
                None => expression,
            };
            // The levels down to the base, read from the definition alone.
            let mut chain = Vec::new();
            let mut current = Some(application.clone());
            while let Some(call) = current {
                levels += 1;
                if levels > MAX_GROUND_RECURSION_LEVELS {
                    attempt::record_search_note(
                        "ground recursion evaluation",
                        format!(
                            "budget exhausted: {MAX_GROUND_RECURSION_LEVELS} levels of `{}`",
                            call.name
                        ),
                    );
                    return Ok(None);
                }
                check_verification_deadline()?;
                let Some((arm, next)) = pure_theorems::ground_recursion_level(functions, &call)
                else {
                    chain.clear();
                    break;
                };
                chain.push((call, arm));
                current = next;
            }
            let Some(value) = pure_theorems::ground_recursion_value(&application.name, &chain)
            else {
                continue;
            };
            // One `have` for the call's value, proved from one `have` per
            // level inside it: only the value joins the proof.
            let call_value = SyntaxProposition::Comparison {
                left: at_point(SyntaxTerm::Call {
                    name: application.name.clone(),
                    arguments: application.arguments.clone(),
                }),
                operator: ComparisonOperator::Equal,
                right: at_point(value),
            };
            let Some(mut scope) = attempt::candidate_outcome(proof.driver().open_have(call_value))?
            else {
                continue;
            };
            let mut complete = true;
            for (call, arm) in chain {
                check_verification_deadline()?;
                let call_expression = at_point(SyntaxTerm::Call {
                    name: call.name.clone(),
                    arguments: call.arguments.clone(),
                });
                let level = SyntaxProposition::Comparison {
                    left: call_expression.clone(),
                    operator: ComparisonOperator::Equal,
                    right: at_point(arm),
                };
                let unfold = if point.is_some() {
                    ProofStep::UnfoldProposition(SyntaxProposition::Value(call_expression))
                } else {
                    ProofStep::UnfoldFunction(call.clone())
                };
                let Some(nested) = attempt::candidate_outcome(scope.driver().open_have(level))?
                else {
                    complete = false;
                    break;
                };
                let Some(mut nested) =
                    attempt::candidate_outcome(nested.driver().apply_step(unfold))?
                else {
                    complete = false;
                    break;
                };
                if !nested.is_complete() {
                    // `close()` decides a level a constructor states; a
                    // `Bool` level's guards are decided by `solve`, which does
                    // not evaluate again (the scope above).
                    if let Some(known) =
                        attempt::candidate_outcome(nested.driver().apply_step(ProofStep::Known))?
                    {
                        nested = known;
                    } else if let Some(solved) = nested.driver().try_solve_closure()? {
                        nested = solved;
                    } else {
                        complete = false;
                        break;
                    }
                }
                let Some(joined) = attempt::candidate_outcome(scope.join_nested(nested))? else {
                    complete = false;
                    break;
                };
                scope = joined;
            }
            if !complete {
                continue;
            }
            if !scope.is_complete() {
                let Some(known) =
                    attempt::candidate_outcome(scope.driver().apply_step(ProofStep::Known))?
                else {
                    continue;
                };
                scope = known;
            }
            let Some(joined) = attempt::candidate_outcome(scope.join())? else {
                continue;
            };
            proof = joined;
            evaluated_any = true;
        }
        if !evaluated_any {
            return Ok(None);
        }
        if proof.is_complete() {
            return Ok(Some(proof));
        }
        // The equations decide the goal through the equality closure:
        // each call equals a constructor over the next.
        if let Some(known) =
            attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Known))?
        {
            return Ok(Some(known));
        }
        if let Some(closed) =
            crate::kernel::search::ProofSearch::try_direct_logical_closure(&proof)?
        {
            return Ok(Some(closed));
        }
        crate::kernel::search::ProofSearch::try_solve_closure_after_direct_with_surfaces_and_function_unfold(
            &proof,
            false,
            introduced_surfaces,
            false,
        )
    }

    /// Evaluate a goal's recursive applications over known constructors, at
    /// most `CONSTRUCTOR_EVALUATION_FUEL` checked steps. Each step is the
    /// first that applies of: an `unfold` of an application in the goal
    /// (which the kernel accepts only when its argument selects one
    /// definition arm), or a `rewrite` by a supplied equation whose right
    /// side is a constructor, exposing one for the next unfold. There is no
    /// branching: one candidate per step, and the goal is checked for
    /// closure after each. Nothing is kept unless the goal closes.
    pub(in crate::surface::proof) fn try_constructor_evaluation_closure(
        search_input: &Proof<'a>,
        introduced_surfaces: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_constructor_evaluation_closure");
        // A fact recorded at a program point keeps its anchor, `at(p, s) ==
        // at(p, Shape::Circle(r))`; the anchored constructor is still one.
        let is_constructor_equation = |surface: &SyntaxProposition| {
            let SyntaxProposition::Comparison {
                operator: ComparisonOperator::Equal,
                right,
                ..
            } = surface
            else {
                return false;
            };
            let mut right = right;
            while let SyntaxTerm::At { expression, .. } = right {
                right = expression;
            }
            matches!(right, SyntaxTerm::AlgebraicConstructor { .. })
        };
        let mut constructor_equations: Vec<SyntaxProposition> = introduced_surfaces
            .iter()
            .filter(|surface| is_constructor_equation(surface))
            .cloned()
            .collect();
        let mut fact_equations_gathered = false;
        let mut proof = search_input.clone();
        // Each step lowers the whole goal again, and the goal grows with each
        // unfold, so the fuel stays small: a longer recursion over constants
        // is `try_ground_recursion_closure`'s, one level at a time.
        for _ in 0..CONSTRUCTOR_EVALUATION_FUEL {
            check_verification_deadline()?;
            let Some(surface_goal) = proof.surface_goal() else {
                return Ok(None);
            };
            let mut next = None;
            // The applications outside undecided guards come first. Only when
            // none unfolds are those in an arm a constant guard selects, such
            // as `if 2 <= 0`, tried as well.
            let outside = pure_theorems::click_function_applications(surface_goal, &[]);
            let in_selected_arms =
                pure_theorems::click_function_applications_deciding_constant_guards(surface_goal)
                    .into_iter()
                    .filter(|application| !outside.contains(application));
            for application in outside.iter().cloned().chain(in_selected_arms) {
                if let Some(unfolded) = attempt::candidate_outcome(
                    proof
                        .driver()
                        .apply_step(ProofStep::UnfoldFunction(application.clone())),
                )? {
                    next = Some(unfolded);
                    break;
                }
            }
            if next.is_none() && !fact_equations_gathered {
                // A constructor equation among the facts connected to the
                // goal, such as a requirement `u == Tree::Node(..)`, read
                // once and only when nothing supplied applies.
                fact_equations_gathered = true;
                if let Some(goal) = proof.goal()
                    && let Some(equalities) =
                        crate::kernel::search::proposition_search::connected_equalities(
                            proof.facts().assumptions(),
                            goal,
                        )
                {
                    for equality in equalities.iter().take(CONSTRUCTOR_EVALUATION_FACTS) {
                        if let Some((_, surface)) =
                            crate::kernel::search::ProofSearch::resolve_solve_premises(
                                &(proof),
                                std::slice::from_ref(equality),
                                &[],
                            )
                            .and_then(|mut spelled| spelled.pop())
                            && is_constructor_equation(&surface)
                            && !constructor_equations.contains(&surface)
                        {
                            constructor_equations.push(surface);
                        }
                    }
                }
            }
            if next.is_none() {
                for equation in &constructor_equations {
                    if let Some(rewritten) = attempt::candidate_outcome(
                        proof
                            .driver()
                            .apply_step(ProofStep::Rewrite(equation.clone())),
                    )? && rewritten.surface_goal() != proof.surface_goal()
                    {
                        next = Some(rewritten);
                        break;
                    }
                }
            }
            let Some(next) = next else {
                return Ok(None);
            };
            proof = next;
            if proof.is_complete() {
                return Ok(Some(proof));
            }
            if let Some(closed) =
                crate::kernel::search::ProofSearch::try_direct_logical_closure(&(proof))?
            {
                return Ok(Some(closed));
            }
        }
        Ok(None)
    }

    /// Splits one atomic goal at the final index licensed by an available
    /// upper bound. Selection happens over recorded Surface facts, and the
    /// result is an ordinary checked proof `if`: the then arm learns
    /// `variable < pivot`, while the else arm derives equality from the same
    /// bound and the exact negated branch fact through normal theorem search.
    ///
    /// Once either polarity of the proposed condition is available, the
    /// candidate is no longer a split. That structural fact is what makes
    /// recursive closure terminate inside both arms; no search-depth guard or
    /// hidden kernel recursion participates.
    pub(in crate::surface::proof) fn try_upper_bound_split_closure(
        search_input: &Proof<'a>,
        introduced_surfaces: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_upper_bound_split_closure");
        // Each arm of a split runs the whole closure, which reaches this
        // split again on the next bound. Along a chain `x0 <= x1 <= ...`
        // that recursion followed every bound, so a goal no split decides
        // cost closure runs linear in the chain. Nest a fixed number.
        let Some(_scope) = UpperBoundSplitScope::enter() else {
            return Ok(None);
        };
        let Some(goal) = search_input.goal() else {
            return Ok(None);
        };
        if matches!(
            goal,
            Proposition::And(_, _)
                | Proposition::Or(_, _)
                | Proposition::Implies(_, _)
                | Proposition::ForAll { .. }
                | Proposition::Exists { .. }
        ) {
            return Ok(None);
        }
        let mut goal_variables = crate::kernel::proposition_variables(goal);
        if let Some(surface_goal) = search_input.surface_goal() {
            let mut surface_names = BTreeSet::new();
            collect_current_proposition_variables(surface_goal, &mut surface_names);
            for name in surface_names {
                let expression =
                    SyntaxTerm::ProgramExpression(ProgramExpression::Variable((name).into()));
                let probe = SyntaxProposition::Comparison {
                    left: expression.clone(),
                    operator: ComparisonOperator::Equal,
                    right: expression,
                };
                if let Ok(kernel) =
                    search_input.lower_surface_proposition(&probe, "upper-bound goal variable")
                {
                    goal_variables.extend(crate::kernel::proposition_variables(&kernel));
                }
            }
        }
        if goal_variables.is_empty() {
            return Ok(None);
        }

        let frontier_anchor: Option<ProgramPointRef>;
        let (surface_facts, premise_anchor) = match search_input.context.as_ref() {
            ProofContext::Pure(context) => (&context.theorem_context.surface_requirements, None),
            ProofContext::FixedState(context) => (
                context.surface_propositions,
                context.premise_anchor.as_ref(),
            ),
            ProofContext::Execution(_) => {
                if let Some(data) = search_input.focused_outcome_data() {
                    (&data.surface_propositions, data.premise_anchor.as_ref())
                } else {
                    let Some(execution) = search_input.execution() else {
                        return Ok(None);
                    };
                    frontier_anchor = frontier_premise_anchor(execution);
                    (
                        &execution.presentation.surface_propositions,
                        frontier_anchor.as_ref(),
                    )
                }
            }
        };

        // An introduced implication guard is the nearest and smallest source
        // of the bound in the quantified-extension shape. Prefer those named
        // facts so ordinary closure does not clone and probe the ambient fact
        // set at every atomic leaf. Fall back to ambient facts only when no
        // introduced bound can concern this goal.
        let mut bound_sources = introduced_surfaces
            .iter()
            .filter_map(|surface| {
                let bound = search_input
                    .lower_surface_proposition(surface, "introduced upper bound")
                    .ok()?;
                let (variable, _) = kernel_upper_bound_split_candidate(&bound)?;
                goal_variables
                    .contains(&variable)
                    .then(|| (bound, Some(surface.clone())))
            })
            .collect::<Vec<_>>();
        if bound_sources.is_empty() {
            // Read each goal variable's bounds from its indexed bucket; a
            // scan of every fact for the few that bound these variables
            // costs work in the whole context at each atomic leaf.
            let mut seen = BTreeSet::new();
            for variable in &goal_variables {
                for (endpoint, other, strict, forward) in search_input
                    .facts()
                    .assumptions()
                    .signed_order_bound_entries(&OldMachineTerm::Variable(*variable))
                {
                    let (left, right) = if forward {
                        (endpoint, other)
                    } else {
                        (other, endpoint)
                    };
                    let condition = if strict {
                        OldConditionTerm::Compare {
                            format: MachineIntegerType::Int32,
                            relation: CompareRelation::LessThan,
                            left: Box::new(left),
                            right: Box::new(right),
                        }
                    } else {
                        OldConditionTerm::Compare {
                            format: MachineIntegerType::Int32,
                            relation: CompareRelation::LessEqual,
                            left: Box::new(left),
                            right: Box::new(right),
                        }
                    };
                    let fact = Proposition::condition_is(condition, true);
                    for bound in
                        std::iter::once(fact.clone()).chain(condition_polarity_forms(&fact))
                    {
                        if search_input.facts().contains(&bound)
                            && kernel_upper_bound_split_candidate(&bound)
                                .is_some_and(|(bounded, _)| goal_variables.contains(&bounded))
                            && seen.insert(bound.clone())
                        {
                            bound_sources.push((bound, None));
                        }
                    }
                }
            }
        }
        let candidates = bound_sources
            .into_iter()
            .filter_map(|(bound, introduced_surface)| {
                let (variable, pivot) = kernel_upper_bound_split_candidate(&bound)?;
                let pivot_probe = Proposition::Equal(
                    Term::Integer(crate::kernel::IntegerTerm::Machine(pivot.clone()).into()),
                    Term::Integer(crate::kernel::IntegerTerm::Machine(pivot.clone()).into()),
                );
                if crate::kernel::proposition_variables(&pivot_probe).contains(&variable) {
                    return None;
                }
                let bound_surface = introduced_surface.or_else(|| {
                    crate::kernel::search::ProofSearch::available_surface_fact(
                        search_input,
                        surface_facts,
                        premise_anchor,
                        &bound,
                    )
                })?;
                let split_kernel = Proposition::condition_is(
                    crate::kernel::machine_integer::comparison::condition_for_operand_views(
                        MachineIntegerType::Int32,
                        CompareRelation::LessThan,
                        [
                            crate::kernel::MachineOperandView::Old(&OldMachineTerm::Variable(
                                variable,
                            )),
                            pivot.operand_view(),
                        ],
                    ),
                    true,
                );
                let direct = surface_upper_bound_direct_condition(&bound_surface)?;
                let direct_surface = std::iter::once(direct.clone())
                    .chain(
                        search_input
                            .premise_fixed_state_view()
                            .into_iter()
                            .flat_map(|view| {
                                view.fixed_state
                                    .recorded_states
                                    .recent(MAX_TRANSPORT_SOURCE_POINTS)
                                    .into_iter()
                                    .filter_map(|(selector, _)| {
                                        surface_at_program_point(&direct, selector).ok()
                                    })
                                    .collect::<Vec<_>>()
                            }),
                    )
                    .find(|surface| {
                        search_input
                            .lower_surface_proposition(surface, "upper-bound premise")
                            .is_ok_and(|lowered| {
                                crate::kernel::proof::fact_reasoning::order_claim_equivalent(
                                    &lowered, &bound,
                                )
                            })
                    })?;
                let mut surface_candidates = vec![
                    surface_upper_bound_split_condition(&bound_surface)?,
                    direct.clone(),
                ];
                if let Some(view) = search_input.premise_fixed_state_view() {
                    surface_candidates.extend(
                        view.fixed_state
                            .recorded_states
                            .recent(MAX_TRANSPORT_SOURCE_POINTS)
                            .into_iter()
                            .filter_map(|(selector, _)| {
                                surface_at_program_point(&direct, selector).ok()
                            }),
                    );
                }
                let split_surface = surface_candidates.into_iter().find(|surface| {
                    search_input
                        .lower_surface_proposition(surface, "upper-bound split condition")
                        .is_ok_and(|lowered| {
                            crate::kernel::proof::fact_reasoning::order_claim_equivalent(
                                &lowered,
                                &split_kernel,
                            )
                        })
                })?;
                let split_negation = SyntaxProposition::Not(Box::new(split_surface.clone()));
                if introduced_surfaces
                    .iter()
                    .any(|surface| surface == &split_surface || surface == &split_negation)
                    || condition_polarity_forms(&split_kernel)
                        .iter()
                        .any(|form| search_input.facts().contains(form))
                {
                    return None;
                }
                Some((split_surface, direct_surface, pivot))
            })
            .collect::<Vec<_>>();
        for (condition, direct_bound, pivot) in candidates {
            let (split_proof, split, ids) = search_input.split_focused_if(condition.clone())?;
            let marker = split_proof.checkpoint();
            let mut then_surfaces = introduced_surfaces.to_vec();
            then_surfaces.push(condition.clone());
            let then_branch = split_proof.focus_branch(ids[0])?;
            let disequality = surface_split_disequality(&condition)
                .expect("an upper-bound split condition is a strict comparison");
            let disequality_scope = then_branch.driver().open_have(disequality.clone())?;
            let disequality_done = (disequality_scope)
                .driver()
                .try_solve_closure_with_surfaces(&then_surfaces)?;
            let Some(disequality_done) = disequality_done else {
                continue;
            };
            let then_branch = disequality_done.join()?;
            then_surfaces.push(disequality);
            let Some(then_done) =
                crate::kernel::search::ProofSearch::try_solve_closure_with_surfaces(
                    &(then_branch),
                    &then_surfaces,
                )?
            else {
                continue;
            };
            let negated = SyntaxProposition::Not(Box::new(condition.clone()));
            let mut else_surfaces = introduced_surfaces.to_vec();
            else_surfaces.push(negated.clone());
            let equality = surface_split_equality(&condition)
                .expect("an upper-bound split condition is a strict comparison");
            let nonstrict = surface_split_nonstrict_bound(&condition)
                .expect("an upper-bound split condition is a strict comparison");
            let else_branch = then_done.focus_branch(ids[1])?;
            let equality_scope = else_branch.driver().open_have(equality.clone())?;
            let nonstrict_scope = equality_scope.driver().open_have(nonstrict.clone())?;
            let nonstrict_done = nonstrict_scope
                .driver()
                .try_solve_closure_with_surfaces(&else_surfaces)?
                .or_else(|| {
                    // `x < pivot + 1` gives `x <= pivot` by arithmetic once
                    // `pivot + 1` is known not to wrap; a direct bound of
                    // the form `x <= pivot` needs nothing more.
                    std::iter::once(None)
                        .chain(
                            crate::kernel::search::ProofSearch::increment_headroom_premises(
                                search_input,
                                pivot.structural_value(),
                                surface_facts,
                                premise_anchor,
                            )
                            .into_iter()
                            .map(Some),
                        )
                        .find_map(|headroom| {
                            let premises = std::iter::once(direct_bound.clone())
                                .chain(headroom)
                                .collect();
                            nonstrict_scope
                                .driver()
                                .apply_step(ProofStep::ArithmeticUsing(premises))
                                .ok()
                        })
                });
            let Some(nonstrict_done) = nonstrict_done else {
                continue;
            };
            let equality_scope = equality_scope.join_nested(nonstrict_done)?;
            else_surfaces.push(nonstrict);
            let Some(equality_done) = (equality_scope)
                .driver()
                .try_solve_closure_with_surfaces(&else_surfaces)?
            else {
                continue;
            };
            let else_branch = equality_done.join()?;
            else_surfaces.push(equality.clone());
            let rewritten_surface_goal =
                surface_strict_parts(&condition).and_then(|(left, right)| {
                    let SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                        crate::kernel::BindingName::Named(name),
                    )) = left
                    else {
                        return None;
                    };
                    substitute_click_proposition(
                        else_branch.surface_goal()?,
                        &std::iter::once((name, right)).collect::<BTreeMap<_, _>>(),
                    )
                    .ok()
                });
            let transported_else = else_branch
                .surface_goal()
                .and_then(old_reflexive_transport_source)
                .and_then(|source| {
                    crate::kernel::search::ProofSearch::try_execution_proposition_read_preservation(
                        &(else_branch),
                        &source,
                        else_branch.surface_goal()?,
                        MAX_TRANSPORT_SOURCE_POINTS,
                    )
                    .ok()
                    .flatten()
                })
                .filter(Proof::focused_discharged);
            let rewritten_else = match else_branch
                .driver()
                .apply_step(ProofStep::Rewrite(equality.clone()))
            {
                Ok(rewritten) if rewritten.focused_discharged() => Some(rewritten),
                Ok(rewritten) => {
                    let transported = rewritten_surface_goal
                        .as_ref()
                        .and_then(old_reflexive_transport_source)
                        .and_then(|source| {
                            crate::kernel::search::ProofSearch::try_execution_proposition_read_preservation(&(rewritten),
                                    &source,
                                    rewritten_surface_goal.as_ref()?,
                                    MAX_TRANSPORT_SOURCE_POINTS,
                                )
                                .ok()
                                .flatten()
                        })
                        .filter(Proof::focused_discharged);
                    if transported.is_some() {
                        transported
                    } else {
                        crate::kernel::search::ProofSearch::try_solve_closure_with_surfaces(
                            &(rewritten),
                            &else_surfaces,
                        )?
                    }
                }
                Err(_) => None,
            };
            let else_done = if transported_else.is_some() {
                transported_else
            } else if rewritten_else.is_some() {
                rewritten_else
            } else {
                crate::kernel::search::ProofSearch::try_solve_closure_with_surfaces(
                    &(else_branch),
                    &else_surfaces,
                )?
            };
            let Some(else_done) = else_done else {
                continue;
            };
            return else_done
                .join_focused_if(&marker, split, ids, condition)
                .map(Some);
        }
        Ok(None)
    }

    /// Proves a two-edge non-strict outcome bound at the return entry or its
    /// immediate predecessor. Outcome lowering deliberately keeps selected
    /// premises in their source form; anchoring those exact premises at
    /// the execution boundary lets the ordinary theorem checker connect a
    /// returned local to its result without consulting the retired planner.
    pub(in crate::surface::proof) fn try_outcome_anchored_order_transitivity(
        search_input: &Proof<'a>,
        premise_pairs: &[(Proposition, SyntaxProposition)],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_outcome_anchored_order_transitivity");
        let data = search_input.focused_outcome_data()?;
        let anchor = data.premise_anchor.as_ref()?;
        let predecessor = match anchor.region {
            CodeRegionRef::Region(index) if index > 0 => Some(ProgramPointRef {
                region: CodeRegionRef::Region(index - 1),
                kind: anchor.kind,
            }),
            _ => None,
        };
        for anchor in predecessor
            .as_ref()
            .into_iter()
            .chain(std::iter::once(anchor))
        {
            let ordered = premise_pairs
                .iter()
                .filter_map(|(_, surface)| {
                    let anchored = surface_at_program_point(surface, anchor).ok()?;
                    let parts = surface_nonstrict_parts(&anchored)?;
                    Some((anchored, parts))
                })
                .collect::<Vec<_>>();
            for (first_surface, (first, middle)) in &ordered {
                for (second_surface, (second_middle, last)) in &ordered {
                    if middle != second_middle {
                        continue;
                    }
                    // `last >= first`, the composed order at the anchor.
                    let composed = SyntaxProposition::Comparison {
                        left: last.clone(),
                        operator: ComparisonOperator::GreaterEqual,
                        right: first.clone(),
                    };
                    let Ok(applied) = search_input.driver().have_by_integer_arithmetic(
                        composed,
                        vec![second_surface.clone(), first_surface.clone()],
                    ) else {
                        continue;
                    };
                    if applied.is_complete() {
                        return Some(applied);
                    }
                    if let Some(closed) =
                        crate::kernel::search::ProofSearch::try_direct_logical_closure(&(applied))
                            .ok()
                            .flatten()
                    {
                        return Some(closed);
                    }
                }
            }
        }
        None
    }

    /// Proves an outcome increment bound at the return entry or its immediate
    /// predecessor. The latter is the assignment boundary that can connect a
    /// named return local to the increment expression. The two propositions
    /// come only from the atomic derivation's selected requirements; the
    /// ordinary arithmetic, `known`, and rewrite checkers decide whether
    /// either constant-size historical application establishes the current
    /// result-aware goal.
    pub(in crate::surface::proof) fn try_outcome_anchored_increment_order(
        search_input: &Proof<'a>,
        premise_pairs: &[(Proposition, SyntaxProposition)],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_outcome_anchored_increment_order");
        let data = search_input.focused_outcome_data()?;
        let anchor = data.premise_anchor.as_ref()?;
        let predecessor = match anchor.region {
            CodeRegionRef::Region(index) if index > 0 => Some(ProgramPointRef {
                region: CodeRegionRef::Region(index - 1),
                kind: anchor.kind,
            }),
            _ => None,
        };
        let surface_goal = search_input.surface_goal()?.clone();
        let SyntaxProposition::Comparison {
            left,
            operator,
            right,
        } = surface_comparison_with_anchored_operands(&surface_goal)
        else {
            return None;
        };
        let (goal_left, goal_right) = match operator {
            ComparisonOperator::LessEqual => (left, right),
            ComparisonOperator::GreaterEqual => (right, left),
            _ => return None,
        };
        for anchor in predecessor
            .as_ref()
            .into_iter()
            .chain(std::iter::once(anchor))
        {
            let mut lower_bounds = Vec::new();
            let mut upper_bounds = Vec::new();
            for (kernel, surface) in premise_pairs {
                let anchored = surface_at_program_point(surface, anchor).ok()?;
                if let Some(parts) = surface_nonstrict_parts(&anchored) {
                    lower_bounds.push((
                        anchored.clone(),
                        parts,
                        signed_nonstrict_parts(kernel).map(|(_, value)| value),
                    ));
                }
                if let Some(parts) = surface_strict_parts(&anchored) {
                    upper_bounds.push((
                        anchored,
                        parts,
                        signed_strict_parts(kernel).map(|(value, _)| value),
                    ));
                }
            }
            for (lower_surface, (surface_lower, lower_value), lower_kernel) in &lower_bounds {
                for (upper_surface, (upper_value, _), upper_kernel) in &upper_bounds {
                    // Entry requirements and resource observations can spell
                    // the same checked value at different states. Select
                    // by the kernel endpoint as well as identical syntax;
                    // ApplyTheoremUsing still validates both named premises
                    // and the result at the chosen historical boundary.
                    if lower_value != upper_value
                        && !(lower_kernel.is_some() && lower_kernel == upper_kernel)
                    {
                        continue;
                    }
                    // `lower + 1 <= value + 1`, the order of the two machine
                    // sums, written as the comparison of their exact
                    // observations: outside `to_integer`, a written `+` is
                    // Integer addition.
                    let one = SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(1)));
                    let observed_sum = |base: &SyntaxTerm| SyntaxTerm::Call {
                        name: "to_integer".to_string(),
                        arguments: vec![SyntaxTerm::Add(
                            Box::new(base.clone()),
                            Box::new(one.clone()),
                        )],
                    };
                    let conclusion_left = observed_sum(surface_lower);
                    let conclusion_right = observed_sum(lower_value);
                    let theorem_conclusion = SyntaxProposition::Comparison {
                        left: conclusion_left.clone(),
                        operator: ComparisonOperator::LessEqual,
                        right: conclusion_right.clone(),
                    };
                    let Ok(applied) = search_input.driver().have_by_integer_arithmetic(
                        theorem_conclusion,
                        vec![lower_surface.clone(), upper_surface.clone()],
                    ) else {
                        continue;
                    };
                    if applied.focused_discharged() {
                        return Some(applied);
                    }
                    let driver = applied.driver();
                    if let Ok(closed) = driver.apply_step(ProofStep::Known) {
                        return Some(closed);
                    }
                    let mut steps = Vec::new();
                    for (left, right) in [
                        (goal_left.clone(), conclusion_left),
                        (goal_right.clone(), conclusion_right),
                    ] {
                        if left == right {
                            continue;
                        }
                        let equality = SyntaxProposition::Comparison {
                            left,
                            operator: ComparisonOperator::Equal,
                            right,
                        };
                        steps.push(ProofStep::Have {
                            proposition: equality.clone(),
                            proof: Box::new(
                                ProofCertificate::from_steps(vec![ProofStep::Known])
                                    .expect("known is an ordinary certificate"),
                            ),
                        });
                        steps.push(ProofStep::Rewrite(equality));
                    }
                    steps.push(ProofStep::Known);
                    if let Ok(closed) = driver.apply_ordinary_transport_steps(&surface_goal, steps)
                    {
                        return Some(closed);
                    }
                    if let Ok(Some(closed)) = Self::try_direct_logical_closure(&applied) {
                        return Some(closed);
                    }
                }
            }
        }
        None
    }

    /// Select the equalities for a load bridge under solve's budget and
    /// submit them to the ordinary transport checker. The checked successor
    /// retains only its explicit proof steps, so opening the goal or replaying
    /// the certificate never enumerates the goal's equality buckets.
    fn try_selected_load_equality_bridge(
        search_input: &Proof<'a>,
        introduced_surfaces: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_selected_load_equality_bridge");
        let (Some(goal), Some(target)) = (search_input.goal(), search_input.surface_goal()) else {
            return Ok(None);
        };
        let facts = search_input.facts();
        if facts.pure_known_available(goal)
            || search_input.premise_fixed_state_view().is_none()
            || !matches!(goal, Proposition::ConditionIs(condition, true)
            if condition.old_form().pointer_offset_sides().is_some()
                || matches!(condition.old_form(), OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    relation: CompareRelation::Equal, ..
                }))
        {
            return Ok(None);
        }
        if crate::instrumentation::replay_forbids_discovery("load equality bridge search") {
            return Err(search_input.step_error("load equality discovery requires solve"));
        }
        let candidates =
            crate::kernel::search::load_equality_candidates(facts, goal, MAX_SOLVE_SOURCE_PREMISES);
        check_verification_deadline()?;
        if candidates.is_empty() {
            return Ok(None);
        }

        let premises =
            Self::resolve_solve_premises_unmeasured(search_input, &candidates, introduced_surfaces);
        check_verification_deadline()?;
        let Some(premises) = premises else {
            return Ok(None);
        };
        let mut premises = premises.into_iter().map(|(_, surface)| surface);
        let Some(source) = premises.next() else {
            return Ok(None);
        };
        // The source is itself one of the available equalities. Use the
        // selected facts to construct an ordinary proof.
        Self::try_fixed_state_fact_transport(
            search_input,
            &source,
            target,
            std::iter::once(source.clone()).chain(premises),
        )
        .map(|proof| proof.filter(Proof::is_complete))
    }

    /// Prove a struct equality from its constructor's individual field
    /// equalities. Each proof names its stored reads and footprint.
    fn try_struct_field_equalities(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_struct_field_equalities");
        if let Some(goal @ SyntaxProposition::And(..)) = search_input.surface_goal() {
            return Self::try_written_field_equalities(search_input, goal);
        }
        let Some(SyntaxProposition::Comparison {
            left:
                SyntaxTerm::AlgebraicConstructor {
                    variant: left_variant,
                    arguments: left_fields,
                    ..
                },
            operator: ComparisonOperator::Equal,
            right:
                SyntaxTerm::AlgebraicConstructor {
                    variant: right_variant,
                    arguments: right_fields,
                    ..
                },
        }) = search_input.surface_goal()
        else {
            return Ok(None);
        };
        if left_variant != right_variant
            || left_fields.len() != right_fields.len()
            || crate::surface::struct_values::field_names(left_variant).is_none()
        {
            return Ok(None);
        }
        if let Some(read) = right_fields.first()
            && let Some(proof) = Self::try_unchanged_struct_operand(search_input, read)?
        {
            return Ok(Some(proof));
        }

        let mut proof = search_input.clone();
        for (left, right) in left_fields.iter().zip(right_fields) {
            check_verification_deadline()?;
            let equality = SyntaxProposition::Comparison {
                left: left.clone(),
                operator: ComparisonOperator::Equal,
                right: right.clone(),
            };
            let Some(field) =
                attempt::candidate_outcome(proof.driver().open_have(equality.clone()))?
            else {
                return Ok(None);
            };
            let Some(closed) = field.driver().try_struct_field_equality(&equality)? else {
                return Ok(None);
            };
            proof = closed.join()?;
        }
        attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Known))
    }

    fn try_written_field_equalities(
        search_input: &Proof<'a>,
        target: &SyntaxProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_written_field_equalities");
        let mut pending = vec![target];
        let mut fields = Vec::new();
        while let Some(proposition) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            match proposition {
                SyntaxProposition::And(left, right) => {
                    pending.push(right);
                    pending.push(left);
                }
                SyntaxProposition::Comparison {
                    left,
                    operator: ComparisonOperator::Equal,
                    right: SyntaxTerm::Field { .. },
                } if is_field_observation(left) => fields.push(proposition),
                _ => return Ok(None),
            }
        }
        if let Some(SyntaxProposition::Comparison { right, .. }) = fields.first()
            && let Some(proof) = Self::try_unchanged_struct_operand(search_input, right)?
        {
            return Ok(Some(proof));
        }
        let mut proof = search_input.clone();
        for field in fields {
            check_verification_deadline()?;
            let Some(scope) = attempt::candidate_outcome(proof.driver().open_have(field.clone()))?
            else {
                return Ok(None);
            };
            let Some(closed) = scope.driver().try_struct_field_equality(field)? else {
                return Ok(None);
            };
            proof = closed.join()?;
        }
        attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Known))
    }

    /// Make the unchanged source read available before checking the group.
    /// The other field reads may already have indexed versions at this point.
    fn try_unchanged_struct_operand(
        search_input: &Proof<'a>,
        read: &SyntaxTerm,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_unchanged_struct_operand");
        let SyntaxTerm::Field { .. } = read else {
            return Ok(None);
        };
        let Some(anchor) = search_input
            .focused_outcome_data()
            .and_then(|outcome| outcome.premise_anchor.as_ref())
        else {
            return Ok(None);
        };
        let at = |expression| SyntaxTerm::At {
            selector: ProgramPointSelector::ProgramPoint(anchor.clone()),
            expression: Box::new(expression),
        };
        let unchanged = SyntaxProposition::Comparison {
            left: at(SyntaxTerm::Old(Box::new(read.clone()))),
            operator: ComparisonOperator::Equal,
            right: at(read.clone()),
        };
        let Some(scope) =
            attempt::candidate_outcome(search_input.driver().open_have(unchanged.clone()))?
        else {
            return Ok(None);
        };
        let Some(closed) = scope.driver().try_struct_field_equality(&unchanged)? else {
            return Ok(None);
        };
        let proof = closed.join()?;
        attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Known))
    }

    pub(in crate::surface::proof) fn try_struct_field_equality(
        search_input: &Proof<'a>,
        equality: &SyntaxProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_struct_field_equality");
        if let Some(known) =
            attempt::candidate_outcome(search_input.driver().apply_step(ProofStep::Known))?
        {
            return Ok(Some(known));
        }
        if let Some(read) = Self::try_struct_field_store_bridge(search_input, equality, true)? {
            return Ok(Some(read));
        }
        Self::try_struct_field_equalities(search_input)
    }

    /// Retain a chain of checked field equalities across recent disjoint stores.
    /// At each entry, also try the mixed-state equality with the other operand.
    pub(in crate::surface::proof) fn try_struct_field_store_bridge(
        search_input: &Proof<'a>,
        equality: &SyntaxProposition,
        allow_distinct_fields: bool,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_struct_field_store_bridge");
        let SyntaxProposition::Comparison {
            left,
            operator: ComparisonOperator::Equal,
            right,
        } = equality
        else {
            return Ok(None);
        };
        let (other, read) = if allow_distinct_fields
            && matches!(right, SyntaxTerm::Field { .. })
            && is_field_observation(left)
        {
            (left, right)
        } else if let Some(pair) = field_at_two_points(left, right) {
            pair
        } else {
            return Ok(None);
        };
        let Some((
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                right,
                ..
            },
            true,
        )) = search_input.goal().and_then(Proposition::old_condition)
        else {
            return Ok(None);
        };
        let load = match right.as_ref() {
            OldMachineTerm::Variable(variable) => {
                crate::kernel::registered_load_term_for_variable(variable)
            }
            term => Some(term.clone()),
        };
        let Some(OldMachineTerm::MemoryLoad(_, address, _)) = load else {
            return Ok(None);
        };
        let Some(view) = search_input.premise_fixed_state_view() else {
            return Ok(None);
        };
        let kept = Resource::Memory(crate::kernel::MemoryRange::new_with_element_width(
            address.into(),
            0u32.into(),
            1u32.into(),
            4,
        ));
        let Some(kept) = super::surface_synthesis::synthesize_surface_resource_subject(
            &kept,
            view.parameter_binding,
            view.fixed_state.state,
            &BTreeMap::new(),
        ) else {
            return Ok(None);
        };
        let records = view.fixed_state.recorded_states;
        let known =
            ProofCertificate::from_steps(vec![ProofStep::Known]).expect("ordinary equality");
        let mut proof = search_input.clone();
        for (selector, _) in records.recent(MAX_TRANSPORT_SOURCE_POINTS) {
            check_verification_deadline()?;
            let ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region: region @ CodeRegionRef::Region(_),
                kind: ProgramPointKind::Exit,
            }) = selector
            else {
                continue;
            };
            let Ok(Resource::Footprint(footprint)) = records.footprint(region) else {
                continue;
            };
            if !footprint.complete || footprint.members.is_empty() {
                continue;
            }
            let at = |kind| SyntaxTerm::At {
                selector: ProgramPointSelector::ProgramPoint(ProgramPointRef {
                    region: region.clone(),
                    kind,
                }),
                expression: Box::new(read.clone()),
            };
            let entry = at(ProgramPointKind::Entry);
            let stored = SyntaxProposition::Comparison {
                left: other.clone(),
                operator: ComparisonOperator::Equal,
                right: entry.clone(),
            };
            let stored =
                attempt::candidate_outcome(proof.driver().apply_have_step(&stored, &known))?;
            let separation = SyntaxProposition::Separate {
                left: ResourceSubject::Footprint(region.clone()),
                right: kept.clone(),
            };
            let Some(separated) = Self::try_memory_footprint_separation(
                stored.as_ref().unwrap_or(&proof),
                &footprint,
                &kept,
                &separation,
            )?
            else {
                continue;
            };
            let bridge = SyntaxProposition::Comparison {
                left: at(ProgramPointKind::Exit),
                operator: ComparisonOperator::Equal,
                right: entry,
            };
            let preserve = ProofCertificate::from_steps(vec![ProofStep::Preserve(separation)])
                .expect("ordinary field preservation");
            let Some(preserved) =
                attempt::candidate_outcome(separated.driver().apply_have_step(&bridge, &preserve))?
            else {
                continue;
            };
            if let Some(closed) =
                attempt::candidate_outcome(preserved.driver().apply_step(ProofStep::Known))?
            {
                return Ok(Some(closed));
            }
            proof = preserved;
        }
        Ok(None)
    }

    /// Follow recorded stores back from the current memory, checking each
    /// read equality before trying the comparison at the earlier point.
    fn try_store_read_rewrite(
        search_input: &Proof<'a>,
        target: &SyntaxProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_store_read_rewrite");
        let outcome = search_input.focused_outcome_data().is_some();
        let mut comparison = target;
        // The outcome closer may leave an indexed comparison grouped with
        // already discharged conjuncts. The final known checks the whole goal.
        while outcome && let SyntaxProposition::And(left, _) = comparison {
            comparison = left;
        }
        fn is_integer_literal(expression: &SyntaxTerm) -> bool {
            match expression {
                SyntaxTerm::IntegerLiteral(_) => true,
                SyntaxTerm::ProgramExpression(ProgramExpression::Value(value)) => {
                    MachineIntegerType::from_program_type(value.program_type())
                        .is_some_and(|kind| kind.constant_from_value(value).is_some())
                }
                _ => false,
            }
        }
        // Signed shift definedness can group two bounds of the same read.
        // Choose the read from the upper bound and rewrite the whole goal.
        if let SyntaxProposition::And(lower, upper) = comparison
            && let SyntaxProposition::Not(lower) = lower.as_ref()
            && let SyntaxProposition::Comparison {
                left: lower_read,
                operator: ComparisonOperator::LessThan,
                right: lower_bound,
            } = lower.as_ref()
            && let SyntaxProposition::Comparison {
                left: upper_read @ SyntaxTerm::Index(..),
                operator: ComparisonOperator::LessEqual,
                right: upper_bound,
            } = upper.as_ref()
            && lower_read == upper_read
            && is_integer_literal(lower_bound)
            && is_integer_literal(upper_bound)
        {
            comparison = upper;
        }
        let SyntaxProposition::Comparison {
            left,
            operator,
            right,
        } = comparison
        else {
            return Ok(None);
        };
        if *operator == ComparisonOperator::In {
            return Ok(None);
        }
        let field_bound = *operator == ComparisonOperator::LessEqual;
        fn operand_against_literal<'e>(
            left: &'e SyntaxTerm,
            right: &'e SyntaxTerm,
        ) -> Option<&'e SyntaxTerm> {
            if is_integer_literal(right) {
                Some(left)
            } else if is_integer_literal(left) {
                Some(right)
            } else {
                None
            }
        }
        let read_operand_against_binding = || {
            [(left, right), (right, left)]
                .into_iter()
                .find_map(|(expression, bound)| {
                    if !matches!(
                        bound,
                        SyntaxTerm::Binding(_)
                            | SyntaxTerm::ProgramBinding(_)
                            | SyntaxTerm::ProgramExpression(ProgramExpression::Variable(_))
                            | SyntaxTerm::QualifiedC {
                                lowered: ProgramExpression::Variable(_),
                                ..
                            }
                    ) {
                        return None;
                    }
                    match expression {
                        SyntaxTerm::Index(..)
                        | SyntaxTerm::CUnary {
                            lowered: ProgramExpression::Load(_),
                            ..
                        }
                        | SyntaxTerm::ProgramExpression(ProgramExpression::Load(_)) => {
                            Some(expression)
                        }
                        SyntaxTerm::BitwiseNot(operand)
                            if matches!(operand.as_ref(), SyntaxTerm::Index(..)) =>
                        {
                            Some(expression)
                        }
                        SyntaxTerm::BitwiseAnd(left, right)
                        | SyntaxTerm::BitwiseOr(left, right)
                        | SyntaxTerm::BitwiseXor(left, right)
                        | SyntaxTerm::ShiftLeft(left, right)
                        | SyntaxTerm::ShiftRight(left, right)
                            if matches!(
                                operand_against_literal(left, right),
                                Some(SyntaxTerm::Index(..))
                            ) =>
                        {
                            Some(expression)
                        }
                        _ => None,
                    }
                })
        };
        let literal_operand = operand_against_literal(left, right);
        let indexed_cell = |base: &SyntaxTerm, index: &SyntaxTerm| ResourceSubject::SavedMemory {
            base: base.clone(),
            start: index.clone(),
            end: None,
        };
        let second_cell = match (left, right) {
            (SyntaxTerm::Index(..), SyntaxTerm::Index(base, index)) if left != right => {
                Some((right, indexed_cell(base, index)))
            }
            _ => None,
        };
        let Some(expression) = literal_operand
            .or_else(read_operand_against_binding)
            .or_else(|| second_cell.as_ref().map(|_| left))
        else {
            return Ok(None);
        };
        fn expression_memory_read(mut expression: &SyntaxTerm) -> Option<&SyntaxTerm> {
            // Find one candidate read. The checked rewrite must still close the
            // original comparison, including any other terms it depends on.
            loop {
                crate::instrumentation::record_deterministic_work(1);
                expression = match expression {
                    SyntaxTerm::Index(..)
                    | SyntaxTerm::CUnary {
                        lowered: ProgramExpression::Load(_),
                        ..
                    }
                    | SyntaxTerm::ProgramExpression(ProgramExpression::Load(_)) => {
                        return Some(expression);
                    }
                    SyntaxTerm::BitwiseNot(operand) => operand,
                    SyntaxTerm::CUnary {
                        operand,
                        lowered: ProgramExpression::Cast { target_type, .. },
                    } if MachineIntegerType::from_program_type(*target_type).is_some() => operand,
                    SyntaxTerm::BitwiseAnd(left, right)
                    | SyntaxTerm::BitwiseOr(left, right)
                    | SyntaxTerm::BitwiseXor(left, right)
                    | SyntaxTerm::ShiftLeft(left, right)
                    | SyntaxTerm::ShiftRight(left, right) => operand_against_literal(left, right)?,
                    SyntaxTerm::Divide(dividend, divisor)
                    | SyntaxTerm::Remainder(dividend, divisor)
                        if is_integer_literal(divisor) =>
                    {
                        dividend
                    }
                    SyntaxTerm::If {
                        then_branch,
                        else_branch,
                        ..
                    } => operand_against_literal(then_branch, else_branch)?,
                    _ => return None,
                };
            }
        }
        let indexed;
        let read = match expression {
            read @ SyntaxTerm::Field { .. } if field_bound => read,
            SyntaxTerm::BitwiseAnd(read, mask)
                if *operator == ComparisonOperator::Equal
                    && matches!(left, SyntaxTerm::BitwiseAnd(..))
                    && matches!(mask.as_ref(), SyntaxTerm::IntegerLiteral(_))
                    && matches!(read.as_ref(), SyntaxTerm::Field { .. }) =>
            {
                read.as_ref()
            }
            SyntaxTerm::If {
                condition,
                then_branch,
                else_branch,
            } if is_integer_literal(then_branch)
                && is_integer_literal(else_branch)
                && let SyntaxProposition::Comparison {
                    left,
                    operator,
                    right,
                } = condition.as_ref()
                && *operator != ComparisonOperator::In =>
            {
                let Some(read) =
                    operand_against_literal(left, right).and_then(expression_memory_read)
                else {
                    return Ok(None);
                };
                read
            }
            _ if (literal_operand.is_none()
                || (outcome && *operator == ComparisonOperator::Equal))
                && matches!(
                    expression,
                    SyntaxTerm::CUnary {
                        lowered: ProgramExpression::Load(_),
                        ..
                    } | SyntaxTerm::ProgramExpression(ProgramExpression::Load(_))
                )
                && let Some(ProgramExpression::Load(pointer)) =
                    contract_expression_as_program_expression(expression)
                && let ProgramExpression::Add(base, index) = *pointer =>
            {
                // Retain the array base and index for same-array separation
                // when an indexed read is spelled as *(a + i).
                indexed = SyntaxTerm::Index(
                    Box::new(SyntaxTerm::ProgramExpression(*base)),
                    Box::new(SyntaxTerm::ProgramExpression(*index)),
                );
                &indexed
            }
            _ if let Some(read) = expression_memory_read(expression) => read,
            _ => return Ok(None),
        };
        let pointed_cell = |base| ResourceSubject::SavedMemory {
            base,
            start: SyntaxTerm::IntegerLiteral("0".into()),
            end: None,
        };
        let cell = match read {
            SyntaxTerm::Index(base, index) => Some(indexed_cell(base, index)),
            SyntaxTerm::CUnary {
                operand,
                lowered: ProgramExpression::Load(_),
            } => Some(pointed_cell(operand.as_ref().clone())),
            SyntaxTerm::ProgramExpression(ProgramExpression::Load(pointer)) => Some(pointed_cell(
                SyntaxTerm::ProgramExpression(pointer.as_ref().clone()),
            )),
            _ => None,
        };
        let cell_read = cell.is_some();
        let anchored = outcome && cell_read;
        let view = if field_bound || anchored {
            search_input.premise_fixed_state_view()
        } else {
            search_input.execution_proposition_fixed_state_view()
        };
        let Some(view) = view else {
            return Ok(None);
        };
        let state = view.fixed_state.state;
        let records = view.fixed_state.recorded_states;
        let spell = |resource: &Resource| {
            super::surface_synthesis::synthesize_surface_resource_subject(
                resource,
                view.parameter_binding,
                state,
                &BTreeMap::new(),
            )
        };
        let kept = if let Some(cell) = cell {
            cell
        } else {
            let Some((
                OldConditionTerm::Compare {
                    format,
                    left,
                    right,
                    ..
                },
                true,
            )) = search_input.goal().and_then(Proposition::old_condition)
            else {
                return Ok(None);
            };
            let load_address =
                |term: &OldMachineTerm, valid_kind: fn(crate::kernel::LoadKind) -> bool| {
                    let load = match term {
                        OldMachineTerm::Variable(variable) => {
                            crate::kernel::registered_load_term_for_variable(variable)?
                        }
                        term => term.clone(),
                    };
                    match load {
                        OldMachineTerm::MemoryLoad(_, address, kind) if valid_kind(kind) => {
                            Some(address)
                        }
                        _ => None,
                    }
                };
            let (address, count, width) = match (field_bound, format) {
                (true, MachineIntegerType::Int32 | MachineIntegerType::UInt32) => (
                    [left, right].into_iter().find_map(|term| {
                        load_address(term, |kind| {
                            matches!(
                                kind,
                                crate::kernel::LoadKind::Int32 | crate::kernel::LoadKind::UInt32
                            )
                        })
                    }),
                    1u32,
                    4,
                ),
                (false, MachineIntegerType::Int64 | MachineIntegerType::UInt64) => (
                    [left, right].into_iter().find_map(|term| {
                        let OldMachineTerm::Binary {
                            op: crate::kernel::MachineBinaryOp::BitwiseAnd,
                            left,
                            right,
                            ..
                        } = term.as_ref()
                        else {
                            return None;
                        };
                        [left, right].into_iter().find_map(|operand| {
                            load_address(operand, |kind| kind == crate::kernel::LoadKind::Bits64)
                        })
                    }),
                    8u32,
                    1,
                ),
                _ => return Ok(None),
            };
            let Some(address) = address else {
                return Ok(None);
            };
            let Some(kept) = spell(&Resource::Memory(
                crate::kernel::MemoryRange::new_with_element_width(
                    address.into(),
                    0u32.into(),
                    count.into(),
                    width,
                ),
            )) else {
                return Ok(None);
            };
            kept
        };
        let current = crate::kernel::intern_memory_ref(state.memory());
        let mut endpoint = current.clone();
        let mut prepared = search_input.clone();
        'regions: for (selector, _) in records.recent(MAX_TRANSPORT_SOURCE_POINTS) {
            check_verification_deadline()?;
            let ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region: region @ CodeRegionRef::Region(_),
                kind: ProgramPointKind::Exit,
            }) = selector
            else {
                continue;
            };
            let Ok(Resource::Footprint(footprint)) = records.footprint(region) else {
                continue;
            };
            if !footprint.complete
                || footprint.members.is_empty()
                || (!cell_read && footprint.members.len() != 1)
                || crate::kernel::intern_memory_ref(&footprint.after) != endpoint
            {
                continue;
            }
            let before = crate::kernel::intern_memory_ref(&footprint.before);
            if before == endpoint {
                continue;
            }
            let mut preserved = prepared.clone();
            let mut closing = Vec::new();
            // Prepare every read at this boundary before rewriting the comparison.
            for (read, kept) in std::iter::once((read, &kept))
                .chain(second_cell.iter().map(|(read, kept)| (*read, kept)))
            {
                let footprint_separation = SyntaxProposition::Separate {
                    left: ResourceSubject::Footprint(region.clone()),
                    right: kept.clone(),
                };
                let at = |kind| SyntaxTerm::At {
                    selector: ProgramPointSelector::ProgramPoint(ProgramPointRef {
                        region: region.clone(),
                        kind,
                    }),
                    expression: Box::new(read.clone()),
                };
                let equality = SyntaxProposition::Comparison {
                    left: if anchored || endpoint != current {
                        at(ProgramPointKind::Exit)
                    } else {
                        read.clone()
                    },
                    operator: ComparisonOperator::Equal,
                    right: at(ProgramPointKind::Entry),
                };
                let have = |proposition, step| ProofStep::Have {
                    proposition,
                    proof: Box::new(
                        ProofCertificate::from_steps(vec![step])
                            .expect("ordinary preservation step"),
                    ),
                };
                let mut steps = Vec::new();
                let proof = if cell_read
                    && footprint.members.len() == 1
                    && let Some(written) = footprint.members.front()
                    && let Some(proof) = Self::try_distinct_indexed_store_separation(
                        &preserved,
                        written,
                        kept,
                        &footprint_separation,
                    )? {
                    proof
                } else if cell_read || field_bound {
                    let Some(proof) =
                        attempt::candidate_outcome(Self::try_memory_footprint_separation(
                            &preserved,
                            &footprint,
                            kept,
                            &footprint_separation,
                        ))?
                        .flatten()
                    else {
                        continue 'regions;
                    };
                    proof
                } else {
                    let Some(written) = footprint
                        .members
                        .front()
                        .filter(|member| matches!(member, Resource::Memory(_)))
                        .and_then(spell)
                    else {
                        continue 'regions;
                    };
                    let separate = SyntaxProposition::Separate {
                        left: written,
                        right: kept.clone(),
                    };
                    steps.extend([
                        have(separate, ProofStep::Known),
                        have(footprint_separation.clone(), ProofStep::Known),
                    ]);
                    preserved
                };
                steps.push(have(
                    equality.clone(),
                    ProofStep::Preserve(footprint_separation),
                ));
                let Some(next) = attempt::candidate_outcome(
                    proof.driver().apply_ordinary_transport_steps(target, steps),
                )?
                else {
                    continue 'regions;
                };
                if next.is_complete() {
                    return Ok(Some(next));
                }
                preserved = next;

                // Keep the checked endpoint equality even if it is too recent to
                // close the comparison. Rewrite only on the closing candidate.
                if !anchored {
                    let rewrite = if endpoint == current {
                        equality
                    } else {
                        let composed = SyntaxProposition::Comparison {
                            left: read.clone(),
                            operator: ComparisonOperator::Equal,
                            right: at(ProgramPointKind::Entry),
                        };
                        closing.push(have(composed.clone(), ProofStep::Known));
                        composed
                    };
                    closing.push(ProofStep::Rewrite(rewrite));
                }
            }
            closing.push(ProofStep::Known);
            if let Some(proof) = attempt::candidate_outcome(
                preserved
                    .driver()
                    .apply_ordinary_transport_steps(target, closing),
            )? && proof.is_complete()
            {
                return Ok(Some(proof));
            }
            if cell_read {
                prepared = preserved;
                endpoint = before;
            }
        }
        Ok(None)
    }

    /// Tries the focused branch goal itself as one explicit fact transport from a
    /// recorded program point. This also applies to proposition scopes opened
    /// mid-execution, such as loop-invariant initialization and preservation.
    /// The candidate space is the execution's
    /// recorded-state index, not the ambient fact set; every accepted source
    /// and target is checked against this immutable proof.
    pub(in crate::surface::proof) fn try_state_transport_closure(
        search_input: &Proof<'a>,
        surface_goal: &SyntaxProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_state_transport_closure");
        if super::selected_arithmetic::machine_equality_bridge_active() {
            return Ok(None);
        }
        // Every candidate below lowers the same goal, so a failing question
        // about the goal's own loads repeats per candidate; remember those
        // failures for this closure (`with_closure_failure_memo`).
        crate::instrumentation::measure_operation(
            "surface",
            "solve closure",
            "solve closure: state transport",
            || {
                crate::kernel::with_closure_failure_memo(|| {
                    crate::kernel::search::ProofSearch::try_state_transport_closure_candidates(
                        search_input,
                        surface_goal,
                    )
                })
            },
        )
    }

    pub(in crate::surface::proof) fn try_state_transport_closure_candidates(
        search_input: &Proof<'a>,
        surface_goal: &SyntaxProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_state_transport_closure_candidates");
        // Introduce the index and its guard before framing this read. Reuse
        // the ordinary indexed equality proof rather than transporting the
        // entire quantified postcondition from function entry.
        if let SyntaxProposition::ForAll { body, .. } = surface_goal
            && let SyntaxProposition::Implies(_, consequent) = body.as_ref()
            && let SyntaxProposition::Comparison {
                left: read @ SyntaxTerm::Index(..),
                operator: ComparisonOperator::Equal,
                right: SyntaxTerm::Old(entry_read),
            } = consequent.as_ref()
            && read == entry_read.as_ref()
            && (search_input.focused_outcome_data().is_some()
                || search_input
                    .execution_proposition_fixed_state_view()
                    .is_some())
            && let Some((binder, introduced)) = attempt::candidate_outcome(
                search_input
                    .driver()
                    .apply_step(ProofStep::Intro)
                    .and_then(|binder| {
                        binder
                            .driver()
                            .apply_step(ProofStep::Intro)
                            .map(|introduced| (binder, introduced))
                    }),
            )?
        {
            let mut closed = introduced.is_complete().then(|| introduced.clone());
            if closed.is_none()
                && search_input.focused_outcome_data().is_some()
                && let Some(goal) = introduced.surface_goal()
                && let Some(source) = old_reflexive_transport_source(goal)
            {
                closed = Self::try_history_indexed_equalities(&introduced, &source, goal)?;
            }
            if closed.is_none()
                && let Some(target) = introduced.surface_goal()
            {
                closed = Self::try_indexed_read_preservation(
                    &introduced,
                    target,
                    MAX_TRANSPORT_SOURCE_POINTS,
                    true,
                )?
                .filter(Proof::is_complete);
            }
            if let Some(closed) = closed {
                let closed = binder.finish_generated_intro(&introduced, closed)?;
                return search_input
                    .finish_generated_intro(&binder, closed)
                    .map(Some);
            }
        }
        if let Some(proof) = crate::kernel::search::ProofSearch::try_cell_frame_transport_closure(
            search_input,
            surface_goal,
        )? {
            return Ok(Some(proof));
        }
        // Outcome transport is a general closure. Extending it to fixed-state
        // and mid-execution proposition scopes is needed for opaque Click
        // applications, whose state arguments cannot be refreshed by
        // ordinary field rewrites, and for goals that read memory: a read
        // written through one alias of a cell whose fact was stated through
        // another, before a store the alias shows separate, is carried here
        // rather than renamed by lowering (lowering is fact-stable,
        // `docs/internals/raise-lower-principle.md`). Other goals keep their more
        // local rewrite plans.
        if search_input.outcome_fixed_state_view().is_none() {
            let mut calls = BTreeSet::new();
            crate::surface::validation::collect_click_function_calls_in_proposition(
                surface_goal,
                &mut calls,
            );
            let reads_memory = search_input.goal().is_some_and(|goal| {
                crate::kernel::proposition_mentions_load_variable(goal)
                    || crate::kernel::proof::term_rewrite::proposition_pointer_terms(goal)
                        .iter()
                        .any(|pointer| matches!(pointer.base, AddressBase::Load(_)))
            });
            if calls.is_empty() && !reads_memory {
                return Ok(None);
            }
        }
        let Some(view) = search_input.premise_fixed_state_view() else {
            return Ok(None);
        };
        if let Some(source) = old_reflexive_transport_source(surface_goal) {
            match crate::kernel::search::ProofSearch::try_fixed_state_fact_transport(
                search_input,
                &source,
                surface_goal,
                std::iter::empty(),
            ) {
                Ok(Some(proof)) if proof.is_complete() => return Ok(Some(proof)),
                Ok(_) => {}
                Err(_) => {
                    check_verification_deadline()?;
                }
            }
        }
        // A goal about `result` exists only once the function has returned,
        // so its first source is function exit rather than entry, and no
        // recorded point before the return is offered.
        let names_result = crate::surface::proposition_names_result(surface_goal);
        let first = ProgramPointRef {
            region: CodeRegionRef::Function,
            kind: if names_result {
                ProgramPointKind::Exit
            } else {
                ProgramPointKind::Entry
            },
        };
        // The source points are that function point and the most recently
        // recorded ones, newest first. A path records a point per statement
        // it ran, so offering every one made this search linear in the
        // path's length for each goal, and quadratic over a function's
        // early-return paths. A proof can cite an older point explicitly.
        let selectors = std::iter::once(ProgramPointSelector::ProgramPoint(first)).chain(
            view.fixed_state
                .recorded_states
                .recent(MAX_TRANSPORT_SOURCE_POINTS)
                .into_iter()
                .map(|(selector, _)| selector.clone()),
        );
        let pointer_field = match surface_goal {
            SyntaxProposition::Comparison {
                left: read @ SyntaxTerm::Field { .. },
                operator: ComparisonOperator::Equal,
                right,
            } if matches!(right, SyntaxTerm::IntegerLiteral(value) if value == "0")
                && matches!(
                    search_input.goal().and_then(Proposition::old_condition),
                    Some((
                        OldConditionTerm::PointerEqual(..) | OldConditionTerm::AddressEqual(..),
                        true
                    ))
                ) =>
            {
                Some(read)
            }
            _ => None,
        };
        let mut tried = BTreeSet::new();
        for selector in selectors {
            if (names_result && !crate::surface::program_point_can_name_result(Some(&selector)))
                || !tried.insert(selector.clone())
            {
                continue;
            }
            // An exact equality between the two reads lets the historical
            // null fact close by rewrite. Both facts must check in the
            // ordinary proof; a failed candidate leaves the goal alone.
            if let Some(read) = pointer_field {
                let equality = SyntaxProposition::Comparison {
                    left: read.clone(),
                    operator: ComparisonOperator::Equal,
                    right: SyntaxTerm::At {
                        selector: selector.clone(),
                        expression: Box::new(read.clone()),
                    },
                };
                let proof = ProofCertificate::from_steps(vec![ProofStep::Known])
                    .expect("known is an ordinary certificate step");
                let steps = vec![
                    ProofStep::Have {
                        proposition: equality.clone(),
                        proof: Box::new(proof),
                    },
                    ProofStep::Rewrite(equality),
                    ProofStep::Known,
                ];
                if let Some(proof) = attempt::candidate_outcome(
                    search_input
                        .driver()
                        .apply_ordinary_transport_steps(surface_goal, steps),
                )? && proof.is_complete()
                {
                    return Ok(Some(proof));
                }
            }
            let source = SyntaxProposition::At {
                selector,
                proposition: Box::new(surface_goal.clone()),
            };
            match crate::kernel::search::ProofSearch::try_fixed_state_fact_transport(
                search_input,
                &source,
                surface_goal,
                std::iter::once(source.clone()),
            ) {
                Ok(Some(proof)) if proof.is_complete() => return Ok(Some(proof)),
                Ok(_) => {}
                Err(_) => {
                    check_verification_deadline()?;
                }
            }
            if let Some(proof) = crate::kernel::search::ProofSearch::try_projected_state_transport(
                search_input,
                &source,
                surface_goal,
            )? {
                return Ok(Some(proof));
            }
        }
        Ok(None)
    }

    /// A guarded universal goal whose recorded-point form is held only as
    /// the conjunct of a larger guarded universal there, such as
    /// `forall k { k < n implies p[k] == v }` from a call's
    /// `forall k { k < n implies defined(p[k]) and p[k] == v }`. The larger
    /// fact is selected by one probe of the indexed conjunct projections
    /// (`PureFactStore::quantified_conjunct_projection_source`) with the goal
    /// lowered at that point, so a point holding no such fact costs one
    /// lowering and one lookup. The proof uses the larger fact to establish
    /// the selected conjunct and records the steps for expansion.
    pub(in crate::surface::proof) fn try_projected_state_transport(
        search_input: &Proof<'a>,
        source: &SyntaxProposition,
        surface_goal: &SyntaxProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_projected_state_transport");
        let Ok(lowered) = search_input
            .lower_surface_proposition_direct(source, "smart projected transport source")
        else {
            check_verification_deadline()?;
            return Ok(None);
        };
        let Some(full) = search_input
            .facts()
            .quantified_conjunct_projection_source(&lowered)
        else {
            return Ok(None);
        };
        let full = full.clone();
        let Some(full_surface) = crate::kernel::search::ProofSearch::resolve_solve_premises(
            search_input,
            std::slice::from_ref(&full),
            &[],
        )
        .and_then(|pairs| pairs.into_iter().next())
        .map(|(_, surface)| surface) else {
            return Ok(None);
        };
        match crate::kernel::search::ProofSearch::try_fixed_state_fact_transport(
            search_input,
            &full_surface,
            surface_goal,
            std::iter::once(full_surface.clone()),
        ) {
            Ok(Some(proof)) if proof.is_complete() => Ok(Some(proof)),
            Ok(_) => Ok(None),
            Err(_) => {
                check_verification_deadline()?;
                Ok(None)
            }
        }
    }

    /// A goal that reads one cell at two states, such as
    /// `owner->cell[0] == owner->phase` right after a store wrote the first
    /// side from the second, holds when nothing in between wrote that cell.
    /// That is a frame fact: carry the cell's reflexive equality from a
    /// recorded point to the goal by `transport`, whose checker takes the
    /// frame evidence (an exact `separate`, say) as its listed premises.
    pub(in crate::surface::proof) fn try_cell_frame_transport_closure(
        search_input: &Proof<'a>,
        surface_goal: &SyntaxProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_cell_frame_transport_closure");
        if let Some(source) = old_reflexive_transport_source(surface_goal)
            && let Some(proof) = Self::try_execution_proposition_read_preservation(
                search_input,
                &source,
                surface_goal,
                MAX_TRANSPORT_SOURCE_POINTS,
            )?
            && proof.is_complete()
        {
            return Ok(Some(proof));
        }
        let Some((
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left,
                right,
            },
            true,
        )) = search_input.goal().and_then(Proposition::old_condition)
        else {
            return Ok(None);
        };
        let load = |term: &OldMachineTerm| match term {
            OldMachineTerm::Variable(variable) => {
                crate::kernel::registered_load_term_for_variable(variable)
            }
            OldMachineTerm::MemoryLoad(..) => Some(term.clone()),
            _ => None,
        };
        let (
            Some(OldMachineTerm::MemoryLoad(left_memory, left_pointer, left_kind)),
            Some(OldMachineTerm::MemoryLoad(right_memory, right_pointer, right_kind)),
        ) = (load(left), load(right))
        else {
            return Ok(None);
        };
        if left_pointer.address() != right_pointer.address()
            || left_kind != right_kind
            || left_memory.point() == right_memory.point()
        {
            return Ok(None);
        }
        if matches!(
            left_kind,
            crate::kernel::LoadKind::Int32 | crate::kernel::LoadKind::UInt32
        ) && let Some(proof) =
            Self::try_anchored_field_preservation(search_input, surface_goal, &left_pointer)?
            && proof.is_complete()
        {
            return Ok(Some(proof));
        }
        let Some(view) = search_input.premise_fixed_state_view() else {
            return Ok(None);
        };
        // The cell as the current state reads it.
        let current = crate::kernel::intern_memory_ref(view.fixed_state.state.memory());
        // A memory-named read of the current memory, compared without
        // making a point for it.
        let reads_current = |point: &crate::kernel::ProgramPoint| {
            point.read_version_id().is_none() && *point.shared_memory() == current
        };
        let current_side = if reads_current(right_memory.point()) {
            right
        } else if reads_current(left_memory.point()) {
            left
        } else {
            return Ok(None);
        };
        let Some(cell) = super::surface_synthesis::synthesize_surface_machine_expression(
            current_side,
            view.parameter_binding,
            view.fixed_state.state,
        ) else {
            return Ok(None);
        };
        let reflexive = SyntaxProposition::Comparison {
            left: cell.clone(),
            operator: ComparisonOperator::Equal,
            right: cell,
        };
        let selectors = view
            .fixed_state
            .recorded_states
            .recent(MAX_TRANSPORT_SOURCE_POINTS)
            .into_iter()
            .map(|(selector, _)| selector.clone())
            .collect::<Vec<_>>();
        for selector in selectors {
            let source = SyntaxProposition::At {
                selector,
                proposition: Box::new(reflexive.clone()),
            };
            match crate::kernel::search::ProofSearch::try_fixed_state_fact_transport(
                search_input,
                &source,
                surface_goal,
                std::iter::empty(),
            ) {
                Ok(Some(proof)) if proof.is_complete() => return Ok(Some(proof)),
                Ok(_) => {}
                Err(_) => check_verification_deadline()?,
            }
        }
        Ok(None)
    }

    /// Close an implication whose algebraic guard is refuted by a checked
    /// rewrite and direct normalization. A miss does not run general solve on
    /// the guard or select the implication's connected fact component.
    pub(in crate::surface::proof) fn try_constructor_guard_refutation(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_constructor_guard_refutation");
        let Some(Proposition::Implies(guard, _)) = search_input.goal() else {
            return Ok(None);
        };
        let comparison = match guard.as_ref() {
            Proposition::Not(body) => body.as_ref(),
            guard => guard,
        };
        if !matches!(
            comparison,
            Proposition::Equal(Term::Algebraic(_), Term::Algebraic(_))
        ) {
            return Ok(None);
        }
        let Some(antecedent) = search_input
            .surface_goal()
            .and_then(surface_implication_antecedent)
        else {
            return Ok(None);
        };
        let opposite = negate_click_proposition(&antecedent);
        let Some(scope) =
            attempt::candidate_outcome(search_input.driver().open_have(opposite.clone()))?
        else {
            return Ok(None);
        };
        let Some(proved) = (scope).driver().try_direct_model_equality_rewrite_closure() else {
            check_verification_deadline()?;
            return Ok(None);
        };
        let Some(joined) = attempt::candidate_outcome(proved.join())? else {
            return Ok(None);
        };
        let Some(introduced) =
            attempt::candidate_outcome(joined.driver().apply_step(ProofStep::Intro))?
        else {
            return Ok(None);
        };
        attempt::candidate_outcome(Self::close_refuted_fact(&introduced, &opposite))?
            .map(|closed| joined.finish_generated_intro(&introduced, closed))
            .transpose()
    }

    // Walk consecutive implication guards without retaining a dispatcher
    // frame for each. Each guard keeps its checked introduction, contradiction
    // probes, and named-premise extraction before the body is simplified.
    #[inline(never)]
    pub(in crate::surface::proof) fn try_implication_solve_closure(
        search_input: &Proof<'a>,
        surface_antecedent: &SyntaxProposition,
        introduced_surfaces: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_implication_solve_closure");
        let mut base = search_input.clone();
        let mut antecedent = surface_antecedent.clone();
        let mut available_surfaces = introduced_surfaces.to_vec();
        let mut openings = Vec::new();
        let mut closed = 'intro: loop {
            let Some(mut introduced) =
                attempt::candidate_outcome(base.driver().apply_step(ProofStep::Intro))?
            else {
                return Ok(None);
            };
            // The introduced antecedent itself is the uniquely selected
            // contradiction candidate. This is a constant-size probe:
            // `Contradiction` checks that exact fact and its indexed
            // opposite, without scanning ambient path facts.
            if let Some(closed) =
                crate::kernel::search::ProofSearch::try_introduced_antecedent_contradiction(
                    &(introduced),
                    &antecedent,
                )?
            {
                openings.push((base, introduced));
                break closed;
            }
            // A selected execution path can make the antecedent false through a
            // short derivation rather than an already-indexed exact opposite.
            // Prove and retain that opposite first; after `intro`, ordinary
            // contradiction checks the two explicit facts.
            let negated_antecedent = negate_click_proposition(&antecedent);
            if let Some(scope) =
                attempt::candidate_outcome(base.driver().open_have(negated_antecedent.clone()))?
                && let Some(proved) = (scope).driver().try_solve_closure()?
                && let Some(with_opposite) = attempt::candidate_outcome(proved.join())?
                && let Some(with_antecedent) =
                    attempt::candidate_outcome(with_opposite.driver().apply_step(ProofStep::Intro))?
                && let Some(closed) = attempt::candidate_outcome(Self::close_refuted_fact(
                    &with_antecedent,
                    &antecedent,
                ))?
            {
                openings.push((with_opposite, with_antecedent));
                break closed;
            }
            openings.push((base, introduced.clone()));
            let mut conjuncts = Vec::new();
            if matches!(&antecedent, SyntaxProposition::And(_, _)) {
                collect_surface_conjunct_leaves(&antecedent, &mut conjuncts);
            }
            for conjunct in &conjuncts {
                let Some(extracted) = attempt::candidate_outcome(Self::publish_selected_fact(
                    &introduced,
                    &(conjunct.clone()),
                ))?
                else {
                    return Ok(None);
                };
                introduced = extracted;
                if introduced.is_complete() {
                    break 'intro introduced;
                }
                // Each conjunct is probed as a curried antecedent would be:
                // `a and b implies c` closes where `a implies b implies c`
                // does, when the facts hold a conjunct's exact opposite.
                if let Some(closed) =
                    crate::kernel::search::ProofSearch::try_introduced_antecedent_contradiction(
                        &(introduced),
                        conjunct,
                    )?
                {
                    break 'intro closed;
                }
            }
            available_surfaces.push(antecedent.clone());
            available_surfaces.extend(conjuncts.iter().cloned());
            // Introducing this guard can make a previously introduced
            // conditional premise usable. Select its written consequent
            // and let an ordinary checked implication application discharge the
            // guard; do not branch over possible guard values.
            for premise in available_surfaces.clone() {
                let mut current = &premise;
                while let SyntaxProposition::Implies(_, consequent) = current {
                    let Some(extracted) = attempt::candidate_outcome(Self::publish_selected_fact(
                        &introduced,
                        &(consequent.as_ref().clone()),
                    ))?
                    else {
                        break;
                    };
                    introduced = extracted;
                    available_surfaces.push(consequent.as_ref().clone());
                    if introduced.is_complete() {
                        break 'intro introduced;
                    }
                    current = consequent;
                }
            }
            if !conjuncts.is_empty()
                && let Some(surface_goal) = introduced.surface_goal()
                && let Some(source) = old_reflexive_transport_source(surface_goal)
            {
                match crate::kernel::search::ProofSearch::try_fixed_state_fact_transport(
                    &(introduced),
                    &source,
                    surface_goal,
                    conjuncts.iter().cloned(),
                ) {
                    Ok(Some(transported)) if transported.is_complete() => {
                        break transported;
                    }
                    Ok(_) => {}
                    Err(_) => check_verification_deadline()?,
                }
            }
            if let Some(split) = crate::kernel::search::ProofSearch::try_upper_bound_split_closure(
                &(introduced),
                &available_surfaces,
            )? {
                break split;
            }
            if let Some(closed) =
                crate::kernel::search::ProofSearch::try_direct_logical_closure(&(introduced))?
            {
                break closed;
            }
            if matches!(introduced.goal(), Some(Proposition::Implies(_, _)))
                && let Some(next) = introduced
                    .surface_goal()
                    .and_then(surface_implication_antecedent)
            {
                base = introduced;
                antecedent = next;
                continue;
            }
            let Some(closed) =
                Self::try_solve_closure_with_surfaces(&introduced, &available_surfaces)?
            else {
                return Ok(None);
            };
            break closed;
        };
        for (parent, introduced) in openings.into_iter().rev() {
            closed = parent.finish_generated_intro(&introduced, closed)?;
        }
        Ok(Some(closed))
    }

    /// Compare the written descriptors with recorded separation facts. Each
    /// proposed equality is applied by ordinary rewrite; there is no call to
    /// solve or transport inside the candidate proof. The tactic work budget
    /// bounds selection, and at most sixteen separation facts are attempted.
    pub(in crate::surface::proof) fn try_resource_descriptor_rewrite_closure(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_resource_descriptor_rewrite_closure");
        let Some(target @ SyntaxProposition::Separate { .. }) = search_input.surface_goal() else {
            return Ok(None);
        };
        let Some(surfaces) = search_input.premise_surface_facts() else {
            return Ok(None);
        };
        let written_sources = surfaces
            .requirement_kernel_atoms_for_search()
            .filter(|fact| matches!(fact, Proposition::ResourceSeparate { .. }))
            .take(16)
            .map(|fact| {
                surfaces
                    .recorded_requirement_surface(fact)
                    .expect("requirement atoms retain their enclosing source clause")
                    .clone()
            });
        for source in Self::marked_entry_separation_sources(search_input, target)
            .into_iter()
            .chain(written_sources)
        {
            check_verification_deadline()?;
            let mut source = &source;
            while let SyntaxProposition::At { proposition, .. } = source {
                source = proposition;
            }
            let Some(steps) = resource_descriptor_rewrite_steps(target, source) else {
                continue;
            };
            let mut candidate = Some(search_input.clone());
            for step in steps {
                let Some(proof) = candidate.take() else {
                    break;
                };
                candidate = attempt::candidate_outcome(proof.driver().apply_step(step))?;
            }
            if let Some(proof) = candidate
                && (proof.focused_discharged() || proof.is_complete())
            {
                return Ok(Some(proof));
            }
        }
        Ok(None)
    }

    fn marked_entry_separation_sources(
        proof: &Proof<'a>,
        target: &SyntaxProposition,
    ) -> Vec<SyntaxProposition> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("marked_entry_separation_sources");
        use crate::surface::{ContractSegmentSurface, ProgramPointSelector, ResourceSubject};
        let Some(view) = proof.premise_fixed_state_view() else {
            return Vec::new();
        };
        let points = view.fixed_state.recorded_states;
        let Some((entry, sources)) = &points.entry_separation_sources else {
            return Vec::new();
        };
        let Some(selector @ ProgramPointSelector::Mark(_)) = points.point_name(*entry) else {
            return Vec::new();
        };
        let Some(mut goal) = proof.goal() else {
            return Vec::new();
        };
        while let Proposition::And(stated, _) = goal {
            goal = stated;
        }
        let (
            SyntaxProposition::Separate { left, right },
            Proposition::ResourceSeparate {
                left: goal_left,
                right: goal_right,
            },
        ) = (target, goal)
        else {
            return Vec::new();
        };
        let anchor = |expression: &SyntaxTerm| match expression {
            SyntaxTerm::ProgramExpression(ProgramExpression::Value(_)) => expression.clone(),
            _ => SyntaxTerm::At {
                selector: selector.clone(),
                expression: Box::new(expression.clone()),
            },
        };
        let source = |resource: &Resource, goal: &Resource, written: &ResourceSubject| {
            if resource == goal {
                return Some(written.clone());
            }
            let Resource::Memory(range) = resource else {
                return None;
            };
            let segment = sources.ranges.get(range)?;
            let ContractSegmentSurface::Range { base, start, end } = &segment.surface else {
                return None;
            };
            Some(ResourceSubject::SavedMemory {
                base: anchor(base),
                start: anchor(start),
                end: Some(anchor(end)),
            })
        };
        sources
            .facts
            .iter()
            .take(16)
            .filter_map(|fact| {
                crate::instrumentation::record_deterministic_work(1);
                let Proposition::ResourceSeparate { left: a, right: b } = fact else {
                    return None;
                };
                Some(SyntaxProposition::Separate {
                    left: source(a, goal_left, left)?,
                    right: source(b, goal_right, right)?,
                })
            })
            .collect()
    }

    /// Search chooses enclosing separated regions; replay cites containment
    /// and the ordinary restriction law. No store invokes this planner.
    pub(in crate::surface::proof) fn try_resource_separation_restriction_closure(
        search_input: &Proof<'a>,
        surface_goal: &SyntaxProposition,
        introduced_surfaces: &[SyntaxProposition],
        indexed_read: bool,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_resource_separation_restriction_closure");
        let SyntaxProposition::Separate { left, right } = surface_goal else {
            return Ok(None);
        };
        let Some(mut kernel_goal) = search_input.goal() else {
            return Ok(None);
        };
        // Resource lowering appends formation conditions to the stated fact.
        // Planning retains and proves the complete Surface goal below.
        while let Proposition::And(stated, _) = kernel_goal {
            kernel_goal = stated;
        }
        let Proposition::ResourceSeparate {
            left: goal_left,
            right: goal_right,
        } = kernel_goal
        else {
            return Ok(None);
        };
        if !matches!(
            (goal_left.as_ref(), goal_right.as_ref()),
            (Resource::Memory(_), Resource::Memory(_))
        ) {
            return Ok(None);
        }
        let Some(view) = search_input.premise_fixed_state_view() else {
            return Ok(None);
        };
        // A covering range can be based on a pointer bound by an enclosing
        // match or a value retained at a recorded program point.
        let _binder_names = search_input.requirement_binder_name_scope();
        let _recorded_points = super::surface_synthesis::SynthesisRecordedPointsScope::enter(
            view.fixed_state.recorded_states,
        );
        let mut candidates = search_input
            .facts()
            .assumptions()
            .resource_separation_candidates(goal_left, goal_right)
            .unwrap_or_default()
            .into_iter()
            .cloned()
            .collect::<Vec<_>>();
        for fact in view.fixed_state.state.resources().facts() {
            if fact.is_own() && matches!(fact.resource(), Resource::Memory(_)) {
                candidates.push(Proposition::ResourceSeparate {
                    left: Box::new(fact.resource().clone()),
                    right: goal_right.clone(),
                });
            }
        }
        for candidate in candidates {
            check_verification_deadline()?;
            let Proposition::ResourceSeparate { left: a, right: b } = &candidate else {
                continue;
            };
            if !matches!(
                (a.as_ref(), b.as_ref()),
                (Resource::Memory(_), Resource::Memory(_))
            ) {
                continue;
            }
            if a == goal_left && b == goal_right {
                continue;
            }
            // The goal already owns exact spellings for these resources,
            // including reads at its selected historical points. Keep those
            // names instead of reconstructing them from the current state.
            let source = |resource: &Resource| {
                if resource == goal_left.as_ref() {
                    return Ok(left.clone());
                }
                if resource == goal_right.as_ref() {
                    return Ok(right.clone());
                }
                super::surface_synthesis::synthesize_surface_resource_subject(
                    resource,
                    view.parameter_binding,
                    view.fixed_state.state,
                    &BTreeMap::new(),
                )
                .ok_or_else(|| {
                    search_input.step_error("a separation restriction source has no Surface form")
                })
            };
            let (a, b) = (source(a)?, source(b)?);
            for (a, b) in [(a.clone(), b.clone()), (b, a)] {
                let separate = SyntaxProposition::Separate {
                    left: a.clone(),
                    right: b.clone(),
                };
                let premises = vec![
                    separate,
                    SyntaxProposition::Contains {
                        parent: a.clone(),
                        child: left.clone(),
                    },
                    SyntaxProposition::Contains {
                        parent: b.clone(),
                        child: right.clone(),
                    },
                ];
                let mut proof = search_input.clone();
                let mut proved = true;
                for (index, premise) in premises.iter().enumerate() {
                    let Some(scope) =
                        attempt::candidate_outcome(proof.driver().open_have(premise.clone()))?
                    else {
                        proved = false;
                        break;
                    };
                    // Never recursively search for a larger separation here.
                    let closed = if index == 0 {
                        scope.driver().try_direct_logical_closure()?
                    } else if indexed_read
                        && let Some(step) = Self::indexed_containment_step(premise)
                        && let Some(closed) =
                            attempt::candidate_outcome(scope.driver().apply_step(step))?
                    {
                        Some(closed)
                    } else {
                        scope
                            .driver()
                            .try_solve_closure_with_surfaces(introduced_surfaces)?
                    };
                    let Some(closed) = closed else {
                        proved = false;
                        break;
                    };
                    proof = closed.join()?;
                }
                if !proved {
                    continue;
                }
                let resource_arg =
                    |r: &crate::surface::ResourceSubject| SyntaxTerm::Resource(Box::new(r.clone()));
                proof = proof.driver().apply_step(ProofStep::ApplyPlannedTheorem {
                    application: TheoremApplication {
                        name: "click::separation::separate_restrict".into(),
                        arguments: vec![
                            resource_arg(&a),
                            resource_arg(&b),
                            resource_arg(left),
                            resource_arg(right),
                        ],
                    },
                    premises,
                })?;
                if proof.is_complete() || proof.goal() != search_input.goal() {
                    return Ok(Some(proof));
                }
                if let Some(closed) = Self::try_direct_logical_closure(&proof)? {
                    return Ok(Some(closed));
                }
            }
        }
        Ok(None)
    }

    /// Expand separation from a conjunction through the existing library laws.
    /// Only search recurses over the descriptor; replay applies each law once.
    pub(in crate::surface::proof) fn try_resource_star_separation_closure(
        search_input: &Proof<'a>,
        surface_goal: &SyntaxProposition,
        introduced_surfaces: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_resource_star_separation_closure");
        let SyntaxProposition::Separate { left, right } = surface_goal else {
            return Ok(None);
        };
        let (a, b, other, reversed) = match (left, right) {
            (crate::surface::ResourceSubject::Star(a, b), other) => (a, b, other, false),
            (other, crate::surface::ResourceSubject::Star(a, b)) => (a, b, other, true),
            _ => return Ok(None),
        };
        let resource_arg = |resource: &crate::surface::ResourceSubject| {
            SyntaxTerm::Resource(Box::new(resource.clone()))
        };
        let separate = |left: &crate::surface::ResourceSubject,
                        right: &crate::surface::ResourceSubject| {
            SyntaxProposition::Separate {
                left: left.clone(),
                right: right.clone(),
            }
        };
        let mut proof = search_input.clone();
        let mut premises = Vec::new();
        for child in [a.as_ref(), b.as_ref()] {
            check_verification_deadline()?;
            let premise = if reversed {
                separate(other, child)
            } else {
                separate(child, other)
            };
            let scope = proof.driver().open_have(premise.clone())?;
            let Some(closed) = scope
                .driver()
                .try_solve_closure_with_surfaces(introduced_surfaces)?
            else {
                return Ok(None);
            };
            proof = closed.join()?;
            if reversed {
                proof = proof.driver().apply_step(ProofStep::ApplyPlannedTheorem {
                    application: TheoremApplication {
                        name: "click::separation::separate_symm".into(),
                        arguments: vec![resource_arg(other), resource_arg(child)],
                    },
                    premises: vec![premise],
                })?;
            }
            premises.push(separate(child, other));
        }
        proof = proof.driver().apply_step(ProofStep::ApplyPlannedTheorem {
            application: TheoremApplication {
                name: "click::separation::separate_star".into(),
                arguments: vec![resource_arg(a), resource_arg(b), resource_arg(other)],
            },
            premises,
        })?;
        if reversed {
            proof = proof.driver().apply_step(ProofStep::ApplyPlannedTheorem {
                application: TheoremApplication {
                    name: "click::separation::separate_symm".into(),
                    arguments: vec![resource_arg(right), resource_arg(left)],
                },
                premises: vec![separate(right, left)],
            })?;
        }
        if proof.is_complete() || proof.goal() != search_input.goal() {
            Ok(Some(proof))
        } else {
            Self::try_direct_logical_closure(&proof)
        }
    }

    /// Refines the Proof-owned Surface goal through audited scopes and steps.
    /// The caller cannot supply a second description of the judgment: this
    /// syntax is the view paired with the kernel goal in `PropositionObligation`.
    /// Keep branch-local proof/syntax temporaries out of this recursive frame.
    #[inline(never)]
    pub(in crate::surface::proof) fn try_structural_solve_closure_with_surfaces(
        search_input: &Proof<'a>,
        surface_goal: &SyntaxProposition,
        introduced_surfaces: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_structural_solve_closure_with_surfaces");
        let Some(goal) = search_input.goal() else {
            return Ok(None);
        };
        if search_input.has_conjunctive_goal() {
            // The split owns the checked Surface-to-kernel correspondence.
            // In particular, a lowered existential body may be a conjunction
            // whose written Surface spelling is only the body; do not gate
            // this on a shape heuristic.
            // A smart closure candidate may encounter a kernel conjunction
            // whose written presentation is not recoverable.  Decline this
            // candidate so the caller can report its ordinary bounded proof
            // failure; the explicit `both` operation still rejects the same
            // mismatch transactionally through the checked split.
            match search_input.checked_both_surface_children() {
                Ok(_) => {}
                Err(_) => {
                    // Preserve the bounded-operation contract: a
                    // presentation mismatch declines this candidate, but a
                    // deadline raised while checking its lowering must still
                    // escape.
                    check_verification_deadline()?;
                    return Ok(None);
                }
            }
            return crate::kernel::search::ProofSearch::try_structural_and_solve_closure(
                search_input,
                introduced_surfaces,
            );
        }
        let disjuncts = if matches!(goal, Proposition::Or(..)) {
            surface_logical_children(surface_goal, false)
        } else {
            // A retained membership goal exposes the same checked choices as
            // its old disjunction. The singleton has just one candidate.
            crate::kernel::sequence_membership_view(goal)
                .and_then(|view| search_input.structural_proposition_candidate(&view))
                .map(|surface| {
                    surface_logical_children(&surface, false)
                        .unwrap_or_else(|| (surface.clone(), surface))
                })
        };
        if let Some((surface_left, surface_right)) = disjuncts {
            return crate::kernel::search::ProofSearch::try_structural_or_solve_closure(
                search_input,
                &surface_left,
                &surface_right,
                introduced_surfaces,
            );
        }
        if matches!(goal, Proposition::Implies(_, _))
            && let Some(surface_antecedent) = surface_implication_antecedent(surface_goal)
        {
            return crate::kernel::search::ProofSearch::try_implication_solve_closure(
                search_input,
                &surface_antecedent,
                introduced_surfaces,
            );
        }
        if let (SyntaxProposition::Exists { .. }, Proposition::Exists { var, body, .. }) =
            (surface_goal, goal)
            && let Some(closed) =
                crate::kernel::search::ProofSearch::try_constructor_witness_exists_closure(
                    search_input,
                    **var,
                    body,
                    introduced_surfaces,
                )?
        {
            return Ok(Some(closed));
        }
        match (surface_goal, goal) {
            (SyntaxProposition::Exists { .. }, goal @ Proposition::Exists { .. })
                if quantified_external_range_goal(goal) =>
            {
                crate::kernel::search::ProofSearch::try_structural_exists_solve_closure(
                    search_input,
                    introduced_surfaces,
                )
            }
            (
                SyntaxProposition::ForAll { .. } | SyntaxProposition::RangeAll { .. },
                Proposition::ForAll { .. },
            ) => crate::kernel::search::ProofSearch::try_structural_forall_solve_closure(
                search_input,
                surface_goal,
                introduced_surfaces,
            ),
            // A predicate-call goal unfolds to its body, which the
            // structural arms and logical closers then work over. Repeat
            // unfolds are refused so recursive predicate bodies cannot loop
            // the search.
            (SyntaxProposition::PredicateCall { name, .. }, _) => {
                crate::kernel::search::ProofSearch::try_structural_predicate_solve_closure(
                    search_input,
                    name,
                    introduced_surfaces,
                )
            }
            _ => Ok(None),
        }
    }

    /// `exists v { x == C(.., v, ..) }` where the facts already give `x` a
    /// constructor `C(.., t, ..)` of the same variant: the witness is `t`,
    /// read off that constructor, as a proof would name it with `witness`.
    /// One lookup in the constructor index; the checked `witness` step and
    /// an ordinary closure of the instance decide it.
    #[inline(never)]
    pub(in crate::surface::proof) fn try_constructor_witness_exists_closure(
        search_input: &Proof<'a>,
        var: Variable,
        body: &Proposition,
        introduced_surfaces: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_constructor_witness_exists_closure");
        use crate::kernel::{AlgebraicTermNode, AlgebraicValue};
        let Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) = body else {
            return Ok(None);
        };
        let is_bound = |field: &AlgebraicValue| match field {
            AlgebraicValue::Program(
                ProgramValue::Int32(term)
                | ProgramValue::UInt32(term)
                | ProgramValue::Int8(term)
                | ProgramValue::Int16(term)
                | ProgramValue::UInt8(term)
                | ProgramValue::UInt16(term)
                | ProgramValue::Int64(term)
                | ProgramValue::UInt64(term)
                | ProgramValue::Bool(term),
            ) => *term == OldMachineTerm::Variable(var),
            _ => false,
        };
        // The written pattern and the value it describes, in either order.
        let split = |pattern: &crate::kernel::AlgebraicTerm| match &pattern.node {
            AlgebraicTermNode::Constructor { variant, fields } => fields
                .iter()
                .position(is_bound)
                .map(|index| (variant.clone(), index)),
            _ => None,
        };
        let Some((value, (variant, index))) = split(right.old_form())
            .map(|found| (left, found))
            .or_else(|| split(left.old_form()).map(|found| (right, found)))
        else {
            return Ok(None);
        };
        let Some(known) = search_input
            .facts()
            .assumptions()
            .known_algebraic_constructor(value.old_form())
        else {
            return Ok(None);
        };
        let AlgebraicTermNode::Constructor {
            variant: known_variant,
            fields,
        } = &known.node
        else {
            return Ok(None);
        };
        let Some(AlgebraicValue::Program(field)) =
            fields.get(index).filter(|_| *known_variant == variant)
        else {
            return Ok(None);
        };
        // A constant is written as itself; any other value by the local,
        // parameter or binder that holds it.
        let constant = matches!(
            field,
            ProgramValue::Int32(term)
                | ProgramValue::UInt32(term)
                | ProgramValue::Int8(term)
                | ProgramValue::Int16(term)
                | ProgramValue::UInt8(term)
                | ProgramValue::UInt16(term)
                | ProgramValue::Int64(term)
                | ProgramValue::UInt64(term)
                | ProgramValue::Bool(term)
                if matches!(
                    term,
                    bits32_constant!(_)
                        | int64_constant!(_)
                        | uint64_constant!(_)
                )
        );
        let variable = match field {
            ProgramValue::Int32(term)
            | ProgramValue::UInt32(term)
            | ProgramValue::Int8(term)
            | ProgramValue::Int16(term)
            | ProgramValue::UInt8(term)
            | ProgramValue::UInt16(term)
            | ProgramValue::Int64(term)
            | ProgramValue::UInt64(term)
            | ProgramValue::Bool(term) => match term {
                OldMachineTerm::Variable(variable) => Some(*variable),
                _ => None,
            },
            _ => None,
        };
        let spelled = if constant {
            Some(SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                field.clone(),
            )))
        } else if let ProofContext::Pure(context) = search_input.context.as_ref() {
            // A theorem's values are its parameters and binders, by name.
            let (intro_names, local_names) = search_input.binder_variable_names();
            context
                .theorem_context
                .values
                .iter()
                .find(|(_, value)| *value == field)
                .map(|(name, _)| SurfaceBinder::from(name))
                .or_else(|| {
                    variable.and_then(|variable| {
                        context
                            .source_names
                            .get(&variable)
                            .cloned()
                            .or_else(|| local_names.get(&variable).cloned())
                            .or_else(|| intro_names.get(&variable).cloned())
                    })
                })
                .map(|name| {
                    SyntaxTerm::ProgramExpression(ProgramExpression::Variable((name).into()))
                })
        } else {
            search_input.premise_fixed_state_view().and_then(|view| {
                super::surface_synthesis::synthesize_surface_value(
                    field,
                    view.parameter_binding,
                    view.fixed_state.state,
                )
            })
        };
        let Some(spelled) = spelled else {
            return Ok(None);
        };
        check_verification_deadline()?;
        let witness = ProofWitness::single(spelled);
        let Some(introduced) = attempt::candidate_outcome(
            search_input
                .driver()
                .apply_step(ProofStep::Witness(witness)),
        )?
        else {
            return Ok(None);
        };
        crate::kernel::search::ProofSearch::try_solve_closure_with_surfaces(
            &(introduced),
            introduced_surfaces,
        )
    }

    // These helpers preserve the dispatcher's search order and checked steps;
    // their stack storage is needed only for the selected connective.
    #[inline(never)]
    pub(in crate::surface::proof) fn try_structural_exists_solve_closure(
        search_input: &Proof<'a>,
        introduced_surfaces: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_structural_exists_solve_closure");
        let ProofContext::Execution(context) = search_input.context.as_ref() else {
            return Ok(None);
        };
        let mut candidates = Vec::new();
        for argument in context.arguments {
            if matches!(argument, ProgramExpression::Value(ProgramValue::Int32(_))) {
                candidates.push(SyntaxTerm::ProgramExpression(argument.clone()));
            }
        }
        // The range-loadability source slice has no witness in its call
        // arguments, so zero is the deterministic fallback.  It is tried
        // after call arguments to keep this operation useful for other
        // source-backed existential requirements without searching ambient
        // facts.
        candidates.push(SyntaxTerm::ProgramExpression(ProgramExpression::Value(
            ProgramValue::Int32(OldMachineTerm::constant(0)),
        )));
        for value in candidates {
            check_verification_deadline()?;
            let witness = ProofWitness::single(value);
            let Some(introduced) = attempt::candidate_outcome(
                search_input
                    .driver()
                    .apply_step(ProofStep::Witness(witness)),
            )?
            else {
                continue;
            };
            if let Some(closed) =
                crate::kernel::search::ProofSearch::try_solve_closure_with_surfaces(
                    &(introduced),
                    introduced_surfaces,
                )?
            {
                return Ok(Some(closed));
            }
        }
        Ok(None)
    }

    #[inline(never)]
    pub(in crate::surface::proof) fn try_structural_forall_solve_closure(
        search_input: &Proof<'a>,
        surface_goal: &SyntaxProposition,
        introduced_surfaces: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_structural_forall_solve_closure");
        if let Some(enumerated) = crate::kernel::search::ProofSearch::try_finite_forall_enumeration(
            search_input,
            surface_goal,
        )? {
            return Ok(Some(enumerated));
        }
        match attempt::candidate_outcome(search_input.driver().apply_step(ProofStep::Intro))? {
            Some(introduced) => {
                crate::kernel::search::ProofSearch::try_solve_closure_with_surfaces(
                    &introduced,
                    introduced_surfaces,
                )?
                .map(|closed| search_input.finish_generated_intro(&introduced, closed))
                .transpose()
            }
            None => Ok(None),
        }
    }

    #[inline(never)]
    pub(in crate::surface::proof) fn try_structural_and_solve_closure(
        search_input: &Proof<'a>,
        introduced_surfaces: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_structural_and_solve_closure");
        let (split_proof, split, ids) = search_input.split_focused_both()?;
        let marker = split_proof.conjunction_checkpoint(ids)?;
        let Some(left) = crate::kernel::search::ProofSearch::try_solve_closure_with_surfaces(
            &(split_proof.focus_branch(ids[0])?),
            introduced_surfaces,
        )?
        else {
            return Ok(None);
        };
        let Some(right) = crate::kernel::search::ProofSearch::try_solve_closure_with_surfaces(
            &(left.focus_branch(ids[1])?),
            introduced_surfaces,
        )?
        else {
            return Ok(None);
        };
        attempt::candidate_outcome(right.join_focused_both(&marker, split, ids))
    }

    #[inline(never)]
    pub(in crate::surface::proof) fn try_structural_predicate_solve_closure(
        search_input: &Proof<'a>,
        name: &str,
        introduced_surfaces: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_structural_predicate_solve_closure");
        let Some(_guard) = PredicateSearchGuard::enter(name) else {
            return Ok(None);
        };
        let target = search_input
            .surface_goal()
            .expect("predicate goal has a Surface form")
            .clone();
        let Some(unfolded) = attempt::candidate_outcome(
            search_input
                .driver()
                .apply_step(ProofStep::UnfoldProposition(target)),
        )?
        else {
            return Ok(None);
        };
        if let Some(closed) = Self::try_solve_closure_with_surfaces(&unfolded, introduced_surfaces)?
        {
            return Ok(Some(closed));
        }
        // A premise at another snapshot is a separate application. Open it
        // explicitly so both its body and its exact source spelling are
        // available to ordinary instantiation and preservation search.
        for source in search_input.facts().mentioning_predicate(&name.to_string()) {
            check_verification_deadline()?;
            let Proposition::Predicate { .. } = source else {
                continue;
            };
            let surface = search_input
                .structural_proposition_candidate(source)
                .ok_or_else(|| {
                    search_input
                        .step_error("selected predicate premise has no structural Surface spelling")
                })?;
            let Some(opened) = attempt::candidate_outcome(
                unfolded
                    .driver()
                    .apply_step(ProofStep::UnfoldProposition(surface)),
            )?
            else {
                continue;
            };
            if let Some(closed) =
                Self::try_solve_closure_with_surfaces(&opened, introduced_surfaces)?
            {
                return Ok(Some(closed));
            }
        }
        Ok(None)
    }

    #[inline(never)]
    pub(in crate::surface::proof) fn try_structural_or_solve_closure(
        search_input: &Proof<'a>,
        surface_left: &SyntaxProposition,
        surface_right: &SyntaxProposition,
        introduced_surfaces: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_structural_or_solve_closure");
        for surface in [surface_left, surface_right] {
            let selected = (|| {
                let Some(scope) =
                    attempt::candidate_outcome(search_input.driver().open_have(surface.clone()))?
                else {
                    return Ok(None);
                };
                let Some(scope) = (scope)
                    .driver()
                    .try_solve_closure_with_surfaces(introduced_surfaces)?
                else {
                    return Ok(None);
                };
                let Some(joined) = attempt::candidate_outcome(scope.join())? else {
                    return Ok(None);
                };
                attempt::candidate_outcome(joined.driver().apply_step(ProofStep::Known))
            })();
            if let Some(selected) = selected? {
                return Ok(Some(selected));
            }
        }
        Ok(None)
    }

    /// Proves the kernel's deterministic constant-bounded universal table as
    /// checked nested `have` scopes, then closes with the ordinary
    /// `Enumerate` rule. Candidate discovery is output-sensitive in the
    /// explicit instance table; each non-vacuous instance recursively uses
    /// the same retained Proof search and no ambient universal scan.
    pub(in crate::surface::proof) fn try_finite_forall_enumeration(
        search_input: &Proof<'a>,
        surface_goal: &SyntaxProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_finite_forall_enumeration");
        let Some(goal) = search_input.goal() else {
            return Ok(None);
        };
        let Some(instances) = crate::kernel::finite_forall_goal_instances(goal, true) else {
            return Ok(None);
        };
        // Local unfolding has already made the quantifier explicit. Use
        // its written binders, including the range syntax for universals.
        let mut binder_names = Vec::new();
        let mut surface_body = surface_goal.clone();
        loop {
            match surface_body {
                SyntaxProposition::ForAll { name, body, .. } => {
                    binder_names.push(name);
                    surface_body = *body;
                }
                SyntaxProposition::RangeAll {
                    start,
                    end,
                    item,
                    body,
                    ..
                } => {
                    binder_names.push(item.clone());
                    let bound = item.reference();
                    surface_body = SyntaxProposition::Implies(
                        Box::new(SyntaxProposition::And(
                            Box::new(SyntaxProposition::Comparison {
                                left: start,
                                operator: ComparisonOperator::LessEqual,
                                right: bound.clone(),
                            }),
                            Box::new(SyntaxProposition::Comparison {
                                left: bound,
                                operator: ComparisonOperator::LessThan,
                                right: end,
                            }),
                        )),
                        body,
                    );
                    break;
                }
                _ => break,
            }
        }
        if binder_names.is_empty() {
            return Ok(None);
        }

        let mut binder_types = Vec::new();
        let mut kernel_body = goal;
        while let Proposition::ForAll { sort, body, .. } = kernel_body {
            let Some(ty) = sort.machine_integer_type() else {
                return Ok(None);
            };
            binder_types.push(ty);
            kernel_body = body;
        }
        let mut proof = search_input.clone();
        for (values, instance) in instances {
            check_verification_deadline()?;
            if values.len() != binder_names.len() {
                return Ok(None);
            }
            if matches!(
                normalize_proposition(&instance),
                NormalizedProposition::True
            ) {
                continue;
            }
            if values.len() != binder_types.len() {
                return Ok(None);
            }
            let value_expressions = values
                .iter()
                .zip(&binder_types)
                .map(|(value, ty)| {
                    SyntaxTerm::ProgramExpression(ProgramExpression::Value(ty.value_from_term(
                        if *ty == MachineIntegerType::UInt64 {
                            OldMachineTerm::uint64_constant(*value as u64)
                        } else {
                            OldMachineTerm::constant(*value as u32)
                        },
                    )))
                })
                .collect::<Vec<_>>();
            let substitutions = binder_names
                .iter()
                .cloned()
                .zip(value_expressions)
                .collect::<BTreeMap<_, _>>();
            let Ok(surface_instance) = substitute_click_proposition(&surface_body, &substitutions)
            else {
                return Ok(None);
            };
            // An instance whose guard is constant true is stated as its
            // conclusion: that is the fact a later instance's proof cites, and
            // `enumerate()` reads the table through the same normalization.
            let surface_instance = match (&instance, &surface_instance) {
                (Proposition::Implies(guard, _), SyntaxProposition::Implies(_, conclusion))
                    if matches!(normalize_proposition(guard), NormalizedProposition::True) =>
                {
                    conclusion.as_ref().clone()
                }
                _ => surface_instance,
            };
            let Some(scope) =
                attempt::candidate_outcome(proof.driver().open_have(surface_instance))?
            else {
                return Ok(None);
            };
            let Some(scope) = (scope).driver().try_solve_closure()? else {
                return Ok(None);
            };
            let Some(joined) = attempt::candidate_outcome(scope.join())? else {
                return Ok(None);
            };
            proof = joined;
        }
        attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Enumerate))
    }

    /// Closes from the just-introduced antecedent and one exact indexed
    /// opposite. The antecedent fixes the kernel pair; Surface lookup visits
    /// only forms recorded for those two facts, never the ambient set.
    pub(in crate::surface::proof) fn try_introduced_antecedent_contradiction(
        search_input: &Proof<'a>,
        surface_antecedent: &SyntaxProposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_introduced_antecedent_contradiction");
        let Some(introduced) = search_input.checked_facts().first() else {
            return Ok(None);
        };
        let opposite = match introduced {
            Proposition::ConditionIs(condition, value) => {
                Proposition::condition_is(condition.clone(), !value)
            }
            Proposition::Not(body) => body.as_ref().clone(),
            proposition => Proposition::Not(Box::new(proposition.clone())),
        };
        // The facts may hold the opposite in another of its spellings,
        // `x > 100` for `x <= 100` false.
        let Some(opposite) = std::iter::once(opposite.clone())
            .chain(crate::kernel::proof::fact_reasoning::condition_polarity_forms(&opposite))
            .find(|form| search_input.facts().contains(form))
        else {
            return Ok(None);
        };
        if let Some(closed) =
            attempt::candidate_outcome(Self::close_refuted_fact(search_input, surface_antecedent))?
        {
            return Ok(Some(closed));
        }
        let surfaces = match search_input.context.as_ref() {
            ProofContext::Pure(context) => context
                .theorem_context
                .surface_requirements
                .surfaces(&opposite)
                .cloned()
                .collect::<Vec<_>>(),
            ProofContext::FixedState(context) => context
                .surface_propositions
                .surfaces(&opposite)
                .cloned()
                .collect::<Vec<_>>(),
            ProofContext::Execution(_) => search_input
                .outcome_fixed_state_view()
                .into_iter()
                .flat_map(|view| view.surface_propositions.surfaces(&opposite))
                .cloned()
                .collect::<Vec<_>>(),
        };
        for surface in surfaces {
            if let Some(closed) =
                attempt::candidate_outcome(Self::close_refuted_fact(search_input, &surface))?
            {
                return Ok(Some(closed));
            }
        }
        Ok(None)
    }

    /// Retains the kernel decision and every exact checkable surface form
    /// among its context premises. A typed evidence translator selects and
    /// requires its own exact premises from this subset; unrelated transitive
    /// search context need not be Surface-synthesizable. This is a read-only smart
    /// query: only the later `apply_step` calls may advance the proof.
    pub(in crate::surface::proof) fn selected_solve_derivation(
        search_input: &Proof<'a>,
        exclude_exact_goal: bool,
    ) -> Option<(
        Proposition,
        PropositionDerivation,
        Vec<(Proposition, SyntaxProposition)>,
    )> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("selected_solve_derivation");
        crate::kernel::search::ProofSearch::selected_solve_derivation_with_surfaces(
            search_input,
            exclude_exact_goal,
            &[],
        )
    }

    pub(in crate::surface::proof) fn selected_solve_derivation_with_surfaces(
        search_input: &Proof<'a>,
        exclude_exact_goal: bool,
        introduced_surfaces: &[SyntaxProposition],
    ) -> Option<(
        Proposition,
        PropositionDerivation,
        Vec<(Proposition, SyntaxProposition)>,
    )> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("selected_solve_derivation_with_surfaces");
        let (goal, derivation) =
            crate::kernel::search::ProofSearch::selected_solve_derivation_plan(
                search_input,
                exclude_exact_goal,
            )?;
        let premise_pairs = crate::kernel::search::ProofSearch::resolve_solve_premises(
            search_input,
            &derivation.context_premises(),
            introduced_surfaces,
        )?;
        Some((goal, derivation, premise_pairs))
    }

    /// The derivation solve selected for the focused goal, before any of its
    /// premises is spelled.
    pub(in crate::surface::proof) fn selected_solve_derivation_plan(
        search_input: &Proof<'a>,
        exclude_exact_goal: bool,
    ) -> Option<(Proposition, PropositionDerivation)> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("selected_solve_derivation_plan");
        // An execution goal is either a focused outcome or a frontier one.
        if matches!(search_input.context.as_ref(), ProofContext::Execution(_))
            && search_input.focused_outcome_data().is_none()
        {
            search_input.execution()?;
        }
        let goal = search_input.goal()?.clone();
        let derivation = if exclude_exact_goal {
            crate::kernel::search::ProofSearch::derive_solve_proposition_without_exact_goal(
                search_input.facts().assumptions(),
                &goal,
            )
        } else {
            match plan_solve_certificate(&goal, search_input.facts().assumptions()) {
                Some(SolveEvidence::Derivation(derivation)) => Some(derivation),
                _ => crate::kernel::search::ProofSearch::derive_atomic_proposition(
                    search_input.facts().assumptions(),
                    &goal,
                ),
            }
        };
        let Some(derivation) = derivation else {
            if matches!(goal, Proposition::MemoryLoadable { .. }) {
                attempt::record_search_note(
                    "solve view derivation selection",
                    "no retained-premise derivation was produced for the requested view",
                );
            }
            return None;
        };
        Some((goal, derivation))
    }

    /// Spells each of `premises` in this context's recorded source forms,
    /// leaving out one that has none.
    pub(in crate::surface::proof) fn resolve_solve_premises(
        search_input: &Proof<'a>,
        premises: &[Proposition],
        introduced_surfaces: &[SyntaxProposition],
    ) -> Option<Vec<(Proposition, SyntaxProposition)>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("resolve_solve_premises");
        // Broad atomic derivations may retain a whole connected fact
        // component even when no checkable source spelling exists. Do not
        // render an unbounded component speculatively. The recorded-path
        // candidate is tried first, and explicit `using` lists have their
        // own presentation/checking path.
        if premises.len() > MAX_SOLVE_SOURCE_PREMISES {
            if matches!(
                search_input.goal(),
                Some(Proposition::MemoryLoadable { .. })
            ) {
                attempt::record_search_note(
                    "solve view premise raising",
                    format!(
                        "budget exhausted: the selected view derivation contains {} premises; source spelling permits at most {MAX_SOLVE_SOURCE_PREMISES}",
                        premises.len()
                    ),
                );
            }
            return None;
        }
        crate::instrumentation::measure_operation(
            "surface",
            "solve closure",
            "solve closure: premise raising",
            || {
                crate::kernel::search::ProofSearch::resolve_solve_premises_unmeasured(
                    search_input,
                    premises,
                    introduced_surfaces,
                )
            },
        )
    }

    pub(in crate::surface::proof) fn resolve_solve_premises_unmeasured(
        search_input: &Proof<'a>,
        premises: &[Proposition],
        introduced_surfaces: &[SyntaxProposition],
    ) -> Option<Vec<(Proposition, SyntaxProposition)>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("resolve_solve_premises_unmeasured");
        let frontier_anchor: Option<ProgramPointRef>;
        let (surface_facts, _, premise_anchor) = match search_input.context.as_ref() {
            ProofContext::Pure(context) => {
                (&context.theorem_context.surface_requirements, true, None)
            }
            ProofContext::FixedState(context) => (
                context.surface_propositions,
                true,
                context.premise_anchor.as_ref(),
            ),
            // A judgment stated at a function outcome supplies the
            // outcome's recorded lowerings and statement-entry anchor.
            ProofContext::Execution(_) => {
                if let Some(data) = search_input.focused_outcome_data() {
                    (
                        &data.surface_propositions,
                        // Entry-anchored premises can add a check-equivalent
                        // outcome fact without discharging the exact goal
                        // form. Keep the ordinary trailing `known` so
                        // the checked successor decides whether it is needed.
                        false,
                        data.premise_anchor.as_ref(),
                    )
                } else {
                    // A judgment stated mid-execution (a `have` before
                    // function exit) supplies the frontier's recorded
                    // lowerings and the entry of the last executed
                    // statement, exactly as an outcome data does.
                    let execution = search_input.execution()?;
                    frontier_anchor = frontier_premise_anchor(execution);
                    (
                        &execution.presentation.surface_propositions,
                        false,
                        frontier_anchor.as_ref(),
                    )
                }
            }
        };
        let resolve_premise = |premise: &Proposition, anchor: Option<&ProgramPointRef>| {
            if crate::instrumentation::deadline_exceeded() {
                return None;
            }
            if let Some(surface) = crate::kernel::search::ProofSearch::available_surface_fact(
                search_input,
                surface_facts,
                anchor,
                premise,
            ) {
                return Some((premise.clone(), surface));
            }
            if let Some(surface) = crate::kernel::search::ProofSearch::available_surface_fact(
                search_input,
                search_input.local_surface_facts(),
                anchor,
                premise,
            ) {
                return Some((premise.clone(), surface));
            }
            if crate::instrumentation::deadline_exceeded() {
                return None;
            }
            if let Some(surface) = introduced_surfaces.iter().find(|surface| {
                search_input
                    .lower_surface_proposition(surface, "introduced solve premise")
                    .is_ok_and(|lowered| {
                        lowered == *premise || condition_polarity_equivalent(&lowered, premise)
                    })
            }) {
                return Some((premise.clone(), surface.clone()));
            }
            condition_polarity_forms(premise)
                .into_iter()
                .find_map(|form| {
                    let surface = crate::kernel::search::ProofSearch::available_surface_fact(
                        search_input,
                        surface_facts,
                        anchor,
                        &form,
                    );
                    surface.map(|surface| (form, surface))
                })
                .or_else(|| {
                    // A conjunct of one source fact's lowering — a contract
                    // clause beside its well-formedness conditions, a
                    // comparison beside the range facts its conversion
                    // adds — is spelled by that whole source fact. The
                    // containing kernel is spelled and re-lowered exactly as
                    // any premise is; citing it supplies this conjunct.
                    surface_facts
                        .kernels_containing_conjunct(premise)
                        .chain(
                            search_input
                                .local_surface_facts()
                                .kernels_containing_conjunct(premise),
                        )
                        .find_map(|whole| {
                            if crate::instrumentation::deadline_exceeded() {
                                return None;
                            }
                            crate::kernel::search::ProofSearch::available_surface_fact(
                                search_input,
                                surface_facts,
                                anchor,
                                whole,
                            )
                            .or_else(|| {
                                crate::kernel::search::ProofSearch::available_surface_fact(
                                    search_input,
                                    search_input.local_surface_facts(),
                                    anchor,
                                    whole,
                                )
                            })
                            .map(|surface| (premise.clone(), surface))
                        })
                })
        };
        let mut premise_pairs = premises
            .iter()
            .filter_map(|premise| resolve_premise(premise, premise_anchor))
            .collect::<Vec<_>>();
        // A structured branch continuation can clear `last_step_entry`, or a
        // later common statement can move it past the point where the
        // selected premises were established. If the initially resolved
        // subset already carries one common explicit `at(...)` form,
        // retry this same finite premise list at that successor. No ambient fact
        // or program-point scan participates.
        let anchors = premise_pairs
            .iter()
            .filter_map(
                |(_, surface)| match surface_program_point_selector(surface) {
                    Some(ProgramPointSelector::ProgramPoint(point)) => Some(point),
                    Some(ProgramPointSelector::Mark(_)) | None => None,
                },
            )
            .collect::<BTreeSet<_>>();
        if anchors.len() == 1 {
            let inferred = anchors.first().expect("one inferred anchor");
            let anchored_pairs = premises
                .iter()
                .filter_map(|premise| resolve_premise(premise, Some(inferred)))
                .collect::<Vec<_>>();
            if anchored_pairs.len() >= premise_pairs.len() {
                premise_pairs = anchored_pairs;
            }
        }
        // Name what has no spelling: a derivation found but not written
        // back is refused for that reason, not for the memory history a
        // supplemental explanation may show. Kernel authority is checked
        // context, never a citable premise, so it owes no spelling.
        let spelled = premise_pairs
            .iter()
            .map(|(premise, _)| premise)
            .collect::<BTreeSet<_>>();
        let unspelled = premises
            .iter()
            .filter(|premise| !premise.is_kernel_authority() && !spelled.contains(premise))
            .collect::<Vec<_>>();
        if !crate::instrumentation::deadline_exceeded() && !unspelled.is_empty() {
            let strategy = if matches!(
                search_input.goal(),
                Some(Proposition::MemoryLoadable { .. })
            ) {
                "solve view premise raising"
            } else {
                "solve premise raising"
            };
            attempt::record_search_premise_note(
                strategy,
                format!(
                    "{} of {} selected derivation premises have checked source spellings; {} were omitted: ",
                    premise_pairs.len(),
                    premise_pairs.len() + unspelled.len(),
                    unspelled.len(),
                ),
                &unspelled,
            );
        }
        (!crate::instrumentation::deadline_exceeded()).then_some(premise_pairs)
    }

    /// Available source facts that keep `pivot + 1` from wrapping: a strict
    /// upper bound on `pivot`, or a nonstrict one by a constant below the
    /// `int32` maximum. Read from `pivot`'s indexed order bounds, at most
    /// [`MAX_INCREMENT_HEADROOM_PREMISES`] of them.
    pub(in crate::surface::proof) fn increment_headroom_premises(
        search_input: &Proof<'a>,
        pivot: &OldMachineTerm,
        surface_facts: &SurfacePropositionMap,
        premise_anchor: Option<&ProgramPointRef>,
    ) -> Vec<SyntaxProposition> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("increment_headroom_premises");
        let mut premises = Vec::new();
        for (endpoint, other, strict, forward) in search_input
            .facts()
            .assumptions()
            .signed_order_bound_entries(pivot)
        {
            if premises.len() == MAX_INCREMENT_HEADROOM_PREMISES {
                break;
            }
            // Only `pivot < other` or `pivot <= other` bounds `pivot` above.
            if !forward {
                continue;
            }
            if !strict
                && !matches!(other, bits32_constant!(constant)
                    if (constant_u32(constant) as i32) < i32::MAX)
            {
                continue;
            }
            let (left, right) = (Box::new(endpoint), Box::new(other));
            let fact = Proposition::condition_is(
                if strict {
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessThan,
                        left,
                        right,
                    }
                } else {
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessEqual,
                        left,
                        right,
                    }
                },
                true,
            );
            if !search_input.facts().contains(&fact) {
                continue;
            }
            if let Some(surface) = crate::kernel::search::ProofSearch::available_surface_fact(
                search_input,
                surface_facts,
                premise_anchor,
                &fact,
            ) {
                premises.push(surface);
            }
        }
        premises
    }

    pub(in crate::surface::proof) fn available_surface_fact(
        search_input: &Proof<'a>,
        surface_facts: &SurfacePropositionMap,
        premise_anchor: Option<&ProgramPointRef>,
        kernel: &Proposition,
    ) -> Option<SyntaxProposition> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("available_surface_fact");
        let surface = crate::kernel::search::ProofSearch::available_surface_fact_raw(
            search_input,
            surface_facts,
            premise_anchor,
            kernel,
        )?;
        crate::kernel::search::ProofSearch::named_returned_pointer_surface_fact(
            search_input,
            &surface,
            kernel,
        )
        .or(Some(surface))
    }

    pub(in crate::surface::proof) fn named_returned_pointer_surface_fact(
        search_input: &Proof<'a>,
        surface: &SyntaxProposition,
        kernel: &Proposition,
    ) -> Option<SyntaxProposition> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("named_returned_pointer_surface_fact");
        let view = search_input.premise_fixed_state_view()?;
        let native_result = view.fixed_state.native_result();
        let Some(result @ ProgramValue::Pointer(_)) = native_result.as_deref() else {
            return None;
        };
        // Resource witnesses may have no written name but coincide with the
        // checked return value. Name that exact value, then re-lower the
        // candidate so presentation cannot change the cited premise.
        let equality = SyntaxProposition::Comparison {
            left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(result.clone())),
            operator: ComparisonOperator::Equal,
            right: SyntaxTerm::Binding("result".to_string()),
        };
        let named =
            crate::surface::rewrite_click_proposition_by_surface_equality(surface, &equality)?;
        search_input
            .lower_surface_proposition_direct(&named, "returned pointer premise form")
            .is_ok_and(|lowered| {
                lowered == *kernel || condition_polarity_equivalent(&lowered, kernel)
            })
            .then_some(named)
    }

    pub(in crate::surface::proof) fn available_surface_fact_raw(
        search_input: &Proof<'a>,
        surface_facts: &SurfacePropositionMap,
        premise_anchor: Option<&ProgramPointRef>,
        kernel: &Proposition,
    ) -> Option<SyntaxProposition> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("available_surface_fact_raw");
        Self::surface_fact_raw_for_purpose(
            search_input,
            surface_facts,
            premise_anchor,
            kernel,
            SurfaceRaisingPurpose::AvailablePremise,
        )
    }

    pub(in crate::surface::proof) fn proposed_surface_goal(
        search_input: &Proof<'a>,
        surface_facts: &SurfacePropositionMap,
        kernel: &Proposition,
    ) -> Option<SyntaxProposition> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("proposed_surface_goal");
        Self::surface_fact_raw_for_purpose(
            search_input,
            surface_facts,
            None,
            kernel,
            SurfaceRaisingPurpose::ProposedGoal,
        )
    }

    fn surface_fact_raw_for_purpose(
        search_input: &Proof<'a>,
        surface_facts: &SurfacePropositionMap,
        premise_anchor: Option<&ProgramPointRef>,
        kernel: &Proposition,
        purpose: SurfaceRaisingPurpose,
    ) -> Option<SyntaxProposition> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("surface_fact_raw_for_purpose");
        let _binder_names = search_input.induction_binder_name_scope();
        // Option-based presentation misses must not restart work after a
        // candidate exhausted the verifier's sticky budget/deadline.
        if crate::instrumentation::deadline_exceeded() {
            return None;
        }
        // Store records and reflexive pointer equalities are internal
        // metadata, with no useful source rewrite. Keep their retained source
        // forms when present; do not invent spellings by searching history.
        if (is_reflexive_pointer_equality(kernel)
            || matches!(kernel, Proposition::ConditionIs(condition, value)
                if crate::kernel::is_store_fact(condition.old_form(), *value)))
            && surface_facts.surfaces(kernel).next().is_none()
            && search_input
                .local_surface_facts()
                .surfaces(kernel)
                .next()
                .is_none()
            && surface_facts
                .kernels_containing_conjunct(kernel)
                .next()
                .is_none()
            && search_input
                .local_surface_facts()
                .kernels_containing_conjunct(kernel)
                .next()
                .is_none()
        {
            return None;
        }
        let _qualified_sources =
            super::surface_synthesis::QualifiedSynthesisScope::enter(surface_facts);
        // A refold moves a constructor equation: a proof `match` arm's case
        // fact states the scrutinee's constructor at unchanged function entry,
        // and once the arm has refolded its instance, `c.model == C(..)` reads
        // the refolded field. Like a program point selector recorded again in a
        // loop, that spelling may stop denoting its old checked fact.
        // Re-lower those movable forms below; other live recorded pairs keep
        // their indexed lookup without repeating proposition lowering.
        let constructor_equation = matches!(&(
            kernel), Proposition::Equal(
                Term::Algebraic(_),
                term_source_0 @ Term::Algebraic(_)
            ) if matches!((term_source_0.algebraic_native(),), (Some(crate::kernel::AlgebraicTerm {
                    node: crate::kernel::AlgebraicTermNode::Constructor { .. },
                    ..
                }),)));
        let retained_branch_equality = match kernel {
            condition_source_0 @ Proposition::ConditionIs(_, _)
                if let Some((
                    OldConditionTerm::IntegerEqual(left, right)
                    | OldConditionTerm::IntegerNotEqual(left, right),
                    _,
                )) = condition_source_0.old_condition() =>
            {
                [left, right].iter().any(|term| match term.as_ref() {
                    crate::kernel::IntegerTerm::Machine(value) => {
                        value.shared_operand().is_some_and(|term| {
                            term.has_machine_conditionals() || term.has_machine_matches()
                        })
                    }
                    _ => false,
                })
            }
            _ => false,
        };
        let pointer_addresses = match kernel.old_condition() {
            Some((OldConditionTerm::AddressEqual(left, right), _)) => {
                Some([left.as_ref(), right.as_ref()])
            }
            Some((OldConditionTerm::PointerEqual(left, right), _)) => {
                Some([left.address(), right.address()])
            }
            _ => None,
        };
        let pointer_read_equality = pointer_addresses.is_some_and(|addresses| {
            addresses
                .iter()
                .any(|address| address.as_loaded_value().is_some())
        });
        let matches_kernel = |candidate: &SyntaxProposition, allow_recorded_pair: bool| {
            if crate::instrumentation::deadline_exceeded() {
                return None;
            }
            // `result` exists only once the function returns: a state
            // before the return that reads it lowers, but does not parse.
            if reads_result_before_return(candidate) {
                return None;
            }
            // Synthesized kernel literals can lower back to this fact yet
            // print as diagnostic-only pointer placeholders. Such a form
            // cannot be cited in an expandable proof; try another spelling.
            let named = crate::kernel::search::ProofSearch::named_returned_pointer_surface_fact(
                search_input,
                candidate,
                kernel,
            );
            if !crate::surface::parser::has_valid_source_tokens(
                &crate::surface::printing::source_click_proposition(
                    named.as_ref().unwrap_or(candidate),
                ),
            ) {
                return None;
            }
            let lower = |candidate: &SyntaxProposition| {
                let operation = || {
                    search_input
                        .lower_surface_proposition_direct(candidate, "typed solve premise form")
                };
                match purpose {
                    SurfaceRaisingPurpose::AvailablePremise => {
                        search_input.lower_proposition_spelling(candidate).ok()
                    }
                    SurfaceRaisingPurpose::ProposedGoal => {
                        // This private probe checks only the candidate's term identity.
                        // It publishes no proof/facts and cannot add debts to an outer
                        // operation. The selected Surface form must be lowered again by
                        // open_have, which proves and retains all its prerequisites.
                        let (lowered, _requirements) =
                            super::super::execution_planning::probe_open_obligations(operation);
                        lowered.ok()
                    }
                }
            };
            if matches!(purpose, SurfaceRaisingPurpose::AvailablePremise)
                && allow_recorded_pair
                && search_input.focused_outcome_data().is_some()
                && surface_facts
                    .available_kernel_matching(candidate, |fact| {
                        search_input.facts().contains(fact)
                    })
                    .is_some_and(|lowered| {
                        lowered == kernel || condition_polarity_equivalent(lowered, kernel)
                    })
            {
                // A terminal path can retain a fact spelled through an
                // automatic local that has since left scope. Its recorded
                // pair remains a valid kernel fact, but the unanchored
                // spelling cannot be used as a source `rewrite`.
                // Only names in this candidate are queried. An outcome's
                // recorded pair cannot make an out-of-scope temporary legal
                // source, even when no call-outcome route was selected.
                let names_a_dead_local =
                    search_input.premise_fixed_state_view().is_some_and(|view| {
                        let mut current_names = BTreeSet::new();
                        crate::surface::collect_current_proposition_variables(
                            candidate,
                            &mut current_names,
                        );
                        current_names.iter().any(|name| {
                            !(name == "result" && view.fixed_state.result.is_some())
                                && !view.fixed_state.state.locals().contains_name(name)
                                && !view.fixed_state.pre_state.locals().contains_name(name)
                                && !premise_anchor
                                    .and_then(|anchor| view.fixed_state.recorded_states.get(anchor))
                                    .is_some_and(|retained_state| {
                                        retained_state.locals().contains_name(name)
                                    })
                                && search_input.local_binding(name).is_none()
                                && search_input.local_integer_values().get(name).is_none()
                                && search_input.known_algebraic_value(name).is_none()
                        })
                    });
                // A statement selector can be recorded again on a later
                // iteration, and a store can change the value an unanchored
                // pointer read names. Check that those spellings still name
                // the fact here.
                let state_spelling = proposition_contains_at_expression(candidate);
                if !constructor_equation
                    && !names_a_dead_local
                    && !state_spelling
                    && !pointer_read_equality
                {
                    // The recorded pair is authoritative for this shape.
                    return Some(());
                }
                // A constructor equation's written spelling can have stopped
                // lowering at all: the arm's instance was consumed and
                // unfolded and never refolded under its name, so `t.model`
                // names nothing here and the rechecked certificate would
                // fail on it. Only the entry-anchored form below still
                // denotes the fact.
                let lowered = lower(candidate)?;
                // The spelling lowers to some other fact, so it has stopped
                // denoting this one: citing it would hand the rechecked proof
                // the fact it now names instead.
                return (lowered == *kernel || condition_polarity_equivalent(&lowered, kernel))
                    .then_some(());
            }
            let lowered = lower(candidate)?;
            (lowered == *kernel
                || condition_polarity_equivalent(&lowered, kernel)
                // A compound fact can quote cached cell values through their
                // explicit state reads. Match at the same read-over-write
                // boundary the exact fact index already checks. Atomic source
                // selection keeps its existing arithmetic spelling policy.
                || (matches!(kernel,
                    Proposition::And(..) | Proposition::Or(..) | Proposition::Implies(..)
                ) && {
                    let lowered_reading = crate::kernel::comparison_form(&lowered);
                    let selected_reading = crate::kernel::comparison_form(kernel);
                    crate::kernel::proof::propositions_are_alpha_equal(
                        lowered_reading.as_ref().unwrap_or(&lowered),
                        selected_reading.as_ref().unwrap_or(kernel),
                    )
                })
                // This candidate spells one already-selected premise. Admit
                // its native/shared equality reading at the same explicit
                // boundary used when the generated certificate cites it.
                || (retained_branch_equality
                    && crate::kernel::proof::fact_reasoning::listed_equality_fact_is_available(
                        kernel, std::slice::from_ref(&lowered),
                    ))
                || quantified_equivalent_available_fact(kernel, std::slice::from_ref(&lowered))
                    .is_some())
            .then_some(())
        };
        // A store of an allocation result can retain the assignment's hidden
        // temporary. The allocation's address has a source name at the
        // producing region, which survives the temporary's scope.
        let view = search_input.premise_fixed_state_view();
        if let (Some(addresses), Some(view)) = (pointer_addresses, view)
            && addresses.into_iter().any(|address| {
                view.fixed_state
                    .recorded_states
                    .allocation_result(address)
                    .is_some()
            })
            && let Some(surface) = search_input.structural_proposition_candidate(kernel)
            && matches_kernel(&surface, false).is_some()
        {
            return Some(surface);
        }
        if let Some(surface) = surface_facts.surfaces(kernel).find(|surface| {
            (proposition_contains_at_expression(surface)
                || proposition_contains_old_expression(surface))
                && matches_kernel(surface, true).is_some()
        }) {
            return Some(surface.clone());
        }
        // A selected fact can instead name a fresh loop-head value in the
        // current state. Recover it there before searching older states
        // which cannot name that value at all.
        let pointer_goal = matches!(&search_input.goal(), Some(condition_source_0 @ Proposition::ConditionIs(_, _)) if matches!(condition_source_0.old_condition(), Some((OldConditionTerm::AddressEqual(..), _))));
        if pointer_goal
            && let Some(surface) = surface_facts
                .surfaces(kernel)
                .find(|surface| matches_kernel(surface, true).is_some())
        {
            return Some(surface.clone());
        }
        if pointer_goal
            && let Some(view) = view
            && let Some(surface) = synthesize_surface_proposition(
                kernel,
                view.parameter_binding,
                view.fixed_state.state,
            )
            && matches_kernel(&surface, true).is_some()
        {
            return Some(surface);
        }
        // Function requirements retain their original unanchored Surface
        // form while their kernel fact is entry-relative. Probe that one
        // canonical source form before the moving statement-entry anchor;
        // the direct lowering check below rejects non-entry facts, and the
        // lookup visits only forms indexed under this selected premise.
        let function_entry = ProgramPointRef {
            region: CodeRegionRef::Function,
            kind: ProgramPointKind::Entry,
        };
        let requirement_surface = if let Some(data) = search_input.focused_outcome_data() {
            data.requirement_surfaces.get(kernel).cloned()
        } else {
            // A judgment stated mid-execution selects its requirement
            // spellings from the frontier's own contract, as an outcome
            // outcome does from its recorded ones.
            search_input
                .execution_proposition_fixed_state_view()
                .and_then(|view| {
                    view.requirement_facts
                        .propositions()
                        .zip(view.original_requirements)
                        .find(|(fact, _)| *fact == kernel)
                        .and_then(|(_, requirement)| requirement.proposition().cloned())
                })
        };
        if let Some(surface) = requirement_surface {
            let anchored = SyntaxProposition::At {
                selector: ProgramPointSelector::ProgramPoint(function_entry.clone()),
                proposition: Box::new(surface.clone()),
            };
            if matches_kernel(&anchored, true).is_some() {
                return Some(anchored);
            }
        }
        if search_input.premise_fixed_state_view().is_some() {
            if let Some(anchored) = surface_facts.surfaces(kernel).find_map(|surface| {
                let anchored = surface_at_program_point(surface, &function_entry).ok()?;
                matches_kernel(&anchored, true).map(|()| anchored)
            }) {
                return Some(anchored);
            }
            if let Some(view) = search_input.premise_fixed_state_view()
                && let Some(surface) = synthesize_surface_proposition(
                    kernel,
                    view.parameter_binding,
                    view.fixed_state.pre_state,
                )
                && let Ok(anchored) = surface_at_program_point(&surface, &function_entry)
                && matches_kernel(&anchored, true).is_some()
            {
                return Some(anchored);
            }
        }
        if let Some(anchor) = premise_anchor
            && let Some(anchored) = surface_facts.surfaces(kernel).find_map(|surface| {
                let anchored = surface_at_program_point(surface, anchor).ok()?;
                matches_kernel(&anchored, true).map(|()| anchored)
            })
        {
            return Some(anchored);
        }
        // A selected scalar fact may combine a current value with an entry
        // read, which no single earlier state can spell. Try these named
        // states before walking history. New scalar candidates lower directly: a
        // recorded unanchored form may name an earlier value of the same local.
        // The structural raiser: values the current state and the proof's
        // binders name, entry reads as `old(..)`, and a read of any other
        // recorded memory at the point that recorded it, found by its memory
        // in one lookup.
        let _recorded_points = view.map(|view| {
            super::surface_synthesis::SynthesisRecordedPointsScope::enter(
                view.fixed_state.recorded_states,
            )
        });
        if let Some(view) = view {
            let (bound_variable_names, binder_names) = search_input.binder_variable_names();
            let surface = super::surface_synthesis::with_proof_binder_names(
                std::sync::Arc::new(binder_names),
                || {
                    super::surface_synthesis::synthesize_surface_proposition_at_entry_post_with_bound_variable_names(
                        kernel,
                        view.parameter_binding,
                        view.fixed_state.pre_state,
                        view.fixed_state.state,
                        &bound_variable_names,
                    )
                },
            );
            let matched = surface
                .as_ref()
                .is_some_and(|surface| matches_kernel(surface, false).is_some());
            if matched {
                return surface;
            }
        }
        if crate::instrumentation::deadline_exceeded() {
            return None;
        }
        if let Some(surface) = surface_facts
            .surfaces(kernel)
            .find(|surface| matches_kernel(surface, true).is_some())
            .cloned()
        {
            return Some(surface);
        }
        // A proof `match` arm's case fact states the scrutinee's constructor at
        // unchanged function entry, and the spelling recorded for it is the
        // written, unanchored `c.model == C(..)`. Once the arm refolds its
        // instance, that spelling denotes the fold's own equation, so the
        // direct check above rejects it. The entry-anchored
        // `old(c.model) == C(..)` still lowers to this exact fact. Offer it
        // exactly where the recorded pair alone used to be taken as proof that
        // the written form named this premise -- that acceptance is what let a
        // certificate cite a spelling that is rechecked as a different fact --
        // and nowhere else, so a lookup that found no spelling at all still
        // finds none.
        if constructor_equation
            && search_input.focused_outcome_data().is_some()
            && let Some(anchored) = surface_facts.surfaces(kernel).find_map(|surface| {
                surface_facts
                    .available_kernel_matching(surface, |fact| search_input.facts().contains(fact))
                    .is_some_and(|recorded| {
                        recorded == kernel || condition_polarity_equivalent(recorded, kernel)
                    })
                    .then(|| entry_anchored_constructor_equality(search_input, surface, kernel))
                    .flatten()
            })
        {
            return Some(anchored);
        }
        // Quantified execution facts may be retained in the canonical memory
        // form used by the kernel while their recorded Surface form lowers to
        // a term carrying a check-equivalent memory state. Probe only the
        // persistent alpha/canonical-form bucket for this selected premise;
        // `Instantiate` validates the same equivalence on check.
        if matches!(kernel, Proposition::ForAll { .. }) {
            for candidate in search_input.facts().matching_quantified_facts(kernel) {
                for surface in surface_facts.surfaces(&candidate) {
                    let lowered = search_input
                        .lower_surface_proposition_direct(
                            surface,
                            "typed quantified solve premise form",
                        )
                        .ok()?;
                    if quantified_equivalent_available_fact(kernel, std::slice::from_ref(&lowered))
                        .is_some()
                    {
                        return Some(surface.clone());
                    }
                }
            }
        }
        // Pure unfolding and induction can add a selected fact without a
        // written requirement entry. Synthesize its presentation from retained
        // binder names, then independently lower it back to this exact fact.
        // This is candidate presentation only; it neither adds facts nor
        // reconstructs a proof context.
        if let ProofContext::Pure(context) = search_input.context.as_ref() {
            // Include arguments of opaque applications: their variables still
            // need names even though the bitvector collector treats the call
            // as an atom.
            let mut selected = BTreeSet::new();
            crate::kernel::planning_api::collect_proposition_connection_variables(
                kernel,
                &mut selected,
            );
            let mut bindings = selected
                .iter()
                .filter_map(|variable| {
                    context
                        .source_names
                        .get(variable)
                        .map(|name| (*variable, name.clone()))
                })
                .collect::<BTreeMap<_, _>>();
            let (intro_names, local_names) = search_input.binder_variable_names();
            for (variable, name) in local_names.into_iter().chain(intro_names) {
                if selected.contains(&variable) {
                    bindings.insert(variable, name);
                }
            }
            let synthesized = synthesize_surface_proposition_with_bound_variable_names(
                kernel,
                ParameterBinding::default(),
                &context.source_state,
                &bindings,
            );
            if let Some(surface) = synthesized
                && matches_kernel(&surface, true).is_some()
            {
                return Some(surface);
            }
        }
        // Branch-condition facts are checked execution outputs, but their
        // arm-local Surface map entry need not survive at the shared outcome.
        // Reconstruct only this derivation-selected premise at the current
        // symbolic state and accept it only when ordinary lowering recovers
        // the exact kernel fact. This is constant work per typed proof edge,
        // not an ambient form search.
        let synthesis_context = match search_input.context.as_ref() {
            ProofContext::Pure(_) => None,
            ProofContext::FixedState(context) => Some((
                context.parameter_binding.parameters,
                context.parameter_binding.arguments,
                context.fixed_state.state,
            )),
            ProofContext::Execution(_) => search_input.premise_fixed_state_view().map(|view| {
                (
                    view.parameter_binding.parameters,
                    view.parameter_binding.arguments,
                    view.fixed_state.state,
                )
            }),
        };
        let (parameters, arguments, state) = synthesis_context?;
        let (bound_variable_names, binder_names) = search_input.binder_variable_names();
        if let Some(surface) = super::surface_synthesis::with_proof_binder_names(
            std::sync::Arc::new(binder_names),
            || {
                synthesize_surface_proposition_with_bound_variable_names(
                    kernel,
                    ParameterBinding::new(parameters, arguments),
                    state,
                    &bound_variable_names,
                )
            },
        ) && matches_kernel(&surface, true).is_some()
        {
            return Some(surface);
        }
        // The same recorded states and matcher already completed their
        // search above. The intervening presentation candidates do not change
        // this proof's state, so repeating that miss cannot find a new source.
        None
    }

    /// A cheap indexed rewrite can close a goal without exploring its
    /// connected component. Every longer chain uses the shared search,
    /// also when this entry point is reached after a split or an unfold.
    #[cfg(test)]
    pub(in crate::surface::proof) fn try_goal_equality_rewrite_closure(
        search_input: &Proof<'a>,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_goal_equality_rewrite_closure");
        crate::kernel::search::ProofSearch::try_goal_equality_rewrite_closure_excluding(
            search_input,
            false,
            true,
        )
        .ok()
        .flatten()
    }

    #[cfg(test)]
    pub(in crate::surface::proof) fn try_goal_equality_rewrite_closure_excluding(
        search_input: &Proof<'a>,
        exclude_goal_fact: bool,
        allow_function_unfold: bool,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_goal_equality_rewrite_closure_excluding");
        match crate::kernel::search::ProofSearch::try_indexed_direct_equality_rewrite(
            search_input,
            exclude_goal_fact,
        ) {
            std::ops::ControlFlow::Break(closed) => Ok(closed),
            std::ops::ControlFlow::Continue(()) => {
                let Some(_scope) = SolveFallbackScope::enter(SolveFallback::ConnectedFacts) else {
                    return Ok(None);
                };
                crate::kernel::search::ProofSearch::try_connected_equality_chain_closure(
                    search_input,
                    RewriteClosers::GoalLocal {
                        allow_function_unfold,
                    },
                )
            }
        }
    }

    /// The chain half of [`Self::try_goal_equality_rewrite_closure_excluding`]:
    /// the search over rewrites by the equalities connected to the goal.
    pub(in crate::surface::proof) fn try_connected_goal_equality_chain_closure(
        search_input: &Proof<'a>,
        allow_function_unfold: bool,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_connected_goal_equality_chain_closure");
        let Some(_scope) = SolveFallbackScope::enter(SolveFallback::ConnectedFacts) else {
            return Ok(None);
        };
        crate::kernel::search::ProofSearch::try_connected_equality_chain_closure(
            search_input,
            RewriteClosers::GoalLocal {
                allow_function_unfold,
            },
        )
    }

    /// One indexed rewrite followed by direct closure of an algebraic
    /// comparison, without general solve or connected-premise discovery.
    pub(in crate::surface::proof) fn try_direct_model_equality_rewrite_closure(
        search_input: &Proof<'a>,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_direct_model_equality_rewrite_closure");
        let goal = match search_input.goal()? {
            Proposition::Not(body) => body.as_ref(),
            goal => goal,
        };
        if !matches!(
            goal,
            Proposition::Equal(Term::Algebraic(_), Term::Algebraic(_))
        ) {
            return None;
        }
        crate::kernel::search::ProofSearch::try_indexed_direct_equality_rewrite(search_input, false)
            .break_value()
            .flatten()
    }

    /// Spell a rewrite at the execution frontier that owns its goal. The
    /// last executed statement can name a different loop iteration state;
    /// rewriting must retain the recorded entry name of the selected fact.
    pub(in crate::surface::proof) fn available_rewrite_equality(
        search_input: &Proof<'a>,
        equality: &Proposition,
    ) -> Option<SyntaxProposition> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("available_rewrite_equality");
        let frontier_anchor;
        let anchor = match search_input.context.as_ref() {
            ProofContext::Pure(_) => None,
            ProofContext::FixedState(context) => context.premise_anchor.as_ref(),
            ProofContext::Execution(_) => match search_input.focused_outcome_data() {
                Some(data) => data.premise_anchor.as_ref(),
                None => {
                    frontier_anchor = ProgramPointRef {
                        region: CodeRegionRef::Region(
                            search_input.execution()?.core.frontier.next_statement_index,
                        ),
                        kind: ProgramPointKind::Entry,
                    };
                    Some(&frontier_anchor)
                }
            },
        };
        crate::kernel::search::ProofSearch::available_surface_fact(
            search_input,
            (search_input).premise_surface_facts()?,
            anchor,
            equality,
        )
        .or_else(|| {
            crate::kernel::search::ProofSearch::available_surface_fact(
                search_input,
                search_input.local_surface_facts(),
                anchor,
                equality,
            )
        })
    }

    /// A derived call equality need not have a recorded source spelling.
    /// Use only an operand already written in this goal, and check the
    /// resulting equality in an ordinary nested proof before citing it.
    pub(in crate::surface::proof) fn try_goal_operand_constant_equality(
        search_input: &Proof<'a>,
        equality: &Proposition,
    ) -> Option<(SyntaxProposition, Proof<'a>)> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_goal_operand_constant_equality");
        let SyntaxProposition::Comparison {
            left: source_left,
            right: source_right,
            ..
        } = search_input.surface_goal()?
        else {
            return None;
        };
        let condition_source = search_input.goal()?;
        let Some((
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left,
                right,
            }
            | OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left,
                right,
            }
            | OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left,
                right,
            }
            | OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left,
                right,
            },
            true,
        )) = condition_source.old_condition()
        else {
            return None;
        };
        let Some((
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left: a,
                right: b,
            },
            true,
        )) = equality.old_condition()
        else {
            return None;
        };
        for (operand, source) in [(left.as_ref(), source_left), (right.as_ref(), source_right)] {
            let literal = if a.as_ref() == operand {
                b.as_ref()
            } else if b.as_ref() == operand {
                a.as_ref()
            } else {
                continue;
            };
            let bits32_constant!(value) = literal else {
                continue;
            };
            if matches!(operand, bits32_constant!(_)) {
                continue;
            }
            let surface = SyntaxProposition::Comparison {
                left: source.clone(),
                operator: ComparisonOperator::Equal,
                right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                    ProgramValue::Int32(OldMachineTerm::constant(constant_u32(*value))),
                )),
            };
            let scope = search_input.driver().open_have(surface.clone()).ok()?;
            let closed = (scope).driver().try_direct_logical_closure().ok()??;
            return Some((surface, closed.join().ok()?));
        }
        None
    }

    /// Try one indexed equality and a direct closer. This shortcut never
    /// refines or branches into its own rewrite chain. `Break(None)` stops
    /// when an equivalent scalar goal is refuted or no source candidate can
    /// start a chain. `Continue` leaves the shared search to try.
    pub(in crate::surface::proof) fn try_indexed_direct_equality_rewrite(
        search_input: &Proof<'a>,
        exclude_goal_fact: bool,
    ) -> std::ops::ControlFlow<Option<Proof<'a>>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_indexed_direct_equality_rewrite");
        use std::ops::ControlFlow::{Break, Continue};
        if matches!(
            search_input.goal(),
            Some(Proposition::Implies(..) | Proposition::ForAll { .. })
        ) {
            return Continue(());
        }
        if crate::kernel::search::ProofSearch::scalar_offset_goal_is_refuted(search_input) {
            return Break(if exclude_goal_fact {
                None
            } else {
                crate::kernel::search::ProofSearch::try_direct_logical_closure(search_input)
                    .ok()
                    .flatten()
            });
        }
        let proof = search_input;
        let (Some(goal), Some(surface_facts)) =
            (proof.goal(), (search_input).premise_surface_facts())
        else {
            return Continue(());
        };
        let goal = goal.clone();
        let attempted_closures = std::cell::RefCell::new(BTreeSet::new());
        // Pointer equalities between scaled offsets are candidates too:
        // `rewrite` carries one through the address of a load, so a
        // goal over `p->q->x` reaches `r->x` under `p->q == r`.
        // Once both pointers have the same base, only their offsets
        // need rewriting. Selecting on the shared base also nominates
        // every historical pointer fact about that object, even when
        // none mentions an offset operand of this comparison.
        let equality_candidates = match &goal {
            condition_source_0 @ Proposition::ConditionIs(_, value)
                if let Some((OldConditionTerm::AddressEqual(left, right), _)) =
                    condition_source_0.old_condition()
                    && (left.base == right.base) =>
            {
                // External arguments share a block and carry the
                // actual base as an offset prefix: `(base + i) == base`
                // needs facts about `i`, not old reads through `base`.
                let zero = crate::kernel::AddressOffset::constant(0);
                let (left, right) = match (left.offset.view(), right.offset.view()) {
                    (OffsetView::Add(base, index), _) if base == &right.offset => (index, &zero),
                    (_, OffsetView::Add(base, index)) if &left.offset == base => (&zero, index),
                    (
                        OffsetView::Add(left_base, left_index),
                        OffsetView::Add(right_base, right_index),
                    ) if left_base == right_base => (left_index, right_index),
                    _ => (&left.offset, &right.offset),
                };
                proof
                    .facts()
                    .load_equalities_mentioning(&Proposition::condition_is(
                        OldConditionTerm::AddressOffsetEqual(
                            Box::new(left.clone()),
                            Box::new(right.clone()),
                        ),
                        *value,
                    ))
            }
            _ => proof.facts().load_equalities_mentioning(&goal),
        };
        let equalities = equality_candidates
            .into_iter()
            .chain(proof.facts().algebraic_equalities_mentioning(&goal));
        let mut has_source_candidate = false;
        for equality in equalities {
            // A reflexive equality cannot change the checked goal.
            // Avoid reconstructing source spellings for these pointer
            // metadata facts before the rewrite.
            if is_reflexive_pointer_equality(&equality) {
                continue;
            }
            // A registered read definition remains available to the
            // kernel, but cannot supply a source rewrite. Do not search
            // recorded states for a spelling of this metadata.
            if crate::kernel::is_verified_load_variable_defining_fact(&equality) {
                continue;
            }
            let equality_has_literal_endpoint = rewrite_equality_sides(&equality)
                .is_some_and(|(left, right)| is_rewrite_literal(left) || is_rewrite_literal(right))
                || matches!(
                    &equality, condition_source_0 @ Proposition::ConditionIs(_, true) if matches!(condition_source_0.old_condition(), Some((OldConditionTerm::IntegerEqual(left, right), _)) if (matches!(&**left, crate::kernel::IntegerTerm::Constant(_))
                            || matches!(&**right, crate::kernel::IntegerTerm::Constant(_)))));
            if exclude_goal_fact
                && (equality == goal
                    || swapped_bitvector_equality(&equality).is_some_and(|swapped| swapped == goal))
            {
                continue;
            }
            let (surface, candidate_proof) =
                match crate::kernel::search::ProofSearch::available_rewrite_equality(
                    proof, &equality,
                ) {
                    Some(surface) => (surface, proof.clone()),
                    None => {
                        match crate::kernel::search::ProofSearch::try_goal_operand_constant_equality(
                            proof, &equality,
                        ) {
                            Some(candidate) => candidate,
                            None => continue,
                        }
                    }
                };
            has_source_candidate = true;
            let proof = &candidate_proof;
            // `available_surface_fact` has already resolved the spelling
            // that still lowers to this fact, anchoring a stale constructor
            // equality at function entry when the written form stopped
            // denoting it, so only the orientation is open here.
            let reverse = reverse_surface_equality(&surface);
            for oriented in std::iter::once(surface).chain(reverse) {
                // Automatic refinement reduces symbolic operands to known
                // literals. Expanding a literal into an alias creates
                // irrelevant branches, especially after a folded cast or
                // unsigned-order bias. An explicit `rewrite` still permits
                // that checked direction.
                if equality_has_literal_endpoint {
                    let literal_endpoint = |kernel: &Proposition, source: bool| {
                        rewrite_equality_sides(kernel).is_some_and(|(left, right)| {
                            is_rewrite_literal(if source { left } else { right })
                        }) || matches!(&kernel, condition_source_0 @ Proposition::ConditionIs(_, true) if matches!(condition_source_0.old_condition(), Some((OldConditionTerm::IntegerEqual(left, right), _)) if (matches!(if source { &**left } else { &**right }, crate::kernel::IntegerTerm::Constant(_)))))
                    };
                    // A retained source spelling may be a proxy for a
                    // symbolic operand. Trust its recorded lowering, not
                    // the spelling's apparent literal syntax.
                    let source_is_literal = surface_facts
                    .available_kernel_matching(&oriented, |fact| proof.facts().contains(fact))
                    .map(|kernel| literal_endpoint(kernel, true))
                    .or_else(|| {
                        let reverse = reverse_surface_equality(&oriented)?;
                        surface_facts.available_kernel_matching(&reverse, |fact| proof.facts().contains(fact))
                            .map(|kernel| literal_endpoint(kernel, false))
                    })
                    .unwrap_or_else(|| matches!(&oriented, SyntaxProposition::Comparison { left, .. } if surface_expression_is_constant(left)));
                    if source_is_literal {
                        continue;
                    }
                }
                // Each candidate is one checked rewrite and a direct closer.
                // Observe the tactic's deadline and work budget between
                // candidates, including when none can close.
                if crate::instrumentation::deadline_exceeded() {
                    return Continue(());
                }
                let rewrite = proof.driver().apply_step(ProofStep::Rewrite(oriented));
                let Ok(rewritten) = rewrite else {
                    continue;
                };
                if rewritten.goal() == proof.goal() {
                    continue;
                }
                // Checked rewrites preserve this obligation. Once one
                // reaches a refuted scalar equality, more equivalent
                // rewrites or function expansions cannot help the search.
                if crate::kernel::search::ProofSearch::scalar_offset_goal_is_refuted(&(rewritten)) {
                    if !exclude_goal_fact
                        && let Some(closed) =
                            crate::kernel::search::ProofSearch::try_direct_logical_closure(
                                &(rewritten),
                            )
                            .ok()
                            .flatten()
                    {
                        return Break(Some(closed));
                    }
                    return Break(None);
                }
                let closure_key = rewritten
                    .goal()
                    .and_then(proposition_identity_key)
                    .map(|goal| {
                        (
                            crate::kernel::assumptions::unsalted_assumptions_memo_id(
                                rewritten.facts().assumptions(),
                            ),
                            goal,
                        )
                    });
                let fresh_closure =
                    closure_key.is_none_or(|key| attempted_closures.borrow_mut().insert(key));
                if fresh_closure
                    && let Some(closed) =
                        crate::kernel::search::ProofSearch::try_direct_logical_closure(&(rewritten))
                            .ok()
                            .flatten()
                {
                    return Break(Some(closed));
                }
            }
        }
        if has_source_candidate {
            Continue(())
        } else {
            // No indexed source equality can start a chain at this goal.
            // In particular, internal store records must not trigger a
            // connected-component walk merely because they mention it.
            Break(None)
        }
    }

    pub(in crate::surface::proof) fn try_typed_atomic_solve_from_selected_premises(
        search_input: &Proof<'a>,
        premise_pairs: &[(Proposition, SyntaxProposition)],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_typed_atomic_solve_from_selected_premises");
        let goal = search_input.goal()?.clone();
        if premise_pairs
            .iter()
            .any(|(kernel, _)| selected_premise_contains_goal(kernel, &goal))
        {
            return search_input
                .driver()
                .apply_step(ProofStep::Known)
                .ok()
                .filter(Proof::is_complete);
        }
        let restricted = premise_pairs
            .iter()
            .map(|(kernel, _)| kernel.clone())
            .collect::<Vec<_>>();
        match plan_solve_certificate(&goal, &assumptions_from_propositions(&restricted))? {
            SolveEvidence::GoalLocal => {
                crate::kernel::search::ProofSearch::try_local_checked_closure(search_input, None)
                    .ok()
                    .flatten()
                    .filter(Proof::is_complete)
            }
            SolveEvidence::Derivation(derivation) => {
                crate::kernel::search::ProofSearch::check_typed_atomic_solve_candidate(
                    search_input,
                    &goal,
                    &derivation,
                    premise_pairs,
                )
            }
        }
    }

    /// Weakens a constant bound. A goal `value >= c` (or `value <= c`)
    /// closes from a stronger context bound `value >= C` with `C >= c`
    /// (`value <= C` with `C <= c`), the shape a loop's negated guard leaves
    /// on its counter. The proof cites only facts it establishes itself, two
    /// nested `have`s closed by the direct logical closer, so the context
    /// bound needs no Surface form; the transitivity theorem then closes
    /// the goal.
    pub(in crate::surface::proof) fn try_selected_constant_bound_weakening(
        search_input: &Proof<'a>,
        goal: &Proposition,
        derivation: &PropositionDerivation,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_selected_constant_bound_weakening");
        let surface_goal = search_input.surface_goal()?.clone();
        let (goal_value, goal_bound, lower_bound) = match goal {
            condition_source_0 @ Proposition::ConditionIs(_, true)
                if let Some((
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterEqual,
                        left: value,
                        right: bound,
                    },
                    _,
                )) = condition_source_0.old_condition() =>
            {
                (value, bound, true)
            }
            condition_source_0 @ Proposition::ConditionIs(_, true)
                if let Some((
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessEqual,
                        left: value,
                        right: bound,
                    },
                    _,
                )) = condition_source_0.old_condition() =>
            {
                (value, bound, false)
            }
            _ => return None,
        };
        let bits32_constant!(goal_bits) = goal_bound.as_ref() else {
            return None;
        };
        let goal_constant = constant_u32(*goal_bits) as i32;
        let (surface_lower, surface_upper) = surface_nonstrict_parts(&surface_goal)?;
        let (surface_value, surface_goal_constant) = if lower_bound {
            (surface_upper, surface_lower)
        } else {
            (surface_lower, surface_upper)
        };
        let mut candidates = Vec::new();
        for premise in derivation.context_premises().iter() {
            let Proposition::ConditionIs(term, polarity) = premise else {
                continue;
            };
            let bound = match (term.old_form(), polarity, lower_bound) {
                (
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterEqual,
                        left: value,
                        right: bound,
                    },
                    true,
                    true,
                )
                | (
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessThan,
                        left: value,
                        right: bound,
                    },
                    false,
                    true,
                )
                | (
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessEqual,
                        left: value,
                        right: bound,
                    },
                    true,
                    false,
                )
                | (
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterThan,
                        left: value,
                        right: bound,
                    },
                    false,
                    false,
                ) if value == goal_value => bound,
                _ => continue,
            };
            let bits32_constant!(bits) = bound.as_ref() else {
                continue;
            };
            let constant = constant_u32(*bits) as i32;
            let stronger = if lower_bound {
                constant > goal_constant
            } else {
                constant < goal_constant
            };
            if stronger && !candidates.contains(&constant) {
                candidates.push(constant);
            }
        }
        let operator = if lower_bound {
            ComparisonOperator::GreaterEqual
        } else {
            ComparisonOperator::LessEqual
        };
        for constant in candidates {
            let surface_constant =
                SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(constant as u32)));
            let bound_surface = SyntaxProposition::Comparison {
                left: surface_value.clone(),
                operator,
                right: surface_constant.clone(),
            };
            let link_surface = SyntaxProposition::Comparison {
                left: surface_constant.clone(),
                operator,
                right: surface_goal_constant.clone(),
            };
            let Ok(scope) = search_input.driver().open_have(bound_surface.clone()) else {
                continue;
            };
            let Some(scope) = (scope).driver().try_direct_logical_closure().ok().flatten() else {
                continue;
            };
            let Ok(proof) = scope.join() else {
                continue;
            };
            let Ok(scope) = proof.driver().open_have(link_surface.clone()) else {
                continue;
            };
            let Some(scope) = scope.driver().try_direct_logical_closure().ok().flatten() else {
                continue;
            };
            let Ok(proof) = scope.join() else {
                continue;
            };
            let composed = SyntaxProposition::Comparison {
                left: surface_value.clone(),
                operator,
                right: surface_goal_constant.clone(),
            };
            let Ok(applied) = proof
                .driver()
                .have_by_integer_arithmetic(composed, vec![bound_surface, link_surface])
            else {
                continue;
            };
            if applied.is_complete() {
                return Some(applied);
            }
            if let Some(closed) =
                crate::kernel::search::ProofSearch::try_direct_logical_closure(&(applied))
                    .ok()
                    .flatten()
            {
                return Some(closed);
            }
        }
        None
    }

    /// Closes an unsigned order goal that is one step of uint32 arithmetic
    /// from an exact fact: a predecessor, a successor under a strict bound,
    /// or the descent of a difference, by the uint32 lemma that states that
    /// wrapping step, or one comparison read the other way round, by Integer
    /// arithmetic.
    ///
    /// The goal's shape names the step and the one premise it needs, which
    /// is looked up exactly, so the work is a fixed number of lookups
    /// whatever the context holds.
    pub(in crate::surface::proof) fn try_unsigned_order_step(
        search_input: &Proof<'a>,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_unsigned_order_step");
        crate::kernel::search::ProofSearch::try_unsigned_order_step_from(
            search_input,
            &|kernel| search_input.unsigned_surface_fact(kernel),
            true,
        )
    }

    /// [`Self::try_unsigned_order_step`] with the premise taken from the
    /// surface premises a tactic lists, and from nowhere else: the step
    /// `arithmetic() using { ... }` promises to use exactly those.
    pub(in crate::surface::proof) fn try_unsigned_order_step_using(
        search_input: &Proof<'a>,
        surface_premises: &[SyntaxProposition],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_unsigned_order_step_using");
        // Only an unsigned order goal has a lemma, so only then are the
        // listed premises lowered.
        unsigned_order_parts(search_input.goal()?)?;
        let listed = surface_premises
            .iter()
            .filter_map(|surface| {
                let kernel = search_input
                    .lower_cited_surface_proposition(surface, "`close() using` premise")
                    .ok()?;
                search_input
                    .facts()
                    .listed_premise_available(&kernel, &[], false)
                    .then(|| (kernel, surface.clone()))
            })
            .collect::<Vec<_>>();
        crate::kernel::search::ProofSearch::try_unsigned_order_step_from(
            search_input,
            &|kernel| {
                listed
                    .iter()
                    .find(|(listed, _)| listed == kernel)
                    .map(|(_, surface)| surface.clone())
            },
            false,
        )
    }

    pub(in crate::surface::proof) fn try_unsigned_order_step_from(
        search_input: &Proof<'a>,
        surface_fact: &dyn Fn(&Proposition) -> Option<SyntaxProposition>,
        reversals: bool,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_unsigned_order_step_from");
        let (order, left, right) = unsigned_order_parts(search_input.goal()?)?;
        let zero = OldMachineTerm::constant(0);
        // The goal from one comparison read the other way round, by
        // Integer arithmetic: the premise's operands, compared the goal's
        // way. `arithmetic() using` reads such a premise itself.
        let reversed_fact = |condition: OldConditionTerm, operator: ComparisonOperator| {
            if !reversals {
                return None;
            }
            let surface = surface_fact(&Proposition::condition_is(condition, true))?;
            let (lower, upper) = match operator {
                ComparisonOperator::LessThan | ComparisonOperator::GreaterThan => {
                    surface_strict_parts(&surface)?
                }
                _ => surface_nonstrict_parts(&surface)?,
            };
            let (left, right) = match operator {
                ComparisonOperator::LessThan | ComparisonOperator::LessEqual => (lower, upper),
                _ => (upper, lower),
            };
            let conclusion = SyntaxProposition::Comparison {
                left,
                operator,
                right,
            };
            let applied = search_input
                .driver()
                .have_by_integer_arithmetic(conclusion, vec![surface])
                .ok()?;
            crate::kernel::search::ProofSearch::try_direct_logical_closure(&(applied))
                .ok()
                .flatten()
        };
        match order {
            UnsignedOrder::Less => {
                // `value - 1 <u value` from `0 <u value`.
                // A `uint32` operator is its own node, its constants
                // `uint32` ones; a word operator of the same bits reads alike.
                if let binary_term!(Bits32, Subtract, decremented, amount) = &left
                    && decremented.as_ref() == &right
                    && amount.constant32() == Some(1)
                {
                    if let Some((proof, premise, _, value)) =
                        Self::try_unsigned_strict_fact(search_input, &zero, &right, surface_fact)
                    {
                        return proof.driver().close_with_unsigned_lemma(
                            "click::integer::uint32_positive_predecessor_strictly_decreases",
                            vec![value],
                            premise,
                        );
                    }
                    // The value is a difference `upper - lower`, nonzero
                    // because `lower <u upper`.
                    if let binary_term!(Bits32, Subtract, upper, lower) = &right
                        && let Some((proof, premise, lower, upper)) =
                            Self::try_unsigned_strict_fact(search_input, lower, upper, surface_fact)
                    {
                        // Keep this wrapping difference native when expansion
                        // reads it back in Integer specification arithmetic.
                        let difference = SyntaxTerm::CUnary {
                            operand: Box::new(SyntaxTerm::Subtract(
                                Box::new(upper.clone()),
                                Box::new(lower.clone()),
                            )),
                            lowered: ProgramExpression::Cast {
                                expression: Box::new(ProgramExpression::Value(int32(0))),
                                target_type: ProgramType::UInt32,
                                integer_mode: crate::kernel::IntegerCastMode::CConversion,
                                pointee_struct: None,
                                pointee_struct_size: None,
                                pointee_volatile: false,
                                pointee_constant: false,
                                explicit_qualification: false,
                            },
                        };
                        let positive = SyntaxProposition::Comparison {
                            left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                                ProgramValue::UInt32(OldMachineTerm::uint32_constant(0)),
                            )),
                            operator: ComparisonOperator::LessThan,
                            right: difference.clone(),
                        };
                        let proof = proof.driver().apply_step(ProofStep::ApplyPlannedTheorem {
                                application: TheoremApplication {
                                    name: "click::integer::uint32_less_than_implies_positive_difference"
                                        .to_string(),
                                    arguments: vec![lower, upper],
                                },
                                premises: vec![premise],
                            })
                            .ok()?;
                        return proof.driver().close_with_unsigned_lemma(
                            "click::integer::uint32_positive_predecessor_strictly_decreases",
                            vec![difference],
                            positive,
                        );
                    }
                    return None;
                }
                // `(0 - value) + (bound - 1) <u (0 - value) + bound` from
                // `value <u bound`: the affine forms a measure `bound -
                // value` over a constant evaluates to.
                if let (
                    binary_term!(Bits32, Add, left_base, left_offset),
                    binary_term!(Bits32, Add, right_base, right_offset),
                ) = (&left, &right)
                    && left_base == right_base
                    && let binary_term!(Bits32, Subtract, negated_zero, value) = left_base.as_ref()
                    && negated_zero.constant32() == Some(0)
                    && let (Some(lower), Some(bound)) =
                        (left_offset.as_const(), right_offset.as_const())
                    && bound != 0
                    && lower == bound - 1
                    && let Some((proof, premise, value, bound)) = Self::try_unsigned_strict_fact(
                        search_input,
                        value,
                        right_offset,
                        surface_fact,
                    )
                {
                    return proof.driver().close_with_unsigned_lemma(
                        "click::integer::uint32_difference_decreases_after_increment",
                        vec![value, bound],
                        premise,
                    );
                }
                reversed_fact(
                    OldConditionTerm::unsigned_greater_than(right, left),
                    ComparisonOperator::LessThan,
                )
            }
            UnsignedOrder::LessEqual => {
                // `value + 1 <=u upper` from `value <u upper`.
                if let binary_term!(Bits32, Add, value, amount) = &left
                    && amount.constant32() == Some(1)
                    && let Some((proof, premise, value, upper)) =
                        Self::try_unsigned_strict_fact(search_input, value, &right, surface_fact)
                {
                    return proof.driver().close_with_unsigned_lemma(
                        "click::integer::uint32_increment_upper_bound",
                        vec![value, upper],
                        premise,
                    );
                }
                reversed_fact(
                    OldConditionTerm::unsigned_greater_equal(right, left),
                    ComparisonOperator::LessEqual,
                )
            }
            UnsignedOrder::Greater => reversed_fact(
                OldConditionTerm::unsigned_less_than(right, left),
                ComparisonOperator::GreaterThan,
            ),
            UnsignedOrder::GreaterEqual => reversed_fact(
                OldConditionTerm::unsigned_less_equal(right, left),
                ComparisonOperator::GreaterEqual,
            ),
        }
    }

    pub(in crate::surface::proof) fn try_selected_predecessor_upper_bound(
        search_input: &Proof<'a>,
        goal: &Proposition,
        premise_pairs: &[(Proposition, SyntaxProposition)],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_selected_predecessor_upper_bound");
        if !matches!(search_input.context.as_ref(), ProofContext::FixedState(_)) {
            return None;
        }
        let Some((
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left: predecessor,
                right: goal_upper,
            },
            true,
        )) = goal.old_condition()
        else {
            return None;
        };
        let binary_term!(Int32, Subtract, value, amount) = predecessor.as_ref() else {
            return None;
        };
        if amount.as_ref() != &OldMachineTerm::constant(1) {
            return None;
        }
        let upper_kernel = Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left: value.clone(),
                right: goal_upper.clone(),
            },
            true,
        );
        let (_, upper_surface) = premise_pairs
            .iter()
            .find(|(kernel, _)| kernel == &upper_kernel)?;
        let (surface_value, _) = surface_nonstrict_parts(upper_surface)?;
        let nonnegative_surface = SyntaxProposition::Comparison {
            left: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(0))),
            operator: ComparisonOperator::LessEqual,
            right: surface_value.clone(),
        };
        for (kernel, surface) in premise_pairs {
            let Some((
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                },
                true,
            )) = kernel.old_condition()
            else {
                continue;
            };
            let selected_constant = if left.as_ref() == value.as_ref() {
                right.as_ref()
            } else if right.as_ref() == value.as_ref() {
                left.as_ref()
            } else {
                continue;
            };
            let bits32_constant!(bits) = selected_constant else {
                continue;
            };
            if (constant_u32(*bits) as i32) < 0 {
                continue;
            }
            let mut orientations = vec![surface.clone()];
            if let Some(reverse) = reverse_surface_equality(surface)
                && reverse != *surface
            {
                orientations.push(reverse);
            }
            for equality in orientations {
                let scope = search_input
                    .driver()
                    .open_have(nonnegative_surface.clone())
                    .ok()?;
                let Ok(scope) = scope.driver().apply_step(ProofStep::Rewrite(equality)) else {
                    continue;
                };
                let Some(scope) = (scope).driver().try_direct_logical_closure().ok().flatten()
                else {
                    continue;
                };
                let joined = scope.join().ok()?;
                // `arithmetic() using` the two premises would need the goal's
                // source form, which a fixed-state goal may lack; the
                // certificate it expands to is planned from the premises'
                // kernel forms and spells the goal from their operands.
                let nonnegative_kernel = joined
                    .lower_surface_proposition_direct(
                        &nonnegative_surface,
                        "nonnegative predecessor premise",
                    )
                    .ok()?;
                let listed = [nonnegative_surface.clone(), upper_surface.clone()];
                let pairs = [
                    (nonnegative_kernel, nonnegative_surface.clone()),
                    (upper_kernel.clone(), upper_surface.clone()),
                ];
                let spelled = spell_signed_goal(goal, &pairs)?;
                let scope = joined.driver().open_have(spelled).ok()?;
                let Some(body) = scope.driver().try_restricted_solve_closure(&listed) else {
                    continue;
                };
                let Ok(applied) = body.join() else {
                    continue;
                };
                if applied.is_complete() {
                    return Some(applied);
                }
                if let Some(closed) =
                    crate::kernel::search::ProofSearch::try_direct_logical_closure(&(applied))
                        .ok()
                        .flatten()
                {
                    return Some(closed);
                }
            }
        }
        None
    }

    /// Disjunctive syllogism: the goal is one disjunct of an available
    /// disjunction whose every other disjunct the context refutes exactly,
    /// as `x <= MAX / rhs` is from `rhs == 0 or x <= MAX / rhs` under
    /// `rhs != 0`. The disjunction is eliminated by `cases`, the refuted arms
    /// closing by `contradiction`. Candidates are the context's disjunction
    /// facts, each refutation one exact lookup.
    pub(in crate::surface::proof) fn try_disjunctive_syllogism_closure(
        search_input: &Proof<'a>,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_disjunctive_syllogism_closure");
        let goal = search_input.goal()?.clone();
        if !matches!(goal, Proposition::ConditionIs(_, _)) {
            return None;
        }
        let assumptions = search_input.facts().assumptions();
        let refuted = |disjunct: &Proposition| {
            let negated = match disjunct {
                Proposition::ConditionIs(condition, value) => {
                    Proposition::condition_is(condition.clone(), !value)
                }
                other => Proposition::Not(Box::new(other.clone())),
            };
            assumptions.states_required_goal(&negated)
        };
        let candidates = crate::kernel::search::disjunction_candidates(assumptions)
            .take_while(|_| !crate::instrumentation::deadline_exceeded_with_work(1))
            .filter(|disjunction| {
                if crate::kernel::search::word_order_cases_exclude(&goal, disjunction) {
                    return true;
                }
                let disjuncts = flattened_disjuncts(disjunction);
                disjuncts.iter().any(|disjunct| **disjunct == goal)
                    && disjuncts
                        .iter()
                        .filter(|disjunct| ***disjunct != goal)
                        .all(|disjunct| refuted(disjunct))
            })
            .cloned()
            .collect::<Vec<_>>();
        let frontier_anchor = match search_input.context.as_ref() {
            ProofContext::Execution(_) if search_input.focused_outcome_data().is_none() => {
                search_input.execution().map(|execution| ProgramPointRef {
                    region: CodeRegionRef::Region(execution.core.frontier.next_statement_index),
                    kind: ProgramPointKind::Entry,
                })
            }
            _ => None,
        };
        let (surface_facts, premise_anchor) = match search_input.context.as_ref() {
            ProofContext::Pure(context) => (&context.theorem_context.surface_requirements, None),
            ProofContext::FixedState(context) => (
                context.surface_propositions,
                context.premise_anchor.as_ref(),
            ),
            ProofContext::Execution(_) => match search_input.focused_outcome_data() {
                Some(data) => (&data.surface_propositions, data.premise_anchor.as_ref()),
                None => (
                    &search_input.execution()?.surface_propositions,
                    frontier_anchor.as_ref(),
                ),
            },
        };
        candidates.into_iter().find_map(|disjunction| {
            let surface = crate::kernel::search::ProofSearch::available_surface_fact(
                search_input,
                surface_facts,
                premise_anchor,
                &disjunction,
            )?;
            crate::kernel::search::ProofSearch::try_selected_disjunction_cases(
                search_input,
                &[(disjunction, surface)],
            )
        })
    }

    /// Refute equality with the excluded literal under a selected word bound.
    /// The hypothetical equality rewrites the opposite bound to a constant.
    fn try_word_order_exclusion_case(
        input: &Proof<'a>,
        assumed: &SyntaxProposition,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_word_order_exclusion_case");
        use crate::kernel::machine_integer::comparison::comparison_view;

        let goal = input
            .surface_goal()
            .cloned()
            .or_else(|| input.structural_proposition_candidate(input.goal()?))?;
        let SyntaxProposition::Comparison {
            left,
            operator: ComparisonOperator::NotEqual,
            right,
        } = surface_comparison_with_anchored_operands(&goal)
        else {
            return None;
        };
        let comparison = |left, right| SyntaxProposition::Comparison {
            left,
            operator: ComparisonOperator::Equal,
            right,
        };
        let equality = comparison(left.clone(), right.clone());
        let lowered = input
            .lower_surface_proposition_direct(&equality, "excluded word equality")
            .ok()?;
        let (condition, truth) = lowered.old_condition()?;
        let view = comparison_view(condition, *truth)?;
        let rewrite = match view
            .operands
            .map(|operand| operand.operand_view().literal().is_some())
        {
            [false, true] => equality.clone(),
            [true, false] => comparison(right, left),
            _ => return None,
        };
        let (proof, split, ids) = input.split_focused_if(equality.clone()).ok()?;
        let marker = proof.checkpoint();
        let equal = proof.focus_branch(ids[0]).ok()?;
        let negated = SyntaxProposition::Not(Box::new(assumed.clone()));
        let certificate =
            ProofCertificate::from_steps(vec![ProofStep::Rewrite(rewrite), ProofStep::Known])
                .expect("ordinary proof of the opposite comparison");
        let refuted = equal
            .driver()
            .apply_have_step(&negated, &certificate)
            .ok()?;
        let equal_done = Self::close_refuted_fact(&refuted, assumed).ok()?;
        let unequal_done = equal_done
            .focus_branch(ids[1])
            .ok()?
            .driver()
            .apply_step(ProofStep::Known)
            .ok()?;
        unequal_done
            .join_focused_if(&marker, split, ids, equality)
            .ok()
    }

    /// Eliminates one disjunction selected by the kernel derivation and
    /// proves both arms on their branch-local `Proof`s. The disjunction is
    /// never reopened once either disjunct is already available, which makes
    /// recursive branch search descend through distinct case assumptions.
    pub(in crate::surface::proof) fn try_selected_disjunction_cases(
        search_input: &Proof<'a>,
        premise_pairs: &[(Proposition, SyntaxProposition)],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_selected_disjunction_cases");
        for (kernel, surface) in premise_pairs {
            let Proposition::Or(left, right) = kernel else {
                continue;
            };
            if search_input.facts().contains(left) || search_input.facts().contains(right) {
                continue;
            }
            let (surface_left, surface_right) = match surface {
                SyntaxProposition::Or(left, right) => {
                    (left.as_ref().clone(), right.as_ref().clone())
                }
                SyntaxProposition::At {
                    selector,
                    proposition,
                } => {
                    let SyntaxProposition::Or(left, right) = proposition.as_ref() else {
                        continue;
                    };
                    (
                        SyntaxProposition::At {
                            selector: selector.clone(),
                            proposition: Box::new(left.as_ref().clone()),
                        },
                        SyntaxProposition::At {
                            selector: selector.clone(),
                            proposition: Box::new(right.as_ref().clone()),
                        },
                    )
                }
                _ => continue,
            };
            // The in-`Proof` split: both case goals coexist in one state,
            // each arm is proven by focusing its recorded id on this one
            // lineage, and the join partitions the retained steps by the
            // per-step goal attribution recorded when they were applied.
            let Ok((split_proof, split, ids)) = search_input.split_focused_cases(surface.clone())
            else {
                continue;
            };
            let marker = split_proof.checkpoint();
            let branch_surfaces = [&surface_left, &surface_right];
            let mut proof = split_proof;
            let mut complete = true;
            for (index, (id, assumed_surface)) in ids.into_iter().zip(branch_surfaces).enumerate() {
                let Ok(focused_branch) = proof.focus_branch(id) else {
                    complete = false;
                    break;
                };
                let assumed = if index == 0 { left } else { right };
                let branch = if focused_branch.goal().is_some_and(|goal| {
                    crate::kernel::proof::arithmetic_special::word_order_excludes_literal(
                        goal, assumed,
                    )
                }) {
                    Self::try_word_order_exclusion_case(&focused_branch, assumed_surface)
                } else {
                    Self::close_refuted_fact(&focused_branch, assumed_surface).ok()
                };
                let selected = branch
                    .or_else(|| {
                        crate::kernel::search::ProofSearch::try_solve_closure(&(focused_branch))
                            .ok()
                            .flatten()
                    })
                    .or_else(|| {
                        let (goal_left, goal_right) =
                            surface_logical_children(focused_branch.surface_goal()?, false)?;
                        let selected_goal = if index == 0 { goal_left } else { goal_right };
                        let scope = focused_branch.driver().open_have(selected_goal).ok()?;
                        let rewritten = scope
                            .driver()
                            .apply_step(ProofStep::Rewrite(assumed_surface.clone()))
                            .ok()?;
                        let closed = (rewritten)
                            .driver()
                            .try_direct_logical_closure()
                            .ok()
                            .flatten()?;
                        let joined = closed.join().ok()?;
                        joined.driver().apply_step(ProofStep::Known).ok()
                    });
                let Some(selected) = selected else {
                    complete = false;
                    break;
                };
                proof = selected;
            }
            if complete
                && let Ok(joined) = proof.join_focused_cases(&marker, split, ids, surface.clone())
            {
                return Some(joined);
            }
        }
        None
    }

    /// Specializes one checkable universal premise selected by the atomic
    /// decision at the current goal. Planning only chooses the explicit
    /// quantified fact, argument, and guards; each selected operation advances
    /// this `Proof` directly.
    pub(in crate::surface::proof) fn try_selected_forall_instantiation(
        search_input: &Proof<'a>,
        goal: &Proposition,
        premise_pairs: &[(Proposition, SyntaxProposition)],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_selected_forall_instantiation");
        let plan = plan_explicit_forall_instantiation(goal, premise_pairs)
            .map(|tactics| UniversalConclusionPlan {
                tactics,
                conclusion: None,
            })
            .or_else(|| {
                let surface_goal = search_input.surface_goal()?;
                let extra_arguments = search_input
                    .proposition_obligation()
                    .into_iter()
                    .flat_map(|goal| goal.surface_bindings.iter())
                    .filter_map(|(name, binding)| match binding {
                        SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                            ProgramValue::Int32(value),
                        )) => Some((
                            value.clone(),
                            SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                                (name.clone()).into(),
                            )),
                        )),
                        _ => None,
                    })
                    .collect::<Vec<_>>();
                plan_explicit_forall_instantiation_transport(
                    goal,
                    surface_goal,
                    premise_pairs,
                    &extra_arguments,
                    &|conclusion| {
                        crate::kernel::search::ProofSearch::derive_solve_atomic_proposition(
                            &(search_input
                                .facts()
                                .assumptions()
                                .clone()
                                .assume_proposition(conclusion.clone())),
                            goal,
                        )
                        .is_some()
                    },
                )
            })?;
        Self::try_universal_steps_with_arithmetic(search_input, plan)
    }

    /// Check the instantiation, then establish its selected conclusion with
    /// ordinary proof steps.
    fn try_universal_steps_with_arithmetic(
        search_input: &Proof<'a>,
        plan: UniversalConclusionPlan,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_universal_steps_with_arithmetic");
        let mut proof = search_input.clone();
        let mut openings = Vec::new();
        for (index, tactic) in plan.tactics.iter().enumerate() {
            if proof.focused_discharged() {
                if index + 1 == plan.tactics.len() && matches!(tactic, ProofTactic::Known) {
                    continue;
                }
                return None;
            }
            let driver = proof.driver();
            if matches!(tactic, ProofTactic::Have(_)) {
                let mut unfinished = None;
                proof = driver
                    .try_authoritative_linear_script_leaving_open(
                        std::slice::from_ref(tactic),
                        &mut unfinished,
                        false,
                    )
                    .ok()?
                    .or(unfinished)?;
                continue;
            }
            let step = SourceContext::PureGoal.leaf_step(tactic)?;
            let introduces = matches!(
                &step,
                ProofStep::Intro | ProofStep::IntroAs(_) | ProofStep::IntroBinder(_)
            );
            let next = driver.apply_step(step).ok()?;
            if introduces {
                openings.push((proof, next.clone()));
            }
            proof = next;
        }
        if !proof.focused_discharged() {
            let conclusion = plan.conclusion?;
            proof = Self::try_ordinary_fact_transport(
                &proof,
                &conclusion.source,
                &conclusion.target,
                &conclusion.premises,
            )
            .ok()?
            .filter(Proof::focused_discharged)?;
        }
        for (parent, introduced) in openings.into_iter().rev() {
            proof = parent.finish_generated_intro(&introduced, proof).ok()?;
        }
        Some(proof)
    }

    /// Close a selected historical conclusion with checked local proof steps.
    pub(in crate::surface::proof) fn try_ordinary_fact_transport(
        search_input: &Proof<'a>,
        source: &SyntaxProposition,
        target: &SyntaxProposition,
        premises: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_ordinary_fact_transport");
        let source_fact =
            search_input.lower_surface_proposition_direct(source, "selected fact source")?;
        let source_known = search_input.facts().pure_known_available(&source_fact);
        if source_known
            && let Some(proof) = attempt::candidate_outcome(
                search_input
                    .driver()
                    .apply_ordinary_transport_steps(target, vec![ProofStep::Known]),
            )?
        {
            return Ok(Some(proof));
        }
        if let Some(proof) = Self::try_direct_selected_fact_transport(
            search_input,
            source,
            target,
            premises,
            &source_fact,
        )? {
            return Ok(Some(proof));
        }
        if search_input.surface_goal() != Some(target) {
            let Some(scope) =
                attempt::candidate_outcome(search_input.driver().open_have(target.clone()))?
            else {
                return Ok(None);
            };
            if scope.body().surface_goal() != Some(target) {
                return Ok(None);
            }
            let Some(closed) = scope
                .driver()
                .try_ordinary_fact_transport(source, target, premises)?
            else {
                return Ok(None);
            };
            return attempt::candidate_outcome(closed.join());
        }
        if (source_known || old_reflexive_transport_source(target).as_ref() == Some(source))
            && let Some(proof) = Self::try_indexed_read_preservation(
                search_input,
                target,
                MAX_TRANSPORT_SOURCE_POINTS,
                true,
            )?
        {
            return Ok(Some(proof));
        }
        if !source_known {
            return Ok(None);
        }
        let current_source = match source {
            SyntaxProposition::At { proposition, .. } => proposition.as_ref(),
            other => other,
        };
        if let Ok(scope) = search_input.driver().open_have(current_source.clone())
            && let Ok(scope) = scope.driver().apply_step(ProofStep::Known)
            && let Ok(current) = scope.join()
            && let Some(closed) = Self::try_arithmetic_with_selected_premises(&current)?
        {
            return Ok(Some(closed));
        }
        let Some(pairs) = comparison_preservation_reads(source, target) else {
            return Ok(None);
        };
        let mut proof = search_input.clone();
        let mut equalities = Vec::new();
        for (historical, current) in pairs {
            let equality = SyntaxProposition::Comparison {
                left: current,
                operator: ComparisonOperator::Equal,
                right: historical,
            };
            let scope =
                match attempt::candidate_outcome(proof.driver().open_have(equality.clone()))? {
                    Some(scope) => scope,
                    None => return Ok(None),
                };
            if let Some(closed) =
                attempt::candidate_outcome(scope.driver().apply_step(ProofStep::Known))?
            {
                proof = closed.join()?;
            } else if let Some(closed) = scope
                .driver()
                .try_preserve_selected_fact(&equality, source.clone())?
            {
                proof = closed.join()?;
            } else {
                return Ok(None);
            }
            equalities.push(equality);
        }
        for equality in equalities {
            if proof.focused_discharged() {
                return Ok(Some(proof));
            }
            let Some(rewritten) = attempt::candidate_outcome(
                proof.driver().apply_step(ProofStep::Rewrite(equality)),
            )?
            else {
                return Ok(None);
            };
            proof = rewritten;
        }
        if proof.focused_discharged() {
            return Ok(Some(proof));
        }
        attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Known))
    }

    /// Apply the local checked rules for the candidate's named evidence.
    pub(in crate::surface::proof) fn try_direct_selected_fact_transport(
        search_input: &Proof<'a>,
        source: &SyntaxProposition,
        target: &SyntaxProposition,
        premises: &[SyntaxProposition],
        source_fact: &Proposition,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_direct_selected_fact_transport");
        // A single named footprint whose exit is current can state the
        // equality directly. Older footprints use the ordinary chain below.
        if search_input.surface_goal() == Some(target)
            && let Some(separation) =
                single_statement_preservation_premise(source, target, premises)
            && let Some(execution) = search_input.execution()
            && let Some(Proposition::ResourceSeparate { left, .. }) = attempt::candidate_outcome(
                search_input.lower_surface_proposition_direct(&separation, "transport separation"),
            )?
            && let crate::kernel::Resource::Footprint(footprint) = left.as_ref()
            && crate::kernel::MemoryStateIdentity::of(&footprint.after)
                == crate::kernel::MemoryStateIdentity::of(execution.core.state.memory())
            && footprint
                .after_resources
                .shares_storage_with(execution.core.state.resources())
            && let Some(proof) = attempt::candidate_outcome(
                search_input
                    .driver()
                    .apply_step(ProofStep::Preserve(separation)),
            )?
        {
            return Ok(Some(proof));
        }
        if let Some((steps, narrow_range)) = viewability_restriction_steps(source, target, premises)
            && let Some(target_fact) = attempt::candidate_outcome(
                search_input.lower_surface_proposition_direct(target, "transport target"),
            )?
        {
            let same_state = match (source_fact, &target_fact) {
                (
                    Proposition::MemoryLoadable {
                        memory: left,
                        wide: false,
                        ..
                    },
                    Proposition::MemoryLoadable {
                        memory: right,
                        wide: false,
                        ..
                    },
                ) if narrow_range => left == right,
                (
                    Proposition::ResourceViewable { memory: left, .. }
                    | Proposition::MemoryLoadable { memory: left, .. },
                    Proposition::ResourceViewable { memory: right, .. }
                    | Proposition::MemoryLoadable { memory: right, .. },
                ) if !narrow_range => left == right,
                _ => false,
            };
            if same_state
                && let Some(proof) = attempt::candidate_outcome(
                    search_input
                        .driver()
                        .apply_ordinary_transport_steps(target, steps),
                )?
            {
                return Ok(Some(proof));
            }
        }
        let separations = premises
            .iter()
            .filter(|premise| {
                matches!(
                    premise,
                    SyntaxProposition::Separate {
                        left: ResourceSubject::Footprint(_),
                        ..
                    }
                )
            })
            .cloned()
            .collect::<Vec<_>>();
        if let Some(steps) = statement_preservation_steps(source, target, &separations)
            .or_else(|| comparison_preservation_steps(source, target, &separations))
            .or_else(|| implication_preservation_steps(source, target, &separations))
            .or_else(|| conjunction_preservation_steps(source, target, &separations))
            .or_else(|| conjunction_projection_preservation_steps(source, target, &separations))
            && let Some(proof) = attempt::candidate_outcome(
                search_input
                    .driver()
                    .apply_ordinary_transport_steps(target, steps),
            )?
        {
            return Ok(Some(proof));
        }
        Ok(None)
    }

    /// Tries available universal facts when the atomic decision cannot name
    /// an instantiated premise. Candidate
    /// discovery is read-only; retain a specialization when the checked
    /// instantiation and subsequent closer prove the goal.
    #[cfg(test)]
    pub(in crate::surface::proof) fn try_indexed_forall_instantiation(
        search_input: &Proof<'a>,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_indexed_forall_instantiation");
        crate::kernel::search::ProofSearch::try_indexed_forall_instantiation_with_surfaces(
            search_input,
            &[],
        )
    }

    pub(in crate::surface::proof) fn try_indexed_forall_instantiation_with_surfaces(
        search_input: &Proof<'a>,
        introduced_surfaces: &[SyntaxProposition],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_indexed_forall_instantiation_with_surfaces");
        let goal = search_input.goal()?;
        let read_defined_goal = matches!(goal, Proposition::MemoryReadDefined { .. });
        let execution_view = matches!(search_input.context.as_ref(), ProofContext::Execution(_))
            .then(|| search_input.premise_fixed_state_view())
            .flatten();
        let surface_facts = match search_input.context.as_ref() {
            ProofContext::Pure(context) => &context.theorem_context.surface_requirements,
            ProofContext::FixedState(context) => context.surface_propositions,
            ProofContext::Execution(_) => execution_view.as_ref()?.surface_propositions,
        };
        let bound_variable_names = match search_input.proposition_obligation() {
            Some(goal) => goal
                .surface_bindings
                .iter()
                .filter_map(|(name, binding)| match binding {
                    SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                        ProgramValue::Int32(OldMachineTerm::Variable(variable)),
                    )) => Some((*variable, name.clone())),
                    _ => None,
                })
                .collect::<BTreeMap<_, _>>(),
            _ => BTreeMap::new(),
        };
        let surface_form = |fact: &Proposition| {
            if let Some(surface) = introduced_surfaces.iter().find(|surface| {
                search_input
                    .lower_surface_proposition(surface, "introduced forall premise")
                    .is_ok_and(|lowered| {
                        lowered == *fact
                            || condition_polarity_equivalent(&lowered, fact)
                            || quantified_equivalent_available_fact(
                                fact,
                                std::slice::from_ref(&lowered),
                            )
                            .is_some()
                    })
            }) {
                return Some(surface.clone());
            }
            let recorded = match search_input.context.as_ref() {
                ProofContext::Pure(context) => context
                    .theorem_context
                    .surface_requirements
                    .surfaces(fact)
                    .next()
                    .cloned(),
                ProofContext::FixedState(context) => {
                    context.surface_propositions.surfaces(fact).next().cloned()
                }
                ProofContext::Execution(_) => execution_view
                    .as_ref()?
                    .surface_propositions
                    .surfaces(fact)
                    .next()
                    .cloned(),
            };
            let synthesized = match search_input.context.as_ref() {
                ProofContext::Pure(_) => None,
                ProofContext::FixedState(context) => {
                    synthesize_surface_proposition_with_bound_variable_names(
                        fact,
                        context.parameter_binding,
                        context.fixed_state.state,
                        &bound_variable_names,
                    )
                }
                ProofContext::Execution(_) => {
                    let view = execution_view.as_ref()?;
                    synthesize_surface_proposition_with_bound_variable_names(
                        fact,
                        view.parameter_binding,
                        view.fixed_state.state,
                        &bound_variable_names,
                    )
                }
            };
            recorded.or(synthesized)
        };
        let introduced_candidates = introduced_surfaces
            .iter()
            .filter_map(|surface| {
                let quantified = surface_facts.available_kernel_matching(surface, |kernel| {
                    matches!(kernel, Proposition::ForAll { .. })
                        && search_input.facts().quantified_fact_available(kernel)
                })?;
                Some((quantified.clone(), Some(surface.clone())))
            })
            .collect::<Vec<_>>();
        let ordinary_candidates = crate::kernel::search::universal_candidates(search_input.facts())
            .take_while(|_| !crate::instrumentation::deadline_exceeded_with_work(1))
            .filter(|quantified| {
                !introduced_candidates
                    .iter()
                    .any(|(candidate, _)| candidate == *quantified)
            })
            .map(|quantified| (quantified.clone(), None));
        let quantified_candidates = introduced_candidates
            .iter()
            .cloned()
            .chain(ordinary_candidates);
        for (quantified, introduced_surface) in quantified_candidates {
            // Reject shape-incompatible universals before Surface lookup or
            // synthesis. Candidate extraction is structural and bounded by
            // this one indexed fact and the focused branch goal; the expensive
            // form work is reserved for a specialization that can
            // actually mention the goal's concrete argument.
            let candidate_values =
                crate::kernel::forall_guided_instantiation_candidate_values(&quantified, goal);
            let Proposition::ForAll { var, body, .. } = &quantified else {
                unreachable!("the universal candidate filter admits only universals")
            };
            if candidate_values.is_empty() {
                continue;
            }
            let recorded_surfaces = match search_input.context.as_ref() {
                ProofContext::Pure(context) => context
                    .theorem_context
                    .surface_requirements
                    .surfaces(&quantified)
                    .cloned()
                    .collect::<Vec<_>>(),
                ProofContext::FixedState(context) => context
                    .surface_propositions
                    .surfaces(&quantified)
                    .cloned()
                    .collect::<Vec<_>>(),
                ProofContext::Execution(_) => execution_view?
                    .surface_propositions
                    .surfaces(&quantified)
                    .cloned()
                    .collect::<Vec<_>>(),
            };
            let predicate_environment = match search_input.context.as_ref() {
                ProofContext::Pure(context) => context.spec_definitions.predicates,
                ProofContext::FixedState(context) => context.spec_definitions.predicates,
                ProofContext::Execution(context) => context.spec_definitions.predicates,
            };
            let mut surfaces = introduced_surface.into_iter().collect::<Vec<_>>();
            for recorded in recorded_surfaces {
                let candidate = match recorded {
                    SyntaxProposition::PredicateCall {
                        ref name,
                        ref arguments,
                    } => predicate_environment.get(name).and_then(|definition| {
                        instantiate_click_predicate_definition(definition, arguments).ok()
                    }),
                    other => Some(other),
                };
                if let Some(candidate) = candidate
                    && !surfaces.contains(&candidate)
                {
                    surfaces.push(candidate);
                }
            }
            let synthesized = {
                // A call's definedness fact names its actual return point.
                // Raise it using that recorded point when the goal is later.
                let read_view = read_defined_goal
                    .then(|| search_input.premise_fixed_state_view())
                    .flatten();
                let _recorded_points = read_view.as_ref().map(|view| {
                    super::surface_synthesis::SynthesisRecordedPointsScope::enter(
                        view.fixed_state.recorded_states,
                    )
                });
                match search_input.context.as_ref() {
                    ProofContext::Pure(_) => None,
                    ProofContext::FixedState(context) => synthesize_surface_proposition(
                        &quantified,
                        context.parameter_binding,
                        context.fixed_state.state,
                    ),
                    ProofContext::Execution(_) => {
                        let view = execution_view?;
                        synthesize_surface_proposition(
                            &quantified,
                            view.parameter_binding,
                            view.fixed_state.state,
                        )
                    }
                }
            };
            if let Some(synthesized) = synthesized
                && !surfaces.contains(&synthesized)
            {
                surfaces.push(synthesized);
            }
            for surface in surfaces {
                for value in candidate_values.iter() {
                    let argument = match value {
                        bits32_constant!(bits) => {
                            Some(SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                                ProgramValue::Int32(OldMachineTerm::constant(constant_u32(*bits))),
                            )))
                        }
                        uint64_constant!(_) => Some(SyntaxTerm::ProgramExpression(
                            ProgramExpression::Value(ProgramValue::UInt64(value.clone())),
                        )),
                        int64_constant!(_) => Some(SyntaxTerm::ProgramExpression(
                            ProgramExpression::Value(ProgramValue::Int64(value.clone())),
                        )),
                        OldMachineTerm::Variable(variable) => {
                            let Some(goal) = search_input.proposition_obligation() else {
                                continue;
                            };
                            goal.surface_bindings.iter().find_map(|(name, binding)| {
                                matches!(
                                    binding,
                                    SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                                        ProgramValue::Int32(OldMachineTerm::Variable(bound))
                                        | ProgramValue::UInt64(OldMachineTerm::Variable(bound))
                                        | ProgramValue::Int64(OldMachineTerm::Variable(bound))
                                    )) if bound == variable
                                )
                                .then(|| {
                                    SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                                        (name.clone()).into(),
                                    ))
                                })
                            })
                        }
                        _ => None,
                    };
                    let argument = argument.or_else(|| {
                        if !read_defined_goal {
                            return None;
                        }
                        let view = search_input.premise_fixed_state_view()?;
                        super::surface_synthesis::synthesize_surface_machine_expression(
                            value,
                            view.parameter_binding,
                            view.fixed_state.state,
                        )
                    });
                    let Some(argument) = argument else {
                        continue;
                    };
                    let instantiated =
                        substitute_int32_variable_in_proposition(body, **var, value.clone());
                    let mut guard_facts = Vec::new();
                    let mut current = &instantiated;
                    let mut guards_available = true;
                    while let Proposition::Implies(guard, consequent) = current {
                        let mut conjuncts = Vec::new();
                        atomic_conjuncts(guard, &mut conjuncts);
                        for conjunct in conjuncts {
                            if matches!(
                                normalize_proposition(conjunct),
                                NormalizedProposition::True
                            ) {
                                continue;
                            }
                            let exact = std::iter::once(conjunct.clone())
                                .chain(condition_polarity_forms(conjunct))
                                .find(|candidate| search_input.facts().contains(candidate));
                            let selected = exact.map(|fact| vec![fact]).or_else(|| {
                                crate::kernel::search::ProofSearch::derive_solve_atomic_proposition(
                                    search_input.facts().assumptions(),
                                    conjunct,
                                )
                                .map(|derivation| derivation.context_premises())
                            });
                            let Some(selected) = selected else {
                                guards_available = false;
                                break;
                            };
                            for actual in selected {
                                let Some(form) = surface_form(&actual) else {
                                    guards_available = false;
                                    break;
                                };
                                if !guard_facts
                                    .iter()
                                    .any(|(candidate, _)| candidate == &actual)
                                {
                                    guard_facts.push((actual, form));
                                }
                            }
                            if !guards_available {
                                break;
                            }
                        }
                        if !guards_available {
                            break;
                        }
                        current = consequent;
                    }
                    if !guards_available {
                        continue;
                    }
                    let Some(mut tactics) = instantiation_guard_tactics(
                        &surface,
                        &argument,
                        &instantiated,
                        &guard_facts,
                    ) else {
                        continue;
                    };
                    tactics.push(ProofTactic::Instantiate {
                        quantified: surface.clone(),
                        arguments: vec![argument.clone()],
                    });
                    let conclusion = current.clone();
                    let close_with_known = &conclusion == goal || read_defined_goal;
                    if close_with_known {
                        tactics.push(ProofTactic::Known);
                    }
                    let mut unfinished = None;
                    let Ok(completed) = search_input
                        .driver()
                        .try_authoritative_linear_script_leaving_open(
                            &tactics,
                            &mut unfinished,
                            false,
                        )
                    else {
                        continue;
                    };
                    let Some(instantiated_proof) = completed.or(unfinished) else {
                        continue;
                    };
                    if close_with_known {
                        if instantiated_proof.is_complete() {
                            return Some(instantiated_proof);
                        }
                        continue;
                    }

                    let transport_assumptions = search_input
                        .facts()
                        .assumptions()
                        .clone()
                        .assume_proposition(conclusion.clone());
                    let Some(transport_derivation) =
                        crate::kernel::search::ProofSearch::derive_solve_atomic_proposition(
                            &(transport_assumptions),
                            goal,
                        )
                    else {
                        continue;
                    };
                    let mut transport_surfaces = Vec::new();
                    let mut transport_written = true;
                    for premise in transport_derivation.context_premises() {
                        if premise == conclusion {
                            continue;
                        }
                        if matches!(premise, Proposition::ForAll { .. })
                            && quantified_equivalent_available_fact(
                                &premise,
                                std::slice::from_ref(&quantified),
                            )
                            .is_some()
                        {
                            // `Instantiate` has already checked this
                            // universal and published its selected conclusion.
                            // Do not feed the quantified source back into the
                            // following transport as an unrelated premise.
                            continue;
                        }
                        let Some(form) = surface_form(&premise) else {
                            transport_written = false;
                            break;
                        };
                        if !transport_surfaces.contains(&form) {
                            transport_surfaces.push(form);
                        }
                    }
                    if !transport_written {
                        continue;
                    }
                    let (selector, quantified_surface) = match &surface {
                        SyntaxProposition::At {
                            selector,
                            proposition,
                        } => (Some(selector.clone()), proposition.as_ref()),
                        other => (None, other),
                    };
                    let SyntaxProposition::ForAll {
                        name,
                        body: surface_body,
                        ..
                    } = quantified_surface
                    else {
                        continue;
                    };
                    let substitutions = std::iter::once((name.clone(), argument.clone()))
                        .collect::<BTreeMap<_, _>>();
                    let Ok(mut source) = substitute_click_proposition(surface_body, &substitutions)
                    else {
                        continue;
                    };
                    while let SyntaxProposition::Implies(_, body) = source {
                        source = *body;
                    }
                    if let Some(selector) = selector {
                        source = SyntaxProposition::At {
                            selector,
                            proposition: Box::new(source),
                        };
                    }
                    transport_surfaces.insert(0, source.clone());
                    let target = search_input.surface_goal()?.clone();
                    match crate::kernel::search::ProofSearch::try_fact_transport_from_candidates(
                        &(instantiated_proof),
                        &source,
                        &target,
                        transport_surfaces,
                    ) {
                        Ok(Some(transported)) if transported.focused_discharged() => {
                            return Some(transported);
                        }
                        Ok(_) | Err(_) => {}
                    }
                }
            }
        }
        None
    }

    /// Builds the binder-introduction chain from only the universal premises
    /// selected by the atomic decision. The planner never scans the ambient
    /// fact set; every resulting refinement applies directly to this `Proof`.
    pub(in crate::surface::proof) fn try_selected_forall_goal(
        search_input: &Proof<'a>,
        goal: &Proposition,
        surface_goal: &SyntaxProposition,
        premise_pairs: &[(Proposition, SyntaxProposition)],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_selected_forall_goal");
        let plan = plan_explicit_forall_goal_from_premises(goal, surface_goal, premise_pairs)?;
        Self::try_universal_steps_with_arithmetic(search_input, plan)
    }

    /// Retains the pointwise unchanged-load certificate for a guarded
    /// universal outcome. The kernel derivation has already selected the
    /// finite context premises relevant to this goal; after introducing the
    /// binder and guard, transport searches only those forms plus the
    /// freshly extracted guard leaves.
    pub(in crate::surface::proof) fn try_selected_unchanged_load_forall_goal(
        search_input: &Proof<'a>,
        surface_goal: &SyntaxProposition,
        premise_pairs: &[(Proposition, SyntaxProposition)],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_selected_unchanged_load_forall_goal");
        search_input.focused_outcome_data()?;
        let mut cursor = surface_goal;
        let mut proof = search_input.clone();
        let mut openings = Vec::new();
        while let SyntaxProposition::ForAll { body, .. } = cursor {
            let introduced = proof.driver().apply_step(ProofStep::Intro).ok()?;
            openings.push((proof, introduced.clone()));
            proof = introduced;
            cursor = body;
        }
        if openings.is_empty() {
            return None;
        }
        let SyntaxProposition::Implies(antecedent, _) = cursor else {
            return None;
        };
        let introduced = proof.driver().apply_step(ProofStep::Intro).ok()?;
        openings.push((proof, introduced.clone()));
        proof = introduced;
        let mut guard_surfaces = Vec::new();
        collect_surface_conjunct_leaves(antecedent, &mut guard_surfaces);
        for guard in &guard_surfaces {
            proof = Self::publish_selected_fact(&proof, &(guard.clone())).ok()?;
        }
        let target = proof.surface_goal()?.clone();
        let source = old_reflexive_transport_source(&target)?;
        let source_pairs = proof
            .lower_surface_proposition(&source, "unchanged-load transport source")
            .ok()
            .and_then(|kernel| {
                crate::kernel::search::ProofSearch::derive_atomic_proposition(
                    proof.facts().assumptions(),
                    &kernel,
                )
            })
            .and_then(|derivation| {
                let data = proof.focused_outcome_data()?;
                let pairs = derivation
                    .context_premises()
                    .into_iter()
                    .filter_map(|premise| {
                        crate::kernel::search::ProofSearch::available_surface_fact(
                            &(proof),
                            &data.surface_propositions,
                            data.premise_anchor.as_ref(),
                            &premise,
                        )
                        .map(|surface| (premise, surface))
                    })
                    .collect::<Vec<_>>();
                Some(pairs)
            })
            .unwrap_or_default();
        let data = proof.focused_outcome_data()?;
        let anchor = data.premise_anchor.as_ref()?;
        let view = proof.outcome_fixed_state_view()?;
        let anchor_state = view.fixed_state.recorded_states.get(anchor)?;
        let mut anchored_candidates = Vec::new();
        for (kernel, _) in premise_pairs.iter().chain(&source_pairs) {
            let Some(surface) =
                synthesize_surface_proposition(kernel, view.parameter_binding, anchor_state)
            else {
                continue;
            };
            let Ok(surface) = surface_at_program_point(&surface, anchor) else {
                continue;
            };
            let Some((left, right)) = surface_nonstrict_parts(&surface) else {
                continue;
            };
            let left_is_atomic_variable = match &left {
                SyntaxTerm::ProgramExpression(ProgramExpression::Variable(_)) => true,
                SyntaxTerm::At { expression, .. } => matches!(
                    expression.as_ref(),
                    SyntaxTerm::ProgramExpression(ProgramExpression::Variable(_))
                ),
                _ => false,
            };
            if left == right || !left_is_atomic_variable || anchored_candidates.contains(&surface) {
                continue;
            }
            let Ok(lowered) =
                proof.lower_surface_proposition(&surface, "unchanged-load transport premise")
            else {
                continue;
            };
            if lowered == *kernel || condition_polarity_equivalent(&lowered, kernel) {
                anchored_candidates.push(surface);
            }
        }
        // The source derivation must identify one exact non-strict bound at
        // the outcome anchor. Ambiguity is a prompt miss, never permission to
        // probe combinations of historical facts.
        let [anchored_candidate] = anchored_candidates.as_slice() else {
            return None;
        };
        let candidates = std::iter::once(anchored_candidate.clone()).chain(guard_surfaces);
        let transported = match crate::kernel::search::ProofSearch::try_fixed_state_fact_transport(
            &(proof),
            &source,
            &target,
            candidates,
        ) {
            Ok(Some(transported)) => transported,
            Ok(None) | Err(_) => return None,
        };
        let mut closed = if transported.is_complete() {
            transported
        } else {
            Self::try_direct_logical_closure(&transported)
                .ok()
                .flatten()?
        };
        for (parent, introduced) in openings.into_iter().rev() {
            closed = parent.finish_generated_intro(&introduced, closed).ok()?;
        }
        Some(closed)
    }

    pub(in crate::surface::proof) fn try_typed_atomic_solve_closure(
        search_input: &Proof<'a>,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_typed_atomic_solve_closure");
        let (goal, derivation, premise_pairs) =
            crate::kernel::search::ProofSearch::selected_solve_derivation(search_input, false)?;
        // Resource unfolding records the body conjunction as one checked
        // fact.  Special derivations cite the exact relation leaf, so expose
        // that leaf through an ordinary checked `have` proof before
        // constructing a certificate.  This keeps certificate premises
        // top-level and preserves the source spelling/state that produced
        // the resource fact.
        match crate::kernel::search::ProofSearch::extract_special_conjunct_premises(
            search_input,
            &derivation,
            &premise_pairs,
        ) {
            Ok(Some(extracted)) if extracted.is_complete() => Some(extracted),
            Ok(Some(extracted)) => {
                crate::kernel::search::ProofSearch::check_typed_atomic_solve_candidate(
                    &(extracted),
                    &goal,
                    &derivation,
                    &premise_pairs,
                )
            }
            Ok(None) => crate::kernel::search::ProofSearch::check_typed_atomic_solve_candidate(
                search_input,
                &goal,
                &derivation,
                &premise_pairs,
            ),
            Err(()) => crate::kernel::search::ProofSearch::check_typed_atomic_solve_candidate(
                search_input,
                &goal,
                &derivation,
                &premise_pairs,
            ),
        }
    }

    pub(in crate::surface::proof) fn extract_special_conjunct_premises(
        search_input: &Proof<'a>,
        derivation: &PropositionDerivation,
        premise_pairs: &[(Proposition, SyntaxProposition)],
    ) -> Result<Option<Proof<'a>>, ()> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("extract_special_conjunct_premises");
        let exact_sources = premise_pairs
            .iter()
            .map(|(kernel, surface)| (kernel, surface))
            .collect::<BTreeMap<_, _>>();
        let (surface_facts, premise_anchor) = match search_input.context.as_ref() {
            ProofContext::Pure(context) => (&context.theorem_context.surface_requirements, None),
            ProofContext::FixedState(context) => {
                (context.surface_propositions, context.premise_anchor.clone())
            }
            ProofContext::Execution(_) => match search_input.focused_outcome_data() {
                Some(data) => (&data.surface_propositions, data.premise_anchor.clone()),
                None => {
                    let execution = search_input.execution().ok_or(())?;
                    (
                        &execution.presentation.surface_propositions,
                        frontier_premise_anchor(execution),
                    )
                }
            },
        };
        let mut proof = search_input.clone();
        let mut extracted = false;
        for premise in derivation.context_premises().iter() {
            check_verification_deadline().map_err(|_| ())?;
            if proof.facts().contains_top_level(premise)
                || !proof.facts().contains_proper_conjunct(premise)
            {
                continue;
            }
            // The selected derivation and its exact Surface correspondence
            // are one candidate. Do not resolve the spelling again after a
            // checked transition: at an execution outcome the same written
            // load may then denote a different memory state.
            let source = exact_sources
                .get(premise)
                .copied()
                .cloned()
                .or_else(|| {
                    crate::kernel::search::ProofSearch::available_surface_fact(
                        &(proof),
                        surface_facts,
                        premise_anchor.as_ref(),
                        premise,
                    )
                })
                .or_else(|| {
                    premise_anchor.as_ref().and_then(|_| {
                        crate::kernel::search::ProofSearch::available_surface_fact(
                            &(proof),
                            surface_facts,
                            None,
                            premise,
                        )
                    })
                })
                .ok_or(())?;
            // Select the exact semantic premise before constructing its
            // `have`: a cached historical spelling may read a newer cell.
            let cited = proof
                .lower_surface_proposition_direct(&source, "selected atomic premise")
                .map_err(|_| ())?;
            if &cited != premise {
                return Err(());
            }
            let successor = Self::publish_selected_fact(&proof, &source).map_err(|_| ())?;
            // `have source` proves only the proposition to which `source`
            // lowers in this successor's context. A stale presentation record
            // can therefore make the step succeed without publishing the
            // exact premise selected above. Exact top-level membership is the
            // progress measure; polarity or state conversion requires its
            // own checked proof step rather than being assumed here.
            if !successor.is_complete() && !successor.facts().contains_top_level(premise) {
                return Err(());
            }
            // Establishing a premise can also discharge the goal. Its checked
            // completion is sufficient; later premises require an open goal.
            if successor.is_complete() {
                return Ok(Some(successor));
            }
            proof = successor;
            extracted = true;
        }
        Ok(extracted.then_some(proof))
    }

    /// Searches from exactly the Surface premises named by `close() using`.
    /// This query cannot add facts or close the goal: it returns only the
    /// descendant obtained by checking the typed atomic decision through the
    /// ordinary Proof transitions.
    pub(in crate::surface::proof) fn try_restricted_solve_closure(
        search_input: &Proof<'a>,
        surfaces: &[SyntaxProposition],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_restricted_solve_closure");
        if crate::surface::proof::implicit_solve_scope::checked_only() {
            crate::instrumentation::replay_forbids_discovery("close() using");
            return None;
        }
        if let Some(closed) =
            crate::kernel::search::ProofSearch::try_restricted_solve_closure_before_arithmetic(
                search_input,
                surfaces,
            )
        {
            return Some(closed);
        }
        // What the closers above miss goes to the arithmetic engine, as
        // `arithmetic() using` sends it: a bound from the goal's own terms,
        // a sum or chain over the premises, or a refutation of
        // contradictory ones. Existing strategies precede theorem discovery
        // so a goal they close keeps its expansion.
        search_input
            .driver()
            .apply_step(ProofStep::ArithmeticUsing(surfaces.to_vec()))
            .ok()
            .filter(|closed| closed.is_complete() || closed.focused_discharged())
            .or_else(|| {
                crate::kernel::search::ProofSearch::try_listed_operation_identities(
                    search_input,
                    surfaces,
                )
                .ok()
                .flatten()
            })
            .or_else(|| Self::try_single_theorem_using(search_input, surfaces))
    }

    /// Discover one application, never its premises or a chain of lemmas.
    /// `ApplyTheoremUsing` receives only the written list, including argument
    /// guards, and retains the ordinary checked step for expansion.
    fn try_single_theorem_using(
        search_input: &Proof<'a>,
        surfaces: &[SyntaxProposition],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_single_theorem_using");
        use crate::surface::planning::theorems::TheoremConclusionMatch;
        use attempt::SearchFailureKind;
        let mut scope = attempt::search_scope("theorem discovery");
        let mut matched = false;
        let Some(goal) = search_input.surface_goal() else {
            attempt::record_theorem_discovery_note(
                SearchFailureKind::Unsupported,
                "no surface goal is available for theorem discovery".into(),
            );
            return None;
        };
        let environment = match search_input.context.as_ref() {
            ProofContext::Pure(context) => context.theorem_environment,
            ProofContext::FixedState(context) => context.theorem_environment,
            ProofContext::Execution(context) => context.theorem_environment,
        };
        for candidate in environment.conclusion_candidates(goal) {
            if crate::instrumentation::deadline_exceeded_with_work(1) {
                attempt::record_theorem_discovery_note(
                    SearchFailureKind::Exhausted,
                    "theorem discovery budget exhausted".into(),
                );
                return None;
            }
            if search_input
                .claim_label()
                .strip_prefix(&candidate.name)
                .is_some_and(|suffix| suffix.is_empty() || suffix.starts_with('.'))
            {
                continue;
            }
            let definition = environment.get(&candidate.name)?;
            for outcome in crate::surface::planning::theorems::theorem_conclusion_matches(
                definition,
                candidate.ensure,
                goal,
            ) {
                matched = true;
                let application = match outcome {
                    TheoremConclusionMatch::Application(application) => application,
                    TheoremConclusionMatch::UndeterminedArgument(name) => {
                        attempt::record_theorem_discovery_note(
                            SearchFailureKind::UndeterminedArgument,
                            format!(
                                "theorem `{}`: argument `{name}` cannot be inferred from the goal; supply it with explicit apply(...)",
                                candidate.name
                            ),
                        );
                        continue;
                    }
                    TheoremConclusionMatch::Exhausted => {
                        attempt::record_theorem_discovery_note(
                            SearchFailureKind::Exhausted,
                            "theorem discovery budget exhausted".into(),
                        );
                        return None;
                    }
                };
                let step = ProofStep::ApplyPlannedTheorem {
                    application,
                    premises: surfaces.to_vec(),
                };
                if let Some(proof) =
                    attempt::candidate_outcome(search_input.driver().apply_step(step)).ok()?
                {
                    if proof.is_complete() || proof.focused_discharged() {
                        scope.succeed();
                        return Some(proof);
                    }
                    // The matched conclusion may use the opposite comparison
                    // spelling. Close its equivalent goal with the existing
                    // indexed rule and retain that explicit step in expansion.
                    if let Some(closed) =
                        attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Known))
                            .ok()?
                        && (closed.is_complete() || closed.focused_discharged())
                    {
                        scope.succeed();
                        return Some(closed);
                    }
                }
            }
        }
        // Index lookup can spend the remaining work even when its bucket is
        // empty. Observe that exhaustion without charging another checkpoint.
        if crate::instrumentation::deadline_exceeded_with_work(0) {
            attempt::record_theorem_discovery_note(
                SearchFailureKind::Exhausted,
                "theorem discovery budget exhausted".into(),
            );
        } else if !matched {
            attempt::record_theorem_discovery_note(
                SearchFailureKind::NoMatch,
                "no available theorem conclusion matched the goal in the supported structural fragment".into(),
            );
        }
        None
    }

    /// Establish the goal's machine-operation identities from only the
    /// listed bounds and type ranges, then retry arithmetic with those
    /// explicit identities. Each bound and identity remains in expansion.
    pub(in crate::surface::proof) fn try_listed_operation_identities(
        search_input: &Proof<'a>,
        surfaces: &[SyntaxProposition],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_listed_operation_identities");
        let (Some(goal), Some(surface_goal)) = (search_input.goal(), search_input.surface_goal())
        else {
            return Ok(None);
        };
        if integer_affine_claim(goal).is_none() {
            return Ok(None);
        }
        let premises = surfaces
            .iter()
            .map(|surface| {
                search_input.lower_cited_surface_proposition(surface, "operation identity premise")
            })
            .collect::<Result<Vec<_>, _>>()?;
        let identities = operation_identities(machine_observations(goal, &premises));
        if identities.is_empty() {
            return Ok(None);
        }
        let written =
            written_integer_observations(std::iter::once(surface_goal).chain(surfaces.iter()));
        let identities = identities.iter().collect::<Vec<_>>();
        let Ok((proof, established)) =
            crate::kernel::search::ProofSearch::prove_operation_identities(
                search_input,
                &identities,
                &written,
                Some(surfaces),
            )?
        else {
            return Ok(None);
        };
        let mut premises = surfaces.to_vec();
        premises.extend(established.into_iter().map(|(_, surface)| surface));
        Ok(proof
            .driver()
            .apply_step(ProofStep::ArithmeticUsing(premises))
            .ok()
            .filter(|closed| closed.is_complete() || closed.focused_discharged()))
    }

    /// Name the file-scope object selected by the pointer's defining
    /// store. Replay cites that equality and checks the current permission.
    fn try_linked_pointer_viewability(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_linked_pointer_viewability");
        let Some(Proposition::MemoryLoadable {
            base,
            bytes,
            wide: false,
            ..
        }) = search_input.goal()
        else {
            return Ok(None);
        };
        let Some(SyntaxProposition::Loadable { segment }) = search_input.surface_goal() else {
            return Ok(None);
        };
        let ContractSegmentSurface::Range {
            base: written,
            start,
            end,
        } = &segment.surface
        else {
            return Ok(None);
        };
        if segment.state != ContractSegmentState::Current || bytes.as_const().is_none() {
            return Ok(None);
        }
        let stored = crate::kernel::pointer_read_over_immediate_store(base);
        let address = stored.as_ref().unwrap_or(base);
        let AddressBase::StaticObject { binding } = &address.base else {
            return Ok(None);
        };
        if binding.function().is_some() || !matches!(address.offset.view(), OffsetView::Constant(0))
        {
            return Ok(None);
        }

        let observe = |segment| ProofStep::ObserveResource(ResourceClause::ViewMemory(segment));
        let observed =
            attempt::candidate_outcome(search_input.driver().apply_step(observe(segment.clone())))?;
        let proof = if let Some(proof) = observed {
            proof
        } else if stored.is_some() {
            let candidate = (|| {
                let object = ProgramExpression::AddressOf(Box::new(ProgramExpression::Variable(
                    binding.clone().into(),
                )));
                let object_expression = SyntaxTerm::ProgramExpression(object.clone());
                let equality = SyntaxProposition::Comparison {
                    left: written.clone(),
                    operator: ComparisonOperator::Equal,
                    right: object_expression.clone(),
                };
                let proof =
                    search_input
                        .driver()
                        .apply_step(super::super::wide_arithmetic::have(
                            equality.clone(),
                            vec![ProofStep::Known],
                        ))?;
                let rewritten = proof.driver().apply_step(ProofStep::Rewrite(equality))?;
                if rewritten.focused_discharged() {
                    return Ok(rewritten);
                }
                rewritten.driver().apply_step(observe(ContractSegment {
                    base: object,
                    surface: ContractSegmentSurface::Range {
                        base: object_expression,
                        start: start.clone(),
                        end: end.clone(),
                    },
                    ..segment.clone()
                }))
            })();
            let Some(proof) = attempt::candidate_outcome(candidate)? else {
                return Ok(None);
            };
            proof
        } else {
            return Ok(None);
        };
        if proof.focused_discharged() {
            return Ok(Some(proof));
        }
        attempt::candidate_outcome(proof.driver().apply_step(ProofStep::Known))
    }

    /// Both forms of solve select the same explicit endpoint proof. Ambient
    /// source enumeration belongs only to the unrestricted smart tactic.
    pub(in crate::surface::proof) fn try_ordinary_viewability_restriction_closure(
        search_input: &Proof<'a>,
        selected: Option<&[SyntaxProposition]>,
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_ordinary_viewability_restriction_closure");
        let Some(Proposition::MemoryLoadable { wide, .. }) = search_input.goal() else {
            return None;
        };
        let target = search_input.surface_goal()?;
        // Reject other goal shapes before selecting any ambient premises.
        let SyntaxProposition::Loadable { segment } = target else {
            return None;
        };
        let ContractSegmentSurface::Range { .. } = &segment.surface else {
            return None;
        };
        let recorded;
        let surfaces = match selected {
            Some(selected) => selected,
            None => {
                let map = search_input.premise_surface_facts()?;
                recorded = map
                    .requirement_kernel_atoms_for_search()
                    .filter(|atom| {
                        matches!(
                            atom,
                            Proposition::MemoryLoadable { .. } | Proposition::ConditionIs(..)
                        )
                    })
                    .map(|atom| {
                        map.recorded_requirement_surface(atom)
                            .expect("requirement atoms retain their enclosing source clause")
                            .clone()
                    })
                    .collect::<Vec<_>>();
                &recorded
            }
        };
        for recorded_source in surfaces {
            let mut source = recorded_source;
            while let SyntaxProposition::At { proposition, .. } = source {
                source = proposition;
            }
            let SyntaxProposition::Loadable { segment } = source else {
                continue;
            };
            // A past view suggests a descriptor to try, not evidence that it
            // is still live. The ordinary observation selects an exact held
            // permission in the current state; it never follows history.
            let mut segment = segment.clone();
            segment.state = ContractSegmentState::Current;
            let source = SyntaxProposition::Loadable {
                segment: segment.clone(),
            };
            let prepared = (|| {
                let scope = search_input.driver().open_have(source.clone())?;
                let scope = scope.driver().apply_step(ProofStep::Known).or_else(|_| {
                    scope.driver().apply_step(ProofStep::ObserveResource(
                        ResourceClause::ViewMemory(segment),
                    ))
                })?;
                scope.join()
            })();
            let Ok(prepared) = prepared else {
                continue;
            };
            if prepared.is_complete() || prepared.focused_discharged() {
                return Some(prepared);
            }
            let mut premises = surfaces.to_vec();
            premises.push(source.clone());
            let goals = if *wide {
                rebased_viewability_restriction_steps(&source, target, &premises)
                    .or_else(|| native_viewability_restriction_steps(&source, target, &premises))
            } else {
                computed_viewability_restriction_steps(&source, target, &premises)
                    .or_else(|| native_viewability_restriction_steps(&source, target, &premises))
            };
            let Some(goals) = goals else {
                continue;
            };
            let candidate = goals
                .into_iter()
                .try_fold(prepared, |proof, (proposition, steps)| {
                    let candidate = (|| {
                        let mut scope = proof.driver().open_have_as_written(proposition)?;
                        for step in steps {
                            scope = scope.driver().apply_step(step)?;
                        }
                        scope.join()
                    })();
                    candidate.ok()
                })
                .and_then(|proof| proof.driver().apply_step(ProofStep::Known).ok());
            if let Some(proof) = candidate
                && (proof.is_complete() || proof.focused_discharged())
            {
                return Some(proof);
            }
        }
        None
    }

    /// Use only selected viewability and condition premises. Prove the
    /// endpoint comparisons separately and apply the range containment law.
    fn try_selected_viewability_containment(
        search_input: &Proof<'a>,
        surfaces: &[SyntaxProposition],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_selected_viewability_containment");
        let SyntaxProposition::Loadable {
            segment: target_segment,
        } = search_input.surface_goal()?
        else {
            return None;
        };
        let child = ResourceSubject::Memory(target_segment.clone());
        for source in surfaces {
            let mut descriptor = source;
            while let SyntaxProposition::At { proposition, .. } = descriptor {
                descriptor = proposition;
            }
            let SyntaxProposition::Loadable {
                segment: source_segment,
            } = descriptor
            else {
                continue;
            };
            if crate::instrumentation::deadline_exceeded_with_work(1) {
                return None;
            }
            // Retain the selected citation. If it names another memory
            // state, first establish the current view across recorded effects.
            let current_source = SyntaxProposition::Loadable {
                segment: source_segment.clone(),
            };
            let prepare_source = || {
                if source == descriptor {
                    return Some((search_input.clone(), source.clone()));
                }
                let retained = search_input
                    .lower_cited_surface_proposition(source, "selected historical view")
                    .ok()?;
                let scope = search_input
                    .driver()
                    .open_have(current_source.clone())
                    .ok()?;
                if scope.goal() == Some(&retained) {
                    return Some((search_input.clone(), source.clone()));
                }
                let current = scope
                    .driver()
                    .try_preserve_selected_fact(&current_source, source.clone())
                    .ok()??
                    .join()
                    .ok()?;
                Some((current, current_source.clone()))
            };
            let Some((view_proof, source)) = prepare_source() else {
                continue;
            };
            let parent = ResourceSubject::Memory(source_segment.clone());
            let containment = SyntaxProposition::Contains {
                parent: parent.clone(),
                child: child.clone(),
            };
            let prepared = (|| {
                // A fixed byte span can cross element widths, where the
                // element-range theorem below does not apply.
                let scope = view_proof.driver().open_have(containment.clone()).ok()?;
                if scope.goal().is_some_and(normalizes_context_free)
                    && let Ok(closed) = scope.driver().apply_step(ProofStep::Known)
                {
                    return closed.join().ok();
                }
                let (base, lo, hi) = source_segment.surface_range()?;
                let (target_base, inner_lo, inner_hi) = target_segment.surface_range()?;
                if source_segment.state != target_segment.state {
                    return None;
                }
                let observe = |value: &SyntaxTerm| SyntaxTerm::Call {
                    name: "to_integer".into(),
                    arguments: vec![value.clone()],
                };
                let point = match contract_expression_as_program_expression(target_base) {
                    Some(ProgramExpression::AddressOf(element))
                        if target_segment.start == ProgramExpression::Value(int32(0))
                            && target_segment.end == ProgramExpression::Value(int32(1)) =>
                    {
                        match *element {
                            ProgramExpression::Index(pointer, index) => Some((
                                SyntaxTerm::ProgramExpression(*pointer),
                                SyntaxTerm::ProgramExpression(*index),
                            )),
                            _ => None,
                        }
                    }
                    _ => None,
                };
                let (target_base, law, arguments, comparisons) =
                    if let Some((pointer, index)) = &point {
                        (
                            pointer,
                            "click::separation::contains_element",
                            vec![base, lo, hi, index],
                            vec![
                                (lo, ComparisonOperator::LessEqual, index),
                                (index, ComparisonOperator::LessThan, hi),
                            ],
                        )
                    } else {
                        (
                            target_base,
                            "click::separation::contains_subrange",
                            vec![base, lo, hi, inner_lo, inner_hi],
                            vec![
                                (lo, ComparisonOperator::LessEqual, inner_lo),
                                (inner_lo, ComparisonOperator::LessEqual, inner_hi),
                                (inner_hi, ComparisonOperator::LessEqual, hi),
                            ],
                        )
                    };
                let mut current = view_proof;
                let alias = if base != target_base {
                    let equality = SyntaxProposition::Comparison {
                        left: target_base.clone(),
                        operator: ComparisonOperator::Equal,
                        right: base.clone(),
                    };
                    let scope = current.driver().open_have(equality.clone()).ok()?;
                    current = scope
                        .driver()
                        .try_restricted_solve_closure(surfaces)?
                        .join()
                        .ok()?;
                    Some(equality)
                } else {
                    None
                };
                let mut bounds = Vec::new();
                for (left, operator, right) in comparisons {
                    let bound = SyntaxProposition::Comparison {
                        left: observe(left),
                        operator,
                        right: observe(right),
                    };
                    let scope = current.driver().open_have(bound.clone()).ok()?;
                    current = scope
                        .driver()
                        .try_restricted_solve_closure(surfaces)?
                        .join()
                        .ok()?;
                    bounds.push(bound);
                }
                let mut scope = current.driver().open_have(containment.clone()).ok()?;
                if let Some(alias) = alias {
                    scope = scope.driver().apply_step(ProofStep::Rewrite(alias)).ok()?;
                }
                scope
                    .driver()
                    .apply_step(ProofStep::ApplyPlannedTheorem {
                        application: TheoremApplication {
                            name: law.into(),
                            arguments: arguments.into_iter().cloned().collect(),
                        },
                        premises: bounds,
                    })
                    .ok()?
                    .join()
                    .ok()
            })();
            let Some(prepared) = prepared else {
                continue;
            };
            let proof = prepared
                .driver()
                .apply_step(ProofStep::ApplyPlannedTheorem {
                    application: TheoremApplication {
                        name: "click::separation::viewable_restrict".into(),
                        arguments: [parent, child.clone()]
                            .into_iter()
                            .map(|resource| SyntaxTerm::Resource(Box::new(resource)))
                            .collect(),
                    },
                    premises: vec![source, containment],
                })
                .ok();
            if let Some(closed) = proof.filter(|proof| proof.focused_discharged()) {
                return Some(closed);
            }
        }
        None
    }

    pub(in crate::surface::proof) fn try_restricted_solve_closure_before_arithmetic(
        search_input: &Proof<'a>,
        surfaces: &[SyntaxProposition],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_restricted_solve_closure_before_arithmetic");
        if let Ok(Some(closed)) = Self::try_pointer_translation_using(search_input, surfaces) {
            return Some(closed);
        }
        if let Ok(Some(closed)) = Self::try_widened_unsigned_sum_using(search_input, surfaces) {
            return Some(closed);
        }
        if let Ok(Some(closed)) = Self::try_address_words_using(search_input, surfaces) {
            return Some(closed);
        }
        if let Ok(Some(closed)) = Self::try_quotient_shift_using(search_input, surfaces) {
            return Some(closed);
        }
        if let Ok(Some(closed)) = Self::try_conditional_bridge_using(search_input, surfaces) {
            return Some(closed);
        }
        if let Ok(Some(closed)) = Self::try_machine_bridge_using(search_input, surfaces) {
            return Some(closed);
        }
        if let Some(proof) =
            Self::try_ordinary_viewability_restriction_closure(search_input, Some(surfaces))
        {
            return Some(proof);
        }
        if let Some(proof) = Self::try_selected_viewability_containment(search_input, surfaces) {
            return Some(proof);
        }
        if search_input.has_conjunctive_goal()
            && !matches!(
                search_input.surface_goal(),
                Some(SyntaxProposition::And(..))
            )
            && !search_input.goal().is_some_and(|goal| {
                crate::kernel::machine_integer::definedness::ordinary_arithmetic_guard_view(goal)
                    .is_some()
            })
        {
            let split = (|| {
                let (proof, split, ids) = search_input.split_focused_both().ok()?;
                let marker = proof.conjunction_checkpoint(ids).ok()?;
                let left = crate::kernel::search::ProofSearch::try_restricted_solve_closure(
                    &(proof.focus_branch(ids[0]).ok()?),
                    surfaces,
                )?;
                let right = crate::kernel::search::ProofSearch::try_restricted_solve_closure(
                    &(left.focus_branch(ids[1]).ok()?),
                    surfaces,
                )?;
                right.join_focused_both(&marker, split, ids).ok()
            })();
            if split.is_some() {
                return split;
            }
        }
        // A conjunction is proved one conjunct at a time, each as a checked
        // `have` from the same listed premises, and then closed from the
        // conjuncts it added.
        if let (Some(Proposition::And(_, _)), Some(SyntaxProposition::And(left, right))) =
            (search_input.goal(), search_input.surface_goal())
        {
            let mut proof = search_input.clone();
            for conjunct in [left, right] {
                let scope = proof.driver().open_have(conjunct.as_ref().clone()).ok()?;
                proof = (scope)
                    .driver()
                    .try_restricted_solve_closure(surfaces)?
                    .join()
                    .ok()?;
            }
            return proof
                .driver()
                .apply_step(ProofStep::Known)
                .ok()
                .filter(Proof::is_complete);
        }
        // A named restricted premise may be a leaf of one exact available
        // conjunction (commonly after `unfold(predicate)`). Materialize that
        // leaf through an explicit `have`/`known` proof before
        // asking the restricted planner to use it. The returned descendant
        // therefore owns both the semantic fact and the Surface evidence;
        // expansion does not need to reconstruct and check a certificate to
        // justify the premise later.
        let mut proof = search_input.clone();
        for surface in surfaces {
            let kernel = proof
                .lower_surface_proposition(surface, "restricted solve premise")
                .ok()?;
            proof = proof.materialize_selected_resource_separation(&kernel)?;
            if !proof.facts().contains_top_level(&kernel)
                && !normalizes_context_free(&kernel)
                && proof.facts().contains_proper_conjunct(&kernel)
            {
                proof = Self::publish_selected_fact(&proof, &(surface.clone())).ok()?;
                if proof.is_complete() {
                    return Some(proof);
                }
            }
        }
        let goal = proof.goal()?;
        if (matches!(&goal, condition_source_0 @ Proposition::ConditionIs(_, _) if matches!(condition_source_0.old_condition(), Some((OldConditionTerm::Float32(_) | OldConditionTerm::Float64(_), _))))
            || crate::kernel::proof::fact_reasoning::is_quotient_remainder_order(goal))
            && Self::known_bridge_using(&proof, surfaces).ok() == Some(true)
        {
            return proof
                .driver()
                .apply_step(ProofStep::Known)
                .ok()
                .filter(Proof::is_complete);
        }
        let premise_pairs = surfaces
            .iter()
            .map(|surface| {
                let kernel = proof
                    .lower_surface_proposition(surface, "restricted solve premise")
                    .ok()?;
                // A listed premise that lowers to a context-free truth needs
                // no ambient fact authority. Retaining it lets the restricted
                // derivation erase reflexive field equalities after the
                // outcome state has evaluated their loads. Resource
                // separation may instead be supplied by the compact
                // composition authority, so use the same checked availability
                // query without publishing unrelated member pairs.
                (proof.facts().available_across_effects(&kernel, &[])
                    || normalizes_context_free(&kernel))
                .then_some((kernel, surface.clone()))
            })
            .collect::<Option<Vec<_>>>()?;
        if crate::surface::planning::solve::computes_with_known(goal) {
            return proof
                .driver()
                .apply_step(ProofStep::Known)
                .ok()
                .filter(|closed| closed.is_complete() || closed.focused_discharged());
        }
        if let Ok(Some(closed)) = Self::try_interval_exclusion_using(&proof, &premise_pairs) {
            return Some(closed);
        }
        // A listed equality under a definedness guard the list does not
        // state: prove the guard from the other listed premises, extract the
        // consequent, and continue from the list with the consequent in the
        // implication's place.
        if let Some(closed) = crate::kernel::search::ProofSearch::try_restricted_guarded_consequent(
            &(proof),
            surfaces,
            &premise_pairs,
        ) {
            return Some(closed);
        }
        // A listed implication and its listed antecedent justify extracting
        // the consequent. Keep this route explicitly tied to `using`, rather
        // than allowing an unrelated ambient implication to discharge it.
        for (premise, fact) in &premise_pairs {
            let Proposition::Implies(antecedent, consequent) = premise else {
                continue;
            };
            if consequent.as_ref() != goal
                || !premise_pairs
                    .iter()
                    .any(|(selected, _)| selected == antecedent.as_ref())
            {
                continue;
            }
            let (premises, _) = crate::surface::proof::driver::fact_application_parts(fact);
            if let Ok(applied) = proof.driver().apply_step(ProofStep::ApplyFactUsing {
                fact: fact.clone(),
                premises,
            }) {
                if applied.is_complete() {
                    return Some(applied);
                }
                if let Ok(closed) = applied.driver().apply_step(ProofStep::Known)
                    && closed.is_complete()
                {
                    return Some(closed);
                }
            }
        }
        let restricted = premise_pairs
            .iter()
            .map(|(kernel, _)| kernel.clone())
            .collect::<Vec<_>>();
        // Signed-order and definedness rules have checked named theorem
        // certificates. Try those before allocating speculative normalization
        // contexts, including for predecessor and negated-bound rules without
        // an explicit `+ 1`.
        let signed_order = signed_nonstrict_parts(goal)
            .or_else(|| signed_strict_parts(goal))
            .is_some();
        let try_typed_derivation = || {
            let SolveEvidence::Derivation(derivation) =
                plan_solve_certificate(goal, &assumptions_from_propositions(&restricted))?
            else {
                return None;
            };
            crate::kernel::search::ProofSearch::check_typed_atomic_solve_candidate(
                &(proof),
                goal,
                &derivation,
                &premise_pairs,
            )
        };
        let arithmetic_domain = signed_definedness_operands(goal).is_some()
            || crate::kernel::machine_integer::definedness::ordinary_arithmetic_guard_view(goal)
                .is_some();
        let typed_first = signed_order || arithmetic_domain;
        if let Some(tactics) = plan_explicit_predecessor_upper_bound(goal, &premise_pairs)
            .or_else(|| plan_explicit_le_and_not_lt_implies_eq(goal, &premise_pairs))
            && matches!(tactics.first(), Some(ProofTactic::ApplyTheoremUsing { .. }))
            && let Ok(Some(closed)) = proof.driver().try_generated_linear_script(&tactics)
            && closed.focused_discharged()
        {
            return Some(closed);
        }
        // Try interval proofs early for scalar word observations. Retained
        // reads and history use their own checked proofs.
        let scalar_observation = proof
            .surface_goal()
            .is_some_and(|surface| !signed_intervals::has_retained_read_source(surface))
            && !surfaces
                .iter()
                .any(signed_intervals::has_retained_read_source)
            && crate::kernel::proof::integer_arithmetic::integer_affine_machine_values(goal)
                .iter()
                .any(|value| value.ty().format().bits() == 32);
        let interval_first = typed_first || scalar_observation;
        if arithmetic_domain
            && let Ok(Some(closed)) =
                Self::try_restricted_signed_definedness_closure(&proof, &premise_pairs)
        {
            return Some(closed);
        }
        // A selected alias or index equality can expose the actual
        // cited read. Retain those substitutions and the exact closing fact.
        if let Some(
            surface @ SyntaxProposition::Comparison {
                operator: ComparisonOperator::Equal,
                ..
            },
        ) = proof.surface_goal()
            && signed_intervals::has_retained_read_source(surface)
            && let Ok(Some(closed)) = Self::try_premise_equality_chain_closure(
                &proof,
                &premise_pairs,
                RewriteClosers::ExactListed(&premise_pairs),
            )
        {
            return Some(closed);
        }
        if interval_first
            && let Ok(Some(closed)) = Self::try_signed_interval_using(&proof, surfaces)
        {
            return Some(closed);
        }
        if typed_first && let Some(closed) = try_typed_derivation() {
            return Some(closed);
        }
        if (crate::kernel::proof::arithmetic_special::checks_selected_float_bounds(
            goal,
            &restricted,
        ) || crate::kernel::proof::arithmetic_special::checks_signed_product_guards(
            goal,
            &restricted,
        )) && let Ok(closed) = proof
            .driver()
            .apply_step(ProofStep::CloseBounds(surfaces.to_vec()))
        {
            return Some(closed);
        }
        if crate::kernel::proof::fact_reasoning::is_single_normalization_condition(goal)
            || !crate::kernel::proof::term_rewrite::TermRewrite::conditional_guards(goal).is_empty()
        {
            let conditions = premise_pairs
                .iter()
                .filter(|&(kernel, _surface)| !condition_polarity_forms(kernel).is_empty())
                .map(|(_kernel, surface)| surface.clone())
                .collect::<Vec<_>>();
            let condition_kernels = premise_pairs
                .iter()
                .filter(|(kernel, _)| !condition_polarity_forms(kernel).is_empty())
                .map(|(kernel, _)| kernel.clone())
                .collect::<Vec<_>>();
            // Use the selected-context reduction only to choose a checked strategy.
            if !conditions.is_empty()
                && crate::kernel::proof::fact_reasoning::normalize_using_conditions(
                    goal,
                    &condition_kernels,
                    &crate::kernel::proof::PureFactStore::from_ordered(&restricted),
                )
                .is_ok()
            {
                // Only a successful selected discovery hint gives an Integer
                // observation this extra typed route. A failed goal must keep
                // its original bounded search and diagnostic behavior.
                if !interval_first
                    && let Ok(Some(closed)) = Self::try_signed_interval_using(&proof, surfaces)
                {
                    return Some(closed);
                }
                if let Ok(Some(closed)) = Self::try_local_checked_closure(&proof, Some(conditions))
                    && closed.is_complete()
                {
                    return Some(closed);
                }
            }
        }
        if let Ok(Some(closed)) = Self::try_integer_composition_using(&proof, surfaces) {
            return Some(closed);
        }
        // A definedness goal is left to the typed candidates and the
        // `int32_defined` / `int64_defined` closer below, so an
        // operand-specific theorem application keeps its priority.
        if let Some(surface_goal) = proof.surface_goal()
            && !arithmetic_domain
            && let Some(plan) = plan_arithmetic(ArithmeticEngine::Special, goal, &restricted)
                .and_then(ArithmeticPlan::special)
        {
            let certificate = special_plan_to_surface(
                &plan,
                &premise_pairs
                    .iter()
                    .map(|(_, surface)| surface.clone())
                    .collect::<Vec<_>>(),
                surface_goal,
            );
            let signed_width = certificate.nodes.iter().find_map(|n| {
                if let SpecialArithmeticNode::SignedDefined { width, .. } = n {
                    Some(*width)
                } else {
                    None
                }
            });
            if let Some(width) = signed_width {
                if let Ok(Some(closed)) =
                    Self::try_signed_definedness_bounds(&proof, width, surfaces.to_vec())
                {
                    return Some(closed);
                }
            } else {
                if let Ok(Some(closed)) = Self::apply_specialized_composition(&proof, &certificate)
                    && closed.is_complete()
                {
                    return Some(closed);
                }
            }
        }
        // The selected context has not changed, so the ordinary derivation
        // slot need not repeat the early attempt.
        let typed = if typed_first {
            None
        } else {
            try_typed_derivation()
        };
        typed
            .or_else(|| {
                crate::kernel::search::ProofSearch::try_premise_equality_chain_closure(
                    &(proof),
                    &premise_pairs,
                    RewriteClosers::Listed(&premise_pairs),
                )
                .ok()
                .flatten()
            })
            .or_else(|| {
                crate::kernel::search::ProofSearch::try_outcome_anchored_order_transitivity(
                    &(proof),
                    &premise_pairs,
                )
            })
            .or_else(|| {
                crate::kernel::search::ProofSearch::try_outcome_anchored_increment_order(
                    &(proof),
                    &premise_pairs,
                )
            })
            // An exact selected premise or context-free normalization may
            // close directly. An arbitrary ambient `known` must remain
            // invisible through this explicitly restricted boundary.
            .or_else(|| {
                crate::kernel::search::ProofSearch::try_typed_atomic_solve_from_selected_premises(
                    &(proof),
                    &premise_pairs,
                )
            })
            // An `int32` or `int64` definedness goal: the listed premises that
            // bound an operand by a constant, checked by the `int32_defined` /
            // `int64_defined` rule. It runs after the operand-specific `int32`
            // theorem applications above, which keep their checked form.
            .or_else(|| {
                crate::kernel::search::ProofSearch::try_restricted_signed_definedness_closure(
                    &(proof),
                    &premise_pairs,
                )
                .ok()
                .flatten()
            })
    }

    pub(in crate::surface::proof) fn try_selected_pointer_inequality_rewrite(
        search_input: &Proof<'a>,
        goal: &Proposition,
        premises: &[(Proposition, SyntaxProposition)],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_selected_pointer_inequality_rewrite");
        if !matches!(&goal, condition_source_0 @ Proposition::ConditionIs(_, false) if matches!(condition_source_0.old_condition(), Some((OldConditionTerm::AddressEqual(_, _), _))))
        {
            return None;
        }
        for (kernel, source) in premises {
            if !matches!(&kernel, condition_source_0 @ Proposition::ConditionIs(_, true) if matches!(condition_source_0.old_condition(), Some((OldConditionTerm::AddressEqual(_, _), _))))
            {
                continue;
            }
            let deanchored = match source {
                SyntaxProposition::Comparison {
                    left:
                        SyntaxTerm::At {
                            selector: left_selector,
                            expression: left,
                        },
                    operator: ComparisonOperator::Equal,
                    right:
                        SyntaxTerm::At {
                            selector: right_selector,
                            expression: right,
                        },
                } if left_selector == right_selector => Some(SyntaxProposition::Comparison {
                    left: left.as_ref().clone(),
                    operator: ComparisonOperator::Equal,
                    right: right.as_ref().clone(),
                }),
                _ => None,
            };
            for spelling in std::iter::once(source.clone()).chain(deanchored) {
                for oriented in
                    std::iter::once(spelling.clone()).chain(reverse_surface_equality(&spelling))
                {
                    let Ok(rewritten) = search_input
                        .driver()
                        .apply_step(ProofStep::Rewrite(oriented))
                    else {
                        continue;
                    };
                    if let Ok(Some(closed)) =
                        crate::kernel::search::ProofSearch::try_direct_logical_closure(&(rewritten))
                    {
                        return Some(closed);
                    }
                }
            }
        }
        None
    }

    fn try_local_viewability_preservation(
        search_input: &Proof<'a>,
        goal: &Proposition,
        premise_pairs: &[(Proposition, SyntaxProposition)],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_local_viewability_preservation");
        let Proposition::MemoryLoadable {
            memory,
            base,
            bytes,
            wide,
            ..
        } = goal
        else {
            return None;
        };
        let surface_goal @ SyntaxProposition::Loadable { segment } = search_input.surface_goal()?
        else {
            return None;
        };
        if segment.state != ContractSegmentState::Current {
            return None;
        }
        let view = search_input.premise_fixed_state_view()?;
        let records = view.fixed_state.recorded_states;
        let mut next_memory = crate::kernel::intern_memory_ref(memory);
        let mut regions = Vec::new();
        for (selector, _) in records.recent(24) {
            let ProgramPointSelector::ProgramPoint(ProgramPointRef {
                region: region @ CodeRegionRef::Region(_),
                kind: ProgramPointKind::Exit,
            }) = selector
            else {
                continue;
            };
            let Ok(Resource::Footprint(footprint)) = records.footprint(region) else {
                continue;
            };
            let before = crate::kernel::intern_memory_ref(&footprint.before);
            let reaches_next = crate::kernel::intern_memory_ref(&footprint.after) == next_memory
                || (regions.is_empty()
                    && footprint.viewability_survives_return_cleanup(memory, base));
            if !footprint.preserves_separate_viewability || before == next_memory || !reaches_next {
                continue;
            }
            regions.push(region.clone());
            let entry = Proposition::MemoryLoadable {
                memory: footprint.before.clone(),
                point: footprint.before_point.path_link().clone(),
                base: base.clone(),
                bytes: bytes.clone(),
                wide: *wide,
            };
            if !premise_pairs.iter().any(|(premise, _)| premise == &entry) {
                next_memory = before;
                continue;
            }

            // The selected view holds at the oldest endpoint. Replay one
            // explicitly separated transition at a time towards the goal.
            let mut current = search_input.clone();
            let separation_proof = ProofCertificate::from_steps(vec![ProofStep::Known])
                .expect("footprint separation uses an ordinary proof step");
            for (index, region) in regions.iter().enumerate().rev() {
                let separation = SyntaxProposition::Separate {
                    left: ResourceSubject::Footprint(region.clone()),
                    right: ResourceSubject::Memory(segment.clone()),
                };
                current = current
                    .driver()
                    .apply_have_step(&separation, &separation_proof)
                    .ok()?;
                let step = ProofStep::Preserve(separation);
                if index == 0 {
                    return current.driver().apply_step(step).ok();
                }
                let at_exit = SyntaxProposition::At {
                    selector: ProgramPointSelector::ProgramPoint(ProgramPointRef {
                        region: region.clone(),
                        kind: ProgramPointKind::Exit,
                    }),
                    proposition: Box::new(surface_goal.clone()),
                };
                let proof = ProofCertificate::from_steps(vec![step])
                    .expect("preserve is an ordinary proof step");
                current = current.driver().apply_have_step(&at_exit, &proof).ok()?;
            }
        }
        None
    }

    pub(in crate::surface::proof) fn check_typed_atomic_solve_candidate(
        search_input: &Proof<'a>,
        goal: &Proposition,
        derivation: &PropositionDerivation,
        premise_pairs: &[(Proposition, SyntaxProposition)],
    ) -> Option<Proof<'a>> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("check_typed_atomic_solve_candidate");
        // Fixed-state obligations can lack a source presentation. Retain a
        // spelled have first; its ordinary child proof has a source goal and
        // follows the same selected-premise path as an authored proof.
        if search_input.surface_goal().is_none()
            && crate::kernel::proof::arithmetic_special::signed_definedness_query(goal).is_some()
            && let Some(spelled) = spell_signed_goal(goal, premise_pairs)
        {
            let scope = search_input.driver().open_have(spelled).ok()?;
            let selected = premise_pairs
                .iter()
                .map(|(_, p)| p.clone())
                .collect::<Vec<_>>();
            let closed = scope.driver().try_restricted_solve_closure(&selected)?;
            return closed
                .join()
                .ok()?
                .driver()
                .apply_step(ProofStep::Known)
                .ok();
        }
        // A direct loadability derivation already selected its source range.
        // Expand that selection through ordinary observation, preservation,
        // or containment.
        if matches!(goal, Proposition::MemoryLoadable { .. }) {
            let selected = premise_pairs
                .iter()
                .map(|(_, surface)| surface.clone())
                .collect::<Vec<_>>();
            if let Some(proof) =
                Self::try_ordinary_viewability_restriction_closure(search_input, Some(&selected))
                    .or_else(|| {
                        Self::try_local_viewability_preservation(search_input, goal, premise_pairs)
                    })
                    .or_else(|| Self::try_selected_viewability_containment(search_input, &selected))
            {
                return Some(proof);
            }
        }
        let surface_goal = search_input.surface_goal();
        let tactics = recorded_signed_order_pairs(derivation, premise_pairs)
            .and_then(|ordered| plan_recorded_signed_order_path(goal, &ordered))
            .or_else(|| {
                let ordered = recorded_wide_order_pairs(derivation, premise_pairs)?;
                plan_recorded_wide_order_path(&ordered)
            })
            .or_else(|| plan_recorded_bitvector_equality_path(goal, derivation, premise_pairs))
            .or_else(|| {
                if !derivation.is_int32_pinned_constant_equality() {
                    return None;
                }
                let kernels = premise_pairs
                    .iter()
                    .map(|(premise, _)| premise.clone())
                    .collect::<Vec<_>>();
                plan_arithmetic(ArithmeticEngine::SignedInt32, goal, &kernels)
                    .and_then(ArithmeticPlan::signed_int32)?;
                Some(vec![ProofTactic::ArithmeticUsing(
                    premise_pairs.iter().map(|(_, p)| p.clone()).collect(),
                )])
            })
            .or_else(|| {
                plan_recorded_pointer_alignment(goal, derivation, premise_pairs, surface_goal?)
            })
            .or_else(|| plan_recorded_pointer_word(goal, derivation, premise_pairs, surface_goal?))
            .or_else(|| {
                let recorded =
                    recorded_load_address_congruence_path_pairs(derivation, premise_pairs)?;
                plan_recorded_load_address_congruence(goal, derivation, &recorded)
            })
            .or_else(|| plan_pointer_advanced_load_equality(goal, premise_pairs))
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation.int32_increment_upper_bound_step()?.premise()],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_increment_upper_bound(goal, &recorded)
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation
                        .int32_increment_constant_upper_bound_step()?
                        .premise()],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_increment_constant_upper_bound(goal, &recorded)
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation
                        .int32_increment_strictly_increases_step()?
                        .premise()],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_increment_strictly_increases(goal, &recorded)
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation
                        .int32_one_plus_strictly_increases_step()?
                        .premise()],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_one_plus_strictly_increases(goal, &recorded)
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation.int32_increment_below_max_is_defined_premise()?],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_increment_below_max_is_defined(goal, &recorded)
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation.int32_one_plus_below_max_is_defined_premise()?],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_one_plus_below_max_is_defined(goal, &recorded)
            })
            .or_else(|| {
                let (first, second) = derivation.int32_nonnegative_add_within_max_premises()?;
                let recorded = recorded_premise_pairs([first, second], premise_pairs, false)?;
                let mut tactics =
                    plan_explicit_nonnegative_add_within_max_is_defined(goal, &recorded)?;
                // Outside an execution the theorem's conclusion is the exact
                // goal and closes it; its trailing `known` is dropped.
                if !matches!(search_input.context.as_ref(), ProofContext::Execution(_)) {
                    tactics.pop();
                }
                Some(tactics)
            })
            .or_else(|| {
                let (first, second) =
                    derivation.int32_nonnegative_subtract_within_value_premises()?;
                let recorded = recorded_premise_pairs([first, second], premise_pairs, false)?;
                plan_explicit_nonnegative_subtract_within_value_is_defined(goal, &recorded)
            })
            .or_else(|| {
                let (first, second) = derivation.int32_increment_lower_bound_steps()?;
                let recorded = recorded_premise_pairs(
                    [first.premise(), second.premise()],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_increment_lower_bound(goal, &recorded)
            })
            .or_else(|| {
                let (first, second) =
                    derivation.int32_increment_greater_equal_lower_bound_steps()?;
                let recorded = recorded_premise_pairs(
                    [first.premise(), second.premise()],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_increment_greater_equal_lower_bound(goal, &recorded)
            })
            .or_else(|| {
                let (first, second) =
                    derivation.int32_increment_strict_greater_lower_bound_steps()?;
                let recorded = recorded_premise_pairs(
                    [first.premise(), second.premise()],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_increment_strict_greater_lower_bound(goal, &recorded)
            })
            .or_else(|| {
                let (first, second) =
                    derivation.int32_increment_strict_greater_from_strict_lower_steps()?;
                let recorded = recorded_premise_pairs(
                    [first.premise(), second.premise()],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_increment_strict_greater_from_strict_lower(goal, &recorded)
            })
            .or_else(|| {
                let (first, second) = derivation.int32_increment_preserves_order_steps()?;
                let recorded = recorded_premise_pairs(
                    [first.premise(), second.premise()],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_increment_preserves_order(goal, &recorded)
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation
                        .int32_positive_predecessor_is_nonnegative_step()?
                        .premise()],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_positive_predecessor_is_nonnegative(goal, &recorded)
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation
                        .int32_positive_predecessor_strictly_decreases_step()?
                        .premise()],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_positive_predecessor_strictly_decreases(goal, &recorded)
            })
            .or_else(|| {
                let (first, second) =
                    derivation.int32_nonnegative_predecessor_upper_bound_steps()?;
                let recorded = recorded_premise_pairs(
                    [first.premise(), second.premise()],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_predecessor_upper_bound(goal, &recorded)
            })
            .or_else(|| {
                let recorded =
                    recorded_int32_equal_one_predecessor_is_zero_pairs(derivation, premise_pairs)?;
                plan_recorded_int32_equal_one_predecessor_is_zero(goal, derivation, &recorded)
            })
            .or_else(|| {
                let recorded = recorded_int32_equal_one_predecessor_is_nonnegative_pairs(
                    derivation,
                    premise_pairs,
                )
                .or_else(|| {
                    recorded_int32_equal_one_predecessor_strictly_decreases_pairs(
                        derivation,
                        premise_pairs,
                    )
                })?;
                plan_recorded_int32_equal_one_predecessor(goal, derivation, &recorded)
            })
            .or_else(|| {
                let recorded = recorded_int32_one_le_predecessor_is_nonnegative_pairs(
                    derivation,
                    premise_pairs,
                )
                .or_else(|| {
                    recorded_int32_one_le_predecessor_strictly_decreases_pairs(
                        derivation,
                        premise_pairs,
                    )
                })?;
                plan_explicit_one_le_predecessor(goal, &recorded)
            })
            .or_else(|| {
                let (first, second) = derivation.int32_le_and_not_lt_implies_equality_premises()?;
                let recorded = recorded_premise_pairs([first, second], premise_pairs, true)?;
                plan_explicit_le_and_not_lt_implies_eq(goal, &recorded)
            })
            .or_else(|| {
                let (first, second) = derivation.int32_ge_and_not_gt_implies_equality_premises()?;
                let recorded = recorded_premise_pairs([first, second], premise_pairs, true)?;
                plan_explicit_ge_and_not_gt_implies_eq(goal, &recorded)
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation.int32_positive_is_nonnegative_step()?.premise()],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_positive_is_nonnegative(goal, &recorded)
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation.int32_successor_le_implies_lt_step()?.premise()],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_successor_le_implies_lt(goal, &recorded)
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation
                        .int32_constant_lower_bound_weakening_step()?
                        .premise()],
                    premise_pairs,
                    false,
                )?;
                plan_explicit_le_transitive_constant_lower(goal, &recorded)
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation
                        .int32_negated_strict_successor_bound_step()?
                        .premise()],
                    premise_pairs,
                    true,
                )?;
                plan_explicit_negated_strict_successor_bound(goal, &recorded)
            })
            .or_else(|| {
                let (first, second) = derivation.int32_le_and_neq_implies_strict_premises()?;
                let recorded = recorded_premise_pairs([first, second], premise_pairs, true)?;
                plan_explicit_le_and_neq_implies_lt(goal, &recorded)
            })
            .or_else(|| {
                let kernels = premise_pairs
                    .iter()
                    .map(|(premise, _)| premise.clone())
                    .collect::<Vec<_>>();
                crate::surface::checking::arithmetic_plans(goal, &kernels, true).next()?;
                Some(vec![ProofTactic::ArithmeticUsing(
                    premise_pairs.iter().map(|(_, p)| p.clone()).collect(),
                )])
            });
        let Some(tactics) = tactics else {
            if matches!(goal, Proposition::MemoryLoadable { .. }) {
                attempt::record_search_note(
                    "solve view certificate planning",
                    "no source certificate plan was produced from the resolved derivation premises",
                );
            }
            return None;
        };
        // An arithmetic tail is a recipe for ordinary composition, not a retained proof step.
        if let Some(ProofTactic::ArithmeticUsing(listed)) = tactics.last() {
            let base = if tactics.len() == 1 {
                search_input.clone()
            } else {
                search_input
                    .driver()
                    .try_generated_linear_script(&tactics[..tactics.len() - 1])
                    .ok()??
            };
            let pairs = listed
                .iter()
                .map(|surface| {
                    premise_pairs
                        .iter()
                        .find(|(_, written)| written == surface)
                        .cloned()
                })
                .collect::<Option<Vec<_>>>()?;
            let Some(surface_goal) = base.surface_goal() else {
                let spelled = spell_signed_goal(goal, &pairs)?;
                let scope = base.driver().open_have(spelled).ok()?;
                let closed = scope.driver().try_restricted_solve_closure(listed)?;
                return closed
                    .join()
                    .ok()?
                    .driver()
                    .apply_step(ProofStep::Known)
                    .ok();
            };
            let kernels = pairs.iter().map(|(p, _)| p.clone()).collect::<Vec<_>>();
            for plan in crate::surface::checking::arithmetic_plans(goal, &kernels, true) {
                let candidate = match plan {
                    ArithmeticPlan::IntegerAffine(plan) => {
                        Self::apply_integer_composition(&base, &plan, &pairs, surface_goal, &[])
                            .ok()
                            .flatten()
                    }
                    ArithmeticPlan::SignedInt32(plan) => {
                        let plan = base.signed_plan_to_surface(&plan, &pairs, surface_goal)?;
                        Self::apply_signed_interval_composition(&base, &plan)
                            .ok()
                            .flatten()
                    }
                    ArithmeticPlan::Special(plan) => {
                        let plan = special_plan_to_surface(&plan, listed, surface_goal);
                        Self::apply_specialized_composition(&base, &plan)
                            .ok()
                            .flatten()
                    }
                };
                if candidate.is_some() {
                    return candidate;
                }
            }
            return None;
        }
        // The planner selects only Surface-expressible explicit operations.
        // Apply those through the same recursive Proof driver used by
        // authoritative source scripts; the plan is evidence input, not an
        // independently interpreted semantic certificate.
        let checked = search_input.driver().try_generated_linear_script(&tactics);
        if matches!(goal, Proposition::MemoryLoadable { .. })
            && let Err(error) = &checked
        {
            attempt::record_search_note("solve view certificate checking", error.raw_summary());
        }
        let proof = attempt::candidate_outcome(checked)
            .ok()
            .flatten()
            .flatten()?;
        proof.focused_discharged().then_some(proof)
    }

    /// Applies one statement step, retaining one newly proved non-load
    /// requirement when the checked step reports it as unavailable.  The
    /// requirement is lowered again at this exact frontier and compared by
    /// the shared alpha-aware identity before any proof operation is accepted.
    /// A failed retry returns the original structured error, allowing the
    /// normal smart caller to preserve its diagnostic and planner behavior.
    pub(in crate::surface::proof) fn try_statement_step_with_retries(
        search_input: &Proof<'a>,
        step: ProofStep,
        retried_requirements: &mut std::collections::BTreeSet<PropositionIdentityKey>,
    ) -> Result<Proof<'a>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_statement_step_with_retries");
        // Smart execution exposes supported missing source-backed
        // prerequisites before contextual compatibility reasoning can
        // discharge them invisibly. The retained proof retries the same
        // ordinary checked step after publishing its `have`.
        // Use the same checked-step entry point as written `step()` so
        // smart execution retains its fact deltas in the opt-in trace too.
        let initial = search_input.driver().apply_step(step.clone());
        let stepped = crate::kernel::search::ProofSearch::retry_statement_after_refusal(
            search_input,
            step.clone(),
            retried_requirements,
            initial,
        )?;
        crate::kernel::search::ProofSearch::retry_statement_keeping_store_cells(
            search_input,
            step,
            stepped,
        )
    }

    /// A store into an array forgets each cached cell of that array unless a
    /// fact states that the two element indices differ: the store-time check
    /// reads that exact fact and derives nothing. When the statement just run
    /// forgot such a cell, prove the index disequality at the statement's
    /// pre-state by selected-premise arithmetic or the disequality bridge
    /// (`try_index_disequality_closure`), retain it as a `have`, and run the same
    /// statement again, which now keeps the cell. The certificate records the
    /// `have` before the step, so expansion writes it and the expanded proof
    /// searches nothing. A disequality `solve` cannot prove leaves the
    /// statement as it first ran; the later read reports the store.
    pub(in crate::surface::proof) fn retry_statement_keeping_store_cells(
        search_input: &Proof<'a>,
        step: ProofStep,
        stepped: Proof<'a>,
    ) -> Result<Proof<'a>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("retry_statement_keeping_store_cells");
        let (Some(before), Some(after)) = (search_input.execution(), stepped.execution()) else {
            return Ok(stepped);
        };
        let candidates = crate::kernel::search::store_separation::cells_forgotten_beside_stores(
            before.core.state.memory(),
            after.core.state.memory(),
            MAX_STORE_SEPARATIONS_PER_STATEMENT,
        );
        if candidates.is_empty() {
            return Ok(stepped);
        }
        let mut proof = search_input.clone();
        let mut proved = 0usize;
        // The spelled disequalities the closure did not prove, kept for the
        // report of a later read of the dropped cell. Recorded on this miss
        // path only, from what the search already constructed.
        let mut misses = Vec::new();
        for candidate in &candidates {
            // The disequality is spelled by construction from its two index
            // words, `((m - 1) as int32) != 0`, and stated for the kernel
            // comparison the store reads; the requirement's round trip
            // checks its lowering. A word with no spelling skips the
            // candidate.
            let Some(surface) = search_input.store_index_disequality_surface(candidate) else {
                continue;
            };
            let requirement = UnresolvedRequirement {
                proposition: candidate.indices_differ.clone(),
                context: None,
                introductions: Default::default(),
                call_site: None,
                assertion_condition: None,
                theorem_source: None,
                statement_safety: false,
                surface: Some(surface),
            };
            let Some(Some(spelling)) =
                attempt::candidate_outcome(proof.requirement_surface(&requirement, &step))?
            else {
                continue;
            };
            let fact = spelling.surface.clone();
            let Some(have) =
                attempt::candidate_outcome(proof.driver().open_have(spelling.surface))?
            else {
                continue;
            };
            let joined = match have.driver().try_index_disequality_closure()? {
                Some(closed) => attempt::candidate_outcome(closed.join())?,
                None => None,
            };
            let Some(joined) = joined else {
                misses.push((candidate, fact));
                continue;
            };
            proof = joined;
            proved += 1;
        }
        let kept = if proved == 0 {
            stepped
        } else {
            // The statement runs again with proved facts only; it can keep
            // more cells than its first run, never fewer.
            attempt::candidate_outcome(proof.driver().apply_step(step))?.unwrap_or(stepped)
        };
        record_store_separation_misses(search_input, kept, misses)
    }

    /// `solve`'s automatic opening (design/proof-reuse.md R4): a C operation
    /// refused because the resource it reads or writes lies inside a folded
    /// resource is retried once that resource is unfolded, one layer per
    /// refused access. The certificate records each `unfold`, so expansion
    /// writes it out. A refusal the opening does not resolve is reported as
    /// the original refusal.
    pub(in crate::surface::proof) fn retry_statement_after_solve_open(
        search_input: &Proof<'a>,
        step: ProofStep,
        retried_requirements: &mut std::collections::BTreeSet<PropositionIdentityKey>,
        error: ClickError,
    ) -> Result<Proof<'a>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("retry_statement_after_solve_open");
        let mut proof = search_input.clone();
        let mut refusal = error.clone();
        for _ in 0..MAX_AUTO_OPENINGS_PER_STATEMENT {
            let Some(missing) = refusal.missing_resource() else {
                break;
            };
            let Some(opened) = Self::try_open_for_missing_resource(&proof, missing)? else {
                break;
            };
            proof = opened;
            match proof.driver().apply_step(step.clone()) {
                Ok(stepped) => return Ok(stepped),
                Err(next) if next.missing_resource().is_some() => refusal = next,
                Err(next) => {
                    return crate::kernel::search::ProofSearch::retry_statement_after_refusal(
                        &(proof),
                        step,
                        retried_requirements,
                        Err(next),
                    )
                    .map_err(|_| error);
                }
            }
        }
        Err(error)
    }

    pub(in crate::surface::proof) fn retry_statement_after_refusal(
        search_input: &Proof<'a>,
        step: ProofStep,
        retried_requirements: &mut std::collections::BTreeSet<PropositionIdentityKey>,
        initial: Result<Proof<'a>, ClickError>,
    ) -> Result<Proof<'a>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("retry_statement_after_refusal");
        match initial {
            Ok(proof) => Ok(proof),
            Err(error) if error.missing_resource().is_some() => {
                crate::kernel::search::ProofSearch::retry_statement_after_solve_open(
                    search_input,
                    step,
                    retried_requirements,
                    error,
                )
            }
            Err(error) => {
                let Some(mut requirement) = error.unresolved_requirement().cloned() else {
                    return Err(error);
                };
                let Some(identity) = proposition_identity_key(&requirement.proposition) else {
                    return Err(if requirement.statement_safety {
                        error.with_safety_preparation_error(
                            "Click could not identify the generated statement safety obligation",
                        )
                    } else {
                        error
                    });
                };
                if !retried_requirements.insert(identity) {
                    return Err(error);
                }
                let mut proof = search_input.clone();
                let mut error = error;
                loop {
                    let Some(spelling) = proof.requirement_surface(&requirement, &step)? else {
                        check_verification_deadline()?;
                        return Err(if requirement.statement_safety {
                            error.with_safety_preparation_error(
                                "Click could not raise the generated statement safety obligation",
                            )
                        } else {
                            error
                        });
                    };
                    let have = match proof.driver().open_have(spelling.surface) {
                        Ok(have) => have,
                        Err(cause)
                            if cause.kind() != crate::surface::ClickErrorKind::Proof
                                || crate::instrumentation::exceeded_verification_limit_context(
                                )
                                .is_some() =>
                        {
                            return Err(cause);
                        }
                        Err(cause) => {
                            check_verification_deadline()?;
                            return Err(if requirement.statement_safety {
                                error.with_safety_preparation_error(&format!("Click could not open the generated statement safety obligation: {}", cause.raw_summary()))
                            } else {
                                error
                            });
                        }
                    };
                    let closed = have.driver().try_solve_closure()?;
                    let Some(closed) = closed else {
                        return Err(error.with_proof_refusal(
                            crate::surface::ProofRefusal::ImplicitStatementSearch,
                        ));
                    };
                    // `join` publishes the checked proposition into the exact
                    // enclosing frontier.  Reapply the original step value so a
                    // future StepContract follows precisely the same contract
                    // selection and certificate lineage as the refused step.
                    proof = closed.join()?;
                    match proof.driver().apply_step(step.clone()) {
                        Ok(next) => return Ok(next),
                        Err(next_error) => {
                            let Some(next_requirement) =
                                next_error.unresolved_requirement().cloned()
                            else {
                                return Err(next_error);
                            };
                            let Some(next_identity) =
                                proposition_identity_key(&next_requirement.proposition)
                            else {
                                return Err(next_error);
                            };
                            if !retried_requirements.insert(next_identity) {
                                return Err(next_error);
                            }
                            requirement = next_requirement;
                            error = next_error;
                            // The next loop iteration uses the newly returned
                            // requirement, but still the same exact step.
                            continue;
                        }
                    }
                }
            }
        }
    }

    /// Tries one bare `step()` in the whole proof context. There is no premise
    /// selection: the checked step either advances the frontier or reports why
    /// the statement cannot run here. An undecided C `if` is left to the
    /// structural branch driver.
    #[cfg(test)]
    pub(in crate::surface::proof) fn try_statement_step(
        search_input: &Proof<'a>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_statement_step");
        crate::kernel::search::ProofSearch::try_statement_step_with_apply(search_input, |proof| {
            proof.driver().apply_step(ProofStep::Step)
        })
    }

    pub(in crate::surface::proof) fn try_smart_statement_step(
        search_input: &Proof<'a>,
        step: ProofStep,
        retried_requirements: &mut std::collections::BTreeSet<PropositionIdentityKey>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_smart_statement_step");
        crate::kernel::search::ProofSearch::try_statement_step_with_apply(search_input, |proof| {
            crate::kernel::search::ProofSearch::try_statement_step_with_retries(
                proof,
                step.clone(),
                retried_requirements,
            )
        })
    }

    pub(in crate::surface::proof) fn try_statement_step_with_apply(
        search_input: &Proof<'a>,
        mut apply: impl FnMut(&Proof<'a>) -> Result<Proof<'a>, ClickError>,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        #[cfg(test)]
        crate::kernel::search::record_discovery("try_statement_step_with_apply");
        let ProofContext::Execution(context) = search_input.context.as_ref() else {
            return Ok(None);
        };
        let Some(execution) = search_input.execution() else {
            return Err(search_input.step_error("execution-frontier proof lost its semantic state"));
        };
        // Structural frontiers belong to the branch and loop operations.
        let (_, _, statement, _) = next_top_level_statement_from_frontier_position(
            execution.view(),
            &execution.core.state,
            context.function,
            context.arguments,
            context.claim_label,
            context.tactic_index,
            "smart step selection",
        )?;
        if matches!(
            statement,
            ProgramStatement::If { .. } | ProgramStatement::Switch { .. }
        ) {
            // A C `if` the context decides is one step into that arm; one it
            // cannot decide is a fork for the driver's branch handling. A
            // symbolic switch likewise belongs to the bounded planner, which
            // materializes its case split before applying one switch theorem
            // per path.
            return match apply(search_input) {
                Ok(proof) => Ok(Some(proof)),
                Err(error) => {
                    if source_backed_refusal(&error, execution.core.state.memory())? {
                        Err(error)
                    } else {
                        check_verification_deadline()?;
                        Ok(None)
                    }
                }
            };
        }
        // A caught throwing call is a proof-object split frontier, not a
        // linear step failure. Let the focused execution driver publish the
        // returned/threw siblings so the eventual certificate is explicit.
        if search_input.is_at_call_outcomes_frontier()? {
            return Ok(None);
        }
        // The statement runs in the whole proof context; nothing can supply
        // more than the step already sees, so its failure is the answer,
        // with the step's diagnostic. The exception is a statement whose
        // successors are path cases: a case split on their facts supplies
        // each case's facts, and that split belongs to the planner.
        match apply(search_input) {
            Ok(proof) => Ok(Some(proof)),
            Err(error) if error.is_path_case_split() || error.requires_call_outcomes() => {
                check_verification_deadline()?;
                Ok(None)
            }
            Err(error) => Err(error),
        }
    }
}

/// Retains each store-search miss on the statement's successor, so a
/// refusal that later reads the dropped cell can name the statement and
/// the fact that keeps it. Presentation only: the checked state and its
/// certificate are unchanged.
fn record_store_separation_misses<'a>(
    search_input: &Proof<'a>,
    stepped: Proof<'a>,
    misses: Vec<(
        &crate::kernel::search::store_separation::ForgottenStoreCell,
        SyntaxProposition,
    )>,
) -> Result<Proof<'a>, ClickError> {
    if misses.is_empty() {
        return Ok(stepped);
    }
    let Some(region) = search_input.current_statement_index()? else {
        return Ok(stepped);
    };
    let statement = crate::surface::diagnostics::describe_statement_region(region);
    let cells = match search_input.execution() {
        Some(before) => misses
            .iter()
            .map(|(candidate, _)| {
                crate::surface::diagnostics::describe_source_cell_at_state(
                    &candidate.cell,
                    &before.core.state,
                )
            })
            .collect(),
        None => vec![None; misses.len()],
    };
    let fallback = stepped.clone();
    Ok(stepped
        .edit_execution_presentation(|presentation| {
            for ((candidate, fact), cell_text) in misses.into_iter().zip(cells) {
                if presentation.store_separation_misses.len()
                    >= MAX_RECORDED_STORE_SEPARATION_MISSES
                {
                    break;
                }
                presentation.store_separation_misses.push(
                    crate::surface::proof::proof_object::StoreSeparationMiss {
                        statement: statement.clone(),
                        cell: candidate.cell.clone(),
                        cell_text,
                        store: candidate.store.clone(),
                        fact,
                    },
                );
            }
        })
        .map_or(fallback, |(proof, ())| proof))
}
