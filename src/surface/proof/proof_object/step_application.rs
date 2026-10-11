//! Simple-step dispatch (`apply_step`) and checked frame application.

use super::*;
use crate::kernel::LoweringIntroduction;
use num_traits::ToPrimitive;

fn signed_constant_expression(expression: &ContractExpression) -> Option<num_bigint::BigInt> {
    match expression {
        ContractExpression::IntegerLiteral(value) => value.parse().ok(),
        ContractExpression::Negate(inner) => signed_constant_expression(inner).map(|value| -value),
        _ => None,
    }
}

fn lower_signed_constant_comparison(
    proposition: &ClickProposition,
) -> Option<crate::kernel::Proposition> {
    let ClickProposition::Comparison {
        left,
        operator,
        right,
    } = proposition
    else {
        return None;
    };
    let left = signed_constant_expression(left)?.to_i32()? as u32;
    let right = signed_constant_expression(right)?.to_i32()? as u32;
    let left = crate::kernel::Bitvector32Term::Constant(left);
    let right = crate::kernel::Bitvector32Term::Constant(right);
    let condition = match operator {
        ComparisonOperator::LessEqual => crate::kernel::ConditionTerm::Bitvector32SignedLessEqual(
            Box::new(left),
            Box::new(right),
        ),
        ComparisonOperator::LessThan => {
            crate::kernel::ConditionTerm::Bitvector32SignedLessThan(Box::new(left), Box::new(right))
        }
        ComparisonOperator::Equal => {
            crate::kernel::ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right))
        }
        ComparisonOperator::NotEqual => {
            crate::kernel::ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right))
        }
        ComparisonOperator::GreaterThan
        | ComparisonOperator::GreaterEqual
        | ComparisonOperator::In => return None,
    };
    let value = !matches!(operator, ComparisonOperator::NotEqual);
    Some(crate::kernel::Proposition::ConditionIs(condition, value))
}

fn signed_step_result_surface(step: &SignedArithmeticStep) -> Option<&ClickProposition> {
    match step {
        SignedArithmeticStep::Premise { result, .. }
        | SignedArithmeticStep::AffinePremise { result, .. }
        | SignedArithmeticStep::Scale { result, .. }
        | SignedArithmeticStep::Add { result, .. }
        | SignedArithmeticStep::EqualityToLessEqual { result, .. }
        | SignedArithmeticStep::EqualityFromBounds { result, .. }
        | SignedArithmeticStep::StrictFromDisequal { result, .. }
        | SignedArithmeticStep::Trivial { result }
        | SignedArithmeticStep::Int32Range { result }
        | SignedArithmeticStep::IntervalCompare { result, .. }
        | SignedArithmeticStep::AffineConclusion { result, .. } => Some(result),
        _ => None,
    }
}

fn is_positive_predecessor_goal(proposition: &crate::kernel::Proposition) -> bool {
    let crate::kernel::Proposition::ConditionIs(
        crate::kernel::ConditionTerm::Bitvector32SignedLessThan(left, right),
        true,
    ) = proposition
    else {
        return false;
    };
    let crate::kernel::Bitvector32Term::Subtract(value, amount) = left.as_ref() else {
        return false;
    };
    signed_atom_matches(value, right)
        && matches!(amount.as_ref(), crate::kernel::Bitvector32Term::Constant(1))
}

fn signed_atom_matches(
    left: &crate::kernel::Bitvector32Term,
    right: &crate::kernel::Bitvector32Term,
) -> bool {
    let mut pending = vec![(left, right)];
    let mut visited = 0usize;
    while let Some((left, right)) = pending.pop() {
        visited += 1;
        if visited > 4096 {
            return false;
        }
        match (left, right) {
            (
                crate::kernel::Bitvector32Term::Constant(left),
                crate::kernel::Bitvector32Term::Constant(right),
            ) if left == right => {}
            (
                crate::kernel::Bitvector32Term::Int64Constant(left),
                crate::kernel::Bitvector32Term::Int64Constant(right),
            ) if left == right => {}
            (
                crate::kernel::Bitvector32Term::UInt64Constant(left),
                crate::kernel::Bitvector32Term::UInt64Constant(right),
            ) if left == right => {}
            (
                crate::kernel::Bitvector32Term::Variable(left),
                crate::kernel::Bitvector32Term::Variable(right),
            ) if left == right => {}
            (left, right)
                if let (Some(left), Some(right)) = (
                    crate::kernel::proof::signed_arithmetic::SignedArithmeticAtom::from_term(left),
                    crate::kernel::proof::signed_arithmetic::SignedArithmeticAtom::from_term(right),
                ) =>
            {
                if left != right {
                    return false;
                }
            }
            (
                crate::kernel::Bitvector32Term::Add(left, right),
                crate::kernel::Bitvector32Term::Add(other_left, other_right),
            )
            | (
                crate::kernel::Bitvector32Term::Subtract(left, right),
                crate::kernel::Bitvector32Term::Subtract(other_left, other_right),
            )
            | (
                crate::kernel::Bitvector32Term::Multiply(left, right),
                crate::kernel::Bitvector32Term::Multiply(other_left, other_right),
            )
            | (
                crate::kernel::Bitvector32Term::Remainder(left, right),
                crate::kernel::Bitvector32Term::Remainder(other_left, other_right),
            ) => {
                pending.push((left, other_left));
                pending.push((right, other_right));
            }
            _ => return false,
        }
    }
    true
}

fn signed_scaled_term_matches(
    target: &crate::kernel::Bitvector32Term,
    source: &crate::kernel::Bitvector32Term,
    coefficient: &num_bigint::BigInt,
) -> bool {
    if let (
        crate::kernel::Bitvector32Term::Constant(value),
        crate::kernel::Bitvector32Term::Constant(source_value),
        Some(coefficient),
    ) = (target, source, coefficient.to_i32())
        && (*source_value as i64).saturating_mul(i64::from(coefficient)) == i64::from(*value as i32)
    {
        return true;
    }
    let crate::kernel::Bitvector32Term::Multiply(left, right) = target else {
        return false;
    };
    let coefficient_i32 = coefficient.to_i32();
    match (left.as_ref(), right.as_ref(), coefficient_i32) {
        (crate::kernel::Bitvector32Term::Constant(value), term, Some(expected))
            if *value as i32 == expected =>
        {
            signed_atom_matches(term, source)
        }
        (term, crate::kernel::Bitvector32Term::Constant(value), Some(expected))
            if *value as i32 == expected =>
        {
            signed_atom_matches(term, source)
        }
        (crate::kernel::Bitvector32Term::Constant(value), _, Some(expected))
            if matches!(
                source,
                crate::kernel::Bitvector32Term::Constant(source_value)
                    if (*source_value as i64).saturating_mul(i64::from(expected))
                        == i64::from(*value as i32)
            ) =>
        {
            true
        }
        _ => false,
    }
}

fn signed_scaled_surface_shape(
    source: &crate::kernel::Proposition,
    target: &crate::kernel::Proposition,
    coefficient: &num_bigint::BigInt,
) -> bool {
    let (source_condition, source_value, target_condition, target_value) = match (source, target) {
        (
            crate::kernel::Proposition::ConditionIs(source_condition, source_value),
            crate::kernel::Proposition::ConditionIs(target_condition, target_value),
        ) => (
            source_condition,
            source_value,
            target_condition,
            target_value,
        ),
        _ => return false,
    };
    if source_value != target_value {
        return false;
    }
    let (source_left, source_right, target_left, target_right) =
        match (source_condition, target_condition) {
            (
                crate::kernel::ConditionTerm::Bitvector32SignedLessThan(source_left, source_right),
                crate::kernel::ConditionTerm::Bitvector32SignedLessThan(target_left, target_right),
            )
            | (
                crate::kernel::ConditionTerm::Bitvector32SignedLessEqual(source_left, source_right),
                crate::kernel::ConditionTerm::Bitvector32SignedLessEqual(target_left, target_right),
            )
            | (
                crate::kernel::ConditionTerm::Bitvector32Equal(source_left, source_right),
                crate::kernel::ConditionTerm::Bitvector32Equal(target_left, target_right),
            ) => (source_left, source_right, target_left, target_right),
            _ => return false,
        };
    signed_scaled_term_matches(target_left, source_left, coefficient)
        && signed_scaled_term_matches(target_right, source_right, coefficient)
}

fn signed_add_surface_shape(
    left: &crate::kernel::Proposition,
    right: &crate::kernel::Proposition,
    target: &crate::kernel::Proposition,
) -> bool {
    let Some((left_left, left_right, left_strict)) = signed_ordered_surface_parts(left) else {
        return false;
    };
    let Some((right_left, right_right, right_strict)) = signed_ordered_surface_parts(right) else {
        return false;
    };
    let Some((target_left, target_right, target_strict)) = signed_ordered_surface_parts(target)
    else {
        return false;
    };
    if target_strict != (left_strict || right_strict) {
        return false;
    }
    let matches_sum = |target: &crate::kernel::Bitvector32Term,
                       first: &crate::kernel::Bitvector32Term,
                       second: &crate::kernel::Bitvector32Term| {
        if signed_term_constant_value(second) == Some(0) && signed_atom_matches(target, first) {
            return true;
        }
        // A zero on either side folds away in lowering: `(0 + u)` is read as
        // `u`, so the sum of `0 <= u` and `u <= v` never reaches the `Add`
        // arm below and a plain transitivity was refused as not encoding
        // its child sum.
        if signed_term_constant_value(first) == Some(0) && signed_atom_matches(target, second) {
            return true;
        }
        if let crate::kernel::Bitvector32Term::Add(target_first, target_second) = target {
            return signed_atom_matches(target_first, first)
                && (signed_atom_matches(target_second, second)
                    || matches!(
                        (
                            signed_term_constant_value(target_second),
                            signed_term_constant_value(second)
                        ),
                        (Some(left), Some(right)) if left == right
                    ));
        }
        if let crate::kernel::Bitvector32Term::Subtract(target_first, target_second) = target {
            return signed_atom_matches(target_first, first)
                && matches!(
                    (
                        signed_term_constant_value(target_second),
                        signed_term_constant_value(second)
                    ),
                    (Some(left), Some(right)) if left.saturating_neg() == right
                );
        }
        if let (Some(target), Some(first), Some(second)) = (
            signed_term_constant_value(target),
            signed_term_constant_value(first),
            signed_term_constant_value(second),
        ) {
            return first.saturating_add(second) == target;
        }
        false
    };
    let left_matches = matches_sum(target_left, left_left, right_left);
    let right_matches = matches_sum(target_right, left_right, right_right);
    left_matches && right_matches
}

fn signed_ordered_surface_parts(
    proposition: &crate::kernel::Proposition,
) -> Option<(
    &crate::kernel::Bitvector32Term,
    &crate::kernel::Bitvector32Term,
    bool,
)> {
    let crate::kernel::Proposition::ConditionIs(condition, value) = proposition else {
        return None;
    };
    // A premise written `i >= 0` is the same ordered pair as `0 <= i`; the
    // planner adds them alike, so the printed sum is read alike.
    let (left, right, strict) = match condition {
        crate::kernel::ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
            (left.as_ref(), right.as_ref(), false)
        }
        crate::kernel::ConditionTerm::Bitvector32SignedLessThan(left, right) => {
            (left.as_ref(), right.as_ref(), true)
        }
        crate::kernel::ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
            (right.as_ref(), left.as_ref(), false)
        }
        crate::kernel::ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
            (right.as_ref(), left.as_ref(), true)
        }
        _ => return None,
    };
    (*value).then_some((left, right, strict))
}

fn signed_term_constant_value(term: &crate::kernel::Bitvector32Term) -> Option<i64> {
    enum Task<'a> {
        Visit(&'a crate::kernel::Bitvector32Term),
        Combine(bool),
    }
    let mut pending = vec![Task::Visit(term)];
    let mut values = Vec::new();
    while let Some(task) = pending.pop() {
        match task {
            Task::Visit(term) => match term {
                crate::kernel::Bitvector32Term::Constant(value) => {
                    values.push(Some(*value as i32 as i64));
                }
                crate::kernel::Bitvector32Term::Add(left, right) => {
                    pending.push(Task::Combine(true));
                    pending.push(Task::Visit(right));
                    pending.push(Task::Visit(left));
                }
                crate::kernel::Bitvector32Term::Subtract(left, right) => {
                    if signed_atom_matches(left, right) {
                        values.push(Some(0));
                    } else {
                        pending.push(Task::Combine(false));
                        pending.push(Task::Visit(right));
                        pending.push(Task::Visit(left));
                    }
                }
                _ => values.push(None),
            },
            Task::Combine(add) => {
                let right = values.pop()??;
                let left = values.pop()??;
                values.push(if add {
                    left.checked_add(right)
                } else {
                    left.checked_sub(right)
                });
            }
        }
    }
    values.pop().flatten()
}
/// What a failing bare `arithmetic()` says in place of "the listed premises":
/// it listed none, and it never reads the context for them.
const BARE_ARITHMETIC_HINT: &str = "`arithmetic()` without `using` reads no facts from the context, so list the facts the goal depends on with `using { ... }`";

/// How `arithmetic` read each listed premise while planning over the Integer
/// linear fragment, written in the reader's own spelling.
///
/// A premise outside the fragment is skipped rather than refused, so a reader
/// whose evidence never entered the planner has to be told which premises did.
/// The two lists are the whole story: no ambient fact participates.
fn describe_integer_premise_reading(
    premises: &[crate::kernel::Proposition],
    surface_premises: &[ClickProposition],
) -> String {
    use crate::kernel::proof::integer_arithmetic::integer_affine_claim;
    let spelled = |index: usize| match surface_premises.get(index) {
        Some(premise) => format!(
            "{index}: `{}`",
            crate::surface::printing::source_click_proposition(premise)
        ),
        None => format!("{index}"),
    };
    let (read, skipped): (Vec<_>, Vec<_>) =
        (0..premises.len()).partition(|index| integer_affine_claim(&premises[*index]).is_some());
    let mut description = String::new();
    if read.is_empty() {
        description.push_str(
            "\n  no listed premise was read as an Integer linear claim, so nothing was combined",
        );
    } else {
        description.push_str(&format!(
            "\n  read as Integer linear claims: {}",
            read.iter()
                .copied()
                .map(spelled)
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }
    if !skipped.is_empty() {
        description.push_str(&format!(
            "\n  skipped, not an Integer linear claim: {}",
            skipped
                .iter()
                .copied()
                .map(spelled)
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }
    description
}

/// Classify the failure of the bounded arithmetic planner without reviving a
/// whole-goal checker.  The planner intentionally returns only `None`; this
/// small, iterative shape scan keeps the established diagnostics useful for
/// unsupported nonlinear products and for goals whose machine operations lack
/// enough definedness evidence.
fn signed_goal_shape_flags(goal: &crate::kernel::Proposition) -> Option<(bool, bool)> {
    let (condition, value) = match goal {
        crate::kernel::Proposition::ConditionIs(condition, value) => (condition, *value),
        crate::kernel::Proposition::Not(body) => match body.as_ref() {
            crate::kernel::Proposition::ConditionIs(condition, value) => (condition, !*value),
            _ => return None,
        },
        _ => return None,
    };
    let (left, right) = match condition {
        crate::kernel::ConditionTerm::Bitvector32SignedLessThan(left, right)
        | crate::kernel::ConditionTerm::Bitvector32SignedLessEqual(left, right)
        | crate::kernel::ConditionTerm::Bitvector32SignedGreaterThan(left, right)
        | crate::kernel::ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
        | crate::kernel::ConditionTerm::Bitvector32Equal(left, right)
            if value =>
        {
            (left.as_ref(), right.as_ref())
        }
        crate::kernel::ConditionTerm::Bitvector32SignedLessThan(left, right)
        | crate::kernel::ConditionTerm::Bitvector32SignedLessEqual(left, right)
        | crate::kernel::ConditionTerm::Bitvector32SignedGreaterThan(left, right)
        | crate::kernel::ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
        | crate::kernel::ConditionTerm::Bitvector32Equal(left, right) => {
            (left.as_ref(), right.as_ref())
        }
        _ => return None,
    };
    let mut machine_operation = false;
    let mut nonlinear = false;
    let mut pending = vec![left, right];
    while let Some(term) = pending.pop() {
        match term {
            crate::kernel::Bitvector32Term::Add(left, right)
            | crate::kernel::Bitvector32Term::Subtract(left, right)
            | crate::kernel::Bitvector32Term::Multiply(left, right)
            | crate::kernel::Bitvector32Term::Divide(left, right)
            | crate::kernel::Bitvector32Term::Remainder(left, right)
            | crate::kernel::Bitvector32Term::ShiftLeft(left, right)
            | crate::kernel::Bitvector32Term::ArithmeticShiftRight(left, right)
            | crate::kernel::Bitvector32Term::LogicalShiftRight(left, right)
            | crate::kernel::Bitvector32Term::BitwiseAnd(left, right)
            | crate::kernel::Bitvector32Term::BitwiseOr(left, right)
            | crate::kernel::Bitvector32Term::BitwiseXor(left, right) => {
                machine_operation = true;
                if matches!(term, crate::kernel::Bitvector32Term::Multiply(_, _))
                    && signed_term_constant_value(left).is_none()
                    && signed_term_constant_value(right).is_none()
                {
                    nonlinear = true;
                }
                pending.push(left);
                pending.push(right);
            }
            crate::kernel::Bitvector32Term::BitwiseNot(inner) => {
                machine_operation = true;
                pending.push(inner);
            }
            crate::kernel::Bitvector32Term::PureFunctionApplication { arguments, .. } => {
                pending.extend(arguments.iter());
            }
            _ => {}
        }
    }
    Some((nonlinear, machine_operation))
}

/// Unsigned order is lowered to signed order by xoring an int32 value with
/// the sign bit.  That xor is total; when the planner cannot prove the
/// resulting bound, the useful failure is missing premises rather than an
/// overflow/definedness failure for a machine operation.
fn signed_goal_is_unsigned_signbit_bound(goal: &crate::kernel::Proposition) -> bool {
    let crate::kernel::Proposition::ConditionIs(condition, true) = goal else {
        return false;
    };
    let (left, right) = match condition {
        crate::kernel::ConditionTerm::Bitvector32SignedLessThan(left, right)
        | crate::kernel::ConditionTerm::Bitvector32SignedLessEqual(left, right)
        | crate::kernel::ConditionTerm::Bitvector32SignedGreaterThan(left, right)
        | crate::kernel::ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
            (left.as_ref(), right.as_ref())
        }
        _ => return false,
    };
    let is_signbit_xor = |term: &crate::kernel::Bitvector32Term| {
        let crate::kernel::Bitvector32Term::BitwiseXor(first, second) = term else {
            return false;
        };
        matches!(
            (first.as_ref(), second.as_ref()),
            (
                crate::kernel::Bitvector32Term::Constant(value),
                crate::kernel::Bitvector32Term::Variable(_)
            )
            | (
                crate::kernel::Bitvector32Term::Variable(_),
                crate::kernel::Bitvector32Term::Constant(value)
            ) if *value == 0x8000_0000
        )
    };
    is_signbit_xor(left) || is_signbit_xor(right)
}

fn signed_interval(
    interval: SignedInt32Interval,
) -> crate::kernel::proof::signed_arithmetic::SignedArithmeticInterval {
    crate::kernel::proof::signed_arithmetic::SignedArithmeticInterval {
        carrier: crate::kernel::proof::signed_arithmetic::SignedArithmeticCarrier::SignedInt32,
        lower: interval.lower,
        upper: interval.upper,
    }
}

fn signed_comparison(
    comparison: SignedInt32Comparison,
) -> crate::kernel::proof::signed_arithmetic::SignedArithmeticComparison {
    match comparison {
        SignedInt32Comparison::LessThan => {
            crate::kernel::proof::signed_arithmetic::SignedArithmeticComparison::LessThan
        }
        SignedInt32Comparison::LessEqual => {
            crate::kernel::proof::signed_arithmetic::SignedArithmeticComparison::LessEqual
        }
        SignedInt32Comparison::Equal => {
            crate::kernel::proof::signed_arithmetic::SignedArithmeticComparison::Equal
        }
        SignedInt32Comparison::Disequal => {
            crate::kernel::proof::signed_arithmetic::SignedArithmeticComparison::Disequal
        }
    }
}

impl<'a> Proof<'a> {
    /// Checks one explicit proof step and atomically returns the checked
    /// successor with that exact step retained as provenance.
    ///
    /// Failure allocates no reachable successor: `self` and all of its other
    /// descendants continue to share the unchanged ancestor state.
    pub(in crate::surface::proof) fn apply_step(
        &self,
        step: ProofStep,
    ) -> Result<Self, ClickError> {
        self.apply_step_with_origin(step, None)
    }

    /// Applies a step while retaining its source occurrence for any ordered
    /// terminal work the checked transition has to schedule. The source site
    /// affects diagnostics and finalization order only; the certificate node
    /// remains exactly the supplied `ProofStep`.
    pub(super) fn apply_step_with_origin(
        &self,
        step: ProofStep,
        origin: Option<ProofStepOrigin>,
    ) -> Result<Self, ClickError> {
        if let Some(execution) = self.execution() {
            execution
                .core
                .state
                .resources()
                .synchronize_memory_equalities(self.facts().assumptions());
        }
        let tactic = proof_step_source_name(&step);
        let call_source = crate::surface::proof_trace::enabled_for(self.claim_label())
            .then(|| self.trace_call_source(&step))
            .flatten();
        let result = self
            .apply_step_with_origin_inner(step, origin)
            .map_err(|error| {
                self.attach_step_diagnostic(error)
                    .with_failed_tactic(tactic)
            });
        if let Ok(next) = &result
            && let Some(execution) = next.execution()
        {
            execution
                .core
                .state
                .resources()
                .synchronize_memory_equalities(next.facts().assumptions());
        }
        if let Ok(next) = &result
            && crate::surface::proof_trace::enabled_for(self.claim_label())
            && !Arc::ptr_eq(&self.node, &next.node)
        {
            self.record_checked_trace_step(next, tactic, call_source);
        }
        result
    }

    /// Retain the call spelling for a checked call in the proof trace.
    fn trace_call_source(
        &self,
        step: &ProofStep,
    ) -> Option<crate::surface::proof_trace::TraceCallSource> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return None;
        };
        let call = match step {
            ProofStep::StepCall(transport) => transport.to_string(),
            ProofStep::StepContract(application) => format!("step({})", application.name),
            ProofStep::Step => {
                let execution = self.execution()?;
                let (_, _, statement, _) = next_top_level_statement_from_frontier_position(
                    execution.view(context),
                    &execution.core.state,
                    context.function,
                    context.arguments,
                    context.claim_label,
                    context.tactic_index,
                    "step",
                )
                .ok()?;
                let callee = match statement {
                    CStatement::CallAssign { function_name, .. }
                    | CStatement::Call { function_name, .. } => function_name,
                    _ => return None,
                };
                format!("step({callee}(...))")
            }
            _ => return None,
        };
        Some(crate::surface::proof_trace::TraceCallSource { call })
    }

    /// Read only the changed fact/resource keys, and only under an explicit
    /// trace request. The checked successor and its certificate are untouched.
    fn record_checked_trace_step(
        &self,
        next: &Self,
        tactic: &str,
        call_source: Option<crate::surface::proof_trace::TraceCallSource>,
    ) {
        let location = self
            .site()
            .path()
            .unwrap_or_else(|| format!("checked step {}", next.node.depth));
        let mut detail = crate::surface::proof_trace::TraceStep {
            header: format!(
                "\n    {location}: {}",
                call_source
                    .as_ref()
                    .map_or(tactic, |call| call.call.as_str())
            ),
            source_tactic_path: self.site().source_tactic_path(),
            call_source,
            facts: Vec::new(),
            more_facts: 0,
            frontier: None,
            resources: Vec::new(),
            more_resources: 0,
        };
        let added = self
            .focused_branch()
            .zip(next.focused_branch())
            .and_then(|(before, after)| after.state.facts.introduced_since(&before.state.facts));
        let added = added
            .as_deref()
            .unwrap_or_else(|| next.state().added_facts());
        let visible = added
            .iter()
            .filter(|fact| crate::surface::proof_trace::visible_checked_fact(fact));
        for fact in visible.clone().take(8) {
            detail.facts.push(next.checked_trace_fact(fact.clone()));
        }
        detail.more_facts = visible.count().saturating_sub(8);
        if let (Some(before), Some(after)) = (self.branch_execution(), next.branch_execution()) {
            let before_frontier = &before.core.frontier;
            let after_frontier = &after.core.frontier;
            let before_position = trace_frontier(before_frontier);
            let after_position = trace_frontier(after_frontier);
            if before_position != after_position && detail.call_source.is_none() {
                detail.frontier = Some(
                    match self.context.as_ref() {
                        ProofContext::Execution(context) => {
                            next_top_level_statement_from_frontier_position(
                                before.view(context),
                                &before.core.state,
                                context.function,
                                context.arguments,
                                context.claim_label,
                                context.tactic_index,
                                "step",
                            )
                            .ok()
                            .map(|(_, _, statement, _)| {
                                format!("steps through: {}", trace_statement_head(&statement))
                            })
                        }
                        _ => None,
                    }
                    .unwrap_or_else(|| {
                        format!("C frontier: {before_position} -> {after_position}")
                    }),
                );
            }
            let before = before.core.reached_state().resources();
            let after = after.core.reached_state().resources();
            if let Some(changed) = after.changed_facts_since(before) {
                for fact in changed.iter().take(8) {
                    let old = before.exact_count(fact);
                    let new = after.exact_count(fact);
                    if old != new {
                        let description = match self.context.as_ref() {
                            ProofContext::Execution(context) => trace_resource_fact(fact, context),
                            _ => {
                                crate::surface::diagnostics::describe_resource_fact(fact, &[], &[])
                            }
                        };
                        detail
                            .resources
                            .push(crate::surface::proof_trace::TraceResourceChange {
                                before: old,
                                after: new,
                                description,
                            });
                    }
                }
                if changed.len() > 8 {
                    detail.more_resources = changed.len() - 8;
                }
            }
        }
        crate::surface::proof_trace::record(Arc::as_ptr(&next.node) as usize, detail);
    }

    fn apply_step_with_origin_inner(
        &self,
        step: ProofStep,
        origin: Option<ProofStepOrigin>,
    ) -> Result<Self, ClickError> {
        #[cfg(test)]
        CHECKED_HAVE_OPERATIONS.with(|count| count.set(count.get() + 1));
        // Diagnostics from this step, and from every scope it opens, name the
        // source occurrence the driver is checking rather than a tree depth.
        // A generated tactic has no source occurrence (`usize::MAX`) and is
        // addressed by nothing, so there is no site to move to for it.
        if let Some(origin) = origin
            && origin.source_index != usize::MAX
            && !self.site().addresses_source_tactic(origin.source_index)
        {
            return self
                .at_source_tactic(origin.source_index)
                .apply_step_with_origin(step, Some(origin));
        }
        if self.focused_discharged() {
            return Err(self.step_error(format!(
                "the goal was already proved by the previous step, so this `{}` has nothing left to prove; you can delete this line",
                proof_step_source_name(&step)
            )));
        }

        // A witness for several binders instantiates them in the order
        // written and is recorded as the one step that was written.
        if let ProofStep::Witness(witness) = &step
            && !witness.is_single()
        {
            let mut current = self.clone();
            for single in witness.singles() {
                current = current.apply_step_with_origin_inner(ProofStep::Witness(single), None)?;
            }
            return Ok(Self {
                site: self.site.clone(),
                context: self.context.clone(),
                state: current.state.clone(),
                node: Arc::new(ProofNode {
                    path_memo: Default::default(),
                    parent: Some(self.node.clone()),
                    step: Some(Arc::new(step)),
                    focused_branch: current.focused_branch_id(),
                    depth: self.node.depth + 1,
                    split_branches: Vec::new(),
                }),
            });
        }
        if let ProofStep::CloseInvariantsBy(body) = &step {
            return self.apply_close_invariants_body(&body.to_proof_tactics());
        }
        if let ProofStep::Have { proposition, proof } = &step {
            return self.apply_have_step(proposition, proof);
        }
        // An unsigned order is the signed order of sign-flipped operands,
        // which the arithmetic certificates treat as opaque atoms. A goal
        // one uint32 lemma away from a listed premise is closed by that
        // lemma, recorded as the `apply` steps it is.
        if let ProofStep::ArithmeticUsing(premises) = &step
            && let Some(proof) = self.try_unsigned_order_lemma_using(premises)
        {
            return Ok(proof);
        }
        // A 64-bit order or equality is proved through its Integer
        // observations, by the bridge steps a proof would write.
        if let ProofStep::ArithmeticUsing(premises) = &step {
            match self.try_wide_arithmetic_using(premises) {
                Ok(proof) => return Ok(proof),
                Err(Some(reason)) => {
                    return Err(self.step_error(format!(
                        "`arithmetic` read the current goal as a 64-bit comparison: {reason}"
                    )));
                }
                Err(None) => {}
            }
        }
        if matches!(
            &step,
            ProofStep::Step
                | ProofStep::StepBind(_)
                | ProofStep::StepContract(_)
                | ProofStep::StepCall(_)
        ) {
            return self.apply_execution_statement_step(step);
        }
        if matches!(&step, ProofStep::UserTactic(_)) {
            return self.apply_execution_user_tactic(step);
        }

        let mut provenance_step = step.clone();
        let checked_proposition_successor = match &step {
            ProofStep::Assumption => Some(self.apply_assumption()),
            ProofStep::Normalize => Some(self.apply_normalize()),
            ProofStep::NormalizeUsing(premises) => Some(self.apply_normalize_using(premises)),
            ProofStep::ArithmeticUsing(premises) => {
                Some(self.apply_arithmetic_using_with_certificate(premises).map(
                    |(handle, certificate)| {
                        if let Some(certificate) = certificate {
                            provenance_step = ProofStep::ArithmeticCertificate(certificate);
                        }
                        handle
                    },
                ))
            }
            ProofStep::ArithmeticCertificate(certificate) => {
                Some(self.apply_arithmetic_certificate(certificate))
            }
            ProofStep::Intro => Some(self.apply_intro(None)),
            ProofStep::IntroAs(name) => Some(self.apply_intro(Some(name))),
            ProofStep::Enumerate => Some(self.apply_enumerate()),
            ProofStep::Contradiction(surface) => Some(self.apply_contradiction(surface)),
            ProofStep::Extract(proposition) => Some(self.apply_extract(proposition)),
            ProofStep::InstantiateUsing {
                quantified,
                argument,
                premises,
            } => Some(self.apply_fixed_state_instantiate_using(
                quantified,
                argument,
                premises.as_deref(),
            )),
            ProofStep::Mark(name) => Some(self.apply_execution_mark(name)),
            _ => None,
        };
        if let Some(successor) = checked_proposition_successor {
            let successor = successor?;
            let successor = if matches!(step, ProofStep::InstantiateUsing { .. }) {
                close_goal_from_added_fact(successor)
            } else {
                successor
            };
            return Ok(Self {
                site: self.site.clone(),
                context: self.context.clone(),
                state: successor,
                node: Arc::new(ProofNode {
                    path_memo: Default::default(),
                    parent: Some(self.node.clone()),
                    step: Some(Arc::new(provenance_step)),
                    focused_branch: self.focused_branch_id(),
                    depth: self.node.depth + 1,
                    split_branches: Vec::new(),
                }),
            });
        }

        let mut transition = match &step {
            ProofStep::Induct {
                parameter,
                hypothesis,
            } => self.apply_induct(parameter, hypothesis),
            ProofStep::ApplyInduction {
                hypothesis,
                arguments,
                premises,
            } => self.apply_induction(hypothesis, arguments, premises),
            ProofStep::ApplyTheoremUsing {
                application,
                premises,
            } => self.apply_theorem_using(application, premises),
            ProofStep::TransportUsing {
                source,
                target,
                premises,
            } => self.apply_transport_using(source, target, premises),
            ProofStep::UnfoldPredicate(name) => self.apply_predicate_unfold(name),
            ProofStep::UnfoldFunction(application) => self.apply_function_unfold(application, None),
            ProofStep::PeelFunction {
                application,
                premises,
            } => self.apply_function_unfold(application, Some(premises)),
            ProofStep::UnfoldResource(resource) => {
                // Resolve proof bindings before either the execution or
                // outcome path interprets ordinary resource arguments.
                let resource = &self.resolve_proof_resource_arguments(resource)?;
                if self.focused_outcome_data().is_some() {
                    self.apply_outcome_resource_unfold(resource)
                } else {
                    self.apply_execution_resource_unfold(resource)
                }
            }
            ProofStep::FoldResource(resource) => {
                // Resolve proof bindings before either the execution or
                // outcome path interprets ordinary resource arguments.
                let source_resource = resource;
                let resource = &self.resolve_proof_resource_arguments(resource)?;
                if self.focused_outcome_data().is_some() {
                    self.apply_outcome_resource_fold(resource)
                } else {
                    self.apply_execution_resource_fold(resource, source_resource)
                }
            }
            ProofStep::ConstructResource(resource) => {
                if self.focused_outcome_data().is_some() {
                    self.apply_outcome_resource_construction(resource)
                } else {
                    Err(self.step_error("resource `construct` requires a function-outcome proof"))
                }
            }
            ProofStep::ObserveResource(resource) => {
                self.apply_execution_resource_observation(resource)
            }
            ProofStep::Iterated(tactic) => self.apply_execution_iterated_step(tactic),
            ProofStep::Choose(choice) => self.apply_fixed_state_choose(choice),
            ProofStep::LetSatisfy(binding) => self.apply_let_satisfy(binding),
            ProofStep::Witness(witness) => self.apply_fixed_state_witness(witness),
            ProofStep::Rewrite(equality) => self.apply_rewrite(equality),
            _ => {
                Err(self
                    .step_error("this proof step has not yet migrated to the checked `Proof` API"))
            }
        }?;

        // A rewrite or transport changes the cited proposition's snapshot
        // context. Do not let a source-epoch projection survive that
        // boundary and accidentally make a later citation look current.
        if matches!(
            step,
            ProofStep::Rewrite(_) | ProofStep::TransportUsing { .. }
        ) {
            transition.clear_chosen_projection();
        }

        let state = self.publish_checked_transition(transition)?;
        let state = if matches!(
            step,
            ProofStep::ApplyTheoremUsing { .. }
                | ProofStep::TransportUsing { .. }
                | ProofStep::LetSatisfy(_)
        ) {
            close_goal_from_added_fact(state)
        } else {
            state
        };
        Ok(Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: Arc::new(ProofNode {
                path_memo: Default::default(),
                parent: Some(self.node.clone()),
                step: Some(Arc::new(step)),
                focused_branch: self.focused_branch_id(),
                depth: self.node.depth + 1,
                split_branches: Vec::new(),
            }),
        })
    }

    /// Applies one explicit `Have` through the same owned scope operations as
    /// a source `have` block. Each body step advances the scope's persistent
    /// child `Proof`; joining publishes only the checked proposition and
    /// retains the body's exact surface operations as provenance. A failed
    /// body leaves this immutable root untouched.
    pub(super) fn apply_have_step(
        &self,
        proposition: &ClickProposition,
        proof: &ProofCertificate,
    ) -> Result<Self, ClickError> {
        let mut scope = self.begin_have(proposition.clone())?;
        for step in proof.steps() {
            scope = scope.apply_step(step.clone())?;
        }
        scope.join()
    }

    pub(in crate::surface::proof) fn apply_step_at(
        &self,
        step: ProofStep,
        source_index: usize,
    ) -> Result<Self, ClickError> {
        self.apply_step_with_origin(step, Some(ProofStepOrigin { source_index }))
    }

    /// Searches for a terminal frame candidate and submits the selected
    /// Surface-operation plan directly to this Proof. Successful search returns
    /// the already-checked descendant; it does not export outcomes or check
    /// the candidate through a second semantic representation.
    pub(super) fn apply_assumption(&self) -> Result<KernelProofHandle, ClickError> {
        let context = match self.context.as_ref() {
            ProofContext::FixedState(_) => PropositionAssumptionContext::Pure,
            ProofContext::Execution(_) => PropositionAssumptionContext::Materialized,
            ProofContext::Pure(_) => PropositionAssumptionContext::Exact,
        };
        self.state
            .apply_assumption(context)
            .map_err(|error| match error {
                PropositionCloseError::NotProposition => {
                    self.step_error("`assumption` requires a proposition goal")
                }
                PropositionCloseError::Unavailable => {
                    let detail = self
                        .goal()
                        .map(|goal| format!(": current goal is {}", describe_assumption_goal(goal)))
                        .unwrap_or_default();
                    self.step_error(format!(
                        "`assumption` requires the current goal as an available semantic fact{detail}"
                    ))
                }
                PropositionCloseError::UnavailableSide(side) => {
                    let (names, values) = self.diagnostic_naming_tables();
                    self.step_error(format!(
                        "`assumption` closes a conjunction when every side is an available fact and a disjunction when one side is; `{}` is not available",
                        crate::surface::diagnostics::describe_pure_fact_spelled(
                            &side, &names, &values
                        )
                    ))
                }
                _ => unreachable!("kernel returned an unrelated assumption error"),
            })
    }

    // Preserve the rule/dispatcher frame boundary described above.
    #[inline(never)]
    pub(super) fn apply_normalize(&self) -> Result<KernelProofHandle, ClickError> {
        self.state.apply_normalize().map_err(|error| match error {
            PropositionCloseError::NotProposition => {
                self.step_error("`normalize` requires a proposition goal")
            }
            PropositionCloseError::DoesNotNormalize => {
                self.step_error("`normalize` goal did not normalize to true")
            }
            _ => unreachable!("kernel returned an unrelated normalize error"),
        })
    }

    #[inline(never)]
    pub(super) fn apply_normalize_using(
        &self,
        surface_premises: &[ClickProposition],
    ) -> Result<KernelProofHandle, ClickError> {
        use crate::kernel::proof::fact_reasoning::ConditionalNormalizationError;
        let premises = surface_premises
            .iter()
            .map(|premise| {
                self.lower_cited_surface_proposition(premise, "`normalize using` premise")
            })
            .collect::<Result<Vec<_>, _>>()?;
        self.state
            .apply_normalize_using(&premises)
            .map_err(|error| match error {
                PropositionCloseError::NotProposition => {
                    self.step_error("`normalize` requires a proposition goal")
                }
                PropositionCloseError::ConditionalNormalization(
                    ConditionalNormalizationError::UnavailablePremise(index),
                ) => self.step_error(format!(
                    "`normalize using` premise {index} is not exactly available"
                )),
                PropositionCloseError::ConditionalNormalization(
                    ConditionalNormalizationError::UnsupportedPremise(index),
                ) => self.step_error(format!(
                    "`normalize using` premise {index} must be a consistent single condition"
                )),
                PropositionCloseError::ConditionalNormalization(
                    ConditionalNormalizationError::DoesNotNormalize,
                ) => self.step_error(
                    "`normalize using` goal did not normalize to true using the listed conditions",
                ),
                _ => unreachable!("kernel returned an unrelated normalize-using error"),
            })
    }

    #[inline(never)]
    fn apply_arithmetic_using_with_certificate(
        &self,
        surface_premises: &[ClickProposition],
    ) -> Result<(KernelProofHandle, Option<ArithmeticCertificate>), ClickError> {
        // A ranking decrease compares the loop-head value with its checked
        // predecessor.  At the back edge the ordinary spelling of a loop
        // invariant re-lowers against the post-body state, whereas this
        // obligation's `n` is the retained iteration-entry value.  Preserve
        // that distinction in the certificate's source premises; the
        // snapshot annotation is checked by the normal direct lowering path.
        let anchored_surface_premises = if self.goal().is_some_and(is_positive_predecessor_goal)
            && let ProofContext::Execution(context) = self.context.as_ref()
            && let Some(bundle) = context.constants.invariant_body_context.as_deref()
            && let Some(selector) = bundle.iteration_entry_selector.as_ref()
        {
            surface_premises
                .iter()
                .map(|premise| {
                    surface_at_snapshot(premise, selector).unwrap_or_else(|_| premise.clone())
                })
                .collect::<Vec<_>>()
        } else {
            surface_premises.to_vec()
        };
        let premises = anchored_surface_premises
            .iter()
            .map(|premise| {
                self.lower_cited_surface_proposition(premise, "`arithmetic using` premise")
            })
            .collect::<Result<Vec<_>, _>>()?;
        for (index, premise) in premises.iter().enumerate() {
            if !self.facts().listed_premise_available(premise, &[], false) {
                return Err(self.step_error(format!(
                    "`arithmetic using` premise {index} is not exactly available"
                )));
            }
        }
        if let Some(goal) = self.goal()
            && let Some(plan) =
                crate::surface::checking::plan_special_arithmetic_certificate(goal, &premises)
            && let Some(surface_goal) = self.surface_goal()
        {
            let pairs = premises
                .iter()
                .cloned()
                .zip(anchored_surface_premises.iter().cloned())
                .collect::<Vec<_>>();
            let certificate = crate::surface::checking::special_plan_to_surface_certificate(
                &plan,
                &pairs.iter().map(|(_, p)| p.clone()).collect::<Vec<_>>(),
                surface_goal,
            );
            let handle = self.apply_special_certificate(match &certificate.family {
                ArithmeticCertificateFamily::Special(c) => c,
                _ => unreachable!(),
            });
            if let Ok(handle) = handle {
                return Ok((handle, Some(certificate)));
            }
        }
        if let Some(goal) = self.goal()
            && let Some(surface_goal) = self.surface_goal()
            && let Some(plan) =
                crate::surface::checking::plan_integer_affine_certificate(goal, &premises)
        {
            let pairs = premises
                .iter()
                .cloned()
                .zip(anchored_surface_premises.iter().cloned())
                .collect::<Vec<_>>();
            if let Some(certificate) =
                crate::surface::proof::smart_closures::integer_plan_to_surface_certificate(
                    &plan,
                    &pairs,
                    surface_goal,
                )
            {
                let handle = self.apply_integer_certificate(&certificate)?;
                return Ok((handle, Some(ArithmeticCertificate::integer(certificate))));
            }
        }
        if let Some(goal) = self.goal()
            && let Some(plan) =
                crate::surface::checking::plan_signed_arithmetic_certificate_with_weakening(
                    goal, &premises,
                )
        {
            let surface_goal = self.surface_goal().cloned().or_else(|| {
                let context = self.execution_context()?;
                let execution = self.execution()?;
                crate::surface::proof::surface_synthesis::synthesize_surface_proposition(
                    goal,
                    context.parsed_function.parameters(),
                    context.arguments,
                    &execution.core.state,
                )
            });
            if let Some(surface_goal) = surface_goal.as_ref() {
                let converted = self.signed_plan_to_surface_certificate(
                    &plan,
                    &premises
                        .iter()
                        .cloned()
                        .zip(anchored_surface_premises.iter().cloned())
                        .collect::<Vec<_>>(),
                    surface_goal,
                );
                if let Some(certificate) = converted {
                    let cited_premise = certificate.nodes.iter().find_map(|node| {
                        let SignedArithmeticStep::Premise { index, .. } = node else {
                            return None;
                        };
                        Some(*index)
                    });
                    let handle =
                        self.apply_signed_int32_certificate(&certificate)
                            .map_err(|error| {
                                if let Some(index) = cited_premise
                                    && error.message().contains("not exactly available")
                                {
                                    return self.step_error(format!(
                                    "`arithmetic using` premise {index} is not exactly available"
                                ));
                                }
                                error
                            })?;
                    return Ok((
                        handle,
                        Some(ArithmeticCertificate {
                            family: ArithmeticCertificateFamily::SignedInt32(certificate),
                        }),
                    ));
                }
                // The plan exists, so the premises were sufficient; what
                // failed is spelling one of its steps in source form. Say
                // so, rather than reporting the premises as insufficient.
                return Err(self.step_error(format!(
                    "`arithmetic` proved the goal from the listed premises with a {}-node signed_int32 certificate, but one of its steps cannot be printed in source form; this is a Click rendering gap, not a missing premise",
                    plan.nodes.len()
                )));
            }
        }
        // A goal in the mathematical `Integer` linear fragment never reaches
        // the signed int32 planner, so reporting that planner's precondition
        // for it names a fragment the goal is not in and sends the reader
        // hunting for an int32 mistake. Say which fragment was recognized and
        // how each listed premise was read inside it.
        if let Some(goal) = self.goal()
            && crate::kernel::proof::integer_arithmetic::integer_affine_claim(goal).is_some()
        {
            if let Some(plan) =
                crate::surface::checking::plan_integer_affine_certificate(goal, &premises)
            {
                return Err(self.step_error(format!(
                    "`arithmetic` proved the goal from the listed premises with a {}-node Integer certificate, but one of its steps cannot be printed in source form; this is a Click rendering gap, not a missing premise",
                    plan.nodes.len()
                )));
            }
            if premises.is_empty() {
                return Err(self.step_error(format!(
                    "`arithmetic` read the current goal as an Integer linear claim, which does not hold on its own; {BARE_ARITHMETIC_HINT}"
                )));
            }
            return Err(self.step_error(format!(
                "`arithmetic` read the current goal as an Integer linear claim; no combination of the listed premises proves it{}",
                describe_integer_premise_reading(&premises, &anchored_surface_premises)
            )));
        }
        if let Some(goal) = self.goal() {
            if crate::kernel::proof::signed_arithmetic::signed_arithmetic_claim(goal).is_none() {
                return Err(self.step_error(
                    "`arithmetic` requires a supported signed int32 comparison or equality goal",
                ));
            }
            if let Some((nonlinear, machine_operation)) = signed_goal_shape_flags(goal) {
                if nonlinear {
                    return Err(self.step_error(
                        "`arithmetic` requires a supported signed int32 comparison or equality goal",
                    ));
                }
                if machine_operation && !signed_goal_is_unsigned_signbit_bound(goal) {
                    if premises.is_empty() {
                        return Err(self.step_error(format!(
                            "`arithmetic` cannot establish that every int32 operation in the current goal is defined without overflow from the goal alone; {BARE_ARITHMETIC_HINT}"
                        )));
                    }
                    return Err(self.step_error(
                        "`arithmetic` cannot establish that every int32 operation in the current goal is defined without overflow from exactly the listed premises",
                    ));
                }
            }
            if premises.is_empty() {
                return Err(self.step_error(format!(
                    "current goal does not follow by arithmetic alone; {BARE_ARITHMETIC_HINT}"
                )));
            }
            if premises
                .iter()
                .all(crate::surface::checking::signed_arithmetic_premise_supported)
            {
                return Err(self.step_error(
                    "current goal does not follow from exactly the listed arithmetic premises (exactly the listed premises were insufficient)",
                ));
            }
        }
        if premises.is_empty() {
            return Err(self.step_error(format!(
                "`arithmetic` could not construct a checked arithmetic certificate from the goal alone; {BARE_ARITHMETIC_HINT}"
            )));
        }
        Err(self.step_error(
            "`arithmetic` could not construct a checked arithmetic certificate from exactly the listed premises",
        ))
    }

    pub(super) fn apply_arithmetic_certificate(
        &self,
        certificate: &ArithmeticCertificate,
    ) -> Result<KernelProofHandle, ClickError> {
        match &certificate.family {
            ArithmeticCertificateFamily::Integer(certificate) => {
                self.apply_integer_certificate(certificate)
            }
            ArithmeticCertificateFamily::SignedInt32(certificate) => {
                self.apply_signed_int32_certificate(certificate)
            }
            ArithmeticCertificateFamily::Special(certificate) => {
                self.apply_special_certificate(certificate)
            }
        }
    }

    fn apply_special_certificate(
        &self,
        certificate: &SpecialArithmeticCertificate,
    ) -> Result<KernelProofHandle, ClickError> {
        use crate::kernel::proof::arithmetic_special::{
            SpecialArithmeticCertificate as KernelCertificate, SpecialArithmeticCheckError,
            SpecialArithmeticNode as KernelNode,
        };
        let has_integer_nodes = certificate.nodes.iter().any(|node| {
            matches!(
                node,
                SpecialArithmeticNode::IntegerProductBounds { .. }
                    | SpecialArithmeticNode::IntegerDivisionBounds { .. }
                    | SpecialArithmeticNode::IntegerMultiplyOrder { .. }
                    | SpecialArithmeticNode::IntegerQuotientBound { .. }
                    | SpecialArithmeticNode::IntegerBoundExclusion { .. }
                    | SpecialArithmeticNode::IntegerRelationTransport { .. }
                    | SpecialArithmeticNode::IntegerPolynomialIdentity { .. }
                    | SpecialArithmeticNode::IntegerQuotientShift { .. }
                    | SpecialArithmeticNode::IntegerCastIdentity { .. }
            )
        });
        let mut premises = Vec::with_capacity(certificate.premises.len());
        for premise in &certificate.premises {
            let lowered = if has_integer_nodes {
                self.lower_integer_surface_proposition(
                    premise,
                    "`rules` arithmetic certificate premise",
                )?
            } else {
                self.lower_surface_proposition_direct(
                    premise,
                    "`rules` arithmetic certificate premise",
                )?
            };
            premises.push(lowered);
        }
        let lower_result = |result: &ClickProposition| {
            self.lower_surface_proposition_direct(result, "`rules` arithmetic certificate result")
        };
        let premise_ref = |index: usize| {
            if index < premises.len() {
                Ok(index)
            } else {
                Err(self.step_error(format!(
                    "`rules` arithmetic premise {index} is out of range"
                )))
            }
        };
        let mut nodes = Vec::with_capacity(certificate.nodes.len());
        for node in &certificate.nodes {
            let lowered = match node {
                SpecialArithmeticNode::IntegerCastIdentity { bounds, result } => {
                    KernelNode::IntegerCastIdentity {
                        bounds: bounds
                            .iter()
                            .map(|i| premise_ref(*i))
                            .collect::<Result<_, _>>()?,
                        result: self.lower_integer_surface_proposition(
                            result,
                            "integer cast identity result",
                        )?,
                    }
                }
                SpecialArithmeticNode::IntegerProductBounds { bounds, result } => {
                    KernelNode::IntegerProductBounds {
                        bounds: bounds
                            .iter()
                            .map(|i| premise_ref(*i))
                            .collect::<Result<_, _>>()?,
                        result: self.lower_integer_surface_proposition(
                            result,
                            "integer product bound result",
                        )?,
                    }
                }
                SpecialArithmeticNode::IntegerDivisionBounds { bounds, result } => {
                    KernelNode::IntegerDivisionBounds {
                        bounds: bounds
                            .iter()
                            .map(|i| premise_ref(*i))
                            .collect::<Result<_, _>>()?,
                        result: self.lower_integer_surface_proposition(
                            result,
                            "integer division bound result",
                        )?,
                    }
                }
                SpecialArithmeticNode::IntegerMultiplyOrder { bounds, result } => {
                    KernelNode::IntegerMultiplyOrder {
                        bounds: bounds
                            .iter()
                            .map(|i| premise_ref(*i))
                            .collect::<Result<_, _>>()?,
                        result: self.lower_integer_surface_proposition(
                            result,
                            "integer multiply order result",
                        )?,
                    }
                }
                SpecialArithmeticNode::IntegerQuotientBound { bounds, result } => {
                    KernelNode::IntegerQuotientBound {
                        bounds: bounds
                            .iter()
                            .map(|i| premise_ref(*i))
                            .collect::<Result<_, _>>()?,
                        result: self.lower_integer_surface_proposition(
                            result,
                            "integer quotient bound result",
                        )?,
                    }
                }
                SpecialArithmeticNode::IntegerBoundExclusion { bounds, result } => {
                    KernelNode::IntegerBoundExclusion {
                        bounds: bounds
                            .iter()
                            .map(|i| premise_ref(*i))
                            .collect::<Result<_, _>>()?,
                        result: self.lower_integer_surface_proposition(
                            result,
                            "integer bound exclusion result",
                        )?,
                    }
                }
                SpecialArithmeticNode::IntegerRelationTransport { bounds, result } => {
                    KernelNode::IntegerRelationTransport {
                        bounds: bounds
                            .iter()
                            .map(|i| premise_ref(*i))
                            .collect::<Result<_, _>>()?,
                        result: self.lower_integer_surface_proposition(
                            result,
                            "integer relation transport bound result",
                        )?,
                    }
                }
                SpecialArithmeticNode::IntegerPolynomialIdentity { bounds, result } => {
                    KernelNode::IntegerPolynomialIdentity {
                        bounds: bounds
                            .iter()
                            .map(|i| premise_ref(*i))
                            .collect::<Result<_, _>>()?,
                        result: self.lower_integer_surface_proposition(
                            result,
                            "integer polynomial identity result",
                        )?,
                    }
                }
                SpecialArithmeticNode::IntegerQuotientShift { bounds, result } => {
                    KernelNode::IntegerQuotientShift {
                        bounds: bounds
                            .iter()
                            .map(|i| premise_ref(*i))
                            .collect::<Result<_, _>>()?,
                        result: self.lower_integer_surface_proposition(
                            result,
                            "integer quotient shift result",
                        )?,
                    }
                }
                SpecialArithmeticNode::PointerTranslation {
                    relation,
                    bounds,
                    result,
                } => KernelNode::PointerTranslation {
                    relation: premise_ref(*relation)?,
                    bounds: bounds
                        .iter()
                        .map(|i| premise_ref(*i))
                        .collect::<Result<_, _>>()?,
                    result: lower_result(result)?,
                },
                SpecialArithmeticNode::PointerAlignment { premise, result } => {
                    KernelNode::PointerAlignment {
                        premise: premise.map(premise_ref).transpose()?,
                        result: lower_result(result)?,
                    }
                }
                SpecialArithmeticNode::PointerWordEquality {
                    relation,
                    alignments,
                    result,
                } => KernelNode::PointerWordEquality {
                    relation: premise_ref(*relation)?,
                    alignments: alignments
                        .iter()
                        .map(|i| premise_ref(*i))
                        .collect::<Result<_, _>>()?,
                    result: lower_result(result)?,
                },
                SpecialArithmeticNode::PointerWordFromAlignment { alignments, result } => {
                    KernelNode::PointerWordFromAlignment {
                        alignments: alignments
                            .iter()
                            .map(|i| premise_ref(*i))
                            .collect::<Result<_, _>>()?,
                        result: lower_result(result)?,
                    }
                }
                SpecialArithmeticNode::FloatReflexive { finite, result } => {
                    KernelNode::FloatReflexive {
                        finite: premise_ref(*finite)?,
                        result: lower_result(result)?,
                    }
                }
                SpecialArithmeticNode::UnsignedSumBound { bounds, result } => {
                    KernelNode::UnsignedSumBound {
                        bounds: bounds
                            .iter()
                            .map(|i| premise_ref(*i))
                            .collect::<Result<_, _>>()?,
                        result: lower_result(result)?,
                    }
                }
                SpecialArithmeticNode::SignedDefined {
                    width,
                    bounds,
                    result,
                } => KernelNode::SignedDefined {
                    width: *width,
                    bounds: bounds
                        .iter()
                        .map(|i| premise_ref(*i))
                        .collect::<Result<_, _>>()?,
                    result: lower_result(result)?,
                },
            };
            nodes.push(lowered);
        }
        if certificate.conclusion >= nodes.len() {
            return Err(self.step_error(format!(
                "`rules` arithmetic conclusion {} is out of range",
                certificate.conclusion
            )));
        }
        self.state
            .apply_special_arithmetic(
                &KernelCertificate {
                    nodes,
                    conclusion: certificate.conclusion,
                },
                &premises,
            )
            .map_err(|error| match error {
                PropositionCloseError::NotProposition => {
                    self.step_error("`rules` arithmetic certificate requires a proposition goal")
                }
                PropositionCloseError::SpecialArithmeticPremiseUnavailable(index) => self
                    .step_error(format!(
                        "`rules` arithmetic premise {index} is not exactly available: {}",
                        crate::surface::proof_diagnostics::render::render_proposition(
                            &premises[index]
                        )
                    )),
                PropositionCloseError::SpecialArithmetic(
                    SpecialArithmeticCheckError::SignedDefinedRangeExceeded {
                        width,
                        lower,
                        upper,
                        ..
                    },
                ) => {
                    let (minimum, maximum) = width.range();
                    let name = width.name();
                    self.step_error(format!(
                        "`{name}_defined` does not follow: the listed bounds and the operands' \
                         widths put the exact result in [{lower}, {upper}], which leaves {name} \
                         [{minimum}, {maximum}]; list a bound on each operand that keeps the \
                         result in range"
                    ))
                }
                PropositionCloseError::SpecialArithmetic(
                    SpecialArithmeticCheckError::SignedDefinedBoundUnrelated {
                        width, premise, ..
                    },
                ) => {
                    let name = width.name();
                    self.step_error(format!(
                        "`{name}_defined` premise {premise} is not a constant {name} order or \
                         equality fact on an operand of the claimed operation"
                    ))
                }
                PropositionCloseError::SpecialArithmetic(error) => self.step_error(format!(
                    "`rules` arithmetic certificate rejected: {}",
                    describe_special_arithmetic_check_error(&error)
                )),
                _ => self.step_error("`rules` arithmetic certificate could not be applied"),
            })
    }

    fn apply_signed_int32_certificate(
        &self,
        certificate: &SignedInt32Certificate,
    ) -> Result<KernelProofHandle, ClickError> {
        use crate::kernel::proof::signed_arithmetic::{
            SignedArithmeticAtom, SignedArithmeticCarrier,
            SignedArithmeticCertificate as KernelCertificate, SignedArithmeticNode,
            SignedArithmeticRelation, scale_claim, signed_arithmetic_claim,
            signed_arithmetic_source_matches,
        };
        let mut source_premises = std::collections::BTreeMap::new();
        let same_signed_claim =
            |left: &crate::kernel::Proposition, right: &crate::kernel::Proposition| {
                signed_arithmetic_source_matches(left, right)
            };
        for node in &certificate.nodes {
            let (index, lowered) = match node {
                SignedArithmeticStep::Premise {
                    index, proposition, ..
                } => (
                    *index,
                    self.lower_surface_proposition_direct(
                        proposition,
                        "signed_int32 certificate premise",
                    )?,
                ),
                SignedArithmeticStep::DefinedPremise { index, term } => (
                    *index,
                    self.lower_surface_proposition_direct(
                        &ClickProposition::Defined {
                            expression: term.clone(),
                        },
                        "signed_int32 definedness premise",
                    )?,
                ),
                _ => continue,
            };
            match source_premises.entry(index) {
                std::collections::btree_map::Entry::Vacant(entry) => {
                    entry.insert(lowered);
                }
                std::collections::btree_map::Entry::Occupied(_entry) => {
                    return Err(self.step_error(format!(
                        "signed_int32 premise {index} is declared more than once"
                    )));
                }
            }
        }
        let mut premises = Vec::with_capacity(source_premises.len());
        for index in 0..source_premises.len() {
            let Some(premise) = source_premises.remove(&index) else {
                return Err(self.step_error(format!(
                    "signed_int32 premise indices must be contiguous; missing {index}"
                )));
            };
            premises.push(premise);
        }
        let lower_term = |proof: &Self,
                          expression: &ContractExpression|
         -> Result<crate::kernel::Bitvector32Term, ClickError> {
            if let ContractExpression::IntegerLiteral(literal) = expression
                && let Ok(value) = literal.parse::<i64>()
                && (i32::MIN as i64..=i32::MAX as i64).contains(&value)
            {
                return Ok(crate::kernel::Bitvector32Term::Constant(
                    value as i32 as u32,
                ));
            }
            if let Some(value) =
                signed_constant_expression(expression).and_then(|value| value.to_i32())
            {
                return Ok(crate::kernel::Bitvector32Term::Constant(value as u32));
            }
            if let ContractExpression::CFragment(crate::kernel::CExpression::Value(
                crate::kernel::CValue::Int32(crate::kernel::Bitvector32Term::Constant(value)),
            )) = expression
            {
                return Ok(crate::kernel::Bitvector32Term::Constant(*value));
            }
            let zero = ContractExpression::IntegerLiteral("0".into());
            let surface = ClickProposition::Comparison {
                left: expression.clone(),
                operator: ComparisonOperator::Equal,
                right: zero,
            };
            let lowered = proof
                .lower_surface_proposition_direct(&surface, "signed_int32 certificate term")?;
            let Proposition::ConditionIs(condition, true) = &lowered else {
                return Err(proof
                    .step_error("signed_int32 certificate term did not lower to a proposition"));
            };
            let term = match condition {
                crate::kernel::ConditionTerm::Bitvector32Equal(left, right)
                    if matches!(right.as_ref(), crate::kernel::Bitvector32Term::Constant(0)) =>
                {
                    left.as_ref().clone()
                }
                crate::kernel::ConditionTerm::Bitvector32Equal(left, right)
                    if matches!(left.as_ref(), crate::kernel::Bitvector32Term::Constant(0)) =>
                {
                    right.as_ref().clone()
                }
                _ => {
                    return Err(proof
                        .step_error("signed_int32 certificate term must be an int32 expression"));
                }
            };
            if SignedArithmeticAtom::from_term(&term).is_none() {
                return Err(proof.step_error(
                    "signed_int32 certificate term is unsupported or exceeds the verification budget",
                ));
            }
            Ok(term)
        };
        let lower_prop = |proof: &Self, proposition: &ClickProposition, description: &str| {
            proof.lower_surface_proposition_direct(proposition, description)
        };
        let claim = |proposition: &Proposition, description: &str| {
            signed_arithmetic_claim(proposition).ok_or_else(|| {
                self.step_error(format!(
                    "{description} must be a supported signed_int32 arithmetic proposition"
                ))
            })
        };
        let node_claim = |node: &SignedArithmeticNode| match node {
            SignedArithmeticNode::Premise { result, .. }
            | SignedArithmeticNode::AffinePremise { result, .. }
            | SignedArithmeticNode::Scale { result, .. }
            | SignedArithmeticNode::Add { result, .. }
            | SignedArithmeticNode::EqualityToLessEqual { result, .. }
            | SignedArithmeticNode::EqualityFromBounds { result, .. }
            | SignedArithmeticNode::StrictFromDisequal { result, .. }
            | SignedArithmeticNode::Trivial { result }
            | SignedArithmeticNode::Int32Range { result } => Some(result.clone()),
            _ => None,
        };
        let mut nodes = Vec::with_capacity(certificate.nodes.len());
        for (node_index, node) in certificate.nodes.iter().enumerate() {
            let lowered = match node {
                SignedArithmeticStep::Premise {
                    index,
                    proposition,
                    result,
                } => {
                    let supplied = premises.get(*index).ok_or_else(|| {
                        self.step_error(format!("signed_int32 premise {index} is out of range"))
                    })?;
                    let declared = lower_prop(self, proposition, "signed_int32 premise")?;
                    if !same_signed_claim(supplied, &declared) {
                        return Err(self.step_error(format!(
                            "signed_int32 premise {index} does not match its source proposition"
                        )));
                    }
                    let declared_result = lower_prop(self, result, "signed_int32 premise result")?;
                    SignedArithmeticNode::Premise {
                        index: *index,
                        result: claim(&declared_result, "signed_int32 premise result")?,
                    }
                }
                SignedArithmeticStep::AffinePremise {
                    source,
                    left_evidence,
                    right_evidence,
                    result,
                } => {
                    let proposition = lower_prop(self, result, "signed_int32 affine premise")?;
                    let result =
                        crate::surface::decomposed_signed_claim(&proposition).ok_or_else(|| {
                            self.step_error("unsupported signed_int32 affine premise")
                        })?;
                    SignedArithmeticNode::AffinePremise {
                        source: *source,
                        left_evidence: *left_evidence,
                        right_evidence: *right_evidence,
                        result,
                    }
                }
                SignedArithmeticStep::Scale {
                    source,
                    coefficient,
                    result,
                } => {
                    let coefficient = signed_constant_expression(coefficient).ok_or_else(|| {
                        self.step_error(
                            "signed_int32 scale coefficient must be a constant int32 expression",
                        )
                    })?;
                    let source_result = signed_step_result_surface(
                        certificate.nodes.get(*source).ok_or_else(|| {
                            self.step_error("signed_int32 scale source is out of range")
                        })?,
                    )
                    .ok_or_else(|| {
                        self.step_error("signed_int32 scale source must produce an affine result")
                    })?;
                    let source_proposition =
                        lower_prop(self, source_result, "signed_int32 scale source")?;
                    let source_claim =
                        nodes.get(*source).and_then(&node_claim).ok_or_else(|| {
                            self.step_error(
                                "signed_int32 scale source must be an earlier affine node",
                            )
                        })?;
                    let expected = scale_claim(&source_claim, &coefficient).ok_or_else(|| {
                        self.step_error("signed_int32 scale exceeds the verification budget")
                    })?;
                    let result_proposition = lower_prop(self, result, "signed_int32 scale result")?;
                    let actual = claim(&result_proposition, "signed_int32 scale result")?;
                    let claims_match =
                        crate::kernel::proof::signed_arithmetic::charge_claim_pair_work(
                            &actual, &expected,
                        ) && actual == expected;
                    if !claims_match
                        && !signed_scaled_surface_shape(
                            &source_proposition,
                            &result_proposition,
                            &coefficient,
                        )
                    {
                        return Err(self.step_error(
                            "signed_int32 scale result does not encode the selected coefficient",
                        ));
                    }
                    SignedArithmeticNode::Scale {
                        source: *source,
                        coefficient,
                        result: expected,
                    }
                }
                SignedArithmeticStep::Add {
                    left,
                    right,
                    result,
                } => {
                    let left_result = signed_step_result_surface(
                        certificate.nodes.get(*left).ok_or_else(|| {
                            self.step_error("signed_int32 addition left is out of range")
                        })?,
                    )
                    .ok_or_else(|| {
                        self.step_error("signed_int32 addition left must produce an affine result")
                    })?;
                    let right_result = signed_step_result_surface(
                        certificate.nodes.get(*right).ok_or_else(|| {
                            self.step_error("signed_int32 addition right is out of range")
                        })?,
                    )
                    .ok_or_else(|| {
                        self.step_error("signed_int32 addition right must produce an affine result")
                    })?;
                    let lower_addend = |surface: &ClickProposition, description: &str| {
                        let lowered = match lower_signed_constant_comparison(surface) {
                            Some(lowered) => lowered,
                            None => lower_prop(self, surface, description)?,
                        };
                        Ok::<_, ClickError>(lowered)
                    };
                    let left_proposition = lower_addend(left_result, "signed_int32 addition left")?;
                    let right_proposition =
                        lower_addend(right_result, "signed_int32 addition right")?;
                    let left_claim = nodes.get(*left).and_then(&node_claim).ok_or_else(|| {
                        self.step_error("signed_int32 addition left must be an earlier affine node")
                    })?;
                    let right_claim = nodes.get(*right).and_then(&node_claim).ok_or_else(|| {
                        self.step_error(
                            "signed_int32 addition right must be an earlier affine node",
                        )
                    })?;
                    let expected = crate::kernel::proof::signed_arithmetic::add_claim(
                        &left_claim,
                        &right_claim,
                    )
                    .ok_or_else(|| {
                        self.step_error("signed_int32 addition exceeds the verification budget")
                    })?;
                    // Keep the exact affine slack and comparison relation.
                    // Ordinary lowering folds a true literal comparison to
                    // truth, losing the sum this node must independently check.
                    let lowered_result = lower_addend(result, "signed_int32 addition result")?;
                    let actual = claim(&lowered_result, "signed_int32 addition result")?;
                    if !(crate::kernel::proof::signed_arithmetic::charge_claim_pair_work(
                        &actual, &expected,
                    ) && actual == expected)
                        && !signed_add_surface_shape(
                            &left_proposition,
                            &right_proposition,
                            &lowered_result,
                        )
                    {
                        return Err(self.step_error(
                            "signed_int32 addition result does not encode the child sum",
                        ));
                    }
                    SignedArithmeticNode::Add {
                        left: *left,
                        right: *right,
                        result: expected,
                    }
                }
                SignedArithmeticStep::EqualityToLessEqual {
                    source,
                    reverse,
                    result,
                } => {
                    SignedArithmeticNode::EqualityToLessEqual {
                        source: *source,
                        reverse: *reverse,
                        result: {
                            let proposition =
                                lower_prop(self, result, "signed_int32 equality bound")?;
                            let opaque = claim(&proposition, "signed_int32 equality bound")?;
                            let mut expected = nodes.get(*source).and_then(&node_claim)
                            .ok_or_else(|| self.step_error("signed_int32 equality source must be an earlier affine node"))?;
                            expected.relation = SignedArithmeticRelation::LessEqual;
                            if *reverse {
                                for coefficient in expected.terms.values_mut() {
                                    *coefficient = -coefficient.clone();
                                }
                                expected.constant = -expected.constant;
                            }
                            if crate::kernel::proof::signed_arithmetic::charge_claim_pair_work(
                                &opaque, &expected,
                            ) && opaque == expected
                            {
                                opaque
                            } else {
                                crate::surface::decomposed_signed_claim(&proposition).ok_or_else(
                                    || self.step_error("unsupported signed_int32 equality bound"),
                                )?
                            }
                        },
                    }
                }
                SignedArithmeticStep::EqualityFromBounds {
                    lower,
                    upper,
                    result,
                } => SignedArithmeticNode::EqualityFromBounds {
                    lower: *lower,
                    upper: *upper,
                    result: claim(
                        &lower_prop(self, result, "signed_int32 equality")?,
                        "signed_int32 equality",
                    )?,
                },
                SignedArithmeticStep::StrictFromDisequal {
                    bound,
                    disequal,
                    result,
                } => SignedArithmeticNode::StrictFromDisequal {
                    bound: *bound,
                    disequal: *disequal,
                    result: claim(
                        &lower_prop(self, result, "signed_int32 strict bound")?,
                        "signed_int32 strict bound",
                    )?,
                },
                SignedArithmeticStep::Trivial { result } => {
                    let lowered = if node_index != certificate.conclusion {
                        match lower_signed_constant_comparison(result) {
                            Some(lowered) => lowered,
                            None => lower_prop(self, result, "signed_int32 trivial result")?,
                        }
                    } else {
                        lower_prop(self, result, "signed_int32 trivial result")?
                    };
                    SignedArithmeticNode::Trivial {
                        result: claim(&lowered, "signed_int32 trivial result")?,
                    }
                }
                SignedArithmeticStep::Int32Range { result } => SignedArithmeticNode::Int32Range {
                    result: claim(
                        &lower_prop(self, result, "signed_int32 int32 range bound")?,
                        "signed_int32 int32 range bound",
                    )?,
                },
                SignedArithmeticStep::IntervalFromAffine {
                    source,
                    term,
                    lower,
                    upper,
                } => SignedArithmeticNode::IntervalFromAffine {
                    source: *source,
                    term: lower_term(self, term)?,
                    lower: *lower,
                    upper: *upper,
                },
                SignedArithmeticStep::IntervalFromAffineDirect {
                    source,
                    term,
                    lower,
                    upper,
                } => SignedArithmeticNode::IntervalFromAffineDirect {
                    source: *source,
                    term: lower_term(self, term)?,
                    lower: *lower,
                    upper: *upper,
                },
                SignedArithmeticStep::IntervalAtom { term, lower, upper } => {
                    SignedArithmeticNode::IntervalAtom {
                        carrier: SignedArithmeticCarrier::SignedInt32,
                        term: lower_term(self, term)?,
                        lower: *lower,
                        upper: *upper,
                    }
                }
                SignedArithmeticStep::DefinedPremise { index, term } => {
                    SignedArithmeticNode::DefinedPremise {
                        index: *index,
                        carrier: SignedArithmeticCarrier::SignedInt32,
                        term: lower_term(self, term)?,
                    }
                }
                SignedArithmeticStep::IntervalIntersect {
                    left,
                    right,
                    result,
                } => SignedArithmeticNode::IntervalIntersect {
                    left: *left,
                    right: *right,
                    result: signed_interval(*result),
                },
                SignedArithmeticStep::IntervalAdd {
                    left,
                    right,
                    defined,
                    result,
                } => SignedArithmeticNode::IntervalAdd {
                    left: *left,
                    right: *right,
                    defined: *defined,
                    result: signed_interval(*result),
                },
                SignedArithmeticStep::IntervalAddBounded {
                    left,
                    right,
                    result,
                } => SignedArithmeticNode::IntervalAddBounded {
                    left: *left,
                    right: *right,
                    result: signed_interval(*result),
                },
                SignedArithmeticStep::IntervalSubtract {
                    left,
                    right,
                    defined,
                    result,
                } => SignedArithmeticNode::IntervalSubtract {
                    left: *left,
                    right: *right,
                    defined: *defined,
                    result: signed_interval(*result),
                },
                SignedArithmeticStep::IntervalMultiply {
                    left,
                    right,
                    defined,
                    result,
                } => SignedArithmeticNode::IntervalMultiply {
                    left: *left,
                    right: *right,
                    defined: *defined,
                    result: signed_interval(*result),
                },
                SignedArithmeticStep::IntervalRemainderAdd {
                    operand,
                    remainder,
                    addend,
                    divisor,
                    result,
                } => SignedArithmeticNode::IntervalRemainderAdd {
                    operand: *operand,
                    remainder: *remainder,
                    addend: *addend,
                    divisor: *divisor,
                    result: signed_interval(*result),
                },
                SignedArithmeticStep::IntervalRemainder {
                    operand,
                    divisor,
                    defined,
                    result,
                } => SignedArithmeticNode::IntervalRemainder {
                    operand: *operand,
                    divisor: *divisor,
                    defined: *defined,
                    result: signed_interval(*result),
                },
                SignedArithmeticStep::IntervalShiftLeft {
                    operand,
                    shift,
                    defined,
                    result,
                } => SignedArithmeticNode::IntervalShiftLeft {
                    operand: *operand,
                    shift: *shift,
                    defined: *defined,
                    result: signed_interval(*result),
                },
                SignedArithmeticStep::IntervalArithmeticShiftRight {
                    operand,
                    shift,
                    result,
                } => SignedArithmeticNode::IntervalArithmeticShiftRight {
                    operand: *operand,
                    shift: *shift,
                    result: signed_interval(*result),
                },
                SignedArithmeticStep::IntervalBitwiseAnd {
                    operand,
                    mask,
                    result,
                } => SignedArithmeticNode::IntervalBitwiseAnd {
                    operand: *operand,
                    mask: *mask,
                    result: signed_interval(*result),
                },
                SignedArithmeticStep::IntervalSignBitFlip { operand, result } => {
                    SignedArithmeticNode::IntervalSignBitFlip {
                        operand: *operand,
                        result: signed_interval(*result),
                    }
                }
                SignedArithmeticStep::IntervalCompare {
                    left,
                    right,
                    comparison,
                    result,
                } => SignedArithmeticNode::IntervalCompare {
                    left: *left,
                    right: *right,
                    comparison: signed_comparison(*comparison),
                    result: lower_prop(self, result, "signed_int32 comparison")?,
                },
                SignedArithmeticStep::AffineConclusion {
                    source,
                    evidence,
                    result,
                } => SignedArithmeticNode::AffineConclusion {
                    source: *source,
                    evidence: *evidence,
                    result: lower_prop(self, result, "signed_int32 conclusion")?,
                },
                SignedArithmeticStep::AffineConclusionWithEvidence {
                    source,
                    left_evidence,
                    right_evidence,
                    result,
                } => SignedArithmeticNode::AffineConclusionWithEvidence {
                    source: *source,
                    left_evidence: *left_evidence,
                    right_evidence: *right_evidence,
                    result: lower_prop(self, result, "signed_int32 conclusion")?,
                },
            };
            if nodes.len() != node_index {
                return Err(
                    self.step_error("signed_int32 certificate node indexing is not contiguous")
                );
            }
            nodes.push(lowered);
        }
        let kernel_certificate = KernelCertificate {
            nodes,
            conclusion: certificate.conclusion,
        };
        self.state
            .apply_signed_arithmetic(&kernel_certificate, &premises)
            .map_err(|error| match error {
                PropositionCloseError::NotProposition => {
                    self.step_error("signed_int32 certificate requires a proposition goal")
                }
                PropositionCloseError::SignedArithmeticPremiseUnavailable(index) => self
                    .step_error(format!(
                        "signed_int32 premise {index} is not exactly available"
                    )),
                PropositionCloseError::SignedArithmetic(error) => self.step_error(format!(
                    "signed_int32 arithmetic certificate rejected: {}",
                    describe_signed_arithmetic_check_error(&error)
                )),
                _ => self.step_error("signed_int32 certificate could not be applied"),
            })
    }

    fn apply_integer_certificate(
        &self,
        certificate: &IntegerCertificate,
    ) -> Result<KernelProofHandle, ClickError> {
        use crate::kernel::proof::integer_arithmetic::{
            IntegerArithmeticCertificate, IntegerArithmeticNode, integer_affine_claim,
        };

        // Source premise nodes are the only way a certificate imports facts.
        // Keep their explicit indices and reject holes or conflicting duplicate
        // declarations before handing anything to the kernel checker.
        let mut source_premises = std::collections::BTreeMap::new();
        let same_integer_claim =
            |left: &crate::kernel::Proposition, right: &crate::kernel::Proposition| match (
                integer_affine_claim(left),
                integer_affine_claim(right),
            ) {
                (Some(left), Some(right)) => {
                    !crate::instrumentation::deadline_exceeded_with_work(
                        left.terms
                            .len()
                            .saturating_add(right.terms.len())
                            .saturating_add(left.constant.bits() as usize + 1)
                            .saturating_add(right.constant.bits() as usize + 1),
                    ) && left == right
                }
                _ => false,
            };
        for node in &certificate.nodes {
            let IntegerCertificateNode::Premise {
                index, proposition, ..
            } = node
            else {
                continue;
            };
            let lowered =
                self.lower_integer_surface_proposition(proposition, "integer certificate premise")?;
            match source_premises.entry(*index) {
                std::collections::btree_map::Entry::Vacant(entry) => {
                    entry.insert(lowered);
                }
                std::collections::btree_map::Entry::Occupied(entry) => {
                    if !same_integer_claim(entry.get(), &lowered) {
                        return Err(self.step_error(format!(
                            "integer certificate premise {index} is declared with two different propositions"
                        )));
                    }
                }
            }
        }
        let mut premises = Vec::with_capacity(source_premises.len());
        for index in 0..source_premises.len() {
            let Some(premise) = source_premises.remove(&index) else {
                return Err(self.step_error(format!(
                    "integer certificate premise indices must be contiguous; missing {index}"
                )));
            };
            premises.push(premise);
        }

        let claim = |proof: &Self,
                     proposition: &ClickProposition,
                     description: &str,
                     preserve_constant_relation: bool| {
            let proposition = if preserve_constant_relation {
                if let Some(raw) = lower_integer_constant_comparison(proposition) {
                    raw
                } else {
                    proof.lower_integer_surface_proposition(proposition, description)?
                }
            } else {
                proof.lower_integer_surface_proposition(proposition, description)?
            };
            integer_affine_claim(&proposition).ok_or_else(|| {
                proof.step_error(format!(
                    "{description} must be a supported mathematical Integer affine proposition"
                ))
            })
        };
        let mut nodes = Vec::with_capacity(certificate.nodes.len());
        for (node_index, node) in certificate.nodes.iter().enumerate() {
            let lowered = match node {
                IntegerCertificateNode::Premise {
                    index,
                    proposition,
                    result,
                } => {
                    let supplied = premises.get(*index).ok_or_else(|| {
                        self.step_error(format!("integer certificate premise {index} is out of range"))
                    })?;
                    let declared = self.lower_integer_surface_proposition(
                        proposition,
                        "integer certificate premise",
                    )?;
                    if !same_integer_claim(supplied, &declared) {
                        return Err(self.step_error(format!(
                            "integer certificate premise {index} does not match its declared source proposition"
                        )));
                    }
                    IntegerArithmeticNode::Premise {
                        index: *index,
                        result: claim(
                            self,
                            result,
                            "integer certificate premise result",
                            false,
                        )?,
                    }
                }
                IntegerCertificateNode::Scale {
                    source,
                    coefficient,
                    result,
                } => IntegerArithmeticNode::Scale {
                    source: *source,
                    coefficient: integer_constant_expression(coefficient).ok_or_else(|| {
                        self.step_error(
                            "integer certificate scale coefficient must be a constant Integer expression",
                        )
                    })?,
                    result: claim(self, result, "integer certificate scale result", false)?,
                },
                IntegerCertificateNode::Add { left, right, result } => {
                    IntegerArithmeticNode::Add {
                        left: *left,
                        right: *right,
                        result: claim(self, result, "integer certificate addition result", false)?,
                    }
                }
                IntegerCertificateNode::EqualityToLessEqual {
                    source,
                    reverse,
                    result,
                } => IntegerArithmeticNode::EqualityToLessEqual {
                    source: *source,
                    reverse: *reverse,
                    result: claim(self, result, "integer certificate equality bound", false)?,
                },
                IntegerCertificateNode::EqualityFromBounds {
                    lower,
                    upper,
                    result,
                } => IntegerArithmeticNode::EqualityFromBounds {
                    lower: *lower,
                    upper: *upper,
                    result: claim(self, result, "integer certificate equality", false)?,
                },
                IntegerCertificateNode::Trivial { result } => IntegerArithmeticNode::Trivial {
                    result: claim(
                        self,
                        result,
                        "integer certificate trivial result",
                        node_index != certificate.conclusion
                            // Peeling can retain an Integer order obligation
                            // whose written constant comparison ordinarily
                            // lowers to `true`. Keep its relation only when it
                            // matches the actual kernel conclusion exactly.
                            || lower_integer_constant_comparison(result)
                                .as_ref()
                                .and_then(integer_affine_claim)
                                .is_some_and(|written| {
                                    self.goal().and_then(integer_affine_claim)
                                        == Some(written)
                                }),
                    )?,
                },
            };
            if nodes.len() != node_index {
                return Err(self.step_error("integer certificate node indexing is not contiguous"));
            }
            nodes.push(lowered);
        }
        let kernel_certificate = IntegerArithmeticCertificate {
            nodes,
            conclusion: certificate.conclusion,
        };
        self.state
            .apply_integer_arithmetic(&kernel_certificate, &premises)
            .map_err(|error| match error {
                PropositionCloseError::NotProposition => {
                    self.step_error("integer certificate requires a proposition goal")
                }
                PropositionCloseError::IntegerArithmeticPremiseUnavailable(index) => self
                    .step_error(format!(
                        "integer certificate premise {index} is not exactly available"
                    )),
                PropositionCloseError::IntegerArithmetic(error) => self.step_error(format!(
                    "integer arithmetic certificate rejected: {}",
                    describe_integer_arithmetic_check_error(&error)
                )),
                _ => unreachable!("kernel returned an unrelated integer arithmetic error"),
            })
    }

    fn lower_integer_surface_proposition(
        &self,
        surface: &ClickProposition,
        description: &str,
    ) -> Result<Proposition, ClickError> {
        match self.context.as_ref() {
            ProofContext::Pure(context) => {
                let mut names = BTreeSet::new();
                collect_click_proposition_referenced_names(surface, &mut names);
                let mut integer_values = context.theorem_context.integer_values.clone();
                for name in &names {
                    crate::instrumentation::record_deterministic_work(1);
                    if let Some(value) = self.state().locals().integer_values.get(name) {
                        integer_values = integer_values.with_inserted(name.clone(), value.clone());
                    }
                }
                let promoted = self.proposition_obligation().map_or_else(
                    || surface.clone(),
                    |goal| {
                        crate::surface::proof::surface_lowering::promote_integer_comparison(
                            surface,
                            &integer_values,
                            &goal.surface_bindings,
                        )
                    },
                );
                if let Ok(proposition) = crate::surface::lower_integer_certificate_proposition(
                    &promoted,
                    &integer_values,
                ) {
                    return Ok(proposition);
                }
                // Mixed atoms need the ordinary checked specification lowerer.
                // Select only bindings referenced by this explicit certificate
                // node, so unrelated theorem parameters are never copied.
                let values = names
                    .iter()
                    .filter_map(|name| {
                        if integer_values.get(name).is_some() {
                            return None;
                        }
                        context
                            .theorem_context
                            .values
                            .get(name)
                            .map(|value| (name.clone(), value.clone()))
                    })
                    .collect();
                let arrays = names
                    .iter()
                    .filter_map(|name| {
                        context
                            .theorem_context
                            .array_refs
                            .get(name)
                            .map(|value| (name.clone(), value.clone()))
                    })
                    .collect();
                let algebraic = names
                    .iter()
                    .filter_map(|name| {
                        context
                            .structural_induction_setup
                            .as_ref()?
                            .algebraic_values
                            .get(name)
                            .map(|value| (name.clone(), value.clone()))
                    })
                    .collect();
                super::super::pure_theorems::lower_pure_theorem_proposition_recording_introductions(
                    context.claim_label,
                    &promoted,
                    self.facts().assumptions(),
                    &values,
                    &arrays,
                    &algebraic,
                    &integer_values,
                    &context.theorem_context.memory,
                    context.spec_definitions,
                )
                .map(|(proposition, _)| proposition)
                .map_err(|message| {
                    self.step_error(format!("could not lower {description}: {message}"))
                })
            }
            _ => self.lower_surface_proposition_direct(surface, description),
        }
    }

    /// The focused universal goal with its binder respelled `name`, for
    /// `intro() as name`. The name must be new here: nothing is shadowed.
    fn universal_goal_renamed_for_intro(&self, name: &str) -> Result<ClickProposition, ClickError> {
        if !matches!(self.goal(), Some(Proposition::ForAll { .. })) {
            return Err(self.step_error(format!(
                "`intro() as {name}` names the variable of a `forall` goal; this goal introduces a fact, which has no name, so write `intro();`"
            )));
        }
        // A range quantifier keeps its variable in the lambda:
        // `(lo..hi).all(|k| { ... })`.
        let (binder, body, c_typed) = match self.surface_goal() {
            Some(ClickProposition::ForAll {
                click_type,
                name: binder,
                body,
                ..
            }) => (binder, body, matches!(click_type, ClickType::C(_))),
            Some(ClickProposition::RangeAll { item, body, .. }) => (item, body, false),
            _ => {
                return Err(self.step_error(format!(
                    "`intro() as {name}` requires a goal written as `forall (x: T) {{ ... }}` or `(lo..hi).all(|x| {{ ... }})`; write `intro();` to keep the name this goal's quantifier has"
                )));
            }
        };
        if binder == name {
            return Ok(self.surface_goal().expect("matched above").clone());
        }
        let mut referenced = BTreeSet::new();
        crate::surface::lowering::collect_click_proposition_referenced_names(body, &mut referenced);
        let (names, _) = self.diagnostic_naming_tables();
        let locals = self.state.locals();
        let in_scope = referenced.contains(name)
            || names.iter().any(|parameter| parameter.name() == name)
            || locals.integer_values.get(name).is_some()
            || locals.algebraic_values.get(name).is_some()
            || self
                .focused_obligation()
                .is_some_and(|obligation| match obligation {
                    Obligation::Proposition(goal) => goal.surface_bindings.get(name).is_some(),
                    _ => false,
                });
        if in_scope {
            return Err(self.step_error(format!(
                "`intro() as {name}`: `{name}` is already in scope here; choose a name that is not"
            )));
        }
        let replacement = if c_typed {
            ContractExpression::CBinding(name.to_string())
        } else {
            ContractExpression::Binding(name.to_string())
        };
        let renaming = BTreeMap::from([(binder.clone(), replacement)]);
        let body = crate::surface::lowering::substitute_click_proposition(body, &renaming)
            .map_err(|message| self.step_error(message))?;
        Ok(match self.surface_goal() {
            Some(ClickProposition::RangeAll { start, end, .. }) => ClickProposition::RangeAll {
                start: start.clone(),
                end: end.clone(),
                item: name.to_string(),
                written_item: None,
                body: Box::new(body),
            },
            Some(ClickProposition::ForAll { click_type, .. }) => ClickProposition::ForAll {
                click_type: click_type.clone(),
                name: name.to_string(),
                written_name: None,
                body: Box::new(body),
            },
            _ => unreachable!("matched as a quantifier above"),
        })
    }

    // Preserve the rule/dispatcher frame boundary described above; `intro`
    // owns several by-value proposition variants.
    #[inline(never)]
    pub(super) fn apply_intro(
        &self,
        rename: Option<&str>,
    ) -> Result<KernelProofHandle, ClickError> {
        // `intro() as name` respells the universal goal's binder before the
        // ordinary introduction runs, so every binding below is made under
        // the chosen name and the remaining goal is written in terms of it.
        let renamed_surface = rename
            .map(|name| self.universal_goal_renamed_for_intro(name))
            .transpose()?;
        let mut integer_binding = None;
        let mut algebraic_binding = None;
        let state = self
            .state
            .apply_intro(|current, introduction, introduced| {
                let mut surface_bindings = current.surface_bindings.clone();
                let mut introduced_antecedents = current.introduced_antecedents.clone();
                let renamed_recorded = match (rename, current.introductions.head()) {
                    (
                        Some(name),
                        Some(LoweringIntroduction::WrittenUniversal {
                            variable,
                            pointer,
                            integer,
                            ..
                        }),
                    ) => Some(LoweringIntroduction::WrittenUniversal {
                        name: name.to_string(),
                        variable: *variable,
                        pointer: *pointer,
                        integer: *integer,
                    }),
                    _ => None,
                };
                let recorded = renamed_recorded
                    .as_ref()
                    .or_else(|| current.introductions.head());
                let current_surface = renamed_surface
                    .as_ref()
                    .or(current.surface.as_deref());
                let introduced_name = match (&introduction, recorded, current_surface) {
                    (
                        PropositionIntroduction::Universal { .. },
                        Some(LoweringIntroduction::WrittenUniversal { name, .. }),
                        _,
                    ) => Some(name),
                    (
                        PropositionIntroduction::Universal { .. },
                        _,
                        Some(ClickProposition::ForAll { name, .. }),
                    ) => Some(name),
                    _ => None,
                };
                if let Some(name) = introduced_name {
                    let previous = current.surface_bindings.get(name).cloned().or_else(|| {
                        let value = match self.context.as_ref() {
                            ProofContext::Pure(context) => {
                                context.theorem_context.values.get(name).cloned().map(CExpression::Value)
                            }
                            ProofContext::FixedState(context) => context
                                .parameters
                                .iter()
                                .zip(context.arguments)
                                .find(|(parameter, _)| parameter.name() == name)
                                .map(|(_, argument)| argument.clone()),
                            ProofContext::Execution(context) => context
                                .parsed_function
                                .parameters()
                                .iter()
                                .zip(context.arguments)
                                .find(|(parameter, _)| parameter.name() == name)
                                .map(|(_, argument)| argument.clone()),
                        };
                        value.map(ContractExpression::CFragment)
                    });
                    if let Some(previous) = previous {
                        let mut depth = 1;
                        loop {
                            let alias = format!("{}{}", "outer.".repeat(depth), name);
                            let Some(older) = current.surface_bindings.get(&alias) else {
                                break;
                            };
                            surface_bindings = surface_bindings.with_inserted(
                                format!("{}{}", "outer.".repeat(depth + 1), name),
                                older.clone(),
                            );
                            depth += 1;
                        }
                        surface_bindings =
                            surface_bindings.with_inserted(format!("outer.{name}"), previous);
                    }
                }
                let surface = match (recorded, introduction, current_surface) {
                    // Lowering inserts implications that guard a body with a
                    // path fact it established or with a load obligation the
                    // state did not discharge. Neither has a Surface
                    // connective, so the written goal stays focused while
                    // `intro` exposes one such kernel implication.
                    (
                        Some(
                            LoweringIntroduction::PathFactGuard
                            | LoweringIntroduction::ObligationGuard,
                        ),
                        PropositionIntroduction::Implication,
                        Some(surface),
                    ) => Some(Arc::new(surface.clone())),
                    // A written implication consumes the written connective.
                    // The pair `intro` just checked is retained here, with
                    // its structural conjuncts, so a later citation does not
                    // re-lower the antecedent under the fact context this
                    // step changed.
                    (
                        Some(LoweringIntroduction::WrittenImplication),
                        PropositionIntroduction::Implication,
                        Some(surface),
                    ) => match written_implication_consequent(surface) {
                        Some(WrittenAntecedent::Implication {
                            antecedent,
                            consequent,
                        }) => {
                            if let Some(kernel) = introduced {
                                introduced_antecedents = retain_introduced_antecedent(
                                    &introduced_antecedents,
                                    &antecedent,
                                    kernel,
                                );
                            }
                            Some(Arc::new(consequent))
                        }
                        // A range quantifier writes no implication of its
                        // own: its kernel form is the binder followed by the
                        // range guard, whose consequent is the written body.
                        Some(WrittenAntecedent::RangeGuard { body }) => Some(Arc::new(body)),
                        None => Some(Arc::new(surface.clone())),
                    },
                    (
                        Some(LoweringIntroduction::WrittenUniversal {
                            name,
                            pointer,
                            integer,
                            ..
                        }),
                        PropositionIntroduction::Universal {
                            variable,
                            pointer: introduced_pointer,
                            algebraic,
                        },
                        surface,
                    ) => {
                        if *integer {
                            integer_binding = Some((name.clone(), variable));
                        } else if let Some(ref algebraic_type) = algebraic {
                            algebraic_binding =
                                Some((name.clone(), variable, algebraic_type.clone()));
                        }
                        // The binding names the exact variable the kernel
                        // bound the body to, not the one lowering first
                        // chose: `intro` freshens the binder away from
                        // ambient facts.
                        let value = match (pointer, introduced_pointer) {
                            (true, Some(c_type)) => {
                                CValue::typed_pointer(Pointer::symbolic(variable), c_type)
                            }
                            _ => match self.proposition_goal("`intro` requires a proposition goal").expect("intro checked its goal") {
                                Proposition::ForAll { sort, .. } if sort.machine_integer_type().is_some() => sort.machine_integer_type().unwrap().symbolic_value(variable),
                                _ => CValue::Int32(Bitvector32Term::Variable(variable)),
                            },
                        };
                        if algebraic.is_some() {
                            surface_bindings = surface_bindings.with_inserted(
                                name.clone(),
                                ContractExpression::Binding(name.clone()),
                            );
                        } else if !*integer {
                            surface_bindings = surface_bindings.with_inserted(
                                name.clone(),
                                ContractExpression::CFragment(CExpression::Value(value)),
                            );
                        }
                        surface.and_then(written_universal_body).map(Arc::new)
                    }
                    // No lowering provenance was recorded for this goal, so
                    // refine the written form structurally, as before.
                    (None, PropositionIntroduction::Implication, Some(surface)) => {
                        surface_implication_parts(surface)
                            .map(|(_, consequent)| Arc::new(consequent))
                            .or_else(|| Some(Arc::new(surface.clone())))
                    }
                    (
                        None,
                        PropositionIntroduction::Universal {
                            variable,
                            algebraic,
                            ..
                        },
                        Some(ClickProposition::ForAll { name, body, .. }),
                    ) => {
                        if let Some(algebraic_type) = algebraic {
                            algebraic_binding =
                                Some((name.clone(), variable, algebraic_type.clone()));
                            surface_bindings = surface_bindings.with_inserted(
                                name.clone(),
                                ContractExpression::Binding(name.clone()),
                            );
                        } else {
                            surface_bindings = surface_bindings.with_inserted(
                                name.clone(),
                                ContractExpression::CFragment(CExpression::Value(
                                    match self.proposition_goal("`intro` requires a proposition goal").expect("intro checked its goal") {
                                        Proposition::ForAll { sort, .. } if sort.machine_integer_type().is_some() => sort.machine_integer_type().unwrap().symbolic_value(variable),
                                        _ => CValue::Int32(Bitvector32Term::Variable(variable)),
                                    },
                                )),
                            );
                        }
                        Some(Arc::new(body.as_ref().clone()))
                    }
                    _ => None,
                };
                PropositionPresentation {
                    surface,
                    surface_bindings,
                    introductions: current.introductions.advanced(),
                    introduced_antecedents,
                    both_children: None,
                    witness_refinement_kernel: current.witness_refinement_kernel.clone(),
                }
            })
            .map_err(|error| match error {
                PropositionCloseError::NotProposition => {
                    self.step_error("`intro` requires a proposition goal")
                }
                PropositionCloseError::ExpectedIntroduction(goal) => self.step_error(format!(
                    "`intro` requires an implication, negation, or universal goal, got {}",
                    describe_assumption_goal(&goal)
                )),
                PropositionCloseError::IntegerFresheningExhausted => {
                    self.step_error("`intro` requires a fresh Integer binder variable")
                }
                PropositionCloseError::UniversalWitnessFresheningExhausted => self.step_error(
                    "`intro` requires a fresh witness identity for the universal's bound variable, and this proof has used every one the reserved witness range holds",
                ),
                _ => unreachable!("kernel returned an unrelated intro error"),
            })?;
        if let Some((name, variable, algebraic_type)) = algebraic_binding {
            let mut locals = state.locals().clone();
            locals.algebraic_values = locals.algebraic_values.with_inserted(
                name,
                crate::kernel::SpecAlgebraicExpression {
                    algebraic_type,
                    node: crate::kernel::SpecAlgebraicExpressionNode::Variable(variable),
                },
            );
            Ok(state.with_locals(locals))
        } else if let Some((name, variable)) = integer_binding {
            let mut locals = state.locals().clone();
            locals.integer_values = locals.integer_values.with_inserted(
                name,
                crate::kernel::SpecIntegerExpression::Term(crate::kernel::IntegerTerm::var(
                    variable,
                )),
            );
            Ok(state.with_locals(locals))
        } else {
            Ok(state)
        }
    }

    #[inline(never)]
    fn apply_induct(
        &self,
        parameter: &str,
        hypothesis: &str,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let ProofContext::Pure(context) = self.context.as_ref() else {
            return Err(self.step_error("`induct` requires a pure theorem proof"));
        };
        let Some(setup) = context.induction_setup.as_ref() else {
            return Err(self.step_error("`induct` is not active for this pure theorem"));
        };
        if parameter != setup.parameter || hypothesis != setup.hypothesis {
            return Err(self.step_error("induction step does not match the theorem setup"));
        }
        let expected_goal =
            self.lower_surface_proposition(&setup.surface_goal, "induction theorem goal")?;
        if self.goal() != Some(&expected_goal) {
            return Err(
                self.step_error("`induct` must be the first step of the pure theorem proof")
            );
        }
        let Some(CValue::Int32(current)) = context.theorem_context.values.get(parameter) else {
            return Err(self.step_error("induction parameter must have type int32"));
        };
        let nonnegative = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedGreaterEqual(
                Box::new(current.clone()),
                Box::new(Bitvector32Term::Constant(0)),
            ),
            true,
        );
        if !self.facts().contains(&nonnegative)
            && !self.facts().has_nonnegative_induction_domain(current)
        {
            return Err(self.step_error(format!(
                "`induct({parameter})` requires a proof that `{parameter}` is nonnegative"
            )));
        }
        let quantified = super::super::pure_theorems::pure_induction_hypothesis(
            setup,
            context.theorem_context,
            context.spec_definitions,
        )?;
        if self.facts().contains(&quantified) {
            return Err(self.step_error("induction hypothesis was already introduced"));
        }
        let facts = self.facts().with_kernel_checked_fact(quantified.clone());
        Ok(self.checked_fact_transition(
            self.state().locals().clone(),
            facts,
            false,
            vec![quantified.clone()],
            vec![quantified],
        ))
    }

    #[inline(never)]
    fn apply_induction(
        &self,
        hypothesis: &str,
        arguments: &[ContractExpression],
        surface_premises: &[ClickProposition],
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let ProofContext::Pure(context) = self.context.as_ref() else {
            return Err(self.step_error("induction application requires a pure theorem proof"));
        };
        if let Some(setup) = context.structural_induction_setup.as_ref() {
            return self.apply_structural_induction_hypothesis(
                context,
                setup,
                hypothesis,
                arguments,
                surface_premises,
            );
        }
        let Some(setup) = context.induction_setup.as_ref() else {
            return Err(self.step_error("induction hypothesis is not active"));
        };
        if hypothesis != setup.hypothesis {
            return Err(self.step_error(format!("unknown induction hypothesis `{hypothesis}`")));
        }
        // Measure induction quantifies one `int32` variable: its hypothesis
        // holds every other theorem parameter at its current value.
        let [argument] = arguments else {
            return Err(self.step_error(format!(
                "induction hypothesis `{hypothesis}` expects one argument"
            )));
        };
        let lowered_premises = surface_premises
            .iter()
            .map(|premise| self.lower_surface_proposition(premise, "induction premise"))
            .collect::<Result<Vec<_>, _>>()?;
        // The hypothesis is the theorem's own statement, so a range premise
        // owes its extent halves beside it. Citing a stated range cites both
        // halves, by the one rule every `apply using` shares.
        let mut explicit_premises = Vec::with_capacity(lowered_premises.len());
        for premise in lowered_premises {
            crate::surface::proof::theorem_application::cite_range_extent_guards(
                &premise,
                &mut explicit_premises,
                |guard| self.facts().exact_available_across_effects(guard, &[]),
            );
            if !explicit_premises.contains(&premise) {
                explicit_premises.push(premise);
            }
        }

        let state = CState::new().with_memory(context.theorem_context.memory.clone());
        let mut active_functions = BTreeSet::new();
        let value = evaluate_contract_expression_with_environment(
            &context.theorem_context.values,
            &context.theorem_context.array_refs,
            &state,
            &state,
            None,
            self.facts().assumptions(),
            argument,
            context.spec_definitions,
            &RecordedSnapshots::new(),
            &mut active_functions,
        )
        .map_err(|message| {
            self.step_error(format!("could not evaluate induction argument: {message}"))
        })?;
        let CValue::Int32(argument) = value else {
            return Err(self.step_error("induction argument must have type int32"));
        };
        let quantified = super::super::pure_theorems::pure_induction_hypothesis(
            setup,
            context.theorem_context,
            context.spec_definitions,
        )?;
        self.state
            .apply_instantiate(quantified, argument, Some(&explicit_premises))
            .map(|state| {
                // `apply_instantiate` has performed the complete kernel
                // premise/order/conclusion check. Publish its exact fact
                // delta through the same Proof transition used by ordinary
                // quantified instantiation.
                let added_facts = state.state().checked_facts().to_vec();
                let mut facts = self.facts().clone();
                for fact in &added_facts {
                    facts = facts.with_kernel_checked_fact(fact.clone());
                }
                let complete = self.goal().is_some_and(|goal| facts.contains(goal));
                self.checked_fact_transition(
                    self.state().locals().clone(),
                    facts,
                    complete,
                    added_facts.clone(),
                    added_facts,
                )
            })
            .map_err(|error| match error {
                PropositionCloseError::NotProposition => {
                    self.step_error("induction application requires a proposition goal")
                }
                PropositionCloseError::InstantiatePremiseUnavailable(_, premise) => self
                    .step_error(format!(
                        "induction premise is not exactly available: {}",
                        crate::surface::proof_diagnostics::render::render_proposition(&premise)
                    )),
                PropositionCloseError::InstantiateQuantifiedUnavailable => {
                    self.step_error("induction hypothesis is not exactly available")
                }
                PropositionCloseError::InstantiateInvalid(error) => {
                    // The kernel says which premise of the hypothesis it could
                    // not discharge. Dropping that left "kernel rejected
                    // induction application", which names nothing a reader can
                    // act on — and a hypothesis premise is exactly what they
                    // have to supply.
                    let (parameters, arguments) = crate::surface::diagnostics::value_naming_tables(
                        &context.theorem_context.values,
                    );
                    self.step_error(format!(
                        "`apply` of the induction hypothesis failed: {}",
                        crate::surface::proof::format_forall_int32_instantiation_error(
                            error,
                            &parameters,
                            &arguments,
                        )
                    ))
                }
                _ => unreachable!("kernel returned an unrelated induction error"),
            })
    }

    fn apply_structural_induction_hypothesis(
        &self,
        _context: &PureProofContext<'_>,
        setup: &PureStructuralInductionBranchSetup,
        hypothesis: &str,
        arguments: &[ContractExpression],
        surface_premises: &[ClickProposition],
    ) -> Result<CheckedFocusedTransition, ClickError> {
        if hypothesis != setup.hypothesis {
            return Err(self.step_error(format!("unknown induction hypothesis `{hypothesis}`")));
        }
        // The inducted position must name a field this arm's pattern bound,
        // whatever the remaining positions instantiate. This is a bounded
        // test against the arm's own bindings.
        if !super::super::pure_theorems::structural_induction_descends(setup, arguments) {
            return Err(self.step_error(
                "structural induction hypothesis expects an immediate recursive field",
            ));
        }
        let Some(application) = setup
            .applications
            .iter()
            .find(|candidate| candidate.arguments == *arguments)
        else {
            return Err(self.step_error(
                "structural induction hypothesis expects an immediate recursive field",
            ));
        };
        if surface_premises != application.surface_premises {
            return Err(self.step_error(
                "structural induction application changed its exact requirement premises",
            ));
        }
        let explicit_premises = surface_premises
            .iter()
            .map(|premise| self.lower_surface_proposition(premise, "induction premise"))
            .collect::<Result<Vec<_>, _>>()?;
        if explicit_premises != application.kernel_premises {
            return Err(self.step_error(
                "structural induction application lowered different requirement premises",
            ));
        }
        if !self.facts().contains(&application.implication) {
            return Err(self.step_error("structural induction hypothesis is not active"));
        }
        if let Some(missing) = explicit_premises
            .iter()
            .find(|premise| !self.facts().listed_premise_available(premise, &[], true))
        {
            return Err(self.step_error(format!(
                "induction premise is not exactly available: {}",
                crate::surface::proof_diagnostics::render::render_proposition(missing)
            )));
        }
        if !self.facts().contains(&application.conclusion)
            && !self
                .facts()
                .contains_discharged_implication_consequent(&application.conclusion)
        {
            return Err(self.step_error("kernel rejected structural induction application"));
        }
        let added = (!self.facts().contains_top_level(&application.conclusion))
            .then(|| application.conclusion.clone())
            .into_iter()
            .collect::<Vec<_>>();
        let mut facts = self.facts().clone();
        for fact in &added {
            facts = facts.with_kernel_checked_fact(fact.clone());
        }
        let complete = self.goal().is_some_and(|goal| facts.contains(goal));
        Ok(self.checked_fact_transition(
            self.state().locals().clone(),
            facts,
            complete,
            added.clone(),
            added,
        ))
    }

    // Preserve the rule/dispatcher frame boundary described above; instance
    // materialization is local to this rule.
    #[inline(never)]
    pub(super) fn apply_enumerate(&self) -> Result<KernelProofHandle, ClickError> {
        self.state.apply_enumerate().map_err(|error| match error {
            PropositionCloseError::NotProposition => {
                self.step_error("`enumerate` requires a proposition goal")
            }
            PropositionCloseError::ExpectedFiniteUniversal => {
                self.step_error("`enumerate` requires a universal goal with constant bounds")
            }
            PropositionCloseError::MissingFiniteInstance => self.step_error(
                "`enumerate` requires each in-range instance as an exact available fact",
            ),
            _ => unreachable!("kernel returned an unrelated enumerate error"),
        })
    }
}

fn trace_frontier(frontier: &ExecutionFrontier) -> String {
    if frontier.is_at_function_entry() {
        "function entry".into()
    } else if frontier.is_at_function_exit() {
        "function exit".into()
    } else if frontier.is_at_region_boundary() {
        "region boundary".into()
    } else {
        format!("C statement {}", frontier.next_statement_index + 1)
    }
}

fn trace_statement_head(statement: &CStatement) -> String {
    if let CStatement::Store { pointer, value } | CStatement::TypedStore { pointer, value, .. } =
        statement
        && let CExpression::Add(base, index) = pointer
    {
        return format!(
            "{}[{}] = {}",
            crate::surface::diagnostics::describe_c_expression(base),
            crate::surface::diagnostics::describe_c_expression(index),
            crate::surface::diagnostics::describe_c_expression(value),
        );
    }
    describe_statement_head(statement)
}

/// Prefer an exact parameter base for a trace. The general diagnostic range
/// printer accepts an offset from any parameter, which can turn a `visited`
/// view into `left[(v100002-v100000)..]` even though `visited` is available.
fn trace_resource_fact(fact: &CResourceFact, context: &ExecutionProofContext<'_>) -> String {
    if let Some(range) = fact.memory_range() {
        for (parameter, argument) in context
            .parsed_function
            .parameters()
            .iter()
            .zip(context.arguments)
        {
            if let CExpression::Value(CValue::Pointer(base)) = argument
                && base.pointer() == range.base()
            {
                return crate::surface::diagnostics::describe_resource_fact(
                    fact,
                    std::slice::from_ref(parameter),
                    std::slice::from_ref(argument),
                );
            }
        }
        return if fact.is_own() {
            "ownership of a memory range (no source name)".into()
        } else {
            "view of a memory range (no source name)".into()
        };
    }
    crate::surface::diagnostics::describe_resource_fact(
        fact,
        context.parsed_function.parameters(),
        context.arguments,
    )
}

fn describe_assumption_goal(goal: &Proposition) -> &'static str {
    match goal {
        Proposition::And(..) => "a conjunction",
        Proposition::Or(..) => "a disjunction",
        Proposition::Implies(..) => "an implication",
        Proposition::Not(..) => "a negation",
        Proposition::ForAll { .. } => "a universal proposition",
        Proposition::Exists { .. } => "an existential proposition",
        Proposition::CMemoryLoadable { .. } => "a memory-viewability fact",
        Proposition::ConditionIs(condition, _) => match condition {
            ConditionTerm::IntegerLessThan(..) => "an Integer less-than fact",
            ConditionTerm::IntegerLessEqual(..) => "an Integer less-or-equal fact",
            ConditionTerm::IntegerGreaterThan(..) => "an Integer greater-than fact",
            ConditionTerm::IntegerGreaterEqual(..) => "an Integer greater-or-equal fact",
            ConditionTerm::IntegerEqual(..) => "an Integer equality fact",
            ConditionTerm::IntegerNotEqual(..) => "an Integer disequality fact",
            _ => "a condition fact",
        },
        Proposition::Equal(Term::Integer(_), Term::Integer(_)) => "an Integer equality fact",
        Proposition::Equal(..) => "an equality fact",
        _ => "a proposition fact",
    }
}

/// Preserve the relation shape of an intermediate constant certificate node.
///
/// The ordinary Integer condition constructors intentionally evaluate two
/// constants immediately.  That is correct for a goal (whose checked claim
/// is then the canonical `Equal(0)` truth claim), but an intermediate
/// weakening node carries a nonzero affine constant that the arithmetic
/// certificate must validate before it is added to another claim.  Construct
/// the raw checked condition only at this certificate boundary; source
/// premise lowering continues to use the ordinary contextual lowerer.
fn lower_integer_constant_comparison(
    proposition: &ClickProposition,
) -> Option<crate::kernel::Proposition> {
    let ClickProposition::Comparison {
        left,
        operator,
        right,
    } = proposition
    else {
        return None;
    };
    let left = crate::kernel::IntegerTerm::constant(integer_constant_expression(left)?).into();
    let right = crate::kernel::IntegerTerm::constant(integer_constant_expression(right)?).into();
    let condition = match operator {
        ComparisonOperator::Equal => crate::kernel::ConditionTerm::IntegerEqual(left, right),
        ComparisonOperator::NotEqual => crate::kernel::ConditionTerm::IntegerNotEqual(left, right),
        ComparisonOperator::LessThan => crate::kernel::ConditionTerm::IntegerLessThan(left, right),
        ComparisonOperator::LessEqual => {
            crate::kernel::ConditionTerm::IntegerLessEqual(left, right)
        }
        ComparisonOperator::GreaterThan => {
            crate::kernel::ConditionTerm::IntegerGreaterThan(left, right)
        }
        ComparisonOperator::GreaterEqual => {
            crate::kernel::ConditionTerm::IntegerGreaterEqual(left, right)
        }
        ComparisonOperator::In => return None,
    };
    Some(crate::kernel::Proposition::ConditionIs(condition, true))
}

fn integer_constant_expression(expression: &ContractExpression) -> Option<num_bigint::BigInt> {
    let literal = match expression {
        ContractExpression::IntegerLiteral(value) => value,
        ContractExpression::Negate(inner) => match inner.as_ref() {
            ContractExpression::IntegerLiteral(value) => value,
            _ => return None,
        },
        _ => return None,
    };
    if crate::instrumentation::deadline_exceeded_with_work(
        literal
            .len()
            .saturating_mul(literal.len().saturating_add(4))
            .max(1),
    ) {
        return None;
    }
    match expression {
        ContractExpression::IntegerLiteral(value) => value.parse::<num_bigint::BigInt>().ok(),
        // Keep the source coefficient grammar deliberately narrow.  Parsing
        // arbitrary arithmetic here would create a second unbounded evaluator
        // outside the checked certificate kernel.
        ContractExpression::Negate(inner) => match inner.as_ref() {
            ContractExpression::IntegerLiteral(value) => {
                value.parse::<num_bigint::BigInt>().ok().map(|value| -value)
            }
            _ => None,
        },
        _ => None,
    }
}

/// An `Integer` certificate refusal in the certificate's own terms: premises
/// and nodes by the zero-based indices the certificate cites them with.
fn describe_integer_arithmetic_check_error(
    error: &crate::kernel::proof::integer_arithmetic::IntegerArithmeticCheckError,
) -> String {
    use crate::kernel::proof::integer_arithmetic::IntegerArithmeticCheckError as Error;
    match error {
        Error::InvalidPremise(index) => format!("premise {index} is not a listed premise"),
        Error::InvalidNodeReference(index) => {
            format!("node {index} is referenced but is not an earlier node")
        }
        Error::UnsupportedPremise(index) => {
            format!("premise {index} is not a linear `Integer` claim")
        }
        Error::UnsupportedGoal => "the goal is not a linear `Integer` claim".to_string(),
        Error::NodeResultMismatch(index) => {
            format!("node {index} does not state what its rule derives from its inputs")
        }
        Error::InvalidCoefficient(index) => format!("node {index} uses an invalid coefficient"),
        Error::InvalidRelation(index) => {
            format!("node {index} combines relations its rule does not accept")
        }
        Error::WorkLimitExceeded => "checking exceeded the work limit".to_string(),
        Error::DoesNotFollow => "the conclusion node does not establish the goal".to_string(),
    }
}

/// As [`describe_integer_arithmetic_check_error`], for `signed_int32`.
fn describe_signed_arithmetic_check_error(
    error: &crate::kernel::proof::signed_arithmetic::SignedArithmeticCheckError,
) -> String {
    use crate::kernel::proof::signed_arithmetic::SignedArithmeticCheckError as Error;
    match error {
        Error::InvalidPremise(index) => format!("premise {index} is not a listed premise"),
        Error::InvalidNodeReference(index) => {
            format!("node {index} is referenced but is not an earlier node")
        }
        Error::UnsupportedCarrier => "a term is not a signed `int32` value".to_string(),
        Error::UnsupportedPremise(index) => {
            format!("premise {index} is not a signed `int32` claim")
        }
        Error::InvalidDefinedness(index) => {
            format!("node {index} lacks the definedness evidence its rule needs")
        }
        Error::InvalidOperator(index) => {
            format!("node {index} applies its rule to an operator it does not accept")
        }
        Error::InvalidCoefficient(index) => format!("node {index} uses an invalid coefficient"),
        Error::InvalidEndpoint(index) => format!("node {index} has an invalid interval endpoint"),
        Error::InvalidRelation(index) => {
            format!("node {index} combines relations its rule does not accept")
        }
        Error::NodeResultMismatch(index) => {
            format!("node {index} does not state what its rule derives from its inputs")
        }
        Error::Overflow(index) => format!("node {index} may overflow `int32`"),
        Error::DoesNotFollow => "the conclusion node does not establish the goal".to_string(),
    }
}

/// As [`describe_integer_arithmetic_check_error`], for the `rules` family.
fn describe_special_arithmetic_check_error(
    error: &crate::kernel::proof::arithmetic_special::SpecialArithmeticCheckError,
) -> String {
    use crate::kernel::proof::arithmetic_special::SpecialArithmeticCheckError as Error;
    match error {
        Error::InvalidIntegerCastIdentity(index) => format!(
            "node {index} requires an exact typed cast observation and two non-strict constant bounds on its source value, in lower/upper order, within the destination range"
        ),
        Error::InvalidIntegerProductBounds(index) => format!(
            "node {index} requires four non-strict bounds with constant endpoints on the product operands, in left-lower/upper then right-lower/upper order"
        ),
        Error::InvalidIntegerDivisionBounds(index) => format!(
            "node {index} requires four non-strict bounds with constant endpoints on the truncating quotient/remainder operands, in numerator-lower/upper then divisor-lower/upper order, with the divisor interval excluding zero"
        ),
        Error::InvalidIntegerMultiplyOrder(index) => format!(
            "node {index} requires exactly a <= b followed by 0 <= factor (preserving order) or factor <= 0 (reversing order), with exact Integer product operands"
        ),
        Error::InvalidIntegerQuotientBound(index) => format!(
            "node {index} requires an exact scaled numerator bound (bound * d <= n or n <= bound * d), followed by 1 <= d, for the claimed truncating quotient bound"
        ),
        Error::InvalidIntegerBoundExclusion(index) => format!(
            "node {index} requires one non-strict Integer bound with a constant endpoint strictly excluding the claimed unequal constant"
        ),
        Error::InvalidIntegerRelationTransport(index) => format!(
            "node {index} requires exactly an Integer equality and an equality or non-strict bound, then replaces one relation operand with its exact equal"
        ),
        Error::IntegerPolynomialLimitExceeded => "Integer polynomial identity exceeds its structural limits: 256 ring DAG nodes, 256 monomials, degree 16, or 4096-bit coefficients".to_string(),
        Error::InvalidIntegerPolynomialIdentity(index) => format!(
            "node {index} requires a true Integer polynomial identity and an empty bounds list (at most 256 ring DAG nodes, 256 monomials, degree 16, and 4096-bit coefficients)"
        ),
        Error::InvalidIntegerQuotientShift(index) => format!(
            "node {index} requires quotient(x + d * k, d) == quotient(x, d) + k, a positive constant d, and exactly the named bounds 0 <= x and 0 <= k"
        ),
        Error::InvalidPremise(index) => format!("premise {index} is not a listed premise"),
        Error::InvalidNodeReference(index) => {
            format!("node {index} is referenced but is not an earlier node")
        }
        Error::InvalidOperator(index) => {
            format!("node {index} applies its rule to an operator it does not accept")
        }
        Error::NodeResultMismatch(index) => {
            format!("node {index} does not state what its rule derives from its inputs")
        }
        Error::WorkLimitExceeded => "checking exceeded the work limit".to_string(),
        Error::DoesNotFollow => "the conclusion node does not establish the goal".to_string(),
        Error::SignedDefinedBoundUnrelated { node, premise, .. } => format!(
            "node {node}: premise {premise} is not a constant order or equality fact on an operand"
        ),
        Error::SignedDefinedRangeExceeded {
            node, lower, upper, ..
        } => format!("node {node} puts the exact result in [{lower}, {upper}], outside its width"),
    }
}

/// A step that adds a fact closes a proposition goal it added, as `extract`
/// does. A goal that was already available before the step stays open.
fn close_goal_from_added_fact(state: KernelProofHandle) -> KernelProofHandle {
    state.closed_if_goal_was_added().unwrap_or(state)
}
