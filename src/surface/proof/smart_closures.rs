//! Smart closure search and linear script interpretation.
mod address_words;
mod integer_algebra;
mod integer_composition;
mod pointer_offsets;
mod quotient_shifts;
mod signed_intervals;
mod specialized;
use crate::kernel::MachineCastSpelling;
use crate::kernel::binary_term;
use crate::kernel::{bits32_constant, constant_u32, int64_constant, uint64_constant};
use crate::surface::planning::solve::{SolveEvidence, plan_solve_certificate};

use super::selected_arithmetic::RewriteClosers;
use super::*;
use crate::kernel::FloatCondition;
use crate::kernel::proof::arithmetic_special::signed_definedness_operands;
use crate::kernel::proof::integer_arithmetic::{
    IntegerAffineClaim, IntegerAffineRelation, IntegerArithmeticNode, IntegerArithmeticPlan,
    integer_affine_claim,
};
use crate::kernel::proof::signed_arithmetic::{
    SignedArithmeticClaim, SignedArithmeticComparison, SignedArithmeticNode,
    SignedArithmeticRelation,
};
use crate::kernel::proof::{
    PropositionIdentityKey, proposition_identity_key, propositions_are_alpha_equal,
};
use crate::kernel::{CompareRelation, OverflowOperation};
use crate::kernel::{MachineBinaryOp, MachineIntegerType};
use crate::surface::checking::{ArithmeticEngine, ArithmeticPlan, plan_arithmetic};
use crate::surface::checking::{IntegerRefutation, machine_observations, refute_integer_goal};
use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};
use proof_object::{collect_surface_conjunct_leaves, frontier_premise_anchor};

const MAX_SOLVE_SOURCE_PREMISES: usize = 64;

/// Constant bounds on the goal's own variables, without relational bounds
/// such as earlier postconditions that also mention those variables.
fn indexed_constant_arithmetic_premises(
    assumptions: &PureFactContext,
    goal: &Proposition,
) -> Vec<Proposition> {
    let canonical = crate::kernel::canonical_condition_fact(goal);
    let mut selected = BTreeSet::new();
    for variable in crate::kernel::proposition_variables(&canonical) {
        selected.extend(assumptions.signed_constant_bound_facts(
            crate::kernel::SignedDefinedWidth::Int32,
            &MachineTerm::Variable(variable),
        ));
    }
    selected.into_iter().collect()
}

/// Equality of mathematical observations requires equality modulo the word
/// width, even if an operation wraps. This is only a search refusal hint;
/// it creates neither a kernel equality nor a definedness fact.
fn incompatible_machine_offsets(
    left: &crate::kernel::IntegerTerm,
    right: &crate::kernel::IntegerTerm,
) -> bool {
    use crate::kernel::IntegerTerm;
    fn offset(term: &IntegerTerm) -> Option<(MachineIntegerType, MachineTerm, BigInt)> {
        match term {
            IntegerTerm::Add(base, delta) | IntegerTerm::Subtract(base, delta)
                if delta.as_const().is_some() =>
            {
                let (format, base, value) = offset(base)?;
                let delta = delta.as_const()?;
                Some((
                    format,
                    base,
                    if matches!(term, IntegerTerm::Subtract(..)) {
                        value - delta
                    } else {
                        value + delta
                    },
                ))
            }
            IntegerTerm::Add(delta, base) if delta.as_const().is_some() => {
                let (format, base, value) = offset(base)?;
                Some((format, base, value + delta.as_const()?))
            }
            IntegerTerm::Machine(machine) => {
                let format = machine.ty();
                let mut base = machine.value();
                let mut delta = BigInt::zero();
                while let MachineTerm::Binary {
                    format: operation_format,
                    op,
                    left,
                    right,
                } = base
                {
                    if *operation_format != format
                        || !matches!(op, MachineBinaryOp::Add | MachineBinaryOp::Subtract)
                    {
                        break;
                    }
                    let Some(value) = IntegerTerm::from_machine(format, right.as_ref().clone())
                        .and_then(|term| term.as_const().cloned())
                    else {
                        break;
                    };
                    delta += if *op == MachineBinaryOp::Subtract {
                        -value
                    } else {
                        value
                    };
                    base = left;
                }
                Some((format, base.clone(), delta))
            }
            _ => None,
        }
    }
    let (Some((a_format, a_base, a_delta)), Some((b_format, b_base, b_delta))) =
        (offset(left), offset(right))
    else {
        return false;
    };
    a_format == b_format
        && a_base == b_base
        && !((a_delta - b_delta) % (BigInt::one() << a_format.format().bits())).is_zero()
}

fn is_reflexive_pointer_equality(mut proposition: &Proposition) -> bool {
    let mut positive = true;
    while let Proposition::Not(inner) = proposition {
        proposition = inner;
        positive = !positive;
    }
    matches!(&proposition, condition_source_0 @ Proposition::ConditionIs(_, value) if matches!(condition_source_0.condition_native(), Some((ConditionTerm::AddressEqual(left, right), _)) if (*value == positive && left == right)))
        || matches!(&proposition, condition_source_0 @ Proposition::ConditionIs(_, value) if matches!(condition_source_0.condition_native(), Some((ConditionTerm::PointerEqual(left, right), _)) if (*value == positive && left == right)))
}

fn collect_signed_surface_terms<'a>(
    expression: &'a ContractExpression,
    terms: &mut Vec<&'a ContractExpression>,
) {
    let mut pending = vec![expression];
    while let Some(expression) = pending.pop() {
        terms.push(expression);
        match expression {
            ContractExpression::IntegerContext(value) => pending.push(value),

            ContractExpression::Proposition(proposition) => {
                collect_signed_surface_proposition_terms(proposition, terms)
            }
            ContractExpression::Resource(_) => {}
            ContractExpression::Lambda { .. } => {}
            ContractExpression::Apply {
                function,
                arguments,
            } => {
                pending.push(function);
                pending.extend(arguments);
            }

            ContractExpression::CUnary { operand: inner, .. }
            | ContractExpression::Negate(inner)
            | ContractExpression::Old(inner)
            | ContractExpression::At {
                expression: inner, ..
            }
            | ContractExpression::BitwiseNot(inner) => pending.push(inner),
            ContractExpression::Add(left, right)
            | ContractExpression::Subtract(left, right)
            | ContractExpression::Multiply(left, right)
            | ContractExpression::Divide(left, right)
            | ContractExpression::Remainder(left, right)
            | ContractExpression::ShiftLeft(left, right)
            | ContractExpression::RustShiftLeft(left, right)
            | ContractExpression::ShiftRight(left, right)
            | ContractExpression::RustShiftRight(left, right)
            | ContractExpression::BitwiseAnd(left, right)
            | ContractExpression::BitwiseOr(left, right)
            | ContractExpression::BitwiseXor(left, right)
            | ContractExpression::SequenceConcat(left, right)
            | ContractExpression::Index(left, right) => {
                pending.push(right);
                pending.push(left);
            }
            ContractExpression::AlgebraicConstructor { arguments, .. }
            | ContractExpression::Call { arguments, .. }
            | ContractExpression::SequenceLiteral(arguments) => {
                for argument in arguments {
                    pending.push(argument);
                }
            }
            ContractExpression::MethodCall {
                receiver,
                arguments,
                ..
            } => {
                pending.push(receiver);
                for argument in arguments {
                    pending.push(argument);
                }
            }
            ContractExpression::Field { base, .. }
            | ContractExpression::ArrayIndex { base, .. } => pending.push(base),
            ContractExpression::If {
                condition,
                then_branch,
                else_branch,
            } => {
                pending.push(then_branch);
                pending.push(else_branch);
                collect_signed_surface_proposition_terms(condition, terms);
            }
            ContractExpression::RangeFold {
                start,
                end,
                initial,
                body,
                ..
            } => {
                pending.push(body);
                pending.push(initial);
                pending.push(end);
                pending.push(start);
            }
            ContractExpression::Let { value, body, .. } => {
                pending.push(body);
                pending.push(value);
            }
            ContractExpression::AlgebraicMatch { scrutinee, arms } => {
                pending.push(scrutinee);
                for arm in arms {
                    pending.push(&arm.body);
                }
            }
            ContractExpression::QualifiedC { .. }
            | ContractExpression::ResourceField(_)
            | ContractExpression::AlgebraicVariable { .. }
            | ContractExpression::Binding(_)
            | ContractExpression::ProgramExpression(_)
            | ContractExpression::ProgramBinding(_)
            | ContractExpression::RegionResult(_)
            | ContractExpression::RegionAllocation(_)
            | ContractExpression::RegionParameter { .. }
            | ContractExpression::ResourceCount(_)
            | ContractExpression::ResourceWildcard
            | ContractExpression::IntegerLiteral(_) => {}
        }
    }
}

// Arithmetic combinations may mix states. Put each selector on its
// operands so generated comparisons keep those states when combined.
fn surface_comparison_with_anchored_operands(proposition: &ClickProposition) -> ClickProposition {
    let mut inner = proposition;
    let mut selectors = Vec::new();
    let mut negated = false;
    loop {
        match inner {
            ClickProposition::At {
                selector,
                proposition,
            } => {
                selectors.push(selector);
                inner = proposition;
            }
            ClickProposition::Not(proposition) => {
                negated = !negated;
                inner = proposition;
            }
            _ => break,
        }
    }
    let ClickProposition::Comparison {
        left,
        operator,
        right,
    } = inner
    else {
        return proposition.clone();
    };
    let operator = if negated {
        match operator {
            ComparisonOperator::LessEqual => ComparisonOperator::GreaterThan,
            ComparisonOperator::LessThan => ComparisonOperator::GreaterEqual,
            ComparisonOperator::GreaterEqual => ComparisonOperator::LessThan,
            ComparisonOperator::GreaterThan => ComparisonOperator::LessEqual,
            ComparisonOperator::Equal => ComparisonOperator::NotEqual,
            ComparisonOperator::NotEqual => ComparisonOperator::Equal,
            ComparisonOperator::In => return proposition.clone(),
        }
    } else {
        *operator
    };
    let anchor = |expression: &ContractExpression| {
        selectors
            .iter()
            .rev()
            .fold(expression.clone(), |expression, selector| {
                ContractExpression::At {
                    selector: (*selector).clone(),
                    expression: Box::new(expression),
                }
            })
    };
    ClickProposition::Comparison {
        left: anchor(left),
        operator,
        right: anchor(right),
    }
}

fn collect_signed_surface_proposition_terms<'a>(
    proposition: &'a ClickProposition,
    terms: &mut Vec<&'a ContractExpression>,
) {
    let mut pending = vec![proposition];
    while let Some(proposition) = pending.pop() {
        match proposition {
            ClickProposition::Value(expression) => collect_signed_surface_terms(expression, terms),
            ClickProposition::Comparison { left, right, .. } => {
                collect_signed_surface_terms(left, terms);
                collect_signed_surface_terms(right, terms);
            }
            ClickProposition::Defined { expression }
            | ClickProposition::FloatClassification { expression, .. } => {
                collect_signed_surface_terms(expression, terms)
            }
            ClickProposition::At { proposition, .. }
            | ClickProposition::Not(proposition)
            | ClickProposition::ForAll {
                body: proposition, ..
            }
            | ClickProposition::Exists {
                body: proposition, ..
            } => pending.push(proposition),
            ClickProposition::And(left, right)
            | ClickProposition::Or(left, right)
            | ClickProposition::Implies(left, right) => {
                pending.push(right);
                pending.push(left);
            }
            ClickProposition::RangeAll {
                start, end, body, ..
            }
            | ClickProposition::RangeAny {
                start, end, body, ..
            } => {
                collect_signed_surface_terms(start, terms);
                collect_signed_surface_terms(end, terms);
                pending.push(body);
            }
            ClickProposition::Separate { .. }
            | ClickProposition::ResourceViewable { .. }
            | ClickProposition::Contains { .. }
            | ClickProposition::Loadable { .. }
            | ClickProposition::PredicateCall { .. } => {}
        }
    }
}

/// The spelling of a certificate's `int32` atom by a source expression that
/// names it. An 8- or 16-bit value's atom is its `int32` widening, so an
/// expression of the narrow value is spelled with its explicit cast,
/// `(x as int32)`: arithmetic over the narrow expression itself would
/// re-lower at its own width, not as the certificate's `int32` arithmetic.
/// An expression that already is a cast to `int32` is kept.
fn int32_widening_spelling(
    term: &crate::kernel::MachineTerm,
    candidate: ContractExpression,
) -> ContractExpression {
    let widening = matches!(
        term,
        crate::kernel::MachineTerm::Cast { spelling: MachineCastSpelling::Generic,
            from: source,
            to: crate::kernel::MachineIntegerType::Int32,
            ..
        } if source.format().bits() < 32
    );
    let already_cast = matches!(
        &candidate,
        ContractExpression::CUnary {
            lowered: ProgramExpression::Cast {
                target_type: crate::kernel::ProgramType::Int32,
                ..
            },
            ..
        }
    );
    if !widening || already_cast {
        return candidate;
    }
    ContractExpression::CUnary {
        operand: Box::new(candidate),
        lowered: ProgramExpression::Cast {
            expression: Box::new(ProgramExpression::Value(crate::kernel::int32(0))),
            target_type: crate::kernel::ProgramType::Int32,
            integer_mode: crate::kernel::IntegerCastMode::CConversion,
            pointee_struct: None,
            pointee_volatile: false,
            pointee_constant: false,
            explicit_qualification: false,
        },
    }
}

/// Whether a written operand is an exact observation, `to_integer(x)`, or
/// Integer arithmetic over one: its value is the Integer the observation
/// reads, not a machine value.
pub(in crate::surface::proof) fn observes_exact_value(operand: &ContractExpression) -> bool {
    match operand {
        ContractExpression::Call { name, .. } => name == "to_integer",
        ContractExpression::Add(left, right)
        | ContractExpression::Subtract(left, right)
        | ContractExpression::Multiply(left, right) => {
            observes_exact_value(left) || observes_exact_value(right)
        }
        ContractExpression::Negate(inner)
        | ContractExpression::Old(inner)
        | ContractExpression::At {
            expression: inner, ..
        } => observes_exact_value(inner),
        _ => false,
    }
}

/// The Integer spelling of a premise whose kernel form is a native
/// comparison: `a < b` as `to_integer(a) < to_integer(b)`. A comparison of
/// exact observations is that native comparison, so the spelling lowers to
/// the same fact, and the Integer nodes built from it combine Integer
/// operands rather than wrapping machine arithmetic. Any other premise keeps
/// its written spelling.
/// [`observed_native_surface_comparison`] for a step this proof prints: only
/// a comparison with arithmetic is respelled, since that is the one a reader
/// with Integer arithmetic would read differently. `x >= 0` reads the same
/// either way and keeps its spelling.
pub(super) fn observed_native_arithmetic(
    kernel: &Proposition,
    written: &ClickProposition,
) -> ClickProposition {
    fn arithmetic(expression: &ContractExpression) -> bool {
        match expression {
            ContractExpression::Add(..)
            | ContractExpression::Subtract(..)
            | ContractExpression::Multiply(..) => true,
            ContractExpression::Negate(inner) => {
                !matches!(inner.as_ref(), ContractExpression::IntegerLiteral(_))
            }
            ContractExpression::Old(inner)
            | ContractExpression::At {
                expression: inner, ..
            } => arithmetic(inner),
            _ => false,
        }
    }
    let comparison = match written {
        ClickProposition::Not(inner) => inner.as_ref(),
        other => other,
    };
    match comparison {
        ClickProposition::Comparison { left, right, .. }
            if (arithmetic(left) || arithmetic(right))
                && !observes_exact_value(left)
                && !observes_exact_value(right) =>
        {
            observed_native_surface_comparison(kernel, written)
        }
        _ => written.clone(),
    }
}

pub(super) fn observed_native_surface_comparison(
    kernel: &Proposition,
    written: &ClickProposition,
) -> ClickProposition {
    // Expose a literal proposition lambda's comparison while retaining its
    // typed argument bindings on each operand. This is the same beta
    // reduction ordinary proposition lowering performs.
    fn comparison_value(expression: &ContractExpression) -> Option<ClickProposition> {
        let expression = lambdas::reduce_head_fully(expression).ok()?;
        match expression.as_ref() {
            ContractExpression::Proposition(proposition) => Some(proposition.as_ref().clone()),
            ContractExpression::Let {
                name,
                click_type,
                value,
                body,
            } => {
                let ClickProposition::Comparison {
                    left,
                    operator,
                    right,
                } = comparison_value(body)?
                else {
                    return None;
                };
                let bind = |body| ContractExpression::Let {
                    name: name.clone(),
                    click_type: click_type.clone(),
                    value: value.clone(),
                    body: Box::new(body),
                };
                Some(ClickProposition::Comparison {
                    left: bind(left),
                    operator,
                    right: bind(right),
                })
            }
            _ => None,
        }
    }
    let exposed;
    let written = if let ClickProposition::Value(expression) = written {
        exposed = comparison_value(expression);
        exposed.as_ref().unwrap_or(written)
    } else {
        written
    };
    let negated;
    let kernel = match kernel {
        Proposition::Not(inner) => match inner.as_ref() {
            Proposition::ConditionIs(condition, value) => {
                negated = Proposition::condition_is(condition.clone(), !value);
                &negated
            }
            _ => kernel,
        },
        _ => kernel,
    };
    // The kernel form is a native comparison with an Integer reading (a
    // promoted comparison of widenings among them), or that Integer reading
    // itself, spelled by the native fact it reads. A 128-bit comparison is
    // held in its Integer reading, so the native fact written `a < b` is
    // that reading too.
    if crate::kernel::machine_integer::comparison::integer_readings_with_promotions(kernel)
        .is_empty()
        && !matches!(kernel, Proposition::ConditionIs(condition, _)
            if crate::kernel::machine_integer::comparison::structural_comparison_view(condition.native_compat()).is_some())
        && !crate::kernel::machine_integer::comparison::reads_wide_integer_observations(kernel)
    {
        return written.clone();
    }
    // A native comparison promotes byte and short operands to int32.
    // Preserve that carrier when its sides become Integer observations;
    // observing the original narrow source instead changes the certificate.
    let native_int32 = matches!(kernel, Proposition::ConditionIs(condition, _)
        if crate::kernel::machine_integer::comparison::structural_comparison_view(condition.native_compat())
            .is_some_and(|view| view.format == MachineIntegerType::Int32));
    // An operand already written as an Integer (an unsuffixed literal, an
    // observation, or arithmetic over one) keeps its spelling.
    // A literal inside machine arithmetic, the `1` of `value + 1`, is typed
    // by that arithmetic; only an observation makes it Integer arithmetic.
    fn written_integer(operand: &ContractExpression) -> bool {
        match operand {
            ContractExpression::IntegerContext(_) => true,
            // An authored Integer let can supply the same sort context.
            // Observing it again would place an Integer inside a machine cast.
            ContractExpression::Let {
                name,
                click_type: Some(ClickType::Integer),
                body,
                ..
            } if matches!(body.as_ref(), ContractExpression::Binding(value) if value == name) => {
                true
            }
            // A theorem's `let n: int32 = v + 1;` binds a machine value, but
            // a body written as an Integer, `to_integer(n)`, is the operand's
            // value. Observing the whole `let` again would place that Integer
            // inside a machine cast.
            ContractExpression::Let { body, .. } => written_integer(body),
            ContractExpression::IntegerLiteral(_) => true,
            ContractExpression::Negate(inner)
            | ContractExpression::Old(inner)
            | ContractExpression::At {
                expression: inner, ..
            } => written_integer(inner),
            _ => observes_exact_value(operand),
        }
    }
    // A read at a state is observed there, `at(s, to_integer(x))`, which
    // lowers to the same read as the fact; `to_integer(at(s, x))` reads `x`
    // anew.
    fn observe_operand(operand: &ContractExpression, native_int32: bool) -> ContractExpression {
        match operand {
            ContractExpression::At {
                selector,
                expression,
            } => ContractExpression::At {
                selector: selector.clone(),
                expression: Box::new(observe_operand(expression, native_int32)),
            },
            ContractExpression::Old(inner) => {
                ContractExpression::Old(Box::new(observe_operand(inner, native_int32)))
            }
            _ => ContractExpression::Call {
                name: "to_integer".to_string(),
                arguments: vec![if native_int32 {
                    native_int32_split_operand(operand.clone())
                } else {
                    operand.clone()
                }],
            },
        }
    }
    let observe = |operand: &ContractExpression| {
        if written_integer(operand) {
            operand.clone()
        } else {
            observe_operand(operand, native_int32)
        }
    };
    fn observed(
        written: &ClickProposition,
        observe: &dyn Fn(&ContractExpression) -> ContractExpression,
    ) -> ClickProposition {
        match written {
            ClickProposition::Comparison {
                left,
                operator,
                right,
            } => ClickProposition::Comparison {
                left: observe(left),
                operator: *operator,
                right: observe(right),
            },
            ClickProposition::Not(inner) => {
                ClickProposition::Not(Box::new(observed(inner, observe)))
            }
            ClickProposition::At {
                selector,
                proposition,
            } => ClickProposition::At {
                selector: selector.clone(),
                proposition: Box::new(observed(proposition, observe)),
            },
            other => other.clone(),
        }
    }
    observed(written, &observe)
}

/// The spelling `bounds` gives the node with this source, value, and
/// direction.
fn spelled_bound(
    bounds: &[SpelledBound],
    source: BoundSource,
    value: &crate::kernel::IntegerTerm,
    upper: bool,
) -> Option<ClickProposition> {
    bounds
        .iter()
        .find(|(kind, observed, bound, _)| *kind == source && observed == value && *bound == upper)
        .map(|(.., surface)| surface.clone())
}

fn integer_surface_ordered_parts(
    proposition: &ClickProposition,
) -> Option<(ContractExpression, ComparisonOperator, ContractExpression)> {
    let ClickProposition::Comparison {
        left,
        operator,
        right,
    } = proposition
    else {
        return None;
    };
    match operator {
        ComparisonOperator::Equal | ComparisonOperator::LessEqual => {
            Some((left.clone(), *operator, right.clone()))
        }
        ComparisonOperator::GreaterEqual => {
            Some((right.clone(), ComparisonOperator::LessEqual, left.clone()))
        }
        ComparisonOperator::LessThan => Some((left.clone(), *operator, right.clone())),
        // `a > 0` is the ordered pair of `0 < a`, exactly as `a >= 0` is the
        // ordered pair of `0 <= a`.  Handing back the "greater" spelling's
        // sides unswapped paired the wrong sides of two addends, so the sum
        // of `a > 0` and `b >= 0` printed as `(a + 0) < (0 + b)` instead of
        // `(0 + 0) < (a + b)` and no longer lowered to the kernel's sum.
        ComparisonOperator::GreaterThan => {
            Some((right.clone(), ComparisonOperator::LessThan, left.clone()))
        }
        ComparisonOperator::NotEqual | ComparisonOperator::In => None,
    }
}

/// Over the integers `l < r` is `l + 1 <= r`, and the kernel's affine claim
/// for a strict bound already carries that `+ 1`. Spelling a scaled or
/// summed strict bound in that non-strict form keeps the written result
/// equal to the claim the kernel derives: `c * (l + 1) <= c * r`, not the
/// weaker `c * l < c * r`.
fn integer_surface_non_strict_parts(
    proposition: &ClickProposition,
) -> Option<(ContractExpression, ComparisonOperator, ContractExpression)> {
    let (left, operator, right) = integer_surface_ordered_parts(proposition)?;
    Some(if operator == ComparisonOperator::LessThan {
        (
            ContractExpression::Add(
                Box::new(left),
                Box::new(ContractExpression::IntegerLiteral("1".into())),
            ),
            ComparisonOperator::LessEqual,
            right,
        )
    } else {
        (left, operator, right)
    })
}

fn integer_plan_surface_scale(
    proposition: &ClickProposition,
    coefficient: &BigInt,
) -> Option<ClickProposition> {
    if coefficient.is_one() {
        return integer_surface_scale(proposition, coefficient);
    }
    let (left, operator, right) = integer_surface_non_strict_parts(proposition)?;
    integer_surface_scale(
        &ClickProposition::Comparison {
            left,
            operator,
            right,
        },
        coefficient,
    )
}

fn integer_plan_surface_add(
    left: &ClickProposition,
    right: &ClickProposition,
) -> Option<ClickProposition> {
    let strict = |proposition| {
        matches!(
            integer_surface_ordered_parts(proposition),
            Some((_, ComparisonOperator::LessThan, _))
        )
    };
    if !(strict(left) && strict(right)) {
        return integer_surface_add(left, right);
    }
    let non_strict = |proposition| {
        let (left, operator, right) = integer_surface_non_strict_parts(proposition)?;
        Some(ClickProposition::Comparison {
            left,
            operator,
            right,
        })
    };
    integer_surface_add(&non_strict(left)?, &non_strict(right)?)
}

fn integer_surface_scale(
    proposition: &ClickProposition,
    coefficient: &BigInt,
) -> Option<ClickProposition> {
    let (left, operator, right) = integer_surface_ordered_parts(proposition)?;
    if operator == ComparisonOperator::LessEqual && coefficient.is_negative() {
        return None;
    }
    let coefficient = surface_signed_integer_literal(coefficient);
    let multiply = |expression| {
        ContractExpression::Multiply(Box::new(coefficient.clone()), Box::new(expression))
    };
    Some(ClickProposition::Comparison {
        left: multiply(left),
        operator,
        right: multiply(right),
    })
}

/// Build a parseable source expression for a signed integer without relying
/// on a negative `IntegerLiteral` token.  In particular, `i32::MIN` must be
/// represented as `Negate(2147483648)`, since its magnitude is not an i32
/// literal even though the signed expression is valid.
fn surface_signed_integer_literal(value: &BigInt) -> ContractExpression {
    if value.is_negative() {
        ContractExpression::Negate(Box::new(ContractExpression::IntegerLiteral(
            value.abs().to_string(),
        )))
    } else {
        ContractExpression::IntegerLiteral(value.to_string())
    }
}

fn integer_surface_add(
    left: &ClickProposition,
    right: &ClickProposition,
) -> Option<ClickProposition> {
    // One strict addend carries the claim's `+ 1`, so `l1 + l2 < r1 + r2`
    // spells the sum. Two strict addends carry `+ 2`, which a single `<`
    // cannot spell; write both in their non-strict form instead.
    let (left_left, operator, left_right) = integer_surface_ordered_parts(left)?;
    let (right_left, right_operator, right_right) = integer_surface_ordered_parts(right)?;
    let operator = match (operator, right_operator) {
        (ComparisonOperator::LessEqual, ComparisonOperator::LessEqual) => {
            ComparisonOperator::LessEqual
        }
        // `integer_surface_ordered_parts` never hands back a "greater"
        // spelling, so a strict addend is always `LessThan` here.
        (ComparisonOperator::LessThan, _) | (_, ComparisonOperator::LessThan) => {
            ComparisonOperator::LessThan
        }
        _ if operator == right_operator => operator,
        _ => return None,
    };
    Some(ClickProposition::Comparison {
        left: ContractExpression::Add(Box::new(left_left), Box::new(right_left)),
        operator,
        right: ContractExpression::Add(Box::new(left_right), Box::new(right_right)),
    })
}

fn integer_surface_transitive(
    left: &ClickProposition,
    right: &ClickProposition,
) -> Option<ClickProposition> {
    let (left_start, left_operator, left_end) = integer_surface_ordered_parts(left)?;
    let (right_start, right_operator, right_end) = integer_surface_ordered_parts(right)?;
    let operator = if matches!(left_operator, ComparisonOperator::LessThan)
        || matches!(right_operator, ComparisonOperator::LessThan)
    {
        ComparisonOperator::LessThan
    } else if left_operator == ComparisonOperator::LessEqual
        && right_operator == ComparisonOperator::LessEqual
    {
        ComparisonOperator::LessEqual
    } else {
        return None;
    };
    let (start, end) = if left_end == right_start {
        (left_start, right_end)
    } else if right_end == left_start {
        (right_start, left_end)
    } else {
        return None;
    };
    Some(ClickProposition::Comparison {
        left: start,
        operator,
        right: end,
    })
}

/// Keep a normalized zero affine claim in a form that direct lowering does
/// not constant-fold to an equality.  `0 <= 0` is mathematically the same
/// claim, but some lowering paths canonicalize that literal proposition as
/// `0 == 0`, changing the signed relation carried by an Add node.  Reusing an
/// already lowered child expression gives `e <= e`, whose affine difference
/// is still exactly zero while preserving the non-strict relation.
///
/// The reused expression must not itself be a constant.  An addend such as
/// `parity >= 0` orders as `0 <= parity`, so taking its first operand printed
/// the very literal proposition this shape exists to avoid, and the Add node
/// the planner had already accepted failed to re-verify.  The two addends
/// cancel, so any one of their four operands names a value whose difference
/// with itself is zero; take the first that direct lowering will not fold.
fn integer_surface_zero_claim(
    left: &ClickProposition,
    right: &ClickProposition,
) -> Option<ClickProposition> {
    let (left_left, _, left_right) = integer_surface_ordered_parts(left)?;
    let (right_left, _, right_right) = integer_surface_ordered_parts(right)?;
    let witness = [left_left, left_right, right_left, right_right]
        .into_iter()
        .find(|expression| !surface_expression_is_constant(expression))?;
    Some(ClickProposition::Comparison {
        left: witness.clone(),
        operator: ComparisonOperator::LessEqual,
        right: witness,
    })
}

/// Whether direct lowering reads this expression as a literal constant.
///
/// A state does not change a literal's value, so `at(<point>, 0)` folds
/// exactly as a bare `0` does; look through one.  This is a syntactic test on
/// one already built expression, not a lowering.
fn surface_expression_is_constant(expression: &ContractExpression) -> bool {
    match expression {
        ContractExpression::IntegerLiteral(_) => true,
        ContractExpression::ProgramExpression(crate::kernel::ProgramExpression::Value(_)) => true,
        ContractExpression::Negate(inner) => surface_expression_is_constant(inner),
        ContractExpression::At { expression, .. } | ContractExpression::Old(expression) => {
            surface_expression_is_constant(expression)
        }
        _ => false,
    }
}

fn integer_surface_equality_to_less_equal(
    proposition: &ClickProposition,
    reverse: bool,
) -> Option<ClickProposition> {
    let (left, operator, right) = integer_surface_ordered_parts(proposition)?;
    if operator != ComparisonOperator::Equal {
        return None;
    }
    let (left, right) = if reverse {
        (right, left)
    } else {
        (left, right)
    };
    Some(ClickProposition::Comparison {
        left,
        operator: ComparisonOperator::LessEqual,
        right,
    })
}

fn integer_surface_equality_from_bounds(
    lower: &ClickProposition,
    upper: &ClickProposition,
) -> Option<ClickProposition> {
    let (lower_left, lower_operator, lower_right) = integer_surface_ordered_parts(lower)?;
    let (upper_left, upper_operator, upper_right) = integer_surface_ordered_parts(upper)?;
    if lower_operator != ComparisonOperator::LessEqual
        || upper_operator != ComparisonOperator::LessEqual
        || lower_left != upper_right
        || lower_right != upper_left
    {
        return None;
    }
    Some(ClickProposition::Comparison {
        left: lower_left,
        operator: ComparisonOperator::Equal,
        right: lower_right,
    })
}

/// `l <= r` sharpened by a disequality on the same two values is `l < r`.
///
/// The result is spelled from the bound's own sides. The disequality is not
/// compared syntactically: two spellings of one kernel term, such as a value
/// read at two states the body did not separate, are the same premise to
/// the checker, and the kernel node checks that the disequality names the
/// bound's affine form. Pairing the printed operands here discarded plans the
/// kernel had already accepted.
fn integer_surface_strict_from_disequal(bound: &ClickProposition) -> Option<ClickProposition> {
    let (left, operator, right) = integer_surface_ordered_parts(bound)?;
    if operator != ComparisonOperator::LessEqual {
        return None;
    }
    Some(ClickProposition::Comparison {
        left,
        operator: ComparisonOperator::LessThan,
        right,
    })
}

/// The connected facts an identity closure reads for operand spellings when
/// the goal and the cited facts spell none.
const MAX_SOLVER_SPELLING_FACTS: usize = 32;

/// The outcome of spelling a refutation for its source certificate.
/// Source spellings a selected-premise arithmetic closure resolved, by fact.
type SpellingCache = std::cell::RefCell<
    std::collections::BTreeMap<Proposition, Option<(Proposition, ClickProposition)>>,
>;

/// A certificate node that cites no premise's spelling for its bound: a
/// machine value's type range, an operation's bound from its operand, or
/// the bound a cited disequality with a type endpoint gives.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::surface::proof) enum BoundSource {
    TypeRange,
    Operation,
    Excluded(usize),
}

/// The written spelling of one such bound, for the node with this source,
/// value, and direction.
pub(in crate::surface::proof) type SpelledBound = (
    BoundSource,
    crate::kernel::IntegerTerm,
    bool,
    ClickProposition,
);

enum Spelling {
    Spelled(Vec<(Proposition, ClickProposition)>, Vec<SpelledBound>),
    /// A native comparison read as an Integer one has no spelling.
    UnspelledReading(Proposition),
    /// A machine observation's type range has no spelling.
    UnspelledRange(crate::kernel::IntegerTerm),
    /// An operation's or a disequality's bound has no spelling.
    UnspelledBound,
}

/// `written`, with `to_integer(a)` added for each written
/// `to_integer(a / b)`, `to_integer(a % b)`, and `to_integer(a >> b)`: the
/// operand an operation bound reads. One pass over `written`.
fn with_operation_operands(written: &[ContractExpression]) -> Vec<ContractExpression> {
    let mut extended = written.to_vec();
    for expression in written {
        let ContractExpression::Call { name, arguments } = expression else {
            continue;
        };
        let [argument] = arguments.as_slice() else {
            continue;
        };
        if name != "to_integer" {
            continue;
        }
        let operand = match argument {
            ContractExpression::Divide(operand, _)
            | ContractExpression::Remainder(operand, _)
            | ContractExpression::ShiftRight(operand, _)
            | ContractExpression::RustShiftRight(operand, _) => operand.as_ref().clone(),
            ContractExpression::ProgramExpression(
                ProgramExpression::Divide(operand, _)
                | ProgramExpression::Remainder(operand, _)
                | ProgramExpression::ShiftRight(operand, _)
                | ProgramExpression::RustShiftRight(operand, _),
            ) => ContractExpression::ProgramExpression(operand.as_ref().clone()),
            _ => continue,
        };
        let observed = ContractExpression::Call {
            name: "to_integer".into(),
            arguments: vec![operand],
        };
        if !extended.contains(&observed) {
            extended.push(observed);
        }
    }
    extended
}

/// The distinct `to_integer(...)` expressions written in `surfaces`.
fn written_integer_observations<'s>(
    surfaces: impl Iterator<Item = &'s ClickProposition>,
) -> Vec<ContractExpression> {
    written_integer_observations_with_entry(surfaces, true)
}

fn written_integer_observations_with_entry<'s>(
    surfaces: impl Iterator<Item = &'s ClickProposition>,
    include_entry: bool,
) -> Vec<ContractExpression> {
    let mut written: Vec<ContractExpression> = Vec::new();
    for surface in surfaces {
        // A native comparison such as `amount <= count(...)` spells the
        // Integer observations of its operands; one read at a state, as a
        // precondition `at(entry, 1u64 <= x)`, spells them at that state.
        let (selector, comparison) = match surface {
            ClickProposition::At {
                selector,
                proposition,
            } => (Some(selector), proposition.as_ref()),
            surface => (None, surface),
        };
        // A negated comparison names the same operands, including when
        // its retained kernel condition needs no separate native reading.
        let comparison = match comparison {
            ClickProposition::Not(inner)
                if matches!(inner.as_ref(), ClickProposition::Comparison { .. }) =>
            {
                inner.as_ref()
            }
            comparison => comparison,
        };
        if let ClickProposition::Comparison { left, right, .. } = comparison {
            for side in [left, right] {
                if matches!(side, ContractExpression::IntegerLiteral(_)) || observed_integer(side) {
                    continue;
                }
                let side = match selector {
                    Some(selector) => ContractExpression::At {
                        selector: selector.clone(),
                        expression: Box::new(side.clone()),
                    },
                    None => side.clone(),
                };
                // Preserve an observation's state selector. Observing an
                // already observed Integer again hides the native operand
                // from explicit definedness proofs.
                let observed = if integer_composition::observed_argument(&side).is_some() {
                    side
                } else if observes_exact_value(&side) {
                    continue;
                } else {
                    ContractExpression::Call {
                        name: "to_integer".into(),
                        arguments: vec![side],
                    }
                };
                if !written.contains(&observed) {
                    written.push(observed);
                }
            }
        }
        crate::surface::proof::fixed_state_proofs::conversion_conditions::walk_written_expressions_in_proposition(
            surface,
            &mut |expression| {
                if matches!(
                    expression,
                    ContractExpression::Call { name, arguments }
                        if name == "to_integer" && arguments.len() == 1
                ) && !written.contains(expression)
                {
                    written.push(expression.clone());
                }
            },
        );
    }
    // The observation of a written machine sum or difference spells its
    // operands too: `to_integer(n - k)` names `to_integer(n)` and
    // `to_integer(k)`, which an operation identity over it cites.
    fn operand_observations(
        expression: &ContractExpression,
        native: bool,
    ) -> Vec<ContractExpression> {
        match expression {
            ContractExpression::At {
                selector,
                expression,
            } => operand_observations(expression, native)
                .into_iter()
                .map(|expression| ContractExpression::At {
                    selector: selector.clone(),
                    expression: Box::new(expression),
                })
                .collect(),
            ContractExpression::Old(expression) => operand_observations(expression, native)
                .into_iter()
                .map(|expression| ContractExpression::Old(Box::new(expression)))
                .collect(),
            ContractExpression::Call { name, arguments }
                if !native && name == "to_integer" && arguments.len() == 1 =>
            {
                operand_observations(&arguments[0], true)
            }
            expression if native => {
                let operands = match expression {
                    ContractExpression::Add(left, right)
                    | ContractExpression::Subtract(left, right) => {
                        vec![left.as_ref().clone(), right.as_ref().clone()]
                    }
                    ContractExpression::CUnary {
                        operand,
                        lowered: ProgramExpression::Cast { .. },
                    } => vec![operand.as_ref().clone()],
                    ContractExpression::ProgramExpression(ProgramExpression::Cast {
                        expression,
                        ..
                    }) => vec![ContractExpression::ProgramExpression(
                        expression.as_ref().clone(),
                    )],
                    _ => Vec::new(),
                };
                operands
                    .into_iter()
                    .map(|operand| ContractExpression::Call {
                        name: "to_integer".into(),
                        arguments: vec![operand],
                    })
                    .collect()
            }
            _ => Vec::new(),
        }
    }
    let mut index = 0;
    while index < written.len() {
        // A scoped operation's operands are read at the same program point.
        for observed in operand_observations(&written[index], false) {
            if !written.contains(&observed) {
                written.push(observed);
            }
        }
        index += 1;
    }
    if !include_entry {
        return written;
    }
    // A value the proof has since replaced, such as a population count
    // before a consumption, is often spelled only at function entry.
    let entry: Vec<ContractExpression> = written
        .iter()
        .filter_map(|expression| {
            let ContractExpression::Call { arguments, .. } = expression else {
                return None;
            };
            let mut retained_state = false;
            crate::surface::proof::fixed_state_proofs::conversion_conditions::walk_written_expressions(
                &arguments[0],
                &mut |inner| {
                    retained_state |= matches!(
                        inner,
                        ContractExpression::Old(_) | ContractExpression::At { .. }
                    );
                },
            );
            (!retained_state).then(|| ContractExpression::Call {
                name: "to_integer".into(),
                arguments: vec![ContractExpression::Old(Box::new(arguments[0].clone()))],
            })
        })
        .collect();
    for expression in entry {
        if !written.contains(&expression) {
            written.push(expression);
        }
    }
    written
}

/// Whether `proposition` reads `result` inside a state that precedes the
/// return, which the parser refuses.
fn reads_result_before_return(proposition: &ClickProposition) -> bool {
    let too_early = |selector: Option<&ProgramPointSelector>| {
        !crate::surface::program_point_can_name_result(selector)
    };
    let proposition_reads = match proposition {
        ClickProposition::At {
            selector,
            proposition,
        } => {
            (too_early(Some(selector)) && crate::surface::proposition_names_result(proposition))
                || reads_result_before_return(proposition)
        }
        ClickProposition::Not(inner) => reads_result_before_return(inner),
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            reads_result_before_return(left) || reads_result_before_return(right)
        }
        _ => false,
    };
    if proposition_reads {
        return true;
    }
    let mut found = false;
    crate::surface::proof::fixed_state_proofs::conversion_conditions::walk_written_expressions_in_proposition(
        proposition,
        &mut |expression| {
            let (selector, inner) = match expression {
                ContractExpression::At {
                    selector,
                    expression,
                } => (Some(selector), expression),
                ContractExpression::Old(inner) => (None, inner),
                _ => return,
            };
            if too_early(selector) {
                let mut names = BTreeSet::new();
                crate::surface::collect_current_contract_expression_variables(inner, &mut names);
                found |= names.contains("result");
            }
        },
    );
    found
}

/// The Integer readings of a native fact: a native comparison read as an
/// Integer one (`1u32 <= x` as `1 <= to_integer(x)`), and a signed
/// definedness fact read as the two bounds of its exact result
/// (`defined(a + b)` as `to_integer(a) + to_integer(b) <= 2147483647` and
/// `>= -2147483648`).
fn integer_readings_of_native_fact(premise: &Proposition) -> Vec<Proposition> {
    let mut readings =
        crate::kernel::machine_integer::comparison::integer_observations_of_native_comparison(
            premise,
        );
    readings.extend(
        crate::kernel::machine_integer::definedness::integer_bounds_of_definedness(premise),
    );
    readings
}

/// `premises` followed by the Integer readings of each native fact among
/// them (`integer_readings_of_native_fact`), each once.
fn with_native_comparisons_as_integer(premises: &[Proposition]) -> Vec<Proposition> {
    let mut extended = premises.to_vec();
    for premise in premises {
        for lifted in integer_readings_of_native_fact(premise) {
            if !extended.contains(&lifted) {
                extended.push(lifted);
            }
        }
    }
    extended
}

/// An observed machine `+`, `-` or `*`, integral cast or Integer-to-machine
/// conversion, its exact Integer value, and the identity equating them. A
/// cast's value is its operand's observation; a conversion `to_T(z)`'s is
/// `z`.
type OperationIdentity = (
    crate::kernel::IntegerTerm,
    crate::kernel::IntegerTerm,
    Proposition,
);

/// The identities `to_integer(a op b) == to_integer(a) op to_integer(b)` of
/// the machine `+`, `-` and `*` among `observations`, and `to_integer((T)x) ==
/// to_integer(x)` of their integral casts. An operand of an observed
/// operation may itself be one, as `available - amount` in `used +
/// (available - amount)`; each identity's operands are observed in turn,
/// once each, so the work follows the operations written, and an operand's
/// identity comes after its operation's. A cast whose operand has two
/// readings (a 64-to-32-bit word narrowing) takes the one observed.
fn operation_identities(observations: Vec<crate::kernel::IntegerTerm>) -> Vec<OperationIdentity> {
    use crate::kernel::machine_integer::conversion::{
        cast_operands, narrow_widening, widened_narrow_word,
    };
    use crate::kernel::machine_integer::identity::mathematical;
    let observed_ids = observations
        .iter()
        .cloned()
        .collect::<std::collections::HashSet<_>>();
    // The narrow observations by word, so a wider observation of the same
    // word finds the value it widens by one lookup.
    let mut narrow_by_word =
        std::collections::HashMap::<crate::kernel::SharedMachineIntegerTerm, Vec<_>>::new();
    for observation in &observations {
        if let crate::kernel::IntegerTerm::Machine(machine) = observation
            && machine.ty().format().bits() < 32
        {
            narrow_by_word
                .entry(
                    machine
                        .operand_view()
                        .retain(crate::kernel::MachineIntegerType::Int32),
                )
                .or_default()
                .push(observation.clone());
        }
    }
    let mut identities = Vec::new();
    let mut pending = observations;
    let mut seen = std::collections::HashSet::new();
    while let Some(observed) = pending.pop() {
        if !seen.insert(observed.clone()) {
            continue;
        }
        let value = match mathematical(&observed) {
            // A product of two observations is planned too: its bounds come
            // from the facts or, when those miss, from `integer_product_bounds`
            // over its operands' type ranges (`prove_operation_identities`).
            Some((_, value)) if identity_operands(&value).is_none() => continue,
            Some((_, value)) => value,
            // `to_integer(to_T(z)) == z` in `T`'s range: its value is the
            // conversion's Integer operand, which has no machine operand to
            // observe in turn.
            None if let Some((value, _)) =
                crate::kernel::machine_integer::conversion::integer_conversion(&observed) =>
            {
                let value = value.as_ref().clone();
                let identity = Proposition::condition_is(
                    ConditionTerm::integer_equal(observed.clone(), value.clone()),
                    true,
                );
                identities.push((observed, value, identity));
                continue;
            }
            None => {
                let operands = cast_operands(&observed);
                let operand = operands
                    .iter()
                    .find(|operand| observed_ids.contains(*operand))
                    // A narrow value read at a containing format widens it
                    // directly, without the intermediate 32-bit reading a
                    // legacy 32-to-64-bit conversion also offers.
                    .or_else(|| {
                        widened_narrow_word(&observed)
                            .and_then(|word| {
                                narrow_by_word
                                    .get(&word.retain(crate::kernel::MachineIntegerType::Int32))
                            })
                            .and_then(|narrow| {
                                narrow
                                    .iter()
                                    .find(|original| narrow_widening(&observed, original))
                            })
                    })
                    .or_else(|| (operands.len() == 1).then(|| &operands[0]));
                let Some(operand) = operand else {
                    continue;
                };
                // A widening's value is its operand's (rule W), which the
                // Integer engines read with no identity to prove.
                if operand.value_read() == observed.value_read() {
                    continue;
                }
                operand.clone()
            }
        };
        let Some(operands) = identity_operands(&value) else {
            continue;
        };
        for operand in operands {
            if matches!(operand, crate::kernel::IntegerTerm::Machine(_)) {
                pending.push(operand.clone());
            }
        }
        let identity = Proposition::condition_is(
            ConditionTerm::integer_equal(observed.clone(), value.clone()),
            true,
        );
        identities.push((observed, value, identity));
    }
    // Initial observations may include both an operation and its operands.
    // Discovery order then need not be dependency order. Sort this selected
    // DAG once, so reversing the result always proves operands first.
    let indexes = identities
        .iter()
        .enumerate()
        .map(|(index, (observed, _, _))| (observed.clone(), index))
        .collect::<std::collections::HashMap<_, _>>();
    let mut visited = vec![false; identities.len()];
    let mut ordered = Vec::with_capacity(identities.len());
    for root in 0..identities.len() {
        let mut pending = vec![(root, false)];
        while let Some((index, finished)) = pending.pop() {
            if finished {
                ordered.push(identities[index].clone());
            } else if !visited[index] {
                visited[index] = true;
                pending.push((index, true));
                for operand in identity_operands(&identities[index].1)
                    .into_iter()
                    .flatten()
                {
                    if let Some(dependency) = indexes.get(operand) {
                        pending.push((*dependency, false));
                    }
                }
            }
        }
    }
    ordered.reverse();
    ordered
}

/// The observations an identity's value is written over: the two operands
/// of a `+`, `-` or `*`, or a cast's operand.
fn identity_operands(
    value: &crate::kernel::IntegerTerm,
) -> Option<Vec<&crate::kernel::IntegerTerm>> {
    use crate::kernel::IntegerTerm;
    match value {
        IntegerTerm::Add(left, right)
        | IntegerTerm::Subtract(left, right)
        | IntegerTerm::Multiply(left, right) => Some(vec![left.as_ref(), right.as_ref()]),
        IntegerTerm::Machine(_) => Some(vec![value]),
        _ => None,
    }
}

fn kernel_upper_bound_split_candidate(
    proposition: &Proposition,
) -> Option<(Variable, crate::kernel::SharedMachineIntegerTerm)> {
    let Proposition::ConditionIs(condition, true) = proposition else {
        return None;
    };
    let comparison = crate::kernel::machine_integer::comparison::structural_comparison_view(
        condition.native_compat(),
    )?;
    if comparison.format != MachineIntegerType::Int32 || comparison.negated {
        return None;
    }
    let variable = *comparison.operands[0].operand_view().variable()?;
    let right = comparison.operands[1].operand_view();
    let pivot = match comparison.relation {
        CompareRelation::LessEqual => right,
        CompareRelation::LessThan => {
            let (MachineIntegerType::Int32, crate::kernel::MachineBinaryOp::Add, [pivot, one]) =
                right.binary()?
            else {
                return None;
            };
            if one.word32_constant() != Some(1) {
                return None;
            }
            pivot
        }
        _ => return None,
    };
    // Candidate inspection retains the shared pivot. Rejected candidates
    // must not export arithmetic or depend on an earlier export's cache.
    Some((variable, pivot.retain(MachineIntegerType::Int32)))
}

/// An Integer observation, `to_integer(x)`, possibly under the `let`s of a
/// theorem statement, `let n: int32 = v + 1; to_integer(n)`.
fn observed_integer(operand: &ContractExpression) -> bool {
    match operand {
        ContractExpression::Call { name, arguments } => {
            name == "to_integer" && arguments.len() == 1
        }
        ContractExpression::Let { body, .. } => observed_integer(body),
        _ => false,
    }
}

// These split conditions come from a native int32 bound. Shield their pivot
// arithmetic from Integer specification arithmetic when printed.
fn native_int32_split_operand(operand: ContractExpression) -> ContractExpression {
    ContractExpression::CUnary {
        operand: Box::new(operand),
        lowered: ProgramExpression::Cast {
            expression: Box::new(ProgramExpression::Value(int32(0))),
            target_type: crate::kernel::ProgramType::Int32,
            integer_mode: crate::kernel::IntegerCastMode::CConversion,
            pointee_struct: None,
            pointee_volatile: false,
            pointee_constant: false,
            explicit_qualification: false,
        },
    }
}

/// [`native_int32_split_operand`] at `uint32`: the operand lowered as the
/// native `uint32` expression it spells.
fn native_uint32_split_operand(operand: ContractExpression) -> ContractExpression {
    ContractExpression::CUnary {
        operand: Box::new(operand),
        lowered: ProgramExpression::Cast {
            expression: Box::new(ProgramExpression::Value(int32(0))),
            target_type: crate::kernel::ProgramType::UInt32,
            integer_mode: crate::kernel::IntegerCastMode::CConversion,
            pointee_struct: None,
            pointee_volatile: false,
            pointee_constant: false,
            explicit_qualification: false,
        },
    }
}

fn surface_upper_bound_split_condition(proposition: &ClickProposition) -> Option<ClickProposition> {
    match proposition {
        ClickProposition::At {
            selector,
            proposition,
        } => Some(ClickProposition::At {
            selector: selector.clone(),
            proposition: Box::new(surface_upper_bound_split_condition(proposition)?),
        }),
        ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::LessEqual,
            right,
        } => Some(ClickProposition::Comparison {
            left: left.clone(),
            operator: ComparisonOperator::LessThan,
            right: native_int32_split_operand(right.clone()),
        }),
        ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::LessThan,
            right: ContractExpression::Add(pivot, one),
        } if **one == ContractExpression::ProgramExpression(ProgramExpression::Value(int32(1))) => {
            Some(ClickProposition::Comparison {
                left: left.clone(),
                operator: ComparisonOperator::LessThan,
                right: native_int32_split_operand(pivot.as_ref().clone()),
            })
        }
        ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::LessThan,
            right,
        } => Some(ClickProposition::Comparison {
            left: left.clone(),
            operator: ComparisonOperator::LessThan,
            right: native_int32_split_operand(ContractExpression::Subtract(
                Box::new(right.clone()),
                Box::new(ContractExpression::ProgramExpression(
                    ProgramExpression::Value(int32(1)),
                )),
            )),
        }),
        _ => None,
    }
}

fn surface_upper_bound_direct_condition(
    proposition: &ClickProposition,
) -> Option<ClickProposition> {
    match proposition {
        ClickProposition::At {
            selector,
            proposition,
        } => Some(ClickProposition::At {
            selector: selector.clone(),
            proposition: Box::new(surface_upper_bound_direct_condition(proposition)?),
        }),
        ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::LessEqual,
            right,
        } => Some(ClickProposition::Comparison {
            left: left.clone(),
            operator: ComparisonOperator::LessEqual,
            right: native_int32_split_operand(right.clone()),
        }),
        ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::LessThan,
            right,
        } => Some(ClickProposition::Comparison {
            left: left.clone(),
            operator: ComparisonOperator::LessThan,
            right: native_int32_split_operand(right.clone()),
        }),
        _ => None,
    }
}

fn surface_split_equality(proposition: &ClickProposition) -> Option<ClickProposition> {
    match proposition {
        ClickProposition::At {
            selector,
            proposition,
        } => Some(ClickProposition::At {
            selector: selector.clone(),
            proposition: Box::new(surface_split_equality(proposition)?),
        }),
        ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::LessThan,
            right,
        } => Some(ClickProposition::Comparison {
            left: left.clone(),
            operator: ComparisonOperator::Equal,
            right: right.clone(),
        }),
        _ => None,
    }
}

fn surface_split_nonstrict_bound(proposition: &ClickProposition) -> Option<ClickProposition> {
    match proposition {
        ClickProposition::At {
            selector,
            proposition,
        } => Some(ClickProposition::At {
            selector: selector.clone(),
            proposition: Box::new(surface_split_nonstrict_bound(proposition)?),
        }),
        ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::LessThan,
            right,
        } => Some(ClickProposition::Comparison {
            left: left.clone(),
            operator: ComparisonOperator::LessEqual,
            right: right.clone(),
        }),
        _ => None,
    }
}

fn surface_split_disequality(proposition: &ClickProposition) -> Option<ClickProposition> {
    match proposition {
        ClickProposition::At {
            selector,
            proposition,
        } => Some(ClickProposition::At {
            selector: selector.clone(),
            proposition: Box::new(surface_split_disequality(proposition)?),
        }),
        ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::LessThan,
            right,
        } => Some(ClickProposition::Comparison {
            left: left.clone(),
            operator: ComparisonOperator::NotEqual,
            right: right.clone(),
        }),
        _ => None,
    }
}

/// Why a written linear proof script did not close its goal.
///
/// The script has not proved its goal. Source callers report this at the
/// written scope; a speculative planner may discard its candidate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::surface::proof) enum LinearScriptDecline {
    /// The script's shape is outside what this driver checks, so no written
    /// step ran.
    Shape,
    /// The written tactic at this position declined.
    Step(usize),
}

/// A branch continuation is checked in each selected arm. Borrow terminal
/// arms unchanged; copied source is proportional to the explicit branch proof
/// being checked and serialized, rather than to ambient semantic state.
/// One `cases` arm as the driver runs it: its assumption, its tactics
/// followed by the rest of the script, and the source sites of those tactics.
struct CaseArmScript<'s> {
    assumption: &'s ClickProposition,
    tactics: std::borrow::Cow<'s, [ProofTactic]>,
    sites: Vec<ProofStepSite>,
}

fn script_arm_with_continuation<'a>(
    arm: &'a [ProofTactic],
    continuation: &[ProofTactic],
) -> std::borrow::Cow<'a, [ProofTactic]> {
    if continuation.is_empty() {
        std::borrow::Cow::Borrowed(arm)
    } else {
        std::borrow::Cow::Owned(arm.iter().chain(continuation).cloned().collect())
    }
}

impl<'a> Proof<'a> {
    fn signed_surface_term(
        &self,
        term: &crate::kernel::MachineTerm,
        candidates: &[&ContractExpression],
    ) -> Option<ContractExpression> {
        if let Some(value) = term.as_const() {
            // Generated interval nodes can introduce a small machine
            // constant (for example the `+ 1` in a bump function) that has no
            // separate source occurrence. Retain its int32 type and bits;
            // a negative decimal IntegerLiteral is not a native expression.
            if matches!(term, bits32_constant!(_)) {
                return Some(ContractExpression::ProgramExpression(
                    ProgramExpression::Value(int32(MachineTerm::constant(value))),
                ));
            }
        }
        // Prefer the most local/int32 source occurrence.  A uint32 cast of
        // the same variable may lower to the same raw bitvector term, but is
        // not a valid typed witness for an int32 interval node.
        for candidate in candidates.iter().rev() {
            if let bits32_constant!(value) = term
                && let ContractExpression::IntegerLiteral(literal) = *candidate
                && literal.parse::<u32>().ok() == Some(constant_u32(*value))
            {
                return Some((*candidate).clone());
            }
            let probe = ClickProposition::Comparison {
                left: (*candidate).clone(),
                operator: ComparisonOperator::Equal,
                right: ContractExpression::IntegerLiteral("0".into()),
            };
            let Ok(lowered) =
                self.lower_surface_proposition_direct(&probe, "signed arithmetic step term")
            else {
                continue;
            };
            let Proposition::ConditionIs(condition, true) = lowered else {
                continue;
            };
            let Some(view) = crate::kernel::machine_integer::comparison::structural_comparison_view(
                (&condition).native_compat(),
            ) else {
                continue;
            };
            if !matches!(
                view.format,
                MachineIntegerType::Int32 | MachineIntegerType::UInt32
            ) || view.relation != crate::kernel::CompareRelation::Equal
                || view.negated
            {
                continue;
            }
            let [left, right] = view
                .operands
                .each_ref()
                .map(|operand| operand.operand_view());
            let equal = |operand| {
                use crate::kernel::proof::signed_arithmetic::SignedArithmeticAtom as Atom;
                Atom::from_canonical_operand(operand)
                    .zip(Atom::from_canonical_operand(
                        crate::kernel::MachineOperandView::Legacy(term),
                    ))
                    .is_some_and(|(left, right)| left == right)
            };
            let names_term = (right.word32_constant() == Some(0) && equal(left))
                || (left.word32_constant() == Some(0) && equal(right));
            if names_term && self.signed_surface_term_is_int32(candidate, term) {
                return Some(int32_widening_spelling(term, (*candidate).clone()));
            }
        }
        None
    }

    /// Whether `candidate` reads `term` as an `int32`, so a certificate node
    /// that names the signed atom re-lowers to that atom. Equality cannot
    /// tell: `n as uint32 == 0` lowers to the same raw bitvector equality as
    /// `n == 0`, while `n as uint32 <= 2147483647` is an unsigned comparison of
    /// another typed value. A signed order does tell, since only an `int32`
    /// operand lowers `candidate < 0` to a signed comparison of that term.
    fn signed_surface_term_is_int32(
        &self,
        candidate: &ContractExpression,
        term: &crate::kernel::MachineTerm,
    ) -> bool {
        let probe = ClickProposition::Comparison {
            left: candidate.clone(),
            operator: ComparisonOperator::LessThan,
            right: ContractExpression::IntegerLiteral("0".into()),
        };
        let Ok(Proposition::ConditionIs(condition, true)) =
            self.lower_surface_proposition_direct(&probe, "signed arithmetic step term")
        else {
            return false;
        };
        let Some(view) = crate::kernel::machine_integer::comparison::structural_comparison_view(
            (&condition).native_compat(),
        ) else {
            return false;
        };
        if view.format != MachineIntegerType::Int32
            || view.relation != crate::kernel::CompareRelation::LessThan
            || view.negated
        {
            return false;
        }
        use crate::kernel::proof::signed_arithmetic::SignedArithmeticAtom as Atom;
        view.operands[1].operand_view().word32_constant() == Some(0)
            && Atom::from_canonical_operand(view.operands[0].operand_view())
                .zip(Atom::from_canonical_operand(
                    crate::kernel::MachineOperandView::Legacy(term),
                ))
                .is_some_and(|(left, right)| left == right)
    }

    pub(super) fn signed_plan_to_surface(
        &self,
        plan: &crate::kernel::proof::signed_arithmetic::SignedArithmeticPlan,
        premise_pairs: &[(Proposition, ClickProposition)],
        surface_goal: &ClickProposition,
    ) -> Option<SignedIntervalPlan> {
        let weakening_source = match plan.nodes.get(plan.conclusion) {
            Some(SignedArithmeticNode::Add { left, right, .. })
                if matches!(
                    plan.nodes.get(*left),
                    Some(SignedArithmeticNode::Add { .. })
                ) && matches!(plan.nodes.get(*right), Some(SignedArithmeticNode::Trivial { result })
                        if result.relation == SignedArithmeticRelation::LessEqual
                            && result.terms.is_empty()
                            && result.constant == BigInt::from(-1)) =>
            {
                Some(*left)
            }
            _ => None,
        };
        let mut used = BTreeSet::new();
        for node in &plan.nodes {
            match node {
                SignedArithmeticNode::Premise { index, .. }
                | SignedArithmeticNode::DefinedPremise { index, .. } => {
                    used.insert(*index);
                }
                _ => {}
            }
        }
        // Preserve native typing at the output boundary. Keep the planning
        // surfaces unchanged so transitive chains still match their endpoints.
        let native_result = |value: ClickProposition, claim: &SignedArithmeticClaim| match value {
            ClickProposition::Comparison {
                left,
                operator,
                right,
            } if !claim.terms.is_empty() => {
                // An exact observation's native operand is the value it
                // observes: `x as int32`, not `to_integer(x) as int32`. A
                // theorem `let` around an observation keeps its binding:
                // `let n: int32 = v + 1; to_integer(n)` is natively
                // `let n: int32 = v + 1; n as int32`.
                fn native(operand: ContractExpression) -> ContractExpression {
                    match operand {
                        ContractExpression::Let {
                            name,
                            click_type,
                            value,
                            body,
                        } if observed_integer(&body) => ContractExpression::Let {
                            name,
                            click_type,
                            value,
                            body: Box::new(native(*body)),
                        },
                        operand => ContractExpression::CUnary {
                            operand: Box::new(match operand {
                                ContractExpression::Call {
                                    name,
                                    mut arguments,
                                } if name == "to_integer" && arguments.len() == 1 => {
                                    arguments.remove(0)
                                }
                                operand => operand,
                            }),
                            lowered: ProgramExpression::Cast {
                                expression: Box::new(ProgramExpression::Value(
                                    crate::kernel::int32(0),
                                )),
                                target_type: crate::kernel::ProgramType::Int32,
                                integer_mode: crate::kernel::IntegerCastMode::CConversion,
                                pointee_struct: None,
                                pointee_volatile: false,
                                pointee_constant: false,
                                explicit_qualification: false,
                            },
                        },
                    }
                }
                ClickProposition::Comparison {
                    left: native(left),
                    operator,
                    right: native(right),
                }
            }
            value => value,
        };
        let native_conclusion = |value, proposition| {
            match crate::kernel::proof::signed_arithmetic::signed_arithmetic_claim(proposition) {
                Some(claim) => native_result(value, &claim),
                None => value,
            }
        };
        let mut source_indices = BTreeMap::new();
        let mut generated = Vec::new();
        for original in used {
            let local = source_indices.len();
            source_indices.insert(original, local);
            if plan.nodes.iter().any(|node| {
                matches!(node, SignedArithmeticNode::Premise { index, .. } if *index == original)
            }) {
                let (kernel, surface) = premise_pairs.get(original)?;
                let surface = native_conclusion(
                    surface_comparison_with_anchored_operands(surface), kernel,
                );
                generated.push(SignedArithmeticStep::Premise {
                    index: local,
                    proposition: surface.clone(),
                    result: surface,
                });
            }
        }
        let mut mapped = Vec::with_capacity(plan.nodes.len());
        let operation_offset = generated.len();
        let mut operation_count = 0;
        for node in &plan.nodes {
            if let SignedArithmeticNode::Premise { index, .. } = node {
                mapped.push(*source_indices.get(index)?);
            } else {
                mapped.push(operation_offset + operation_count);
                operation_count += 1;
            }
        }
        let rendered_premises: Vec<_> = premise_pairs
            .iter()
            .map(|(_, surface)| surface_comparison_with_anchored_operands(surface))
            .collect();
        let mut terms: Vec<&ContractExpression> = Vec::new();
        collect_signed_surface_proposition_terms(surface_goal, &mut terms);
        for surface in &rendered_premises {
            collect_signed_surface_proposition_terms(surface, &mut terms);
        }
        let term = |term: &crate::kernel::MachineTerm| self.signed_surface_term(term, &terms);
        let generated_goal;
        let surface_goal = if integer_surface_ordered_parts(
            &surface_comparison_with_anchored_operands(surface_goal),
        )
        .is_none()
        {
            let Proposition::ConditionIs(condition, true) = self.goal()? else {
                return None;
            };
            let view = crate::kernel::machine_integer::comparison::structural_comparison_view(
                condition.native_compat(),
            )?;
            if view.negated || view.relation != crate::kernel::CompareRelation::LessEqual {
                return None;
            }
            // An implicit resource span has no written comparison. Its two
            // operands are still explicit source terms of this plan.
            let native = |operand| ContractExpression::CUnary {
                operand: Box::new(operand),
                lowered: ProgramExpression::Cast {
                    expression: Box::new(ProgramExpression::Value(crate::kernel::int32(0))),
                    target_type: view.format.program_type(),
                    integer_mode: crate::kernel::IntegerCastMode::CConversion,
                    pointee_struct: None,
                    pointee_volatile: false,
                    pointee_constant: false,
                    explicit_qualification: false,
                },
            };
            let operands = view
                .operands
                .each_ref()
                .map(|operand| operand.operand_view().retain(view.format));
            generated_goal = Some(ClickProposition::Comparison {
                left: native(term(operands[0].value())?),
                operator: ComparisonOperator::LessEqual,
                right: native(term(operands[1].value())?),
            });
            generated_goal.as_ref()?
        } else {
            generated_goal = None;
            surface_goal
        };
        let interval =
            |value: crate::kernel::proof::signed_arithmetic::SignedArithmeticInterval| {
                SignedInt32Interval {
                    lower: value.lower,
                    upper: value.upper,
                }
            };
        let comparison = |value: SignedArithmeticComparison| match value {
            SignedArithmeticComparison::LessThan => SignedInt32Comparison::LessThan,
            SignedArithmeticComparison::LessEqual => SignedInt32Comparison::LessEqual,
            SignedArithmeticComparison::Equal => SignedInt32Comparison::Equal,
            SignedArithmeticComparison::Disequal => SignedInt32Comparison::Disequal,
            SignedArithmeticComparison::UnsignedLessThan => SignedInt32Comparison::UnsignedLessThan,
            SignedArithmeticComparison::UnsignedLessEqual => {
                SignedInt32Comparison::UnsignedLessEqual
            }
        };
        // The additions of a chain of three or more inequalities: an `Add`
        // whose left input is an `Add` of two inequalities, and that input.
        // Each is spelled as the comparison of the chain's ends, because the
        // sum of the source operands grows by one term per premise and no
        // longer reads back as the claim it denotes.
        let mut chain_additions = BTreeSet::new();
        for (index, node) in plan.nodes.iter().enumerate() {
            if let SignedArithmeticNode::Add { left, right, .. } = node
                && matches!(
                    plan.nodes.get(*left),
                    Some(SignedArithmeticNode::Add { .. })
                )
                && !matches!(
                    plan.nodes.get(*right),
                    Some(SignedArithmeticNode::Trivial { .. })
                )
            {
                chain_additions.insert(index);
                chain_additions.insert(*left);
            }
        }
        let has_affine_premise = plan
            .nodes
            .iter()
            .any(|node| matches!(node, SignedArithmeticNode::AffinePremise { .. }));
        let observe_operand = |operand: ContractExpression| {
            if observed_integer(&operand) {
                operand
            } else {
                ContractExpression::Call {
                    name: "to_integer".into(),
                    // Observe the promoted operand used by the signed certificate.
                    arguments: vec![native_int32_split_operand(operand)],
                }
            }
        };
        let observe_comparison = |surface: ClickProposition| match surface {
            ClickProposition::Comparison {
                left,
                operator,
                right,
            } => ClickProposition::Comparison {
                left: observe_operand(left),
                operator,
                right: observe_operand(right),
            },
            surface => surface,
        };
        let mut surfaces: Vec<Option<ClickProposition>> = Vec::with_capacity(plan.nodes.len());
        let claim_surface = |claim: &SignedArithmeticClaim| {
            let value = claim.constant.to_i32()?;
            let left = surface_signed_integer_literal(&BigInt::from(value));
            (claim.terms.is_empty()).then_some(ClickProposition::Comparison {
                left,
                operator: match claim.relation {
                    SignedArithmeticRelation::LessEqual => ComparisonOperator::LessEqual,
                    SignedArithmeticRelation::Equal => ComparisonOperator::Equal,
                    SignedArithmeticRelation::Disequal => ComparisonOperator::NotEqual,
                },
                right: ContractExpression::IntegerLiteral("0".into()),
            })
        };
        for node in &plan.nodes {
            let value = match node {
                SignedArithmeticNode::Premise { index, .. } => {
                    Some(observe_comparison(rendered_premises.get(*index)?.clone()))
                }
                SignedArithmeticNode::AffinePremise { source, .. } => {
                    surfaces.get(*source)?.clone()
                }
                SignedArithmeticNode::Scale {
                    source,
                    coefficient,
                    result,
                } => integer_plan_surface_scale(surfaces.get(*source)?.as_ref()?, coefficient)
                    .or_else(|| claim_surface(result)),
                SignedArithmeticNode::Add {
                    left,
                    right,
                    result,
                } => {
                    // Preserve the planner's normalized affine claim
                    // whenever it has no atoms. Reconstructing it by adding
                    // the source propositions can leave an equivalent but
                    // differently grouped expression (for example
                    // `i < i + 1` for the cancellation claim `0 <= 0`).
                    let left_surface = surfaces.get(*left)?.as_ref()?;
                    let right_surface = surfaces.get(*right)?.as_ref()?;
                    if has_affine_premise && surfaces.len() == plan.conclusion {
                        // The checked premise conversion gives the sum a
                        // different affine spelling than its opaque source.
                        // The kernel independently checks this exact goal.
                        Some(surface_goal.clone())
                    } else if result.terms.is_empty()
                        && result.constant == BigInt::from(0)
                        && result.relation == SignedArithmeticRelation::LessEqual
                    {
                        integer_surface_zero_claim(left_surface, right_surface)
                    } else if chain_additions.contains(&surfaces.len())
                        && let Some(chained) =
                            integer_surface_transitive(left_surface, right_surface)
                    {
                        Some(chained)
                    } else {
                        claim_surface(result).or_else(|| {
                            if weakening_source == Some(surfaces.len()) {
                                integer_surface_transitive(left_surface, right_surface)
                            } else {
                                integer_plan_surface_add(left_surface, right_surface)
                            }
                        })
                    }
                }
                SignedArithmeticNode::EqualityToLessEqual {
                    source,
                    reverse,
                    result,
                } => integer_surface_equality_to_less_equal(
                    surfaces.get(*source)?.as_ref()?,
                    *reverse,
                )
                .or_else(|| claim_surface(result)),
                SignedArithmeticNode::EqualityFromBounds {
                    lower,
                    upper,
                    result,
                } => integer_surface_equality_from_bounds(
                    surfaces.get(*lower)?.as_ref()?,
                    surfaces.get(*upper)?.as_ref()?,
                )
                .or_else(|| claim_surface(result))
                // Affine bounds may have different source groupings after
                // equality substitution. The final goal supplies their
                // equality spelling; the checker still validates both
                // opposite claims and the stated result independently.
                .or_else(|| (surfaces.len() == plan.conclusion).then(|| surface_goal.clone())),
                SignedArithmeticNode::StrictFromDisequal { bound, result, .. } => {
                    integer_surface_strict_from_disequal(surfaces.get(*bound)?.as_ref()?)
                        .or_else(|| claim_surface(result))
                }
                SignedArithmeticNode::Trivial { result } => claim_surface(result),
                SignedArithmeticNode::Int32Range { result } => {
                    let (atom, coefficient) = result.terms.iter().next()?;
                    let atom = term(&crate::kernel::MachineTerm::Variable(atom.as_variable()?))?;
                    Some(observe_comparison(if coefficient.is_positive() {
                        ClickProposition::Comparison {
                            left: atom,
                            operator: ComparisonOperator::LessEqual,
                            right: surface_signed_integer_literal(&BigInt::from(i32::MAX)),
                        }
                    } else {
                        ClickProposition::Comparison {
                            left: surface_signed_integer_literal(&BigInt::from(i32::MIN)),
                            operator: ComparisonOperator::LessEqual,
                            right: atom,
                        }
                    }))
                }
                SignedArithmeticNode::IntervalCompare { .. }
                | SignedArithmeticNode::AffineConclusion { .. }
                | SignedArithmeticNode::AffineConclusionWithEvidence { .. } => {
                    Some(surface_goal.clone())
                }
                _ => None,
            };
            surfaces.push(value);
        }
        if let Some(goal) = &generated_goal {
            surfaces[plan.conclusion] = Some(goal.clone());
        }
        for (node_index, node) in plan.nodes.iter().enumerate() {
            let r = |index: usize| mapped[index];
            let result = || surfaces.get(node_index)?.as_ref().cloned();
            let surface_node = match node {
                SignedArithmeticNode::Premise { .. } => continue,
                SignedArithmeticNode::Scale {
                    source,
                    coefficient,
                    result: _,
                } => SignedArithmeticStep::Scale {
                    source: r(*source),
                    coefficient: surface_signed_integer_literal(coefficient),
                    result: result()?,
                },
                SignedArithmeticNode::Add {
                    left,
                    right,
                    result: _,
                } => SignedArithmeticStep::Add {
                    left: r(*left),
                    right: r(*right),
                    // The final sum is already checked against the goal's
                    // affine claim. Reuse that source spelling instead of
                    // printing another composite expression whose machine
                    // additions may lower to different atoms.
                    result: if node_index == plan.conclusion && weakening_source.is_some() {
                        surface_goal.clone()
                    } else {
                        result()?
                    },
                },
                SignedArithmeticNode::EqualityToLessEqual {
                    source, reverse, ..
                } => SignedArithmeticStep::EqualityToLessEqual {
                    source: r(*source),
                    reverse: *reverse,
                    result: result()?,
                },
                SignedArithmeticNode::EqualityFromBounds { lower, upper, .. } => {
                    SignedArithmeticStep::EqualityFromBounds {
                        lower: r(*lower),
                        upper: r(*upper),
                        result: result()?,
                    }
                }
                SignedArithmeticNode::StrictFromDisequal {
                    bound, disequal, ..
                } => SignedArithmeticStep::StrictFromDisequal {
                    bound: r(*bound),
                    disequal: r(*disequal),
                    result: result()?,
                },
                SignedArithmeticNode::Trivial { .. } => {
                    SignedArithmeticStep::Trivial { result: result()? }
                }
                SignedArithmeticNode::Int32Range { .. } => {
                    SignedArithmeticStep::Int32Range { result: result()? }
                }
                SignedArithmeticNode::IntervalFromAffine {
                    source,
                    term: machine_term,
                    lower,
                    upper,
                } => SignedArithmeticStep::IntervalFromAffine {
                    source: r(*source),
                    term: term(machine_term)?,
                    lower: *lower,
                    upper: *upper,
                },
                SignedArithmeticNode::IntervalFromAffineDirect {
                    source,
                    term: machine_term,
                    lower,
                    upper,
                } => SignedArithmeticStep::IntervalFromAffineDirect {
                    source: r(*source),
                    term: term(machine_term)?,
                    lower: *lower,
                    upper: *upper,
                },
                SignedArithmeticNode::IntervalIntersect {
                    left,
                    right,
                    result,
                } => SignedArithmeticStep::IntervalIntersect {
                    left: r(*left),
                    right: r(*right),
                    result: interval(result.clone()),
                },
                SignedArithmeticNode::IntervalAtom {
                    term: machine_term,
                    lower,
                    upper,
                    ..
                } => SignedArithmeticStep::IntervalAtom {
                    term: term(machine_term)?,
                    lower: *lower,
                    upper: *upper,
                },
                SignedArithmeticNode::DefinedPremise {
                    index,
                    term: machine_term,
                    ..
                } => {
                    // The selected premise can be written as ordinary range
                    // bounds. The generated `defined(term)` is independently
                    // lowered and matched to that complete premise by the checker.
                    premise_pairs.get(*index)?;
                    SignedArithmeticStep::DefinedPremise {
                        index: *source_indices.get(index)?,
                        term: term(machine_term)?,
                    }
                }
                SignedArithmeticNode::IntervalAdd {
                    left,
                    right,
                    defined,
                    result,
                } => SignedArithmeticStep::IntervalAdd {
                    left: r(*left),
                    right: r(*right),
                    defined: r(*defined),
                    result: interval(result.clone()),
                },
                SignedArithmeticNode::IntervalAddBounded {
                    left,
                    right,
                    result,
                } => SignedArithmeticStep::IntervalAddBounded {
                    left: r(*left),
                    right: r(*right),
                    result: interval(result.clone()),
                },
                SignedArithmeticNode::IntervalSubtract {
                    left,
                    right,
                    defined,
                    result,
                } => SignedArithmeticStep::IntervalSubtract {
                    left: r(*left),
                    right: r(*right),
                    defined: r(*defined),
                    result: interval(result.clone()),
                },
                SignedArithmeticNode::IntervalMultiply {
                    left,
                    right,
                    defined,
                    result,
                } => SignedArithmeticStep::IntervalMultiply {
                    left: r(*left),
                    right: r(*right),
                    defined: r(*defined),
                    result: interval(result.clone()),
                },
                SignedArithmeticNode::IntervalRemainderAdd {
                    operand,
                    remainder,
                    addend,
                    divisor,
                    result,
                } => SignedArithmeticStep::IntervalRemainderAdd {
                    operand: r(*operand),
                    remainder: r(*remainder),
                    addend: *addend,
                    divisor: *divisor,
                    result: interval(result.clone()),
                },
                SignedArithmeticNode::IntervalRemainder {
                    operand,
                    divisor,
                    defined,
                    result,
                } => SignedArithmeticStep::IntervalRemainder {
                    operand: r(*operand),
                    divisor: *divisor,
                    defined: r(*defined),
                    result: interval(result.clone()),
                },
                SignedArithmeticNode::IntervalShiftLeft {
                    operand,
                    shift,
                    defined,
                    result,
                } => SignedArithmeticStep::IntervalShiftLeft {
                    operand: r(*operand),
                    shift: *shift,
                    defined: r(*defined),
                    result: interval(result.clone()),
                },
                SignedArithmeticNode::IntervalArithmeticShiftRight {
                    operand,
                    shift,
                    result,
                } => SignedArithmeticStep::IntervalArithmeticShiftRight {
                    operand: r(*operand),
                    shift: *shift,
                    result: interval(result.clone()),
                },
                SignedArithmeticNode::IntervalBitwiseAnd {
                    operand,
                    mask,
                    result,
                } => SignedArithmeticStep::IntervalBitwiseAnd {
                    operand: r(*operand),
                    mask: *mask,
                    result: interval(result.clone()),
                },
                SignedArithmeticNode::IntervalNarrowedCast {
                    operand,
                    source,
                    destination,
                    result,
                } => SignedArithmeticStep::IntervalNarrowedCast {
                    operand: r(*operand),
                    source: *source,
                    destination: *destination,
                    result: interval(result.clone()),
                },
                SignedArithmeticNode::IntervalCompare {
                    left,
                    right,
                    comparison: comparison_kind,
                    ..
                } => SignedArithmeticStep::IntervalCompare {
                    left: r(*left),
                    right: r(*right),
                    comparison: comparison(*comparison_kind),
                    result: surface_goal.clone(),
                },
                SignedArithmeticNode::AffinePremise {
                    source,
                    left_evidence,
                    right_evidence,
                    ..
                } => SignedArithmeticStep::AffinePremise {
                    source: r(*source),
                    left_evidence: r(*left_evidence),
                    right_evidence: r(*right_evidence),
                    result: result()?,
                },
                SignedArithmeticNode::AffineConclusion {
                    source,
                    evidence,
                    result: claim,
                } => SignedArithmeticStep::AffineConclusion {
                    source: r(*source),
                    evidence: r(*evidence),
                    result: native_conclusion(surface_goal.clone(), claim),
                },
                SignedArithmeticNode::AffineConclusionWithEvidence {
                    source,
                    left_evidence,
                    right_evidence,
                    result: claim,
                } => SignedArithmeticStep::AffineConclusionWithEvidence {
                    source: r(*source),
                    left_evidence: r(*left_evidence),
                    right_evidence: r(*right_evidence),
                    result: native_conclusion(surface_goal.clone(), claim),
                },
            };
            generated.push(surface_node);
        }
        Some(SignedIntervalPlan {
            nodes: generated,
            conclusion: *mapped.get(plan.conclusion)?,
        })
    }

    /// Name the leaves of a wide logical conjunction before closing it.
    /// Sequential checked `have` steps and `known` keep the certificate
    /// shallow without changing the kernel goal or its grouping. Reification
    /// is presentation only: every leaf must lower back to the exact goal.
    pub(in crate::surface::proof) fn wide_conjunction_surfaces(
        &self,
    ) -> Option<Vec<ClickProposition>> {
        self.conjunction_leaf_surfaces(9)
    }

    /// The spelling of each leaf of the focused conjunction, when it has at
    /// least `min_leaves` leaves and every leaf is spelled so that it lowers
    /// back to that leaf. A loop's invariant bundle is closed member by
    /// member through these at any width, as a function's `ensures` are.
    pub(in crate::surface::proof) fn conjunction_leaf_surfaces(
        &self,
        min_leaves: usize,
    ) -> Option<Vec<ClickProposition>> {
        let mut pending = vec![self.goal()?];
        let mut leaves = Vec::new();
        while let Some(goal) = pending.pop() {
            if let Proposition::And(left, right) = goal {
                pending.push(right);
                pending.push(left);
            } else {
                leaves.push(goal);
            }
        }
        // Binary certificates below this width fit comfortably inside the
        // parser's existing structural limit, including enclosing scopes.
        if leaves.len() < min_leaves {
            return None;
        }
        // Leaves are checked last first. A loop-invariant bundle guards each
        // member by every earlier declaration, so its last members are the
        // largest and the ones that exceed the synthesis bounds. Checking
        // them first makes a refusal one bounded attempt; checking in order
        // reified every earlier member first, and the binary descent that
        // follows a refusal repeated that at each level. The result does not
        // depend on the order.
        // A member is spelled as its loop head writes it, the way an
        // `ensures` is: each invariant guarded by the ones declared before
        // it, one pass on where it reads `iterations`, then the `decreases`
        // members. A written form is kept only when it lowers back to its
        // leaf. A leaf no written form matches, such as a guard lowering
        // adds, takes the goal's own spelling when the goal has one, and is
        // otherwise synthesized from the kernel goal; either is likewise
        // kept only when it lowers back. Written text comes first because it
        // prints as it was read, which a synthesized form need not.
        let goal_surfaces = self.surface_goal().and_then(|surface| {
            let mut pending = vec![surface];
            let mut surfaces = Vec::new();
            while let Some(surface) = pending.pop() {
                if let ClickProposition::And(left, right) = surface {
                    pending.push(right);
                    pending.push(left);
                } else {
                    surfaces.push(surface.clone());
                }
            }
            (surfaces.len() == leaves.len()).then_some(surfaces)
        });
        if self.surface_goal().is_some() && goal_surfaces.is_none() {
            return None;
        }
        // A goal that carries its own spelling keeps it for the ranking
        // members, which are compared with the iteration's entry value.
        let written = self
            .written_bundle_member_surfaces(goal_surfaces.is_none())
            .unwrap_or_default();
        // Each written form is lowered once, and it and each distinct part of
        // a member are keyed once: every later member repeats the guards of
        // the earlier ones, so matching is one key lookup per part.
        struct Written<'w> {
            surfaces: &'w [ClickProposition],
            lowered: Option<Vec<WrittenForm>>,
        }
        struct WrittenForm {
            index: usize,
            lowered: Proposition,
            guards: usize,
            key: Option<crate::kernel::proof::PropositionIdentityKey>,
        }
        fn guards(proposition: &Proposition) -> usize {
            let mut depth = 0;
            let mut current = proposition;
            while let Proposition::Implies(_, body) = current {
                depth += 1;
                current = body;
            }
            depth
        }
        fn written_form<'g>(
            proof: &Proof<'_>,
            goal: &'g Proposition,
            written: &mut Written<'_>,
            matched: &mut BTreeMap<&'g Proposition, Option<ClickProposition>>,
        ) -> Option<ClickProposition> {
            if let Some(known) = matched.get(goal) {
                return known.clone();
            }
            let surfaces = written.surfaces;
            let forms = written.lowered.get_or_insert_with(|| {
                surfaces
                    .iter()
                    .enumerate()
                    .filter_map(|(index, surface)| {
                        let lowered = proof
                            .lower_surface_goal(surface, "loop invariant bundle member")
                            .ok()?;
                        Some(WrittenForm {
                            index,
                            guards: guards(&lowered),
                            key: crate::kernel::proof::proposition_identity_key(&lowered),
                            lowered,
                        })
                    })
                    .collect()
            });
            // A form can only be a goal with as many guards as it has, so a
            // member's chain of guards is not keyed at every suffix.
            let depth = guards(goal);
            let mut goal_key = None;
            let direct = forms
                .iter()
                .filter(|form| form.guards == depth)
                .find(|form| {
                    let goal_key = goal_key.get_or_insert_with(|| {
                        crate::kernel::proof::proposition_identity_key(goal)
                    });
                    match (&form.key, &*goal_key) {
                        (Some(form_key), Some(goal_key)) if form_key != goal_key => false,
                        _ => {
                            crate::kernel::proof::propositions_are_alpha_equal(&form.lowered, goal)
                        }
                    }
                })
                .map(|form| surfaces[form.index].clone());
            let form = match (direct, goal) {
                (Some(surface), _) => Some(surface),
                (None, Proposition::Implies(guard, body)) => {
                    match (
                        written_form(proof, guard, written, matched),
                        written_form(proof, body, written, matched),
                    ) {
                        (Some(guard), Some(body)) => {
                            Some(ClickProposition::Implies(Box::new(guard), Box::new(body)))
                        }
                        _ => None,
                    }
                }
                (None, _) => None,
            };
            matched.insert(goal, form.clone());
            form
        }
        let mut written = Written {
            surfaces: &written,
            lowered: None,
        };
        let mut matched = BTreeMap::new();
        let mut surfaces = vec![None; leaves.len()];
        for (position, goal) in leaves.iter().enumerate().rev() {
            let member = written_form(self, goal, &mut written, &mut matched);
            surfaces[position] = Some(match (member, &goal_surfaces) {
                (Some(surface), _) => surface,
                (None, Some(goal_surfaces)) => {
                    let surface = &goal_surfaces[position];
                    let lowered = self
                        .lower_surface_goal(surface, "conjunction certificate leaf")
                        .ok()?;
                    if !crate::kernel::proof::propositions_are_alpha_equal(&lowered, goal) {
                        return None;
                    }
                    surface.clone()
                }
                (None, None) => self.synthesized_bundle_member_surface(goal)?,
            });
        }
        let surfaces = surfaces.into_iter().collect::<Option<Vec<_>>>()?;
        Some(surfaces)
    }

    /// Spell a refutation's cited premises and type ranges. A cited fact
    /// uses `spelled` or its resolved source spelling; a native comparison
    /// read as an Integer one, and a type range, are spelled from the goal's
    /// and cited facts' written observations.
    fn spell_refutation(
        &self,
        certificate: &IntegerArithmeticPlan,
        premises: &[Proposition],
        candidates: &[Proposition],
        spelled: &[(Proposition, ClickProposition)],
        surface_goal: &ClickProposition,
        spellings: &SpellingCache,
    ) -> Spelling {
        // The source spelling of a fact, resolved once per closure:
        // a retried plan cites mostly the same facts.
        let resolve = |fact: &Proposition| -> Option<(Proposition, ClickProposition)> {
            if let Some(known) = spellings.borrow().get(fact) {
                return known.clone();
            }
            let resolved = crate::kernel::search::ProofSearch::resolve_solve_premises(
                self,
                std::slice::from_ref(fact),
                &[],
            )
            .and_then(|mut spelled| spelled.pop());
            spellings
                .borrow_mut()
                .insert(fact.clone(), resolved.clone());
            resolved
        };
        // A certificate cites its premises by their source spelling; one
        // that needs a fact with none (a conjunct of a written invariant,
        // for one) is not closed by selected-premise arithmetic.
        let mut pairs: Vec<Option<(Proposition, ClickProposition)>> =
            Vec::with_capacity(premises.len());
        for premise in premises {
            if !candidates.contains(premise) {
                // Keep the actual native fact as the composition input. The
                // emitter states its observed and ordered forms with explicit
                // normalization; a synthesized reversed reading is not itself
                // an exact available premise.
                let source = candidates
                    .iter()
                    .find(|candidate| integer_readings_of_native_fact(candidate).contains(premise))
                    .and_then(resolve);
                pairs.push(source);
                continue;
            }
            if let Some(pair) = spelled.iter().find(|(fact, _)| fact == premise) {
                pairs.push(Some(pair.clone()));
                continue;
            }
            // An Integer reading the context filed beside a native fact is
            // spelled by that fact, observed: `1u32 <= x` spells
            // `1 <= to_integer(x)`.
            let Some(pair) = resolve(premise).or_else(|| {
                let native =
                    crate::kernel::assumptions::native_reading_of_integer_observation_fact(
                        premise,
                    )?;
                let (_, written) = resolve(&native)?;
                Some((
                    premise.clone(),
                    observed_native_surface_comparison(premise, &written),
                ))
            }) else {
                // A candidate with no spelling is dropped and the plan retried.
                return Spelling::UnspelledReading(premise.clone());
            };
            pairs.push(Some(pair));
        }
        let mut written = written_integer_observations(
            std::iter::once(surface_goal).chain(pairs.iter().flatten().map(|(_, surface)| surface)),
        );
        // A native comparison read as an Integer one is also spelled by the
        // native fact's own written operands: `old(*pool) >= 1` spells
        // `to_integer(old(*pool))`.
        for premise in premises
            .iter()
            .filter(|premise| !candidates.contains(premise))
        {
            let Some(source) = candidates
                .iter()
                .find(|candidate| integer_readings_of_native_fact(candidate).contains(premise))
            else {
                continue;
            };
            let Some((_, source)) = resolve(source) else {
                continue;
            };
            // `defined(a + b)` spells by its operation's operands, and a
            // fact spelled at a state keeps that state on each.
            let (selector, source) = match source {
                ClickProposition::At {
                    selector,
                    proposition,
                } => (Some(selector), *proposition),
                source => (None, source),
            };
            // A negated comparison, such as the else arm of a proof `if`,
            // `not ((b >> 32) != 0u64)`, names the same operands.
            let source = match source {
                ClickProposition::Not(inner)
                    if matches!(inner.as_ref(), ClickProposition::Comparison { .. }) =>
                {
                    *inner
                }
                source => source,
            };
            let (left, right) = match source {
                ClickProposition::Comparison { left, right, .. } => (left, right),
                ClickProposition::Defined {
                    expression:
                        ContractExpression::Add(left, right)
                        | ContractExpression::Subtract(left, right)
                        | ContractExpression::Multiply(left, right),
                } => (*left, *right),
                _ => continue,
            };
            let at = |side: ContractExpression| match &selector {
                Some(selector) => ContractExpression::At {
                    selector: selector.clone(),
                    expression: Box::new(side),
                },
                None => side,
            };
            let (left, right) = (at(left), at(right));
            for side in [left, right] {
                if matches!(side, ContractExpression::IntegerLiteral(_)) {
                    continue;
                }
                let observed = ContractExpression::Call {
                    name: "to_integer".into(),
                    arguments: vec![side],
                };
                if !written.contains(&observed) {
                    written.push(observed);
                }
            }
        }
        for (premise, pair) in premises.iter().zip(pairs.iter_mut()) {
            if pair.is_none() {
                let Some(surface) = self.spell_integer_comparison(premise, &written) else {
                    return Spelling::UnspelledReading(premise.clone());
                };
                *pair = Some((premise.clone(), surface));
            }
        }
        let pairs: Vec<(Proposition, ClickProposition)> = pairs.into_iter().flatten().collect();
        let mut ranges = match self.spell_type_ranges(certificate, &written) {
            Ok(ranges) => ranges,
            Err(value) => return Spelling::UnspelledRange(value),
        };
        match self.spell_derived_bounds(certificate, premises, &written) {
            Some(bounds) => ranges.extend(bounds),
            None => return Spelling::UnspelledBound,
        }
        Spelling::Spelled(pairs, ranges)
    }

    /// Spell an Integer comparison of two observations from `written`.
    fn spell_integer_comparison(
        &self,
        proposition: &Proposition,
        written: &[ContractExpression],
    ) -> Option<ClickProposition> {
        let Proposition::ConditionIs(condition, truth) = proposition else {
            return None;
        };
        let (left, operator, right) = match (condition.native_compat(), truth) {
            (ConditionTerm::IntegerLessEqual(left, right), true) => {
                (left, ComparisonOperator::LessEqual, right)
            }
            (ConditionTerm::IntegerLessThan(left, right), true) => {
                (left, ComparisonOperator::LessThan, right)
            }
            (ConditionTerm::IntegerGreaterEqual(left, right), true) => {
                (left, ComparisonOperator::GreaterEqual, right)
            }
            (ConditionTerm::IntegerGreaterThan(left, right), true) => {
                (left, ComparisonOperator::GreaterThan, right)
            }
            (ConditionTerm::IntegerEqual(left, right), true) => {
                (left, ComparisonOperator::Equal, right)
            }
            (ConditionTerm::IntegerEqual(left, right), false) => {
                (left, ComparisonOperator::NotEqual, right)
            }
            _ => return None,
        };
        Some(ClickProposition::Comparison {
            left: self.spell_integer_observation(left.as_ref(), written)?,
            operator,
            right: self.spell_integer_observation(right.as_ref(), written)?,
        })
    }

    /// The written expression of `term` among `written`, its literal when
    /// it is a constant, or, for `+`, `-`, `*` and negation, the same
    /// operation over its spelled operands. The checked step that cites the
    /// spelling lowers it again, so a spelling that names another term is
    /// refused there.
    fn spell_integer_observation(
        &self,
        term: &crate::kernel::IntegerTerm,
        written: &[ContractExpression],
    ) -> Option<ContractExpression> {
        if let Some(value) = term.as_const() {
            return Some(surface_signed_integer_literal(value));
        }
        if let Some(spelled) = self.spell_written_integer_observation(term, written) {
            return Some(spelled);
        }
        // An observation nothing written names, such as a population's
        // count at entry, is spelled from its value at the proof's state.
        if let crate::kernel::IntegerTerm::Machine(machine) = term
            && matches!(
                machine.ty(),
                crate::kernel::MachineIntegerType::Int32
                    | crate::kernel::MachineIntegerType::UInt32
            )
            && let Some(view) = self.premise_fixed_state_view()
        {
            // An operation under a stored narrowing refers to the counter's
            // previous value. Its introduction already has a recorded name;
            // keep that naming index in scope while spelling the operation.
            let _recorded =
                crate::surface::proof::surface_synthesis::SynthesisRecordedPointsScope::enter(
                    view.fixed_state.recorded_states,
                );
            let unsigned = machine.ty() == crate::kernel::MachineIntegerType::UInt32;
            let value = if unsigned {
                ProgramValue::UInt32(machine.value().clone())
            } else {
                ProgramValue::Int32(machine.value().clone())
            };
            if let Some(value) = crate::surface::proof::surface_synthesis::synthesize_surface_value(
                &value,
                view.parameter_binding,
                view.fixed_state.state,
            ) {
                return Some(ContractExpression::Call {
                    name: "to_integer".into(),
                    arguments: vec![if unsigned {
                        native_uint32_split_operand(value)
                    } else {
                        native_int32_split_operand(value)
                    }],
                });
            }
        }
        let operand = |inner: &crate::kernel::SharedIntegerTerm| {
            self.spell_integer_observation(inner, written).map(Box::new)
        };
        match term {
            crate::kernel::IntegerTerm::Add(left, right) => {
                Some(ContractExpression::Add(operand(left)?, operand(right)?))
            }
            crate::kernel::IntegerTerm::Subtract(left, right) => Some(
                ContractExpression::Subtract(operand(left)?, operand(right)?),
            ),
            crate::kernel::IntegerTerm::Multiply(left, right) => Some(
                ContractExpression::Multiply(operand(left)?, operand(right)?),
            ),
            crate::kernel::IntegerTerm::Negate(inner) => {
                Some(ContractExpression::Negate(operand(inner)?))
            }
            _ => None,
        }
    }

    /// The written expression among `written` that lowers to `term`, else,
    /// for the observation of a narrow value's widening, one that lowers to
    /// the narrow value's observation, the same value (rule W): the planner
    /// reads a native narrow comparison through its `int32` widenings
    /// (rule K8), whose observations are the narrow ones written. Each
    /// written expression is lowered at most once.
    fn spell_written_integer_observation(
        &self,
        term: &crate::kernel::IntegerTerm,
        written: &[ContractExpression],
    ) -> Option<ContractExpression> {
        let mut observed = Vec::with_capacity(written.len());
        for expression in written {
            let probe = ClickProposition::Comparison {
                left: expression.clone(),
                operator: ComparisonOperator::LessEqual,
                right: ContractExpression::IntegerLiteral("0".into()),
            };
            // The probe of an exact observation lowers to its native
            // comparison, which is read back as the Integer one. Zero is the
            // probe's upper side because `0 <= v` of an unsigned `v` folds to
            // true.
            let Ok(lowered) = self.lower_integer_surface_proposition(&probe, "integer observation")
            else {
                continue;
            };
            let lowered =
                crate::kernel::machine_integer::comparison::integer_observations_of_native_comparison(&lowered)
                    .into_iter()
                    .next()
                    .unwrap_or(lowered);
            let Some((ConditionTerm::IntegerLessEqual(value, _), true)) =
                lowered.condition_native()
            else {
                continue;
            };
            if value.as_ref() == term {
                return Some(expression.clone());
            }
            observed.push((expression, value.clone()));
        }
        // Only on a miss, and only a widening of a narrow value, is read
        // through: the observation the planner reads a native narrow
        // comparison by.
        let read = term.value_read();
        if std::ptr::eq(read, term)
            || !matches!(read, crate::kernel::IntegerTerm::Machine(narrow)
                if narrow.ty().format().bits() < 32)
        {
            return None;
        }
        observed
            .into_iter()
            .find(|(_, value)| value.value_read() == read)
            .map(|(expression, _)| expression.clone())
    }

    /// Spell the type range of each machine observation a `TypeRange` node
    /// of `certificate` cites, as `MIN <= to_integer(v)` or
    /// `to_integer(v) <= MAX`. The observation is spelled by a written
    /// `to_integer(...)` in the goal or a cited premise that lowers to it;
    /// `None` when one has no such spelling.
    fn spell_type_ranges(
        &self,
        certificate: &IntegerArithmeticPlan,
        written: &[ContractExpression],
    ) -> Result<Vec<SpelledBound>, crate::kernel::IntegerTerm> {
        let wanted: Vec<(&crate::kernel::IntegerTerm, bool)> = certificate
            .nodes
            .iter()
            .filter_map(|node| match node {
                IntegerArithmeticNode::TypeRange { value, upper, .. } => Some((value, *upper)),
                _ => None,
            })
            .collect();
        let mut spelled: Vec<(crate::kernel::IntegerTerm, ContractExpression)> = Vec::new();
        let mut ranges = Vec::with_capacity(wanted.len());
        for (value, upper) in wanted {
            let crate::kernel::IntegerTerm::Machine(machine) = value else {
                return Err(value.clone());
            };
            let spelling = match spelled.iter().find(|(observed, _)| observed == value) {
                Some((_, spelling)) => spelling.clone(),
                None => {
                    let Some(spelling) = self.spell_integer_observation(value, written) else {
                        return Err(value.clone());
                    };
                    spelled.push((value.clone(), spelling.clone()));
                    spelling
                }
            };
            let (min, max) = crate::kernel::machine_integer::range::observation_range(machine);
            let bound = if upper {
                ClickProposition::Comparison {
                    left: spelling,
                    operator: ComparisonOperator::LessEqual,
                    right: surface_signed_integer_literal(&max),
                }
            } else {
                ClickProposition::Comparison {
                    left: surface_signed_integer_literal(&min),
                    operator: ComparisonOperator::LessEqual,
                    right: spelling,
                }
            };
            ranges.push((BoundSource::TypeRange, value.clone(), upper, bound));
        }
        Ok(ranges)
    }

    /// The spellings of the certificate's operation bounds and excluded
    /// type bounds, each spelled side by side from `written`, or `None` when
    /// one has no spelling. An operation's operand is spelled from the
    /// operation's own written spelling: `to_integer(a >> 32)` gives
    /// `to_integer(a)`. Work is one spelling per bound node.
    fn spell_derived_bounds(
        &self,
        certificate: &IntegerArithmeticPlan,
        premises: &[Proposition],
        written: &[ContractExpression],
    ) -> Option<Vec<SpelledBound>> {
        let mut bounds = Vec::new();
        let mut operands: Option<Vec<ContractExpression>> = None;
        for node in &certificate.nodes {
            let (source, value, upper, bound) = match node {
                IntegerArithmeticNode::OperationBound { value, upper, .. } => {
                    let crate::kernel::IntegerTerm::Machine(machine) = value else {
                        return None;
                    };
                    (
                        BoundSource::Operation,
                        value.clone(),
                        *upper,
                        crate::kernel::machine_integer::bounds::operation_bound(machine, *upper)?,
                    )
                }
                IntegerArithmeticNode::ExcludedTypeBound { index, .. } => {
                    let bound = crate::kernel::proof::integer_arithmetic::excluded_type_bound(
                        premises.get(*index)?,
                    )?;
                    (
                        BoundSource::Excluded(*index),
                        crate::kernel::IntegerTerm::constant(BigInt::zero()),
                        false,
                        bound,
                    )
                }
                _ => continue,
            };
            let Some((crate::kernel::ConditionTerm::IntegerLessEqual(left, right), true)) =
                (&bound).condition_native()
            else {
                return None;
            };
            let operands = operands.get_or_insert_with(|| with_operation_operands(written));
            let left = self.spell_integer_observation(left, operands)?;
            let right = self.spell_integer_observation(right, operands)?;
            bounds.push((
                source,
                value,
                upper,
                ClickProposition::Comparison {
                    left,
                    operator: ComparisonOperator::LessEqual,
                    right,
                },
            ));
        }
        Some(bounds)
    }

    /// The premise raiser's spelling of a goal a search states, as
    /// `Proof::spelled_goal` spells a refined one, without its exemption for
    /// a smart tactic: the search writes a `have` of it.
    fn spelled_goal_for_search(&self, goal: &Proposition) -> Option<ClickProposition> {
        let recorded = (self).premise_surface_facts()?;
        crate::kernel::search::ProofSearch::available_surface_fact(self, recorded, None, goal)
            .or_else(|| {
                crate::kernel::search::ProofSearch::available_surface_fact(
                    self,
                    self.local_surface_facts(),
                    None,
                    goal,
                )
            })
    }

    /// Resolves one exact retained fact to a surface form that will lower
    /// back to that same kernel proposition when the selected proof step is
    /// checked. Historical locals are anchored before ordinary forms are
    /// considered, so a same-written newer state cannot be substituted.
    /// The fixed-state view against which a premise lookup is spelled: the
    /// focused branch's outcome data, the frontier's current state for a
    /// judgment stated mid-execution, or a fixed-state proof's own state.
    /// The last is a loop's `initialize` phase, a proof at the loop entry: it
    /// spells the contract's entry-state facts against function entry exactly
    /// as the same judgment stated in the function body does. A fixed-state
    /// proof whose state is its entry state (the same object) needs no such
    /// anchoring, and keeps its plain spellings.
    /// The fixed state premises are spelled against. Every proof state has
    /// one: an outcome, a proposition judged mid-execution, the execution
    /// frontier itself, or a fixed-state proof
    /// (`docs/internals/raise-lower-principle.md`).
    pub(super) fn premise_fixed_state_view(&self) -> Option<FixedStateOperationView<'_>> {
        self.outcome_fixed_state_view()
            .or_else(|| self.execution_proposition_fixed_state_view())
            .or_else(|| self.execution_frontier_fixed_state_view())
            .or_else(|| match self.context.as_ref() {
                ProofContext::FixedState(context)
                    if !std::ptr::eq(context.fixed_state.pre_state, context.fixed_state.state) =>
                {
                    Some(FixedStateOperationView::from_fixed_state(context))
                }
                _ => None,
            })
    }

    /// Searches the structured predecessor proof already expressible through
    /// the checked API. The goal itself fixes the value and upper bound, so
    /// this visits only selected equalities connected to that value and one
    /// exact upper-bound premise; it never tries every partially synthesizable
    /// context fact as a candidate step.
    /// The surface spelling of an exact fact, looked up as `solve` resolves
    /// the premises of a derivation it selected.
    fn unsigned_surface_fact(&self, kernel: &Proposition) -> Option<ClickProposition> {
        // A reconstructible spelling is not evidence that the fact is held.
        // In particular, a positive difference may need to be derived from
        // the unsigned guard before the predecessor lemma can use it.
        if !self.facts().contains(kernel) {
            return None;
        }
        match self.context.as_ref() {
            ProofContext::Pure(context) => {
                crate::kernel::search::ProofSearch::available_surface_fact(
                    self,
                    &context.theorem_context.surface_requirements,
                    None,
                    kernel,
                )
            }
            ProofContext::FixedState(context) => {
                crate::kernel::search::ProofSearch::available_surface_fact(
                    self,
                    context.surface_propositions,
                    context.premise_anchor.as_ref(),
                    kernel,
                )
            }
            ProofContext::Execution(_) => {
                if let Some(data) = self.focused_outcome_data() {
                    crate::kernel::search::ProofSearch::available_surface_fact(
                        self,
                        &data.surface_propositions,
                        data.premise_anchor.as_ref(),
                        kernel,
                    )
                } else {
                    let execution = self.execution()?;
                    let anchor = frontier_premise_anchor(execution);
                    crate::kernel::search::ProofSearch::available_surface_fact(
                        self,
                        &execution.presentation.surface_propositions,
                        anchor.as_ref(),
                        kernel,
                    )
                }
            }
        }
    }

    pub(super) fn solve_failure(&self) -> ClickError {
        // A range-loadability goal has a reason a reader can act on, in the
        // spelling they wrote it with. The lowered rendering below would show
        // them a byte span over an internal pointer name instead.
        if let Some(reason) = self.unproved_loadable_range_goal_reason() {
            return self.step_error(format!(
                "`solve` failed for `{}`: {reason}",
                self.claim_label()
            ));
        }
        // Name the goal as the user wrote it. Only a goal with no source
        // spelling falls back to the kind of check it makes, and that kind is
        // what was asked for, never a value it was found to have.
        let goal = self
            .surface_goal()
            .map(crate::surface::printing::authored_click_proposition)
            .filter(|source| !source.contains("__click_"))
            .map(|source| format!("`{source}`"))
            .or_else(|| {
                self.goal().map(|goal| match goal {
                    Proposition::And(_, _)
                    | Proposition::Or(_, _)
                    | Proposition::Implies(_, _)
                    | Proposition::ForAll { .. }
                    | Proposition::Exists { .. } => {
                        "a compound goal with no Click spelling".to_string()
                    }
                    Proposition::ConditionIs(condition, true) => format!(
                        "an internal {} goal with no Click spelling",
                        condition_kind(condition.native_compat())
                    ),
                    Proposition::ConditionIs(condition, false) => format!(
                        "the negation of an internal {} goal with no Click spelling",
                        condition_kind(condition.native_compat())
                    ),
                    _ => format!(
                        "the goal {}",
                        describe_pure_fact(goal, ParameterBinding::default())
                    ),
                })
            })
            .unwrap_or_else(|| "a goal that is not a proposition".into());
        self.step_error(format!(
            "`solve` failed for `{}`: could not establish {goal}{}",
            self.claim_label(),
            self.describe_goal_version_mismatch()
                .or_else(|| self.describe_goal_decided_false())
                .map(|mismatch| format!("\n  {mismatch}"))
                .unwrap_or_default(),
        ))
    }

    /// A goal whose reads all resolved to values, and that is false with
    /// them whatever else holds, is not merely unproved: it is refuted at
    /// this point. Saying so sends the reader to what was read, not to look
    /// for a missing fact.
    fn describe_goal_decided_false(&self) -> Option<String> {
        let Proposition::ConditionIs(condition, expected) = self.goal()? else {
            return None;
        };
        (crate::surface::checking::normalize_condition_without_assumptions(
            condition.native_compat(),
        ) == Some(!*expected))
        .then(|| {
            "it is false at this point: the values its reads resolve to here refute it, so no \
             further fact proves it."
                .to_string()
        })
    }

    /// The one explanation for "the goal and an available fact spell alike
    /// and read different versions", which is what a `solve` over a term that
    /// reads memory most often fails on.
    pub(super) fn describe_goal_version_mismatch(&self) -> Option<String> {
        let goal = self.goal()?;
        let names = self
            .outcome_fixed_state_view()
            .or_else(|| self.execution_fixed_state_view());
        let (parameters, arguments) = names
            .as_ref()
            .map(|view| {
                (
                    view.parameter_binding.parameters,
                    view.parameter_binding.arguments,
                )
            })
            .unwrap_or((&[], &[]));
        if !crate::kernel::resource_tracker::reads_any_resource(goal) {
            return None;
        }
        let premises = self.facts().propositions().collect::<Vec<_>>();
        let binding = ParameterBinding::new(parameters, arguments);
        let Some((mut message, explanation)) =
            crate::surface::diagnostics::describe_proposition_version_mismatch_explained(
                goal,
                &premises,
                "the available fact was stated",
                binding,
            )
        else {
            // No fact compares versions, but the goal may read a cell a
            // store on this path dropped because the store search missed.
            return self
                .store_separation_miss_for_goal(goal)
                .map(|(miss, _)| describe_recorded_store_separation_miss(&miss));
        };
        if let Some(miss) = self.store_separation_miss(&explanation) {
            message.push_str("\n  ");
            message.push_str(&describe_recorded_store_separation_miss(&miss));
        }
        Some(message)
    }

    /// The store-search miss this path retained for the store that stopped
    /// `explanation`'s walk at the cell it reads: the same written cell and
    /// the same dropped cell. It reads the path's bounded record only.
    pub(in crate::surface::proof) fn store_separation_miss(
        &self,
        explanation: &crate::kernel::resource_tracker::Explanation,
    ) -> Option<crate::surface::proof::proof_object::StoreSeparationMiss> {
        let (_, stop) = explanation.outcome.blocking_step()?;
        let crate::kernel::resource_tracker::Change::Store { pointer: written } = &stop.change
        else {
            return None;
        };
        let crate::kernel::resource_tracker::OwnedResource::Cell { pointer: read, .. } =
            &explanation.resource
        else {
            return None;
        };
        let execution = self.execution()?;
        execution
            .presentation
            .store_separation_misses
            .recent(MAX_RECORDED_STORE_SEPARATION_MISSES)
            .into_iter()
            .find(|miss| &miss.cell == read && &miss.store == written)
            .cloned()
    }

    /// The store-search miss for a cell `goal` reads, with the history
    /// explanation that ties the read to that miss's store: the read's last
    /// stretch of agreement ends at the store that dropped the cell. Only
    /// the reads of `goal` whose cell this path recorded a miss for are
    /// explained, each by one bounded history walk; diagnostics only.
    pub(in crate::surface::proof) fn store_separation_miss_for_goal(
        &self,
        goal: &Proposition,
    ) -> Option<(
        crate::surface::proof::proof_object::StoreSeparationMiss,
        crate::kernel::resource_tracker::Explanation,
    )> {
        use crate::kernel::resource_tracker::{Change, OwnedResource};
        let misses = self
            .execution()?
            .presentation
            .store_separation_misses
            .recent(MAX_RECORDED_STORE_SEPARATION_MISSES);
        if misses.is_empty() {
            return None;
        }
        crate::kernel::resource_tracker::reads_of_proposition(goal)
            .into_iter()
            .take(MAX_EXPLAINED_STORE_SEPARATION_READS)
            .find_map(|read| {
                let OwnedResource::Cell { pointer, .. } = &read.resource else {
                    return None;
                };
                let miss = misses.iter().find(|miss| &miss.cell == pointer)?;
                let explanation = crate::kernel::resource_tracker::explain_last_same(
                    read.resource.as_resource(),
                    &read.point,
                );
                let (_, stop) = explanation.outcome.blocking_step()?;
                matches!(&stop.change, Change::Store { pointer } if *pointer == miss.store)
                    .then(|| ((*miss).clone(), explanation))
            })
    }

    /// The disequality a store's index check reads for `forgotten`, spelled
    /// at this frontier from the two index words the store search compared
    /// (`surface_synthesis::synthesize_store_index_disequality`).
    pub(in crate::surface::proof) fn store_index_disequality_surface(
        &self,
        forgotten: &crate::kernel::search::store_separation::ForgottenStoreCell,
    ) -> Option<ClickProposition> {
        self.index_disequality_surface(
            &forgotten.store_index,
            &forgotten.cell_index,
            forgotten.format,
        )
    }

    /// `left != right` for two element index words compared in `format`,
    /// spelled at this frontier by
    /// `surface_synthesis::synthesize_store_index_disequality`: in a pure
    /// proof over its source names, at an execution frontier over its state
    /// with the frontier's recorded points and qualified sources in scope, as
    /// a requirement's spelling has them. Other contexts have none.
    pub(in crate::surface::proof) fn index_disequality_surface(
        &self,
        left: &crate::kernel::SharedMachineIntegerTerm,
        right: &crate::kernel::SharedMachineIntegerTerm,
        format: crate::kernel::MachineIntegerType,
    ) -> Option<ClickProposition> {
        match self.context.as_ref() {
            ProofContext::Pure(context) => {
                super::surface_synthesis::synthesize_store_index_disequality(
                    left.structural_value(),
                    right.structural_value(),
                    format,
                    ParameterBinding::new(&[], &[]),
                    &context.source_state,
                    &context.source_names,
                )
            }
            ProofContext::Execution(context) => {
                let execution = self.execution()?;
                let execution_view = execution.view(context);
                let _recorded_points =
                    super::surface_synthesis::SynthesisRecordedPointsScope::enter(
                        execution_view.recorded_states,
                    );
                let _qualified_sources = super::surface_synthesis::QualifiedSynthesisScope::enter(
                    execution_view.surface_propositions,
                );
                super::surface_synthesis::synthesize_store_index_disequality(
                    left.structural_value(),
                    right.structural_value(),
                    format,
                    context.parameter_binding(),
                    &execution.core.state,
                    &BTreeMap::new(),
                )
            }
            ProofContext::FixedState(_) => None,
        }
    }

    /// Continues one checked smart statement after its initial checked attempt
    /// has reported an unresolved requirement.  Keeping the refused result as
    /// an input makes the retry core directly testable without changing the
    /// production checked-step dispatch.
    /// A Surface spelling of `requirement` at this frontier that lowers back
    /// to it, chosen as the smart retry chooses one: the source-backed call
    /// clause first, with the caller's own predicate requirement unfolded when
    /// the call passes it through, then a synthesized spelling. `None` when
    /// neither lowers to the requirement.
    pub(in crate::surface::proof) fn requirement_surface(
        &self,
        requirement: &UnresolvedRequirement,
        step: &ProofStep,
    ) -> Result<Option<RequirementSpelling>, ClickError> {
        // A tactic that spelled its requirement where it created it is
        // stated that way, at any frontier.
        if let Some(surface) = &requirement.surface {
            return Ok(self
                .lower_surface_goal(surface, "tactic requirement")
                .is_ok_and(|lowered| lowered_covers_recorded_requirement(&lowered, requirement))
                .then(|| RequirementSpelling {
                    surface: surface.clone(),
                }));
        }
        // Reuse an exact recorded source by its proposition key. This keeps
        // proof-local binders and opaque function calls that structural
        // synthesis cannot reconstruct from C locals. A stale recorded source
        // is a spelling defect, not a reason to search other spellings.
        // Calls have their own authoritative source at this frontier. A
        // context fact's source may instead be relative to function entry.
        // Generated loan separation already names its caller-side ranges.
        // Its call site restricts proof to entry, but supplies no source clause.
        let generated_separation = requirement.call_site.as_ref().is_some_and(|site| {
            site.source_requirement_ordinal.is_none()
                && matches!(
                    requirement.proposition,
                    Proposition::ResourceSeparate { .. }
                )
        });
        let recorded = if requirement.call_site.is_none() || generated_separation {
            self.local_surface_facts()
                .recorded_requirement_surface(&requirement.proposition)
                .or_else(|| {
                    self.context_surface_propositions()?
                        .recorded_requirement_surface(&requirement.proposition)
                })
        } else {
            None
        };
        if let Some(surface) = recorded {
            let lowered = self.lower_surface_goal(surface, "recorded tactic requirement")?;
            if !lowered_covers_recorded_requirement(&lowered, requirement) {
                return Err(self.step_error("a recorded tactic requirement does not round-trip"));
            }
            return Ok(Some(RequirementSpelling {
                surface: surface.clone(),
            }));
        }
        if requirement.call_site.is_none()
            && let Some(spelling) = literal_requirement_spelling(requirement)
        {
            return Ok(Some(spelling));
        }
        // Fixed-state and focused-outcome requirements can refer to reads
        // retained from an intermediate statement. Give their raiser the
        // same indexed historical names as ordinary facts and goals.
        let _binder_names = self.requirement_binder_name_scope();
        let spelling_view = self.premise_fixed_state_view();
        let _requirement_points = spelling_view.as_ref().map(|view| {
            super::surface_synthesis::SynthesisRecordedPointsScope::enter(
                view.fixed_state.recorded_states,
            )
        });
        let non_execution_surface = match self.context.as_ref() {
            ProofContext::Pure(context) => Some(
                super::surface_synthesis::synthesize_surface_proposition_with_bound_variable_names(
                    &requirement.proposition,
                    ParameterBinding::new(&[], &[]),
                    &context.source_state,
                    &context.source_names,
                ),
            ),
            ProofContext::FixedState(context) => Some(
                super::surface_synthesis::synthesize_surface_proposition_at_entry_and_post(
                    &requirement.proposition,
                    context.parameter_binding,
                    context.fixed_state.pre_state,
                    context.fixed_state.state,
                ),
            ),
            ProofContext::Execution(_) => self.outcome_fixed_state_view().map(|view| {
                let post = view.fixed_state.native_result().map_or_else(
                    || view.fixed_state.state.clone(),
                    |result| {
                        view.fixed_state
                            .state
                            .clone()
                            .with_local(crate::kernel::CONTRACT_RESULT, result.into_owned())
                    },
                );
                super::surface_synthesis::synthesize_surface_proposition_at_entry_and_post(
                    &requirement.proposition,
                    view.parameter_binding,
                    view.fixed_state.pre_state,
                    &post,
                )
            }),
        };
        if let Some(surface) = non_execution_surface {
            let surface = surface.ok_or_else(|| self.step_error(
                "a generated prerequisite has no Surface form; this is a raise-lower principle defect",
            ).with_unresolved_requirement(&ProofObligation::verification_condition(requirement.proposition.clone())))?;
            let lowered = self.lower_surface_goal(&surface, "proof definedness requirement")?;
            if !lowered_states_requirement(&lowered, requirement) {
                return Err(self.step_error(
                    "a proof definedness requirement does not round-trip; this is a raise-lower principle defect",
                ));
            }
            return Ok(Some(RequirementSpelling { surface }));
        }
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Ok(None);
        };
        let Some(execution) = self.execution() else {
            return Ok(None);
        };
        let execution_view = execution.view(context);
        let _recorded_points = super::surface_synthesis::SynthesisRecordedPointsScope::enter(
            execution_view.recorded_states,
        );
        let _qualified_sources = super::surface_synthesis::QualifiedSynthesisScope::enter(
            execution_view.surface_propositions,
        );
        let admit = |candidate: ClickProposition| {
            let lowered = self.lower_surface_goal(&candidate, "step obligation");
            match lowered {
                Ok(lowered) if lowered_states_requirement(&lowered, requirement) => Some(candidate),
                _ => None,
            }
        };
        // An `assert`'s false-path truthiness obligation (`0 == 1`) holds only
        // where that path is unreachable; at the pre-state, the requirement it
        // stands for is the asserted condition, which is what a proof shows.
        // Proving it there lets the step decide the assertion and prune the
        // false path; the step's own checking then confirms that it did.
        if let Some(condition) = &requirement.assertion_condition {
            let surface = self.asserted_condition_given_context(condition);
            return Ok(self
                .lower_surface_goal(&surface, "asserted condition")
                .is_ok()
                .then_some(RequirementSpelling { surface }));
        }
        if requirement.call_site.is_some() && !generated_separation {
            // A call requirement must retain its authoritative call source.
            // Synthesis may restate an admitted source, never replace missing
            // or mismatching call metadata.
            let Some(registry_surface) =
                source_backed_call_requirement_surface(requirement, step, execution, context)
            else {
                return Ok(literal_requirement_spelling(requirement));
            };
            let direct_caller =
                source_backed_direct_caller_requirement(requirement, step, execution, context);
            let candidate = match &direct_caller {
                Some((predicate_name, _)) => {
                    let unfolded = vec![predicate_name.clone()];
                    unfold_surface_predicates(
                        context.spec_definitions.predicates,
                        &registry_surface.proposition,
                        &unfolded,
                    )
                    .map_err(|message| self.step_error(message))?
                }
                None => registry_surface.proposition,
            };

            if let Some(surface) = admit(candidate) {
                return Ok(Some(RequirementSpelling { surface }));
            }
        }
        check_verification_deadline()?;
        Ok(synthesize_surface_proposition(
            &requirement.proposition,
            context.parameter_binding(),
            &execution.core.state,
        )
        .and_then(|surface| {
            // Synthesis spells a conjunction conjunct by conjunct, but one
            // conjunct's spelling can already state the whole requirement:
            // `defined(owner->len + 1)` over a read through a resource lowers
            // to the sum's overflow condition and the read's definedness, so
            // spelling the read's definedness again changes the lowering.
            let conjuncts = match &surface {
                ClickProposition::And(left, right) => {
                    vec![left.as_ref().clone(), right.as_ref().clone()]
                }
                _ => Vec::new(),
            };
            admit(surface).or_else(|| conjuncts.into_iter().find_map(admit))
        })
        .map(|surface| RequirementSpelling { surface }))
    }
}

/// How many resources `solve` opens for one C statement before it reports
/// the statement's refusal. A statement touches a bounded number of places,
/// and each opening must hold one of them.
const MAX_AUTO_OPENINGS_PER_STATEMENT: usize = 4;

/// How many forgotten cells the implicit tail tries to keep across one C
/// statement's stores. Each costs one `solve` of an index disequality.
const MAX_STORE_SEPARATIONS_PER_STATEMENT: usize = 4;

/// How many reads of one failed goal are compared with the path's
/// store-search misses.
const MAX_EXPLAINED_STORE_SEPARATION_READS: usize = 8;

/// How many store-search misses one execution path retains for its reports.
/// Recording stops at the cap; a report names only a miss it retained.
pub(in crate::surface::proof) const MAX_RECORDED_STORE_SEPARATION_MISSES: usize = 32;

/// How many available disequalities `solve` tries, in turn, as the fact an
/// assumed equality of its disequality goal contradicts.
const MAX_REFUTED_EQUALITY_PREMISES: usize = 4;

/// How many variables solve's bound selection visits from a goal's own
/// variables before it stops following bounds to further variables.
const MAX_BOUND_VARIABLES: usize = 8;

thread_local! {
    static ACTIVE_SOLVE_FALLBACKS: std::cell::Cell<u8> = const { std::cell::Cell::new(0) };
}

#[derive(Clone, Copy)]
enum SolveFallback {
    FunctionUnfold = 2,
    ConnectedFacts = 4,
    ArithmeticSubgoal = 8,
    StoredValue = 16,
    MatchArithmetic = 32,
    RefutedEquality = 64,
    ElementAddress = 128,
}

/// A candidate can try the other fallback and descend through logical
/// structure, but cannot restart a fallback already evaluating that candidate.
/// The outer rewrite search still owns its equality chain and closing probes.
struct SolveFallbackScope(SolveFallback);

impl SolveFallbackScope {
    fn active(fallback: SolveFallback) -> bool {
        ACTIVE_SOLVE_FALLBACKS.with(|active| active.get() & fallback as u8 != 0)
    }

    fn enter(fallback: SolveFallback) -> Option<Self> {
        ACTIVE_SOLVE_FALLBACKS.with(|active| {
            let bit = fallback as u8;
            if active.get() & bit != 0 {
                return None;
            }
            active.set(active.get() | bit);
            Some(Self(fallback))
        })
    }
}

impl Drop for SolveFallbackScope {
    fn drop(&mut self) {
        ACTIVE_SOLVE_FALLBACKS.with(|active| active.set(active.get() & !(self.0 as u8)));
    }
}

/// The checked unfold and rewrite steps one constructor evaluation may take.
const CONSTRUCTOR_EVALUATION_FUEL: usize = 8;

/// The connected facts one constructor evaluation reads for constructor
/// equations once it is stuck.
const CONSTRUCTOR_EVALUATION_FACTS: usize = 16;

/// How deeply one upper-bound split may nest inside another's arms.
const MAX_UPPER_BOUND_SPLIT_DEPTH: usize = 2;

thread_local! {
    static UPPER_BOUND_SPLIT_DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

struct UpperBoundSplitScope;

impl UpperBoundSplitScope {
    fn enter() -> Option<Self> {
        UPPER_BOUND_SPLIT_DEPTH.with(|depth| {
            (depth.get() < MAX_UPPER_BOUND_SPLIT_DEPTH).then(|| {
                depth.set(depth.get() + 1);
                UpperBoundSplitScope
            })
        })
    }
}

impl Drop for UpperBoundSplitScope {
    fn drop(&mut self) {
        UPPER_BOUND_SPLIT_DEPTH.with(|depth| depth.set(depth.get().saturating_sub(1)));
    }
}

/// How many recently recorded program points solve offers, beside function
/// entry, as the source of a transport of its goal.
const MAX_TRANSPORT_SOURCE_POINTS: usize = 8;

/// How many available upper bounds on a split pivot an upper-bound split
/// offers, in turn, as the headroom premise that keeps `pivot + 1` from
/// wrapping.
const MAX_INCREMENT_HEADROOM_PREMISES: usize = 4;

/// The entry-anchored spelling of a constructor equality whose written form no
/// longer lowers to `equality` at this frontier. `None` when the written form
/// still denotes the fact, when the equality is not a constructor equation, or
/// when anchoring does not recover the same fact. Anchoring is a last resort in
/// [`Proof::available_surface_fact`]: it renames one premise the source already
/// stated, never a fact no spelling reached.
fn entry_anchored_constructor_equality(
    proof: &Proof<'_>,
    surface: &ClickProposition,
    equality: &Proposition,
) -> Option<ClickProposition> {
    let ClickProposition::Comparison {
        left,
        operator: ComparisonOperator::Equal,
        right,
    } = surface
    else {
        return None;
    };
    if !matches!(right, ContractExpression::AlgebraicConstructor { .. })
        || matches!(left, ContractExpression::Old(_))
        || proof
            .lower_surface_proposition_direct(surface, "entry-anchored premise form")
            .is_ok_and(|lowered| &lowered == equality)
    {
        return None;
    }
    let anchored = ClickProposition::Comparison {
        left: ContractExpression::Old(Box::new(left.clone())),
        operator: ComparisonOperator::Equal,
        right: right.clone(),
    };
    proof
        .lower_surface_proposition_direct(&anchored, "entry-anchored premise form")
        .is_ok_and(|lowered| &lowered == equality)
        .then_some(anchored)
}

/// The direct logical closing steps, in their fixed order, whose kernel rule
/// can match the goal's outer connective. `known` closes a conjunction
/// or disjunction from facts as well as a goal that is itself a fact, and
/// `enumerate` closes only a universal; on any other goal it is refused
/// before it reads a fact, so omitting it changes no outcome and saves
/// rendering the goal into a refusal once per candidate at every `intro`
/// level.
/// Whether context-free normalization proves a condition false: its other
/// polarity normalizes to true, the check `contradiction` makes.
fn normalization_refutes(proposition: &Proposition) -> bool {
    let Proposition::ConditionIs(condition, value) = proposition else {
        return false;
    };
    crate::kernel::proof::fact_reasoning::normalizes_context_free_leaf(&Proposition::condition_is(
        condition.clone(),
        !value,
    ))
}

fn direct_logical_candidates(goal: Option<&Proposition>) -> Vec<ProofStep> {
    let mut steps = vec![ProofStep::Known, ProofStep::Normalize];
    // Without a proposition goal every candidate is refused alike; keep the
    // complete list so the recorded refusals are unchanged.
    if matches!(goal, Some(Proposition::ForAll { .. }) | None) {
        steps.push(ProofStep::Enumerate);
    }
    steps
}

/// Whether the goal is one or more implications or universals over a
/// conjunction, which the direct logical closer introduces but cannot split.
fn conjunction_under_binders(goal: Option<&Proposition>) -> bool {
    let mut current = match goal {
        Some(Proposition::Implies(_, body) | Proposition::ForAll { body, .. }) => body.as_ref(),
        _ => return false,
    };
    loop {
        match current {
            Proposition::And(_, _) => return true,
            Proposition::Implies(_, body) | Proposition::ForAll { body, .. } => {
                current = body.as_ref()
            }
            _ => return false,
        }
    }
}

/// The existential witness closer is reserved for the source-backed range
/// slice.  In particular, a generated overflow guard (as in `string::readable`)
/// remains on the dynamic state-transport route.  The worklist is bounded
/// because this predicate is part of smart closure dispatch.
fn quantified_external_range_goal(goal: &Proposition) -> bool {
    const MAX_NODES: usize = 4096;
    let mut work = vec![goal];
    let mut visited = 0usize;
    let mut saw_range = false;
    while let Some(current) = work.pop() {
        visited = visited.saturating_add(1);
        crate::instrumentation::record_deterministic_work(1);
        if check_verification_deadline().is_err() {
            return false;
        }
        if visited > MAX_NODES {
            return false;
        }
        match current {
            Proposition::MemoryLoadable { base, .. }
                if matches!(base.base, crate::kernel::AddressBase::ExternalArgument) =>
            {
                saw_range = true;
            }
            condition_source_0 @ Proposition::ConditionIs(_, _)
                if let Some((
                    ConditionTerm::Overflows {
                        format: MachineIntegerType::Int32,
                        op: OverflowOperation::Add,
                        left: _,
                        right: _,
                    },
                    _,
                )) = condition_source_0.condition_native() =>
            {
                return false;
            }
            Proposition::And(left, right)
            | Proposition::Or(left, right)
            | Proposition::Implies(left, right) => {
                work.push(right);
                work.push(left);
            }
            Proposition::Not(body)
            | Proposition::ForAll { body, .. }
            | Proposition::Exists { body, .. } => work.push(body),
            Proposition::MemoryLoadable { .. } => return false,
            Proposition::ConditionIs(_, _) => {}
            _ => return false,
        }
    }
    saw_range
}

/// Compare retained-have round-trip forms while applying the kernel's load
/// naming law to condition leaves. The lockstep worklist keeps this path
/// iterative and bounded and never clones an entire proposition tree.
/// Whether a lowered proposition states `requirement`: exactly, up to
/// canonical condition loads, or as the consequent left under the guards
/// lowering put in front of it (generated arithmetic guards and path-fact
/// guards, which no Surface connective spells). Proving that consequent is
/// enough for the retried step, whose kernel check still sees the guard.
impl<'a> Proof<'a> {
    /// An asserted condition as the pre-state proof states it: a disjunct
    /// whose negation the context states exactly is dropped, so `rhs == 0 or
    /// x <= MAX / rhs` under `rhs != 0` is `x <= MAX / rhs`. The step's false
    /// path then carries the negation of what was proved, and is pruned by
    /// the exact conflict check. Each disjunct is one exact lookup.
    fn asserted_condition_given_context(&self, condition: &ProgramExpression) -> ClickProposition {
        let surface = asserted_condition_proposition(condition);
        let mut disjuncts = Vec::new();
        let mut pending = vec![surface.clone()];
        while let Some(next) = pending.pop() {
            match next {
                ClickProposition::Or(left, right) => {
                    pending.push(*right);
                    pending.push(*left);
                }
                other => disjuncts.push(other),
            }
        }
        if disjuncts.len() < 2 {
            return surface;
        }
        let assumptions = self.facts().assumptions();
        let refuted = |disjunct: &ClickProposition| {
            self.lower_surface_goal(disjunct, "asserted condition disjunct")
                .ok()
                .is_some_and(|lowered| {
                    let negated = match lowered {
                        Proposition::ConditionIs(condition, value) => {
                            Proposition::condition_is(condition, !value)
                        }
                        other => Proposition::Not(Box::new(other)),
                    };
                    assumptions.states_required_goal(&negated)
                })
        };
        let kept = disjuncts
            .into_iter()
            .filter(|disjunct| !refuted(disjunct))
            .collect::<Vec<_>>();
        kept.into_iter()
            .reduce(|left, right| ClickProposition::Or(Box::new(left), Box::new(right)))
            .unwrap_or(surface)
    }

    /// Whether `lowered`, a written proposition, states `requirement`. An
    /// `assert`'s truthiness obligation is stated by the asserted condition,
    /// as written or as [`Self::asserted_condition_given_context`] narrows
    /// it, which is how `requirement_surface` spells it.
    pub(in crate::surface::proof) fn written_states_requirement(
        &self,
        lowered: &Proposition,
        requirement: &UnresolvedRequirement,
    ) -> bool {
        let Some(condition) = &requirement.assertion_condition else {
            return lowered_states_requirement(lowered, requirement);
        };
        [
            asserted_condition_proposition(condition),
            self.asserted_condition_given_context(condition),
        ]
        .iter()
        .any(|surface| {
            self.lower_surface_goal(surface, "asserted condition")
                .is_ok_and(|spelled| propositions_match_after_canonical_loads(&spelled, lowered))
        })
    }
}

/// The Surface proposition that a C condition is true: its comparisons and
/// logical connectives as written, and any other operand as `e != 0`.
fn asserted_condition_proposition(condition: &ProgramExpression) -> ClickProposition {
    let comparison = |left: &ProgramExpression, operator, right: &ProgramExpression| {
        ClickProposition::Comparison {
            left: ContractExpression::ProgramExpression(left.clone()),
            operator,
            right: ContractExpression::ProgramExpression(right.clone()),
        }
    };
    match condition {
        ProgramExpression::And(left, right) => ClickProposition::And(
            Box::new(asserted_condition_proposition(left)),
            Box::new(asserted_condition_proposition(right)),
        ),
        ProgramExpression::Or(left, right) => ClickProposition::Or(
            Box::new(asserted_condition_proposition(left)),
            Box::new(asserted_condition_proposition(right)),
        ),
        ProgramExpression::Not(inner) => {
            ClickProposition::Not(Box::new(asserted_condition_proposition(inner)))
        }
        ProgramExpression::Equal(left, right) => comparison(left, ComparisonOperator::Equal, right),
        ProgramExpression::NotEqual(left, right) => {
            comparison(left, ComparisonOperator::NotEqual, right)
        }
        ProgramExpression::LessThan(left, right) => {
            comparison(left, ComparisonOperator::LessThan, right)
        }
        ProgramExpression::LessEqual(left, right) => {
            comparison(left, ComparisonOperator::LessEqual, right)
        }
        ProgramExpression::GreaterThan(left, right) => {
            comparison(left, ComparisonOperator::GreaterThan, right)
        }
        ProgramExpression::GreaterEqual(left, right) => {
            comparison(left, ComparisonOperator::GreaterEqual, right)
        }
        other => comparison(
            other,
            ComparisonOperator::NotEqual,
            &ProgramExpression::Value(int32(0)),
        ),
    }
}

/// A completely evaluated obligation still goes through an ordinary proof.
/// Prefer its authoritative source when one exists; this literal is the
/// complete source for an evaluated inlined call without an outer source clause.
fn literal_requirement_spelling(
    requirement: &UnresolvedRequirement,
) -> Option<RequirementSpelling> {
    let Some((ConditionTerm::Constant(value), polarity)) =
        (&requirement.proposition).condition_native()
    else {
        return None;
    };
    if requirement.assertion_condition.is_some() {
        return None;
    }
    // The `bool` literal lowers to exactly this constant condition; a closed
    // comparison such as `0 == 1` is retained by lowering instead.
    let literal = ClickProposition::Value(crate::surface::bool_literal(*value));
    Some(RequirementSpelling {
        surface: if *polarity {
            literal
        } else {
            ClickProposition::Not(Box::new(literal))
        },
    })
}

// A recorded source was already selected by its exact proposition key. It
// may state evaluation guards together with that proposition. This is not
// the matcher that chooses among a tactic's written `requires` clauses:
// proving a trivial goal cannot identify which clause the author selected.
fn lowered_covers_recorded_requirement(
    lowered: &Proposition,
    requirement: &UnresolvedRequirement,
) -> bool {
    lowered_states_requirement(lowered, requirement)
        || crate::kernel::listed_premise_holds(&requirement.proposition, |part| {
            crate::kernel::proof::fact_reasoning::exact_fact_contains_conjunct(lowered, part)
        })
}

pub(super) fn lowered_states_requirement(
    lowered: &Proposition,
    requirement: &UnresolvedRequirement,
) -> bool {
    if propositions_match_after_canonical_loads(lowered, &requirement.proposition)
        // A resource spelling includes its formation prerequisites. Proving
        // that complete conjunction proves the selected exact requirement;
        // never discard the extra goals or consult ambient facts here.
        || (matches!(requirement.proposition, Proposition::ResourceSeparate { .. } | Proposition::ResourceContains { .. })
            && crate::kernel::proof::fact_reasoning::exact_fact_contains_conjunct(
                lowered,
                &requirement.proposition,
            ))
    {
        return true;
    }
    let mut target = &requirement.proposition;
    for introduction in &requirement.introductions {
        if !matches!(
            introduction,
            crate::kernel::LoweringIntroduction::ObligationGuard
                | crate::kernel::LoweringIntroduction::PathFactGuard
        ) {
            break;
        }
        let Proposition::Implies(_, consequent) = target else {
            break;
        };
        target = consequent;
        if propositions_match_after_canonical_loads(lowered, target) {
            return true;
        }
    }
    false
}

// The selected source and requirement can use native or retained comparisons.
// Compare their normalized direction and canonical read operands, without
// exporting a retained arithmetic tree or consulting the proof context.
fn same_canonical_word_comparison(left: &Proposition, right: &Proposition) -> bool {
    use crate::kernel::machine_integer::{Relation, comparison::comparison_view};
    use crate::kernel::proof::signed_arithmetic::SignedArithmeticAtom as Atom;
    let (Proposition::ConditionIs(a, av), Proposition::ConditionIs(b, bv)) = (left, right) else {
        return false;
    };
    let (Some(a), Some(b)) = (
        comparison_view(a.native_compat(), *av),
        comparison_view(b.native_compat(), *bv),
    ) else {
        return false;
    };
    if a.format.format().bits() != 32 || b.format.format().bits() != 32 || a.relation != b.relation
    {
        return false;
    }
    let equality = matches!(a.relation, Relation::Equal | Relation::NotEqual);
    if !equality && a.format != b.format {
        return false;
    }
    let atoms = |view: &crate::kernel::machine_integer::comparison::NativeComparisonView<'_>| {
        view.operands
            .each_ref()
            .map(|v| Atom::from_canonical_operand(v.operand_view()))
    };
    let ([Some(al), Some(ar)], [Some(bl), Some(br)]) = (atoms(&a), atoms(&b)) else {
        return false;
    };
    al == bl && ar == br || equality && al == br && ar == bl
}

// Null comparisons may lower with the null operand on the other side.
// Both operands must name the same canonical addresses at the same polarity.
fn same_reversed_address_comparison(left: &Proposition, right: &Proposition) -> bool {
    let (
        Some((ConditionTerm::AddressEqual(left_a, left_b), left_value)),
        Some((ConditionTerm::AddressEqual(right_a, right_b), right_value)),
    ) = (left.condition_native(), right.condition_native())
    else {
        return false;
    };
    left_value == right_value && left_a == right_b && left_b == right_a
}

pub(super) fn propositions_match_after_canonical_loads(
    left: &Proposition,
    right: &Proposition,
) -> bool {
    const MAX_NODES: usize = 4096;
    let mut work = vec![(left, right)];
    let mut visited = 0usize;
    while let Some((left, right)) = work.pop() {
        visited = visited.saturating_add(1);
        if visited > MAX_NODES {
            return false;
        }
        match (left, right) {
            (Proposition::And(left, right), Proposition::And(other_left, other_right))
            | (Proposition::Or(left, right), Proposition::Or(other_left, other_right))
            | (Proposition::Implies(left, right), Proposition::Implies(other_left, other_right)) => {
                work.push((right, other_right));
                work.push((left, other_left));
            }
            (Proposition::Not(body), Proposition::Not(other_body)) => {
                work.push((body, other_body));
            }
            // A constant condition and a closed literal comparison, which
            // lowering retains as written, match by the truth they state.
            (Proposition::ConditionIs(left, expected), Proposition::ConditionIs(right, other))
                if closed_condition_value(left.native_compat()).is_some()
                    && closed_condition_value(right.native_compat()).is_some() =>
            {
                if (closed_condition_value(left.native_compat()) == Some(*expected))
                    != (closed_condition_value(right.native_compat()) == Some(*other))
                {
                    return false;
                }
            }
            (Proposition::ConditionIs(_, _), Proposition::ConditionIs(_, _)) => {
                let left = crate::kernel::canonical_condition_fact(left);
                let right = crate::kernel::canonical_condition_fact(right);
                if !propositions_are_alpha_equal(&left, &right)
                    && !same_canonical_word_comparison(&left, &right)
                    && !same_reversed_address_comparison(&left, &right)
                {
                    return false;
                }
            }
            (
                Proposition::MemoryLoadable {
                    memory: lm,
                    base: lb,
                    bytes: ln,
                    wide: lw,
                },
                Proposition::MemoryLoadable {
                    memory: rm,
                    base: rb,
                    bytes: rn,
                    wide: rw,
                },
            ) => {
                let left = crate::kernel::pointer_read_over_immediate_store(lb);
                let right = crate::kernel::pointer_read_over_immediate_store(rb);
                if lm != rm
                    || ln != rn
                    || lw != rw
                    || left.as_ref().unwrap_or(lb) != right.as_ref().unwrap_or(rb)
                {
                    return false;
                }
            }
            _ => {
                if !propositions_are_alpha_equal(left, right) {
                    return false;
                }
            }
        }
    }
    true
}

use crate::kernel::machine_integer::comparison::closed_condition_value;

#[test]
fn literal_requirement_matching_respects_both_truth_and_polarity() {
    for value in [false, true] {
        for polarity in [false, true] {
            let requirement = Proposition::condition_is(ConditionTerm::Constant(value), polarity);
            for written in [false, true] {
                let spelling = Proposition::condition_is(ConditionTerm::Constant(written), true);
                assert_eq!(
                    propositions_match_after_canonical_loads(&spelling, &requirement),
                    written == (value == polarity),
                );
            }
        }
    }
}

fn source_backed_refusal(
    error: &ClickError,
    current_memory: &crate::kernel::SymbolicMemory,
) -> Result<bool, ClickError> {
    let Some(requirement) = error.unresolved_requirement() else {
        return Ok(false);
    };
    let Some(site) = requirement.call_site.as_ref() else {
        return Ok(false);
    };
    if crate::kernel::MemoryStateIdentity::of(current_memory) != site.source_memory_state {
        return Ok(false);
    }
    source_backed_requirement_is_supported(
        &requirement.proposition,
        site.source_requirement_ordinal,
        site.source_requirement_is_state_independent,
        site.source_load_state,
    )
}

/// Recover the written source clause that produced one unresolved call
/// requirement.  This is deliberately a narrow, fail-closed lookup: the
/// carrier's callee, interface, source ordinal, argument expressions, and
/// frontier memory identity all have to agree before a source form is
/// admitted to the retained-have retry.
struct SourceBackedCallSurface {
    arguments: Vec<ProgramExpression>,
    source_proposition: ClickProposition,
    proposition: ClickProposition,
}

/// Validate the carrier against the current concrete call before any source
/// declaration is consulted.  The returned owned call is deliberately small:
/// the statement splitter does not expose borrowed argument storage.
fn source_backed_call_requirement_surface(
    requirement: &UnresolvedRequirement,
    step: &ProofStep,
    execution: &ExecutionProofState,
    context: &ExecutionProofContext<'_>,
) -> Option<SourceBackedCallSurface> {
    let source = requirement.call_site.as_ref()?;
    let source_ordinal = source.source_requirement_ordinal?;
    let site = source.site.as_ref();

    if crate::kernel::MemoryStateIdentity::of(execution.core.state.memory())
        != site.source_memory_state
    {
        return None;
    }

    // Confirm that the refused operation is still the exact source call that
    // generated this carrier. This protects retries after a caller has been
    // moved to a different frontier, and keeps source arguments authoritative
    // rather than reconstructing them from a reduced state.
    let (_, _, statement, _) = next_top_level_statement_from_frontier_position(
        execution.view(context),
        &execution.core.state,
        context.function,
        context.arguments,
        context.claim_label,
        context.tactic_index,
        "smart retained-have call source",
    )
    .ok()?;
    // A call made while a C++ local with a destructor lives carries that
    // destructor for its exceptional exit; the call is its body.
    let mut statement = &statement;
    while let ProgramStatement::UnwindCleanup { body, .. } = statement {
        statement = body;
    }
    let (callee, arguments) = match statement {
        ProgramStatement::Call {
            function_name,
            arguments,
            ..
        }
        | ProgramStatement::CallConstruct {
            function_name,
            arguments,
            ..
        }
        | ProgramStatement::CallResult {
            function_name,
            arguments,
            ..
        } => (function_name, arguments),
        _ => return None,
    };
    let source_registry = context.function_source_registry();
    let ordinary_source = source_registry.ordinary_function(site.callee.as_ref());
    // Named callback application records the selected contract name as both
    // callee and interface, while the C statement names the callback
    // expression.  This is the one authorized alias for an indirect call;
    // every other carrier must name the exact current C callee.
    let named_interface_alias =
        site.callee.as_str() == site.interface.as_ref() && ordinary_source.is_none();
    let source_callee = site.source_callee.as_deref().unwrap_or(&site.callee);
    match step {
        ProofStep::StepContract(_) => {
            // A named callback interface still belongs to the exact C call
            // that produced the refusal.  The selected named-contract alias
            // above is the only indirect representation that may differ.
            if callee != source_callee && !named_interface_alias {
                return None;
            }
        }
        ProofStep::StepCall(transport) if transport.is_named_contract() => {
            if callee != source_callee && !named_interface_alias {
                return None;
            }
        }
        ProofStep::StepCall(_) => {
            // StepCall is the concrete-call operation: both the C symbol and
            // the selected interface must be the carrier's concrete callee.
            if callee != source_callee || site.interface.as_ref() != site.callee {
                return None;
            }
        }
        ProofStep::Step | ProofStep::StepBind(_) => {
            // Even an indirect callback must retain the exact function-pointer
            // expression named by the carrier before routing through its
            // selected interface, except for the named-contract alias above.
            if callee != source_callee && !named_interface_alias {
                return None;
            }
        }
        _ => return None,
    }
    if arguments.as_slice()
        != site
            .source_invocation_arguments
            .as_ref()
            .unwrap_or(&site.source_arguments)
            .as_slice()
    {
        return None;
    }
    let arguments = site.source_arguments.as_ref().clone();
    let expected_interface = match step {
        ProofStep::StepContract(application) => application.name.as_str(),
        ProofStep::StepCall(transport) if transport.is_named_contract() => transport.callee(),
        ProofStep::Step | ProofStep::StepBind(_) | ProofStep::StepCall(_) => {
            site.interface.as_ref()
        }
        _ => return None,
    };
    if site.interface.as_ref() != expected_interface {
        return None;
    }

    let use_named_interface = matches!(step, ProofStep::StepContract(_))
        || matches!(step, ProofStep::StepCall(transport) if transport.is_named_contract())
        || site.interface.as_ref() != site.callee.as_str()
        || ordinary_source.is_none();

    // Ordinary C calls use the file-scoped registry keyed by the carrier's
    // callee. Named callback and StepContract interfaces instead resolve by
    // their interface name. Both paths index directly by the checked source
    // ordinal; resources, generated clauses, and out-of-range entries fail
    // closed without consulting ambient/project facts.
    // The by-value aggregate parameters of an ordinary callee: the call
    // copies each argument into its parameter object, and its contract reads
    // that copy, which this call's parameter point names.
    let mut aggregate_parameters = BTreeSet::new();
    let (source_parameter_names, source_parameter_types, source_proposition) =
        if use_named_interface {
            let definition = context
                .spec_definitions
                .predicates
                .contract_definition(source.interface.as_ref());
            let definition = definition?;
            let requirement = definition.function_block().requires().get(source_ordinal)?;
            let parameters = definition.function_block().signature().parameters();
            (
                parameters
                    .iter()
                    .map(|parameter| {
                        crate::surface::surface_parameter_binding(&parameter.binding_name())
                    })
                    .collect::<Vec<_>>(),
                parameters
                    .iter()
                    .map(|parameter| {
                        parameter
                            .click_type()
                            .interface_type()
                            .map(InterfaceType::to_kernel_type)
                    })
                    .collect::<Vec<_>>(),
                requirement.proposition()?.clone(),
            )
        } else {
            let source = ordinary_source?.get(source_ordinal)?;
            let proposition = match source {
                FunctionRequirementSource::Proposition(proposition) => proposition.clone(),
                FunctionRequirementSource::LoadableSegment(segment) => ClickProposition::Loadable {
                    segment: segment.clone(),
                },
            };
            let function = context
                .function_environment
                .get_function(site.callee.as_ref())?;
            aggregate_parameters.extend(
                function
                    .parameters()
                    .iter()
                    .filter(|parameter| parameter.aggregate_layout().is_some())
                    .map(|parameter| parameter.name().to_string()),
            );
            (
                function
                    .parameters()
                    .iter()
                    .map(|parameter| {
                        crate::surface::surface_parameter_binding(&parameter.binding_name())
                    })
                    .collect::<Vec<_>>(),
                function
                    .parameters()
                    .iter()
                    .map(|parameter| Some(parameter.program_type()))
                    .collect::<Vec<_>>(),
                proposition,
            )
        };

    let value_parameter_count = if use_named_interface {
        site.value_arguments.len()
    } else {
        0
    };
    if source_parameter_names.len() != site.source_arguments.len() + value_parameter_count {
        return None;
    }
    let mut substitutions = source_parameter_names
        .iter()
        .zip(&source_parameter_types)
        .zip(site.source_arguments.iter())
        .map(|((parameter, parameter_type), argument)| {
            // An identity cast of a caller parameter is that parameter: the
            // surface names it as the caller's own requirement does, with the
            // C-string bridge elaborated as its explicit byte view.
            let argument = match caller_parameter_through_identity_cast(
                argument,
                context.parsed_function.parameters(),
                &execution.core.state,
            ) {
                Some(slot) => caller_parameter_as_argument(
                    &context.parsed_function.parameters()[slot],
                    *parameter_type,
                ),
                None => caller_embedded_record_argument(argument, context.parsed_function)
                    .unwrap_or_else(|| {
                        ContractExpression::ProgramExpression(
                            super::surface_synthesis::source_c_argument(argument),
                        )
                    }),
            };
            (parameter.clone(), argument)
        })
        .collect::<BTreeMap<_, _>>();
    if !aggregate_parameters.is_empty() {
        // This call's parameter point, which the step that prepared it
        // recorded; it must bind each by-value aggregate parameter.
        let point = execution
            .presentation
            .surface_record
            .last_call_parameters
            .as_ref()?;
        let bound = execution.presentation.recorded_states.get(point)?;
        for parameter in &aggregate_parameters {
            bound.locals().aggregate_layout(parameter)?;
            substitutions.insert(
                parameter.clone().into(),
                ContractExpression::RegionParameter {
                    region: point.region.clone(),
                    name: parameter.clone(),
                },
            );
        }
    }
    let written_values = match step {
        ProofStep::StepCall(transport) => transport
            .value_arguments()
            .iter()
            .map(|(name, value)| (name.as_str(), value))
            .collect::<BTreeMap<_, _>>(),
        _ => BTreeMap::new(),
    };
    // Value parameters belong to the selected contract application, not the
    // C argument list. Use the exact held-term index (one selected name),
    // or the value's literal; do not enumerate aliases or ambient facts.
    for (name, value) in site.value_arguments.iter() {
        let expression = if let Some(written) = written_values.get(name.as_str()) {
            (*written).clone()
        } else if super::resources::is_integer_constant(value) {
            ContractExpression::ProgramExpression(ProgramExpression::Value(value.clone()))
        } else {
            let term = match value {
                ProgramValue::Int32(term)
                | ProgramValue::UInt32(term)
                | ProgramValue::Int64(term)
                | ProgramValue::UInt64(term) => term,
                _ => return None,
            };
            let local = execution
                .core
                .state
                .locals()
                .names_holding_integer(term)
                .next()?;
            ContractExpression::ProgramExpression(ProgramExpression::Variable(
                crate::kernel::program_local_source_name(local).to_owned(),
            ))
        };
        substitutions.insert(name.clone().into(), expression);
    }
    // Match contract lowering: adapt a signed character argument to the
    // predicate's byte parameter before substituting the call arguments.
    // Keep the original source clause for source-ID and parameter selection.
    let elaborated = crate::surface::lowering::elaborate_character_byte_views(
        &source_proposition,
        context.spec_definitions.predicates,
        &|name| {
            let slot = source_parameter_names
                .iter()
                .position(|parameter| parameter.source_name() == name)?;
            match source_parameter_types[slot]? {
                crate::kernel::ProgramType::Int8Pointer => Some(InterfaceType::Int8Pointer),
                crate::kernel::ProgramType::Int8Array(size) => Some(InterfaceType::Int8Array(size)),
                _ => None,
            }
        },
    );
    // A call step's binder map names the caller instance each callee binder
    // is: the callee's field reads become reads of that caller instance.
    let mut referenced_instances = BTreeSet::new();
    crate::surface::proof::fixed_state_proofs::conversion_conditions::walk_written_expressions_in_proposition(
        &source_proposition,
        &mut |expression| {
            if let ContractExpression::ResourceField(access) = expression {
                referenced_instances.insert(access.identity);
            }
        },
    );
    let instance_renames = match step {
        ProofStep::StepCall(transport) => transport
            .binders()
            .iter()
            .map(|binding| {
                (
                    binding.binder().to_string(),
                    crate::surface::lowering::InstanceRename {
                        name: binding.instance().to_string(),
                        identity: binding.binder_identity(),
                        target_identity: Some(binding.identity()),
                    },
                )
            })
            .collect::<BTreeMap<_, _>>(),
        _ => site
            .resource_arguments
            .iter()
            .filter(|(_, identity, _)| referenced_instances.contains(identity))
            .map(|(binder, identity, actual)| {
                let name = crate::kernel::model_fields::registered_instance_spelling(*actual)?;
                Some((
                    binder.clone(),
                    crate::surface::lowering::InstanceRename {
                        name: name.to_string(),
                        identity: *identity,
                        target_identity: Some(*actual),
                    },
                ))
            })
            .collect::<Option<BTreeMap<_, _>>>()?,
    };

    let proposition = crate::surface::lowering::substitute_click_proposition_in(
        elaborated.as_ref().unwrap_or(&source_proposition),
        &crate::surface::lowering::ContractSubstitutions::with_instance_renames(
            &substitutions,
            &instance_renames,
        ),
    )
    .ok()?;
    Some(SourceBackedCallSurface {
        arguments,
        source_proposition,
        proposition,
    })
}

pub(in crate::surface::proof) fn source_backed_direct_caller_requirement(
    requirement: &UnresolvedRequirement,
    step: &ProofStep,
    execution: &ExecutionProofState,
    context: &ExecutionProofContext<'_>,
) -> Option<(String, CallerRequirementSelection)> {
    let source = requirement.call_site.as_ref()?;
    if !matches!(
        step,
        ProofStep::Step | ProofStep::StepBind(_) | ProofStep::StepCall(_)
    ) || source.interface.as_ref() != source.callee.as_str()
    {
        return None;
    }
    let resolved = source_backed_call_requirement_surface(requirement, step, execution, context)?;
    let ClickProposition::PredicateCall { arguments, .. } = &resolved.source_proposition else {
        return None;
    };
    let callee = context
        .function_environment
        .get_function(source.callee.as_ref())?;
    if callee.parameters().len() != resolved.arguments.len() {
        return None;
    }
    let selected = arguments
        .iter()
        .enumerate()
        .filter_map(|(predicate_argument_slot, argument)| {
            let ContractExpression::ProgramExpression(ProgramExpression::Variable(callee_name)) =
                argument
            else {
                return None;
            };
            let callee_slot = callee.parameters().iter().position(|parameter| {
                parameter.binding_name() == callee_name || callee_name.is_named(parameter.name())
            })?;
            let caller_slot = caller_parameter_through_identity_cast(
                &resolved.arguments[callee_slot],
                context.parsed_function.parameters(),
                &execution.core.state,
            )?;
            Some((predicate_argument_slot, caller_slot))
        })
        .collect::<Vec<_>>();
    let [(predicate_argument_slot, caller_parameter_slot)] = selected.as_slice() else {
        return None;
    };
    let ClickProposition::PredicateCall {
        name: predicate_name,
        arguments: mut substituted_arguments,
    } = resolved.proposition
    else {
        return None;
    };
    // The caller's requirement names its parameter; an identity cast of it
    // is the same pointer, so the registry is consulted with the bare name,
    // or with its byte view where the predicate reads `uint8` bytes of a
    // signed plain `char` pointer (the elaborated C-string bridge).
    let caller_parameter = &context.parsed_function.parameters()[*caller_parameter_slot];
    let predicate_parameter_type = context
        .spec_definitions
        .predicates
        .get(&predicate_name)?
        .parameters()
        .get(*predicate_argument_slot)
        .and_then(|parameter| parameter.click_type().interface_type())
        .map(InterfaceType::to_kernel_type);
    *substituted_arguments.get_mut(*predicate_argument_slot)? =
        caller_parameter_as_argument(caller_parameter, predicate_parameter_type);
    let entry_state = context.constants.function_entry_state.as_ref()?;
    let entry_memory_state = crate::kernel::MemoryStateIdentity::of(entry_state.memory());
    // Phase 1 projects entry requirements only across an effect-free prefix.
    // Local declarations change the current state without adding an
    // effect, while stores and havoc do add one. Crossing a recorded memory
    // effect requires the later generated-load transport identity.
    if !execution.core.effect_facts.is_empty() {
        return None;
    }
    let owner = context.constants.caller_source_owner.as_ref()?;
    let selection = context
        .constants
        .caller_requirement_index
        .lookup_unique_caller_requirement(
            owner,
            &predicate_name,
            *predicate_argument_slot,
            *caller_parameter_slot,
            &substituted_arguments,
            entry_memory_state,
        )?;
    Some((predicate_name, selection))
}

/// Resolve a nominal embedded-reference cast through its declared offset/type
/// index. A zero-offset child retains its own field path and receiver type.
fn caller_embedded_record_argument(
    argument: &ProgramExpression,
    function: &crate::languages::interface::ImportedFunction,
) -> Option<ContractExpression> {
    let mut root = argument;
    let mut projections = Vec::new();
    while let ProgramExpression::Cast {
        expression,
        pointee_struct: Some(target),
        ..
    } = root
    {
        crate::instrumentation::record_deterministic_work(1);
        let (parent, offset) = match expression.as_ref() {
            ProgramExpression::PointerOffsetBytes { pointer, bytes } => (pointer.as_ref(), *bytes),
            parent => (parent, 0),
        };
        projections.push((offset, target.as_str()));
        root = parent;
    }
    if projections.is_empty() {
        return None;
    }
    let ProgramExpression::Variable(binding) = root else {
        return None;
    };
    let parameter = function
        .parameters()
        .iter()
        .find(|parameter| parameter.matches_binding(binding));
    let nominal = parameter
        .and_then(|parameter| parameter.struct_name())
        .or_else(|| {
            function
                .local_struct_pointers()
                .get(binding)
                .map(String::as_str)
        })
        .or_else(|| {
            function
                .local_struct_values()
                .get(binding)
                .map(String::as_str)
        })?;
    let mut layout = function.record_layout(nominal)?;
    let mut result = match parameter {
        Some(parameter) => caller_parameter_as_argument(parameter, None),
        None => {
            ContractExpression::ProgramExpression(super::surface_synthesis::source_c_argument(root))
        }
    };
    let source_root = crate::surface::lowering::contract_expression_as_program_expression(&result)
        .expect("declared object source is a program expression");
    let mut accumulated_offset = 0;
    for (offset, target) in projections.into_iter().rev() {
        crate::instrumentation::record_deterministic_work(1);
        let name = layout.embedded_struct_field(offset, target)?;
        let field = layout.field(name).expect("indexed embedded field");
        let nominal = field.struct_name().expect("indexed embedded record");
        accumulated_offset += field.offset_bytes();
        result = ContractExpression::Field {
            base: Box::new(result),
            field: name.to_owned(),
            pointee_struct: None,
            lowered: crate::kernel::program_expression::pointer_offset_bytes(
                source_root.clone(),
                accumulated_offset,
            ),
            offset_bytes: field.offset_bytes(),
        };
        layout = function
            .record_layout(nominal)
            .expect("indexed record layout");
    }
    Some(result)
}

/// A caller parameter, with its explicit byte view when the expected type
/// reads unsigned bytes through a signed character pointer.
fn caller_parameter_as_argument(
    parameter: &crate::languages::interface::ImportedParameter,
    expected: Option<crate::kernel::ProgramType>,
) -> ContractExpression {
    match expected {
        Some(expected)
            if crate::surface::lowering::needs_character_byte_view(
                parameter.interface_type(),
                expected,
            ) =>
        {
            crate::surface::lowering::character_byte_view(
                crate::surface::surface_parameter_binding(parameter.binding_name()),
            )
        }
        _ => ContractExpression::ProgramExpression(ProgramExpression::Variable(
            crate::surface::surface_parameter_binding(parameter.binding_name()),
        )),
    }
}

/// The caller parameter a call argument names, directly or through a cast
/// that leaves the pointer unchanged: the same kernel type, such as `char *`
/// or `unsigned char *` for a `uint8 *` parameter, adding no `volatile`.
/// Constness is a property of the access path, not of the pointer, and a
/// read predicate grants no write permission, so a `const` cast is identity
/// here too.
fn caller_parameter_through_identity_cast(
    argument: &ProgramExpression,
    parameters: &[crate::languages::interface::ImportedParameter],
    state: &crate::kernel::ExecutionState,
) -> Option<usize> {
    let (name, cast_type, cast_struct) = match argument {
        ProgramExpression::Variable(name) => (name, None, None),
        ProgramExpression::Cast {
            expression,
            target_type,
            pointee_struct,
            pointee_volatile: false,
            ..
        } => match expression.as_ref() {
            ProgramExpression::Variable(name) => {
                (name, Some(*target_type), pointee_struct.as_deref())
            }
            _ => return None,
        },
        _ => return None,
    };
    // A local holding a parameter's own pointer value, as `p = bytes;`
    // leaves it, names the same storage; the caller has already required
    // that no effect separates entry from this call.
    let slot = parameters
        .iter()
        .position(|parameter| parameter.matches_binding(name))
        .or_else(|| {
            let held = state.scalar_local_value(name)?;
            let mut matching = parameters.iter().enumerate().filter(|(_, parameter)| {
                state.scalar_local_value(parameter.binding_name()).as_ref() == Some(&held)
            });
            match (matching.next(), matching.next()) {
                (Some((slot, _)), None) => Some(slot),
                _ => None,
            }
        })?;
    // Equal numeric addresses do not erase a projected object's record type.
    // Its fields may differ from the enclosing parameter's, even at offset zero.
    if cast_struct.is_some_and(|name| parameters[slot].struct_name() != Some(name)) {
        return None;
    }
    // A cast between character pointer types also names the same storage:
    // one byte has one value, read through either signedness.
    match cast_type {
        Some(target_type)
            if target_type != parameters[slot].interface_type().to_kernel_type()
                && !(target_type.is_character_pointer()
                    && parameters[slot]
                        .interface_type()
                        .to_kernel_type()
                        .is_character_pointer()) =>
        {
            None
        }
        _ => Some(slot),
    }
}

/// Whether a fact the last step checked is the focused goal under another
/// spelling of the same order claim. A theorem may check an already-stated
/// conclusion, so this uses its checked conclusions rather than only its new
/// facts. One comparison per conclusion of that explicit step.
fn checked_fact_spells_the_goal(proof: &Proof<'_>) -> bool {
    proof.goal().is_some_and(|goal| {
        proof.checked_facts().iter().any(|fact| {
            fact != goal && crate::kernel::proof::fact_reasoning::order_claim_equivalent(fact, goal)
        })
    })
}

// Probe with the already-lowered goal: its bound variables retain their
// identities even when the surface goal uses an internal alpha-renamed binder.
// Re-lowering that surface spelling outside its binder scope is not valid.
fn mirrored_order_goal(goal: &Proposition) -> Option<Proposition> {
    let Proposition::ConditionIs(condition, value) = goal else {
        return None;
    };
    let mirrored = match condition.native_compat() {
        ConditionTerm::Compare {
            format,
            relation,
            left,
            right,
        } => {
            let relation = match relation {
                CompareRelation::LessThan => CompareRelation::GreaterThan,
                CompareRelation::LessEqual => CompareRelation::GreaterEqual,
                CompareRelation::GreaterThan => CompareRelation::LessThan,
                CompareRelation::GreaterEqual => CompareRelation::LessEqual,
                CompareRelation::Equal => return None,
            };
            ConditionTerm::Compare {
                format: *format,
                relation,
                left: right.clone(),
                right: left.clone(),
            }
        }
        ConditionTerm::IntegerLessThan(left, right) => {
            ConditionTerm::IntegerGreaterThan(right.clone(), left.clone())
        }
        ConditionTerm::IntegerLessEqual(left, right) => {
            ConditionTerm::IntegerGreaterEqual(right.clone(), left.clone())
        }
        ConditionTerm::IntegerGreaterThan(left, right) => {
            ConditionTerm::IntegerLessThan(right.clone(), left.clone())
        }
        ConditionTerm::IntegerGreaterEqual(left, right) => {
            ConditionTerm::IntegerLessEqual(right.clone(), left.clone())
        }
        _ => return None,
    };
    Some(Proposition::condition_is(mirrored, *value))
}

/// `b == a` for the fact `a == b`.
fn swapped_bitvector_equality(fact: &Proposition) -> Option<Proposition> {
    // A 32-bit equality swaps at `int32` (rule K6); an 8- or 16-bit one at
    // its own format.
    let Some((
        ConditionTerm::Compare {
            format:
                format @ (MachineIntegerType::Int32
                | MachineIntegerType::UInt32
                | MachineIntegerType::Int8
                | MachineIntegerType::UInt8
                | MachineIntegerType::Int16
                | MachineIntegerType::UInt16),
            relation: CompareRelation::Equal,
            left,
            right,
        },
        value,
    )) = fact.condition_native()
    else {
        return None;
    };
    Some(Proposition::condition_is(
        ConditionTerm::Compare {
            format: ConditionTerm::fact_format(*format, CompareRelation::Equal),
            relation: CompareRelation::Equal,
            left: right.clone(),
            right: left.clone(),
        },
        *value,
    ))
}

/// Whether a goal is explicitly named by a restricted premise, either as
/// the premise itself or as one of its conjunction leaves. Checked fact
/// indexing makes those leaves available to `known`; this predicate
/// keeps that closure tied to the user's finite `using` list.
fn selected_premise_contains_goal(premise: &Proposition, goal: &Proposition) -> bool {
    if premise == goal || condition_polarity_equivalent(premise, goal) {
        return true;
    }
    match premise {
        Proposition::And(left, right) => {
            selected_premise_contains_goal(left, goal)
                || selected_premise_contains_goal(right, goal)
        }
        _ => false,
    }
}

#[cfg(test)]
mod synthesized_literal_tests {
    use super::*;

    #[test]
    fn native_comparison_observation_preserves_synthesized_integer_alias() {
        let kernel = Proposition::condition_is(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left: Box::new(MachineTerm::Variable(Variable(991984))),
                right: Box::new(MachineTerm::constant(10)),
            },
            true,
        );
        let value = crate::surface::proof::surface_synthesis::integer_typed_expression(
            ContractExpression::Call {
                name: "to_integer".into(),
                arguments: vec![ContractExpression::Binding("x".into())],
            },
        );
        let written = ClickProposition::Comparison {
            left: ContractExpression::At {
                selector: ProgramPointSelector::ProgramPoint(ProgramPointRef {
                    region: CodeRegionRef::Function,
                    kind: ProgramPointKind::Entry,
                }),
                expression: Box::new(value),
            },
            operator: ComparisonOperator::LessEqual,
            right: ContractExpression::IntegerLiteral("10".into()),
        };
        assert_eq!(
            observed_native_surface_comparison(&kernel, &written),
            written
        );
    }

    #[test]
    fn requirement_matching_does_not_select_an_unrelated_trivial_goal() {
        let _session = crate::kernel::VerificationSession::enter();
        let requirement = |proposition| UnresolvedRequirement {
            proposition,
            context: None,
            introductions: Default::default(),
            call_site: None,
            assertion_condition: None,
            surface: None,
        };
        let less_equal = |left, right| ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessEqual,
            left: Box::new(left),
            right: Box::new(right),
        };
        let trivial = Proposition::condition_is(less_equal(0u32.into(), 0u32.into()), true);
        let bound = Proposition::condition_is(
            less_equal(MachineTerm::var(Variable(71_229)), 10u32.into()),
            true,
        );
        assert!(!lowered_states_requirement(
            &bound,
            &requirement(trivial.clone())
        ));
        assert!(lowered_states_requirement(
            &trivial,
            &requirement(trivial.clone())
        ));
        let whole = Proposition::And(Box::new(trivial.clone()), Box::new(bound));
        assert!(!lowered_states_requirement(&whole, &requirement(trivial)));
        let separation = Proposition::ResourceSeparate {
            left: Box::new(crate::kernel::Resource::Emp),
            right: Box::new(crate::kernel::Resource::Emp),
        };
        let whole = Proposition::And(Box::new(whole), Box::new(separation.clone()));
        assert!(lowered_states_requirement(&whole, &requirement(separation)));
    }

    #[test]
    fn signed_certificate_spelling_matches_exact_read_atoms() {
        use crate::kernel::{Address, LoadKind, SymbolicMemory, intern_memory};
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Address::symbolic(Variable(71_230));
        let before = intern_memory(SymbolicMemory::new());
        let after = intern_memory(before.memory().clone().store(
            pointer.clone(),
            ProgramValue::Int32(MachineTerm::constant(1)),
        ));
        let read = |memory, pointer, kind| MachineTerm::MemoryLoad(memory, Box::new(pointer), kind);
        let value = read(
            crate::kernel::ProgramPoint::at(&before),
            pointer.clone(),
            LoadKind::Int32,
        );
        let atom = |term: &MachineTerm| {
            crate::kernel::proof::signed_arithmetic::SignedArithmeticAtom::from_canonical_operand(
                crate::kernel::MachineOperandView::Legacy(term),
            )
        };
        assert_eq!(atom(&value), atom(&value));
        for other in [
            read(
                crate::kernel::ProgramPoint::at(&after),
                pointer.clone(),
                LoadKind::Int32,
            ),
            read(
                crate::kernel::ProgramPoint::at(&before),
                pointer.offset_by_bytes(4),
                LoadKind::Int32,
            ),
            read(
                crate::kernel::ProgramPoint::at(&before),
                pointer,
                LoadKind::UInt32,
            ),
        ] {
            assert_ne!(atom(&value), atom(&other));
        }
    }

    #[test]
    fn retained_requirements_match_mirrored_orders_and_stored_read_sources() {
        use crate::kernel::{
            Address, CompareRelation as R, KernelTerm, LoadKind, MachineBinaryOp as Op,
            MachineOperandView as V, SymbolicMemory, intern_memory,
        };
        let _session = crate::kernel::VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let x = MachineTerm::Variable(Variable(71231));
        let sum = MachineTerm::logical_machine_binary(ty, Op::Add, x, 1u32.into());
        let pointer = Address::symbolic(Variable(71232));
        let before = intern_memory(SymbolicMemory::new());
        let after = intern_memory(
            before
                .memory()
                .clone()
                .store(pointer.clone(), ProgramValue::Int32(sum.clone())),
        );
        let read =
            |memory| MachineTerm::MemoryLoad(memory, Box::new(pointer.clone()), LoadKind::Int32);
        let retained = |relation, left: &MachineTerm, right: &MachineTerm| {
            let roots =
                [left, right].map(|v| KernelTerm::retained_machine_operand(ty, V::Legacy(v)));
            Proposition::condition_is(
                crate::kernel::machine_integer::comparison::condition_for_operand_views(
                    ty,
                    relation,
                    roots.each_ref().map(V::Shared),
                ),
                true,
            )
        };
        let zero = MachineTerm::constant(0);
        let order = retained(R::GreaterEqual, &sum, &zero);
        let mirror = retained(R::LessEqual, &zero, &sum);
        let exports = crate::kernel::KernelTermExport::machine_export_count();
        assert!(propositions_match_after_canonical_loads(&order, &mirror));
        assert!(!propositions_match_after_canonical_loads(
            &order,
            &retained(R::LessThan, &zero, &sum)
        ));
        let native = Proposition::condition_is(
            ConditionTerm::Compare {
                format: ty,
                relation: R::Equal,
                left: Box::new(sum.clone()),
                right: Box::new(sum.clone()),
            },
            true,
        );
        assert!(propositions_match_after_canonical_loads(
            &native,
            &retained(
                R::Equal,
                &read(crate::kernel::ProgramPoint::at(&after)),
                &sum
            )
        ));
        assert!(!propositions_match_after_canonical_loads(
            &native,
            &retained(
                R::Equal,
                &read(crate::kernel::ProgramPoint::at(&before)),
                &sum
            )
        ));
        assert_eq!(
            crate::kernel::KernelTermExport::machine_export_count(),
            exports
        );
    }

    #[test]
    fn upper_bound_split_reads_integer_observations_of_the_native_increment() {
        let _session = crate::kernel::VerificationSession::enter();
        let index = Variable(71_220);
        let pivot = MachineTerm::Variable(Variable(71_221));
        let observe = |value| {
            crate::kernel::IntegerTerm::from_machine(MachineIntegerType::Int32, value).unwrap()
        };
        let bound = |amount| {
            Proposition::condition_is(
                ConditionTerm::integer_less_than(
                    observe(MachineTerm::Variable(index)),
                    observe(MachineTerm::add_at(
                        MachineIntegerType::Int32,
                        pivot.clone(),
                        MachineTerm::constant(amount),
                    )),
                ),
                true,
            )
        };
        let accepted = bound(1);
        let rejected = bound(2);
        let exports = crate::kernel::KernelTermExport::machine_export_count();
        assert_eq!(
            kernel_upper_bound_split_candidate(&accepted),
            Some((
                index,
                crate::kernel::SharedMachineIntegerTerm::intern(
                    MachineIntegerType::Int32,
                    pivot.clone()
                )
            ))
        );
        assert!(kernel_upper_bound_split_candidate(&rejected).is_none());
        assert_eq!(
            crate::kernel::KernelTermExport::machine_export_count(),
            exports
        );
    }

    #[test]
    fn signed_literal_spelling_handles_int32_minimum_without_overflow() {
        let minimum = surface_signed_integer_literal(&BigInt::from(i32::MIN));
        assert!(matches!(
            minimum,
            ContractExpression::Negate(inner)
                if matches!(inner.as_ref(), ContractExpression::IntegerLiteral(value) if value == "2147483648")
        ));

        let ordinary = surface_signed_integer_literal(&BigInt::from(-17));
        assert!(matches!(
            ordinary,
            ContractExpression::Negate(inner)
                if matches!(inner.as_ref(), ContractExpression::IntegerLiteral(value) if value == "17")
        ));
    }

    fn comparison(left: &str, operator: ComparisonOperator, right: &str) -> ClickProposition {
        let expression = |text: &str| match text.parse::<i64>() {
            Ok(_) => ContractExpression::IntegerLiteral(text.to_string()),
            Err(_) => ContractExpression::Binding(text.to_string()),
        };
        ClickProposition::Comparison {
            left: expression(left),
            operator,
            right: expression(right),
        }
    }

    #[test]
    fn arithmetic_operand_anchoring_preserves_negated_comparison_polarity() {
        for (operator, complement) in [
            (
                ComparisonOperator::LessEqual,
                ComparisonOperator::GreaterThan,
            ),
            (
                ComparisonOperator::LessThan,
                ComparisonOperator::GreaterEqual,
            ),
            (
                ComparisonOperator::GreaterEqual,
                ComparisonOperator::LessThan,
            ),
            (
                ComparisonOperator::GreaterThan,
                ComparisonOperator::LessEqual,
            ),
            (ComparisonOperator::Equal, ComparisonOperator::NotEqual),
            (ComparisonOperator::NotEqual, ComparisonOperator::Equal),
        ] {
            let original = comparison("a", operator, "b");
            let negated = ClickProposition::Not(Box::new(original.clone()));
            assert_eq!(
                surface_comparison_with_anchored_operands(&negated),
                comparison("a", complement, "b")
            );
            let doubled = ClickProposition::Not(Box::new(negated));
            assert_eq!(
                surface_comparison_with_anchored_operands(&doubled),
                original
            );
        }
    }

    /// A `>`-spelled premise is the same ordered pair as its `<` restatement,
    /// so adding it to a `>=`-spelled premise must pair the lower sides with
    /// each other.  Leaving the "greater" sides unswapped printed
    /// `(a + 0) < (0 + b)`, which no longer lowered to the kernel's sum.
    #[test]
    fn printed_sum_orders_a_greater_than_premise_like_its_less_than_spelling() {
        let strict = comparison("a", ComparisonOperator::GreaterThan, "0");
        let loose = comparison("b", ComparisonOperator::GreaterEqual, "0");
        let sum = integer_surface_add(&strict, &loose).expect("the sum is printable");

        let restated = comparison("0", ComparisonOperator::LessThan, "a");
        let restated_sum = integer_surface_add(&restated, &loose).expect("the sum is printable");
        assert_eq!(sum, restated_sum);

        let ClickProposition::Comparison {
            left,
            operator,
            right,
        } = &sum
        else {
            panic!("the printed sum is a comparison");
        };
        assert_eq!(*operator, ComparisonOperator::LessThan);
        assert_eq!(
            *left,
            ContractExpression::Add(
                Box::new(ContractExpression::IntegerLiteral("0".into())),
                Box::new(ContractExpression::IntegerLiteral("0".into())),
            )
        );
        assert_eq!(
            *right,
            ContractExpression::Add(
                Box::new(ContractExpression::Binding("a".into())),
                Box::new(ContractExpression::Binding("b".into())),
            )
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/surface/proof/smart_closures/synthesized_literal_tests.rs");
    }
}

/// How a 32-bit unsigned order relates its two operands.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum UnsignedOrder {
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
}

/// A held `uint32` order and its operands.
fn unsigned_order_parts(
    proposition: &Proposition,
) -> Option<(UnsignedOrder, MachineTerm, MachineTerm)> {
    let Some((
        ConditionTerm::Compare {
            format: MachineIntegerType::UInt32,
            relation:
                relation @ (crate::kernel::CompareRelation::LessThan
                | crate::kernel::CompareRelation::LessEqual
                | crate::kernel::CompareRelation::GreaterThan
                | crate::kernel::CompareRelation::GreaterEqual),
            left,
            right,
        },
        true,
    )) = proposition.condition_native()
    else {
        return None;
    };
    let order = match relation {
        CompareRelation::LessThan => UnsignedOrder::Less,
        CompareRelation::LessEqual => UnsignedOrder::LessEqual,
        CompareRelation::GreaterThan => UnsignedOrder::Greater,
        CompareRelation::GreaterEqual => UnsignedOrder::GreaterEqual,
        CompareRelation::Equal => return None,
    };
    Some((order, left.as_ref().clone(), right.as_ref().clone()))
}

/// A step requirement spelled in Surface syntax.
pub(in crate::surface::proof) struct RequirementSpelling {
    pub(in crate::surface::proof) surface: ClickProposition,
}

/// The disjuncts of a disjunction, flattened.
fn flattened_disjuncts(proposition: &Proposition) -> Vec<&Proposition> {
    let mut disjuncts = Vec::new();
    let mut pending = vec![proposition];
    while let Some(next) = pending.pop() {
        match next {
            Proposition::Or(left, right) => {
                pending.push(right);
                pending.push(left);
            }
            other => disjuncts.push(other),
        }
    }
    disjuncts
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/surface/proof/smart_closures/indexed_arithmetic_tests.rs");
    mod product_identity {
        include!("../../scaling_tests/surface/proof/smart_closures/product_identity_tests.rs");
    }
}

/// The sides of a native machine equality fact a smart `rewrite` can cite:
/// a 32- or 64-bit equality, or an 8- or 16-bit one, which is the same fact
/// as the `int32` equality of its widenings (rule K8).
fn rewrite_equality_sides(equality: &Proposition) -> Option<(&MachineTerm, &MachineTerm)> {
    match equality {
        condition_source_0 @ Proposition::ConditionIs(_, true)
            if let Some((
                ConditionTerm::Compare {
                    format,
                    relation: CompareRelation::Equal,
                    left,
                    right,
                },
                _,
            )) = condition_source_0.condition_native()
                && (format.format().bits() < 32
                    || matches!(
                        format,
                        MachineIntegerType::Int32
                            | MachineIntegerType::UInt32
                            | MachineIntegerType::Int64
                    )) =>
        {
            Some((left, right))
        }
        _ => None,
    }
}

/// A machine literal: a smart `rewrite` reduces operands to literals and
/// never expands one.
fn is_rewrite_literal(term: &MachineTerm) -> bool {
    matches!(term, MachineTerm::Constant { .. })
}

#[test]
fn machine_offset_refusal_respects_wraparound_and_word_width() {
    use crate::kernel::IntegerTerm;
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        MachineIntegerType::Int64,
        MachineIntegerType::UInt64,
    ] {
        let base = MachineTerm::Variable(Variable(981_772));
        let observe = |value| IntegerTerm::from_machine(format, value).unwrap();
        let three =
            crate::kernel::machine_integer::range::constant_word(format, &3.into()).unwrap();
        let plus_three = observe(MachineTerm::logical_machine_binary(
            format,
            MachineBinaryOp::Add,
            base.clone(),
            three,
        ));
        let exact_three = IntegerTerm::add(observe(base.clone()), IntegerTerm::constant(3.into()));
        let exact_four = IntegerTerm::add(observe(base.clone()), IntegerTerm::constant(4.into()));
        assert!(!incompatible_machine_offsets(&plus_three, &exact_three));
        assert!(incompatible_machine_offsets(&plus_three, &exact_four));
        let modulo_three = IntegerTerm::add(
            observe(base),
            IntegerTerm::constant(BigInt::from(3) + (BigInt::one() << format.format().bits())),
        );
        assert!(
            !incompatible_machine_offsets(&plus_three, &modulo_three),
            "congruence alone must not reject equal residues"
        );
    }
}

#[test]
fn operation_identities_order_dependencies_with_multiple_roots() {
    use crate::kernel::IntegerTerm;
    let format = MachineIntegerType::Int32;
    let inner = MachineTerm::logical_machine_binary(
        format,
        MachineBinaryOp::Add,
        MachineTerm::Variable(Variable(989_776)),
        MachineTerm::constant(1),
    );
    let outer = MachineTerm::logical_machine_binary(
        format,
        MachineBinaryOp::Add,
        inner.clone(),
        MachineTerm::constant(2),
    );
    let inner = IntegerTerm::from_machine(format, inner).unwrap();
    let outer = IntegerTerm::from_machine(format, outer).unwrap();
    for roots in [
        vec![inner.clone(), outer.clone()],
        vec![outer.clone(), inner.clone()],
    ] {
        let identities = operation_identities(roots);
        assert_eq!(identities.len(), 2);
        assert_eq!(identities[0].0, outer);
        assert_eq!(identities[1].0, inner);
    }
}

// Discovery methods are deliberately not methods of Proof.

// Source spelling adapters for the kernel ProofSearch interface.
mod search;

impl<'a> Proof<'a> {
    /// The recorded spellings premises are read from: a pure theorem's
    /// requirements, a fixed-state proof's or outcome's recorded lowerings,
    /// or the execution frontier's.
    pub(super) fn premise_surface_facts(&self) -> Option<&SurfacePropositionMap> {
        match self.context.as_ref() {
            ProofContext::Pure(context) => Some(&context.theorem_context.surface_requirements),
            ProofContext::FixedState(context) => Some(context.surface_propositions),
            ProofContext::Execution(_) => match self.focused_outcome_data() {
                Some(data) => Some(&data.surface_propositions),
                None => Some(&self.execution()?.presentation.surface_propositions),
            },
        }
    }
}

#[path = "driver/scripts.rs"]
mod driver;

/// One line naming the statement that may have overwritten a cell and the
/// fact that keeps it, as the store search spelled that fact.
pub(in crate::surface::proof) fn describe_recorded_store_separation_miss(
    miss: &crate::surface::proof::proof_object::StoreSeparationMiss,
) -> String {
    crate::surface::diagnostics::describe_store_separation_miss(
        &miss.statement,
        miss.cell_text.as_deref(),
        &crate::surface::printing::source_click_proposition(&miss.fact),
    )
}

mod division;
mod fact_projection;
mod machine_bridges;
mod multiplication;
