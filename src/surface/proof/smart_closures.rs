//! Smart closure search and linear script interpretation.

use super::*;
use crate::kernel::CFloatCondition;
use crate::kernel::proof::arithmetic_special::signed_definedness_operands;
use crate::kernel::proof::integer_arithmetic::{
    IntegerAffineClaim, IntegerAffineRelation, IntegerArithmeticCertificate, IntegerArithmeticNode,
    integer_affine_claim,
};
use crate::kernel::proof::signed_arithmetic::{
    SignedArithmeticClaim, SignedArithmeticComparison, SignedArithmeticNode,
    SignedArithmeticRelation,
};
use crate::kernel::proof::{
    PropositionIdentityKey, proposition_identity_key, propositions_are_alpha_equal,
};
use crate::surface::checking::plan_signed_arithmetic_certificate;
use crate::surface::checking::{IntegerRefutation, plan_integer_refutation_with_ranges};
use crate::surface::planning::proposition_search::PropositionSearch;
use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};
use proof_object::{collect_surface_conjunct_leaves, frontier_premise_anchor};

const MAX_DIRECT_CALLER_BINDING_NAMES: usize = 4096;
const MAX_SIMP_SOURCE_PREMISES: usize = 64;

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
            &Bitvector32Term::Variable(variable),
        ));
    }
    selected.into_iter().collect()
}

/// Goal-changing rewrites kept per link of an equality chain: the first
/// continues the chain, the others get a one-link closing probe.
/// How many times the solver behind `auto` plans again without the
/// premises it could not spell.
const MAX_EQUALITY_REWRITE_BRANCHES: usize = 4;

fn is_reflexive_pointer_equality(mut proposition: &Proposition) -> bool {
    let mut positive = true;
    while let Proposition::Not(inner) = proposition {
        proposition = inner;
        positive = !positive;
    }
    matches!(proposition,
        Proposition::ConditionIs(ConditionTerm::PointerEqual(left, right), value)
            if *value == positive && left == right)
        || matches!(proposition,
            Proposition::ConditionIs(ConditionTerm::PointerValueEqual(left, right), value)
                if *value == positive && left == right)
}

fn collect_signed_surface_terms<'a>(
    expression: &'a ContractExpression,
    terms: &mut Vec<&'a ContractExpression>,
) {
    let mut pending = vec![expression];
    while let Some(expression) = pending.pop() {
        terms.push(expression);
        match expression {
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
            | ContractExpression::ShiftRight(left, right)
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
            | ContractExpression::CFragment(_)
            | ContractExpression::CBinding(_)
            | ContractExpression::ResourceCount(_)
            | ContractExpression::ResourceWildcard
            | ContractExpression::IntegerLiteral(_) => {}
        }
    }
}

// Arithmetic combinations may mix snapshots. Put each selector on its
// operands so generated comparisons keep those snapshots when combined.
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
            | ClickProposition::Contains { .. }
            | ClickProposition::Loadable { .. }
            | ClickProposition::PredicateCall { .. } => {}
        }
    }
}

/// Compare the bounded arithmetic term fragment iteratively.  Certificate
/// expansion must recover the original source spelling for operation nodes;
/// leaf-atom comparison alone would silently decline deep but valid plans.
fn signed_surface_terms_equal(
    left: &crate::kernel::Bitvector32Term,
    right: &crate::kernel::Bitvector32Term,
) -> bool {
    let left = crate::kernel::canonical_term(left);
    let right = crate::kernel::canonical_term(right);
    let mut pending = vec![(&left, &right)];
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
            (
                crate::kernel::Bitvector32Term::UInt32From64(left),
                crate::kernel::Bitvector32Term::UInt32From64(right),
            ) => pending.push((left, right)),
            _ => {
                use crate::kernel::BitvectorBinaryOp as Op;
                let (Some((operator, left, right)), Some((other, other_left, other_right))) =
                    (left.as_binary(), right.as_binary())
                else {
                    return false;
                };
                let signed_or_native = (operator.is_bitvector32()
                    && !matches!(operator, Op::UnsignedDivide | Op::UnsignedRemainder))
                    || matches!(
                        operator,
                        Op::UInt64Add
                            | Op::UInt64Subtract
                            | Op::UInt64Multiply
                            | Op::UInt64Divide
                            | Op::UInt64Remainder
                    );
                if operator != other || !signed_or_native {
                    return false;
                }
                pending.push((left, other_left));
                pending.push((right, other_right));
            }
        }
    }
    true
}

/// The Integer spelling of a premise whose kernel form is a native
/// comparison: `a < b` as `to_integer(a) < to_integer(b)`. A comparison of
/// exact observations is that native comparison, so the spelling lowers to
/// the same fact, and the Integer nodes built from it combine Integer
/// operands rather than wrapping machine arithmetic. Any other premise keeps
/// its written spelling.
pub(super) fn observed_native_surface_comparison(
    kernel: &Proposition,
    written: &ClickProposition,
) -> ClickProposition {
    let negated;
    let kernel = match kernel {
        Proposition::Not(inner) => match inner.as_ref() {
            Proposition::ConditionIs(condition, value) => {
                negated = Proposition::ConditionIs(condition.clone(), !value);
                &negated
            }
            _ => kernel,
        },
        _ => kernel,
    };
    // The kernel form is a native comparison with an Integer reading, or
    // that Integer reading itself, spelled by the native fact it reads.
    if crate::kernel::assumptions::integer_observations_of_native_comparison(kernel).is_empty()
        && crate::kernel::assumptions::native_reading_of_integer_observation_fact(kernel).is_none()
    {
        return written.clone();
    }
    // An operand already written as an Integer (an unsuffixed literal, an
    // observation, or arithmetic over one) keeps its spelling.
    // A literal inside machine arithmetic, the `1` of `value + 1`, is typed
    // by that arithmetic; only an observation makes it Integer arithmetic.
    fn observes(operand: &ContractExpression) -> bool {
        match operand {
            ContractExpression::Call { name, .. } => name == "to_integer",
            ContractExpression::Add(left, right)
            | ContractExpression::Subtract(left, right)
            | ContractExpression::Multiply(left, right) => observes(left) || observes(right),
            ContractExpression::Negate(inner)
            | ContractExpression::Old(inner)
            | ContractExpression::At {
                expression: inner, ..
            } => observes(inner),
            _ => false,
        }
    }
    fn written_integer(operand: &ContractExpression) -> bool {
        match operand {
            ContractExpression::IntegerLiteral(_) => true,
            ContractExpression::Negate(inner)
            | ContractExpression::Old(inner)
            | ContractExpression::At {
                expression: inner, ..
            } => written_integer(inner),
            _ => observes(operand),
        }
    }
    // A read at a snapshot is observed there, `at(s, to_integer(x))`, which
    // lowers to the same read as the fact; `to_integer(at(s, x))` reads `x`
    // anew.
    fn observe_operand(operand: &ContractExpression) -> ContractExpression {
        match operand {
            ContractExpression::At {
                selector,
                expression,
            } => ContractExpression::At {
                selector: selector.clone(),
                expression: Box::new(observe_operand(expression)),
            },
            ContractExpression::Old(inner) => {
                ContractExpression::Old(Box::new(observe_operand(inner)))
            }
            _ => ContractExpression::Call {
                name: "to_integer".to_string(),
                arguments: vec![operand.clone()],
            },
        }
    }
    let observe = |operand: &ContractExpression| {
        if written_integer(operand) {
            operand.clone()
        } else {
            observe_operand(operand)
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

pub(in crate::surface::proof) fn integer_plan_to_surface_certificate(
    plan: &IntegerArithmeticCertificate,
    premise_pairs: &[(Proposition, ClickProposition)],
    surface_goal: &ClickProposition,
) -> Option<IntegerCertificate> {
    integer_plan_to_surface_certificate_with_ranges(plan, premise_pairs, surface_goal, &[])
}

/// As [`integer_plan_to_surface_certificate`], spelling each type-range
/// node by the matching entry of `ranges`: the machine observation, whether
/// the bound is the upper one, and its written bound.
pub(in crate::surface::proof) fn integer_plan_to_surface_certificate_with_ranges(
    plan: &IntegerArithmeticCertificate,
    premise_pairs: &[(Proposition, ClickProposition)],
    surface_goal: &ClickProposition,
    ranges: &[(crate::kernel::IntegerTerm, bool, ClickProposition)],
) -> Option<IntegerCertificate> {
    let mut source_indices = BTreeMap::new();
    let mut node_surfaces = Vec::with_capacity(plan.nodes.len());
    let mut nodes = Vec::with_capacity(plan.nodes.len());
    for (node_index, node) in plan.nodes.iter().enumerate() {
        let (surface, certificate_node) = match node {
            IntegerArithmeticNode::Premise { index, .. } => {
                let (kernel, written) = premise_pairs.get(*index)?;
                let surface = observed_native_surface_comparison(kernel, written);
                let source_index = {
                    let next = source_indices.len();
                    *source_indices.entry(*index).or_insert(next)
                };
                // The source and its result keep the written spelling, which
                // lowers to the available fact itself; the kernel reads a
                // native result as the Integer claim the node uses. Later
                // nodes combine the observed spelling.
                let certificate = IntegerCertificateNode::Premise {
                    index: source_index,
                    proposition: written.clone(),
                    result: written.clone(),
                };
                (
                    surface_comparison_with_anchored_operands(&surface),
                    certificate,
                )
            }
            IntegerArithmeticNode::Scale {
                source,
                coefficient,
                ..
            } => {
                let source_surface = node_surfaces.get(*source)?;
                let surface = integer_certificate_surface_scale(source_surface, coefficient)?;
                let certificate = IntegerCertificateNode::Scale {
                    source: *source,
                    coefficient: surface_signed_integer_literal(coefficient),
                    result: surface.clone(),
                };
                (surface, certificate)
            }
            IntegerArithmeticNode::Add { left, right, .. } => {
                let left_surface = node_surfaces.get(*left)?;
                let right_surface = node_surfaces.get(*right)?;
                let surface = integer_certificate_surface_add(left_surface, right_surface)?;
                let certificate = IntegerCertificateNode::Add {
                    left: *left,
                    right: *right,
                    result: surface.clone(),
                };
                (surface, certificate)
            }
            IntegerArithmeticNode::EqualityToLessEqual {
                source, reverse, ..
            } => {
                let source_surface = node_surfaces.get(*source)?;
                let surface = integer_surface_equality_to_less_equal(source_surface, *reverse)?;
                let certificate = IntegerCertificateNode::EqualityToLessEqual {
                    source: *source,
                    reverse: *reverse,
                    result: surface.clone(),
                };
                (surface, certificate)
            }
            IntegerArithmeticNode::EqualityFromBounds { lower, upper, .. } => {
                // The kernel compares normalized affine bounds. Their source
                // spellings need not be syntactic opposites (for example,
                // b <= x and not (b + 1 <= x)). At the conclusion, retain
                // the caller's equality; certificate checking recomputes it.
                let surface = if node_index == plan.conclusion {
                    surface_goal.clone()
                } else {
                    let lower_surface = node_surfaces.get(*lower)?;
                    let upper_surface = node_surfaces.get(*upper)?;
                    integer_surface_equality_from_bounds(lower_surface, upper_surface)?
                };
                let certificate = IntegerCertificateNode::EqualityFromBounds {
                    lower: *lower,
                    upper: *upper,
                    result: surface.clone(),
                };
                (surface, certificate)
            }
            IntegerArithmeticNode::Trivial { result } => {
                let surface = if node_index == plan.conclusion {
                    surface_goal.clone()
                } else {
                    integer_surface_trivial(result)?
                };
                let certificate = IntegerCertificateNode::Trivial {
                    result: surface.clone(),
                };
                (surface, certificate)
            }
            IntegerArithmeticNode::NegatedGoal { .. } => {
                let surface = integer_surface_negated_goal(surface_goal)?;
                let certificate = IntegerCertificateNode::NegatedGoal {
                    result: surface.clone(),
                };
                (surface, certificate)
            }
            IntegerArithmeticNode::TypeRange { value, upper, .. } => {
                let surface = ranges
                    .iter()
                    .find(|(observed, bound, _)| observed == value && bound == upper)?
                    .2
                    .clone();
                let certificate = IntegerCertificateNode::TypeRange {
                    result: surface.clone(),
                };
                (
                    surface_comparison_with_anchored_operands(&surface),
                    certificate,
                )
            }
            // A divided bound has no general source spelling derived from
            // its source's spelling; planners that divide spell the result
            // from their own atom table.
            IntegerArithmeticNode::Divide { .. } => return None,
        };
        node_surfaces.push(surface);
        nodes.push(certificate_node);
    }
    Some(IntegerCertificate {
        nodes,
        conclusion: plan.conclusion,
    })
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

/// The `Integer` certificate's spelling of a scaled bound. `c * l < c * r`
/// is the kernel's scaled claim only for `c == 1`; otherwise the strict
/// bound is scaled in its non-strict form. The `signed_int32` family keeps
/// [`integer_surface_scale`], whose checker reads the `c * l < c * r` shape.
fn integer_certificate_surface_scale(
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

/// The `Integer` certificate's spelling of a sum. One strict addend carries
/// the claim's `+ 1`, so `l1 + l2 < r1 + r2` spells the sum; two strict
/// addends carry `+ 2`, which a single `<` cannot, so both are added in
/// their non-strict form.
fn integer_certificate_surface_add(
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
/// A snapshot does not change a literal's value, so `at(<point>, 0)` folds
/// exactly as a bare `0` does; look through one.  This is a syntactic test on
/// one already built expression, not a lowering.
fn surface_expression_is_constant(expression: &ContractExpression) -> bool {
    match expression {
        ContractExpression::IntegerLiteral(_) => true,
        ContractExpression::CFragment(crate::kernel::CExpression::Value(_)) => true,
        ContractExpression::Negate(inner) => surface_expression_is_constant(inner),
        ContractExpression::At { expression, .. } | ContractExpression::Old(expression) => {
            surface_expression_is_constant(expression)
        }
        _ => false,
    }
}

/// The integer negation of a goal `l <= r` is `r < l`, and of `l < r` is
/// `r <= l`. An equality goal has no single-bound negation.
fn integer_surface_negated_goal(goal: &ClickProposition) -> Option<ClickProposition> {
    let (left, operator, right) = integer_surface_ordered_parts(goal)?;
    let operator = match operator {
        ComparisonOperator::LessEqual => ComparisonOperator::LessThan,
        ComparisonOperator::LessThan => ComparisonOperator::LessEqual,
        _ => return None,
    };
    Some(ClickProposition::Comparison {
        left: right,
        operator,
        right: left,
    })
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
/// read at two snapshots the body did not separate, are the same premise to
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
/// Source spellings a solver closure resolved, by fact.
type SpellingCache = std::cell::RefCell<
    std::collections::BTreeMap<Proposition, Option<(Proposition, ClickProposition)>>,
>;

enum Spelling {
    Spelled(
        Vec<(Proposition, ClickProposition)>,
        Vec<(crate::kernel::IntegerTerm, bool, ClickProposition)>,
    ),
    /// A native comparison read as an Integer one has no spelling.
    UnspelledReading(Proposition),
    /// A machine observation's type range has no spelling.
    UnspelledRange(crate::kernel::IntegerTerm),
}

/// The distinct `to_integer(...)` expressions written in `surfaces`.
fn written_integer_observations<'s>(
    surfaces: impl Iterator<Item = &'s ClickProposition>,
) -> Vec<ContractExpression> {
    let mut written: Vec<ContractExpression> = Vec::new();
    for surface in surfaces {
        // A native comparison such as `amount <= count(...)` spells the
        // Integer observations of its operands.
        if let ClickProposition::Comparison { left, right, .. } = surface {
            for side in [left, right] {
                if matches!(side, ContractExpression::IntegerLiteral(_))
                    || matches!(side, ContractExpression::Call { name, .. } if name == "to_integer")
                {
                    continue;
                }
                let observed = ContractExpression::Call {
                    name: "to_integer".into(),
                    arguments: vec![side.clone()],
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
    let mut index = 0;
    while index < written.len() {
        if let ContractExpression::Call { arguments, .. } = &written[index]
            && let ContractExpression::Add(left, right) | ContractExpression::Subtract(left, right) =
                &arguments[0]
        {
            let operands = [left.as_ref().clone(), right.as_ref().clone()];
            for operand in operands {
                let observed = ContractExpression::Call {
                    name: "to_integer".into(),
                    arguments: vec![operand],
                };
                if !written.contains(&observed) {
                    written.push(observed);
                }
            }
        }
        index += 1;
    }
    // A value the proof has since replaced, such as a population count
    // before a consumption, is often spelled only at function entry.
    let entry: Vec<ContractExpression> = written
        .iter()
        .filter_map(|expression| {
            let ContractExpression::Call { arguments, .. } = expression else {
                return None;
            };
            let mut snapshot = false;
            crate::surface::proof::fixed_state_proofs::conversion_conditions::walk_written_expressions(
                &arguments[0],
                &mut |inner| {
                    snapshot |= matches!(
                        inner,
                        ContractExpression::Old(_) | ContractExpression::At { .. }
                    );
                },
            );
            (!snapshot).then(|| ContractExpression::Call {
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

/// Whether `proposition` reads `result` inside a snapshot that precedes the
/// return, which the parser refuses.
fn reads_result_before_return(proposition: &ClickProposition) -> bool {
    let too_early =
        |selector: Option<&SnapshotSelector>| !crate::surface::snapshot_can_name_result(selector);
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
        crate::kernel::assumptions::integer_observations_of_native_comparison(premise);
    readings.extend(crate::kernel::assumptions::integer_bounds_of_definedness(
        premise,
    ));
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

/// The machine observations in `goal` and `premises` whose type ranges a
/// refutation may use, each once.
fn machine_observations(
    goal: &Proposition,
    premises: &[Proposition],
) -> Vec<crate::kernel::IntegerTerm> {
    let mut seen = std::collections::HashSet::new();
    std::iter::once(goal)
        .chain(premises)
        .flat_map(crate::kernel::proof::integer_arithmetic::integer_affine_machine_values)
        .filter(|value| seen.insert(value.id()))
        .map(crate::kernel::IntegerTerm::Machine)
        .collect()
}

fn integer_surface_trivial(claim: &IntegerAffineClaim) -> Option<ClickProposition> {
    if !claim.terms.is_empty() {
        return None;
    }
    let operator = match claim.relation {
        IntegerAffineRelation::LessEqual if claim.constant <= BigInt::zero() => {
            ComparisonOperator::LessEqual
        }
        IntegerAffineRelation::Equal if claim.constant.is_zero() => ComparisonOperator::Equal,
        _ => return None,
    };
    Some(ClickProposition::Comparison {
        left: surface_signed_integer_literal(&claim.constant),
        operator,
        right: ContractExpression::IntegerLiteral("0".into()),
    })
}

fn kernel_upper_bound_split_candidate(
    proposition: &Proposition,
) -> Option<(Variable, Bitvector32Term)> {
    let Proposition::ConditionIs(condition, true) = proposition else {
        return None;
    };
    let (left, right, plus_one) = match condition {
        ConditionTerm::Bitvector32SignedLessThan(left, right) => (left, right, true),
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => (left, right, false),
        _ => return None,
    };
    let Bitvector32Term::Variable(variable) = left.as_ref() else {
        return None;
    };
    if !plus_one {
        return Some((*variable, right.as_ref().clone()));
    }
    let Bitvector32Term::Add(pivot, one) = right.as_ref() else {
        return None;
    };
    (**one == Bitvector32Term::Constant(1)).then(|| (*variable, pivot.as_ref().clone()))
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
            right: right.clone(),
        }),
        ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::LessThan,
            right: ContractExpression::Add(pivot, one),
        } if **one == ContractExpression::CFragment(CExpression::Value(int32(1))) => {
            Some(ClickProposition::Comparison {
                left: left.clone(),
                operator: ComparisonOperator::LessThan,
                right: pivot.as_ref().clone(),
            })
        }
        ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::LessThan,
            right,
        } => Some(ClickProposition::Comparison {
            left: left.clone(),
            operator: ComparisonOperator::LessThan,
            right: ContractExpression::Subtract(
                Box::new(right.clone()),
                Box::new(ContractExpression::CFragment(CExpression::Value(int32(1)))),
            ),
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
            right: right.clone(),
        }),
        ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::LessThan,
            right,
        } => Some(ClickProposition::Comparison {
            left: left.clone(),
            operator: ComparisonOperator::LessThan,
            right: right.clone(),
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
        term: &crate::kernel::Bitvector32Term,
        candidates: &[&ContractExpression],
    ) -> Option<ContractExpression> {
        // Unsigned ordering lowers to signed ordering by xoring both sides
        // with the sign bit.  The transformed bound is not itself present in
        // source, so reconstruct it from the source uint32 literal while
        // preserving the typed expression that direct lowering understands.
        if let Some(value) = term.as_const() {
            for candidate in candidates {
                let Some(base) = (match *candidate {
                    ContractExpression::CFragment(crate::kernel::CExpression::Value(
                        crate::kernel::CValue::UInt32(crate::kernel::Bitvector32Term::Constant(
                            base,
                        )),
                    )) => Some(base),
                    _ => None,
                }) else {
                    continue;
                };
                if base ^ 0x8000_0000 == value {
                    return Some(ContractExpression::CFragment(
                        crate::kernel::CExpression::Value(crate::kernel::CValue::Int32(
                            crate::kernel::Bitvector32Term::Constant(value),
                        )),
                    ));
                }
            }
            // Generated interval nodes can introduce a small machine
            // constant (for example the `+ 1` in a bump function) that has no
            // separate source occurrence.  It is still source-printable as
            // an ordinary signed literal, and the certificate checker will
            // re-lower that literal before accepting the step.
            if matches!(term, Bitvector32Term::Constant(_)) {
                return Some(ContractExpression::IntegerLiteral(
                    i32::from_ne_bytes(value.to_ne_bytes()).to_string(),
                ));
            }
        }
        // Prefer the most local/int32 source occurrence.  A uint32 cast of
        // the same variable may lower to the same raw bitvector term, but is
        // not a valid typed witness for an int32 interval node.
        for candidate in candidates.iter().rev() {
            if let crate::kernel::Bitvector32Term::Constant(value) = term
                && let ContractExpression::IntegerLiteral(literal) = *candidate
                && literal.parse::<u32>().ok() == Some(*value)
            {
                return Some((*candidate).clone());
            }
            let probe = ClickProposition::Comparison {
                left: (*candidate).clone(),
                operator: ComparisonOperator::Equal,
                right: ContractExpression::IntegerLiteral("0".into()),
            };
            let Ok(lowered) =
                self.lower_surface_proposition_direct(&probe, "signed arithmetic certificate term")
            else {
                continue;
            };
            let Proposition::ConditionIs(
                crate::kernel::ConditionTerm::Bitvector32Equal(left, right),
                true,
            ) = lowered
            else {
                continue;
            };
            let names_term = (right.as_ref().as_const() == Some(0)
                && signed_surface_terms_equal(left.as_ref(), term))
                || (left.as_ref().as_const() == Some(0)
                    && signed_surface_terms_equal(right.as_ref(), term));
            if names_term && self.signed_surface_term_is_int32(candidate, term) {
                return Some((*candidate).clone());
            }
        }
        None
    }

    /// Whether `candidate` reads `term` as an `int32`, so a certificate node
    /// that names the signed atom re-lowers to that atom. Equality cannot
    /// tell: `(uint32) n == 0` lowers to the same raw bitvector equality as
    /// `n == 0`, while `(uint32) n <= 2147483647` is an unsigned comparison of
    /// another typed value. A signed order does tell, since only an `int32`
    /// operand lowers `candidate < 0` to a signed comparison of that term.
    fn signed_surface_term_is_int32(
        &self,
        candidate: &ContractExpression,
        term: &crate::kernel::Bitvector32Term,
    ) -> bool {
        let probe = ClickProposition::Comparison {
            left: candidate.clone(),
            operator: ComparisonOperator::LessThan,
            right: ContractExpression::IntegerLiteral("0".into()),
        };
        let Ok(Proposition::ConditionIs(
            crate::kernel::ConditionTerm::Bitvector32SignedLessThan(left, right),
            true,
        )) = self.lower_surface_proposition_direct(&probe, "signed arithmetic certificate term")
        else {
            return false;
        };
        right.as_ref().as_const() == Some(0) && signed_surface_terms_equal(left.as_ref(), term)
    }

    pub(super) fn signed_plan_to_surface_certificate(
        &self,
        plan: &crate::kernel::proof::signed_arithmetic::SignedArithmeticCertificate,
        premise_pairs: &[(Proposition, ClickProposition)],
        surface_goal: &ClickProposition,
    ) -> Option<SignedInt32Certificate> {
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
        let mut source_indices = BTreeMap::new();
        let mut generated = Vec::new();
        for original in used {
            let local = source_indices.len();
            source_indices.insert(original, local);
            if plan.nodes.iter().any(|node| {
                matches!(node, SignedArithmeticNode::Premise { index, .. } if *index == original)
            }) {
                let surface = premise_pairs.get(original)?.1.clone();
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
        let term = |term: &crate::kernel::Bitvector32Term| self.signed_surface_term(term, &terms);
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
                    Some(rendered_premises.get(*index)?.clone())
                }
                SignedArithmeticNode::AffinePremise { source, .. } => {
                    surfaces.get(*source)?.clone()
                }
                SignedArithmeticNode::Scale {
                    source,
                    coefficient,
                    result,
                } => integer_surface_scale(surfaces.get(*source)?.as_ref()?, coefficient)
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
                    } else if surfaces.len() == plan.conclusion
                        && !result.terms.is_empty()
                        && result.terms.keys().all(|atom| atom.is_sign_bit_flip())
                    {
                        // An unsigned bound weakened by a constant slack is
                        // affine in sign-bit-flipped atoms. Adding the source
                        // operands instead would use wrapping uint32 sums,
                        // and signed constant slack cannot form an unsigned
                        // transitivity chain. The goal already spells the
                        // conclusion; the Add checker independently requires
                        // it to encode the exact child sum.
                        Some(surface_goal.clone())
                    } else if result.terms.is_empty()
                        && result.constant == BigInt::from(0)
                        && result.relation == SignedArithmeticRelation::LessEqual
                    {
                        integer_surface_zero_claim(left_surface, right_surface)
                    } else if !result.terms.is_empty()
                        && result.terms.keys().all(|atom| atom.is_sign_bit_flip())
                        && let Some(chained) =
                            integer_surface_transitive(left_surface, right_surface)
                    {
                        // A sum over sign-bit-flipped atoms is a step of an
                        // unsigned chain: `x <u n` and `n <=u 4` add to
                        // `x <u 4`, which is the source comparison of the
                        // chain's ends. Summing the source operands instead
                        // would spell a wrapping `uint32` addition, a
                        // different value from the flipped atoms' sum.
                        Some(chained)
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
                                integer_surface_add(left_surface, right_surface)
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
                    let atom = term(&crate::kernel::Bitvector32Term::Variable(
                        atom.as_variable()?,
                    ))?;
                    Some(if coefficient.is_positive() {
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
                    })
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
        // Preserve native typing at the output boundary. Keep the planning
        // surfaces unchanged so transitive chains still match their endpoints.
        let native_result = |value: ClickProposition, claim: &SignedArithmeticClaim| match value {
            ClickProposition::Comparison {
                left,
                operator,
                right,
            } if !claim.terms.is_empty()
                && claim.terms.keys().all(|atom| !atom.is_sign_bit_flip()) =>
            {
                let native = |operand| ContractExpression::CUnary {
                    operand: Box::new(operand),
                    lowered: CExpression::Cast {
                        expression: Box::new(CExpression::Value(crate::kernel::int32(0))),
                        target_type: crate::kernel::CType::Int32,
                        integer_mode: crate::kernel::CIntegerCastMode::CConversion,
                        pointee_struct: None,
                        pointee_volatile: false,
                        pointee_constant: false,
                        explicit_qualification: false,
                    },
                };
                ClickProposition::Comparison {
                    left: native(left),
                    operator,
                    right: native(right),
                }
            }
            value => value,
        };
        for (node_index, node) in plan.nodes.iter().enumerate() {
            let r = |index: usize| mapped[index];
            let result = || surfaces.get(node_index)?.as_ref().cloned();
            let surface_node = match node {
                SignedArithmeticNode::Premise { .. } => continue,
                SignedArithmeticNode::Scale {
                    source,
                    coefficient,
                    result: claim,
                } => SignedArithmeticStep::Scale {
                    source: r(*source),
                    coefficient: surface_signed_integer_literal(coefficient),
                    result: native_result(result()?, claim),
                },
                SignedArithmeticNode::Add {
                    left,
                    right,
                    result: claim,
                } => SignedArithmeticStep::Add {
                    left: r(*left),
                    right: r(*right),
                    // The final sum is already checked against the goal's
                    // affine claim. Reuse that source spelling instead of
                    // printing another composite expression whose machine
                    // additions may lower to different atoms.
                    result: native_result(
                        if node_index == plan.conclusion && weakening_source.is_some() {
                            surface_goal.clone()
                        } else {
                            result()?
                        },
                        claim,
                    ),
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
                    let source = premise_pairs.get(*index)?.1.clone();
                    let ClickProposition::Defined { .. } = source else {
                        return None;
                    };
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
                SignedArithmeticNode::IntervalSignBitFlip { operand, result } => {
                    SignedArithmeticStep::IntervalSignBitFlip {
                        operand: r(*operand),
                        result: interval(result.clone()),
                    }
                }
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
                    source, evidence, ..
                } => SignedArithmeticStep::AffineConclusion {
                    source: r(*source),
                    evidence: r(*evidence),
                    result: surface_goal.clone(),
                },
                SignedArithmeticNode::AffineConclusionWithEvidence {
                    source,
                    left_evidence,
                    right_evidence,
                    ..
                } => SignedArithmeticStep::AffineConclusionWithEvidence {
                    source: r(*source),
                    left_evidence: r(*left_evidence),
                    right_evidence: r(*right_evidence),
                    result: surface_goal.clone(),
                },
            };
            generated.push(surface_node);
        }
        Some(SignedInt32Certificate {
            nodes: generated,
            conclusion: *mapped.get(plan.conclusion)?,
        })
    }
    /// A small shared search combinator for structural proposition closure.
    /// Every candidate is accepted only through `apply_step`; `intro` is the
    /// sole nonterminal move and strictly removes one outer goal connective.
    ///
    /// A miss is `Ok(None)` and leaves `self` the unchanged authority. An
    /// error is a tooling failure such as an exceeded deadline; it must abort
    /// the enclosing search rather than read as one more rejection.
    pub(in crate::surface::proof) fn try_direct_logical_closure(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        let mut scope = attempt::search_scope("direct logical closure");
        let mut budget = attempt::AttemptBudget::unbounded();
        let mut proof = self.clone();
        loop {
            if let Some(closed) =
                attempt::try_steps(&proof, &mut budget, direct_logical_candidates(proof.goal()))?
            {
                scope.succeed();
                return Ok(Some(closed));
            }
            // A literal false premise needs no source search or arithmetic
            // derivation. Fixed-state goals can use the same explicit
            // contradiction as pure goals.
            if proof.goal().is_some()
                && proof.facts().contains(&Proposition::ConditionIs(
                    ConditionTerm::Constant(false),
                    true,
                ))
                && let Some(closed) = attempt::candidate_outcome(proof.apply_step(
                    ProofStep::Contradiction(ClickProposition::Comparison {
                        // Machine literals cannot be shadowed by C parameters
                        // named `false` or `true` when the certificate is read.
                        left: ContractExpression::CFragment(CExpression::Value(CValue::UInt32(
                            0u32.into(),
                        ))),
                        operator: ComparisonOperator::Equal,
                        right: ContractExpression::CFragment(CExpression::Value(CValue::UInt32(
                            1u32.into(),
                        ))),
                    }),
                ))?
            {
                scope.succeed();
                return Ok(Some(closed));
            }
            if let Some(closed) = proof.try_discharged_consequent_closure()? {
                scope.succeed();
                return Ok(Some(closed));
            }
            if let Some(closed) = proof.try_quantified_conjunct_projection_closure()? {
                scope.succeed();
                return Ok(Some(closed));
            }
            // The kernel introduces only these outer connectives. An
            // atomic goal cannot take this step; constructing its rejection
            // would also capture an unused memory-history diagnostic.
            if !matches!(
                proof.goal(),
                Some(Proposition::Implies(..) | Proposition::ForAll { .. } | Proposition::Not(_))
            ) {
                return Ok(None);
            }
            match attempt::candidate_outcome(proof.apply_step(ProofStep::Intro))? {
                Some(introduced) => proof = introduced,
                None => return Ok(None),
            }
        }
    }

    /// Modus ponens as a direct logical step: the goal is the consequent of
    /// an available implication (or chain) whose antecedents are exactly
    /// available, such as a call guarantee `left_result == 0 implies X`
    /// inside the branch whose path condition is `left_result == 0`. The
    /// indexed consequent lookup that the checked `extract` rule performs
    /// decides it; nothing is searched, and a goal no available implication
    /// concludes costs one index probe. Expansion prints `extract(goal)`.
    fn try_discharged_consequent_closure(&self) -> Result<Option<Self>, ClickError> {
        let (Some(goal), Some(surface)) = (self.goal(), self.surface_goal()) else {
            return Ok(None);
        };
        if !self
            .facts()
            .contains_discharged_implication_consequent(goal)
        {
            return Ok(None);
        }
        Ok(
            attempt::candidate_outcome(self.apply_step(ProofStep::Extract(surface.clone())))?
                .filter(Self::focused_discharged),
        )
    }

    /// Weakening a guarded universal by dropping conjuncts of its conclusion:
    /// the goal `forall k { G implies A }` follows from an available
    /// `forall k { G implies A and B }` with the same binder and guards.
    /// The source is selected by one probe of the indexed conjunct
    /// projections (`ProofFacts::quantified_conjunct_projection_source`), so
    /// a universal goal no such fact concludes costs one lookup and no
    /// unrelated fact is visited. The proof is the explicit sequence
    /// `intro()` for the binder and each guard, `instantiate(F, k)` at the
    /// introduced binder, and `assumption()`; each step is checked as written
    /// and expansion prints it.
    fn try_quantified_conjunct_projection_closure(&self) -> Result<Option<Self>, ClickError> {
        let Some(goal @ Proposition::ForAll { body, .. }) = self.goal() else {
            return Ok(None);
        };
        let Some(source) = self.facts().quantified_conjunct_projection_source(goal) else {
            return Ok(None);
        };
        let binder = match self.surface_goal() {
            Some(ClickProposition::ForAll { name, .. }) => name.clone(),
            Some(ClickProposition::RangeAll { item, .. }) => item.clone(),
            _ => return Ok(None),
        };
        let source = source.clone();
        let mut guards = 0usize;
        let mut conclusion = body.as_ref();
        while let Proposition::Implies(_, consequent) = conclusion {
            guards += 1;
            conclusion = consequent;
        }
        let Some(quantified) = self
            .resolve_simp_premises(std::slice::from_ref(&source), &[])
            .and_then(|pairs| pairs.into_iter().next())
            .map(|(_, surface)| surface)
        else {
            return Ok(None);
        };
        let mut scope = attempt::search_scope("quantified conjunct projection");
        let steps = std::iter::repeat_n(ProofStep::Intro, guards + 1).chain([
            ProofStep::InstantiateUsing {
                quantified,
                argument: ContractExpression::CFragment(CExpression::Variable(binder)),
                premises: None,
            },
        ]);
        let mut proof = self.clone();
        for step in steps {
            let Some(next) = attempt::candidate_outcome(proof.apply_step(step))? else {
                return Ok(None);
            };
            proof = next;
        }
        if !proof.focused_discharged() {
            let Some(closed) = attempt::candidate_outcome(proof.apply_step(ProofStep::Assumption))?
            else {
                return Ok(None);
            };
            proof = closed;
        }
        if !proof.focused_discharged() {
            return Ok(None);
        }
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
    fn try_direct_structural_closure(&self) -> Result<Option<Self>, ClickError> {
        let mut scope = attempt::search_scope("direct structural closure");
        let result = self.try_direct_structural_closure_inner(&mut |_| Ok(None))?;
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
    fn try_direct_structural_closure_under_binders(&self) -> Result<Option<Self>, ClickError> {
        if !conjunction_under_binders(self.goal()) {
            return Ok(None);
        }
        crate::instrumentation::measure_operation(
            "surface",
            "simp closure",
            "simp closure: direct structural",
            || self.try_direct_structural_closure(),
        )
    }

    /// [`Self::try_direct_structural_closure`] with one more closer at a
    /// universal node the direct candidates miss: `quantified` is offered
    /// the universal whole before `intro` descends into it. The walk is
    /// otherwise the same goal-sized descent, so the extra work is one
    /// `quantified` attempt per universal node of the goal.
    pub(in crate::surface::proof) fn try_direct_structural_closure_with_quantified(
        &self,
        quantified: &mut dyn FnMut(&Self) -> Result<Option<Self>, ClickError>,
    ) -> Result<Option<Self>, ClickError> {
        let mut scope = attempt::search_scope("direct structural closure");
        let result = self.try_direct_structural_closure_inner(quantified)?;
        if result.is_some() {
            scope.succeed();
        }
        Ok(result)
    }

    /// Name the leaves of a wide logical conjunction before closing it.
    /// Sequential checked `have` steps and `assumption` keep the certificate
    /// shallow without changing the kernel goal or its grouping. Reification
    /// is presentation only: every leaf must lower back to the exact goal.
    pub(in crate::surface::proof) fn wide_conjunction_surfaces(
        &self,
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
        if leaves.len() <= 8 {
            return None;
        }
        // Leaves are checked last first. A loop-invariant bundle guards each
        // member by every earlier declaration, so its last members are the
        // largest and the ones that exceed the synthesis bounds. Checking
        // them first makes a refusal one bounded attempt; checking in order
        // reified every earlier member first, and the binary descent that
        // follows a refusal repeated that at each level. The result does not
        // depend on the order.
        let surfaces = if let Some(surface) = self.surface_goal() {
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
            if surfaces.len() != leaves.len() {
                return None;
            }
            for (surface, goal) in surfaces.iter().zip(&leaves).rev() {
                let lowered = self
                    .lower_surface_goal(surface, "conjunction certificate leaf")
                    .ok()?;
                if !crate::kernel::proof::propositions_are_alpha_equal(&lowered, goal) {
                    return None;
                }
            }
            surfaces
        } else {
            // A synthesized member is kept only when it lowers back to its
            // leaf, so it needs no second check.
            let mut surfaces = leaves
                .iter()
                .rev()
                .map(|goal| self.synthesized_bundle_member_surface(goal))
                .collect::<Option<Vec<_>>>()?;
            surfaces.reverse();
            surfaces
        };
        Some(surfaces)
    }

    fn try_direct_structural_closure_inner(
        &self,
        quantified: &mut dyn FnMut(&Self) -> Result<Option<Self>, ClickError>,
    ) -> Result<Option<Self>, ClickError> {
        self.try_direct_structural_closure_inner_impl(quantified)
            .map_err(|error| self.attach_step_diagnostic(error))
    }

    fn try_direct_structural_closure_inner_impl(
        &self,
        quantified: &mut dyn FnMut(&Self) -> Result<Option<Self>, ClickError>,
    ) -> Result<Option<Self>, ClickError> {
        check_verification_deadline()?;
        let mut budget = attempt::AttemptBudget::unbounded();
        if let Some(closed) =
            attempt::try_steps(self, &mut budget, direct_logical_candidates(self.goal()))?
        {
            return Ok(Some(closed));
        }
        if let Some(closed) = self.try_discharged_consequent_closure()? {
            return Ok(Some(closed));
        }
        if let Some(surfaces) = self.wide_conjunction_surfaces() {
            let mut proof = self.clone();
            for surface in surfaces {
                let scope = proof.begin_have(surface)?;
                let Some(closed) =
                    scope.try_direct_structural_closure_with_quantified(quantified)?
                else {
                    return Ok(None);
                };
                proof = closed.join()?;
            }
            return attempt::candidate_outcome(proof.apply_step(ProofStep::Assumption));
        }
        if matches!(self.goal(), Some(Proposition::And(_, _))) {
            let Some((split_proof, split, ids)) =
                attempt::candidate_outcome(self.split_focused_both())?
            else {
                return Ok(None);
            };
            let marker = split_proof.checkpoint();
            let Some(left) = split_proof
                .focus_branch(ids[0])?
                .try_direct_structural_closure_inner(quantified)?
            else {
                return Ok(None);
            };
            let Some(right) = left
                .focus_branch(ids[1])?
                .try_direct_structural_closure_inner(quantified)?
            else {
                return Ok(None);
            };
            return attempt::candidate_outcome(right.join_focused_both(&marker, split, ids));
        }
        if matches!(self.goal(), Some(Proposition::ForAll { .. }))
            && let Some(closed) = quantified(self)?
        {
            return Ok(Some(closed));
        }
        if matches!(self.goal(), Some(Proposition::Implies(_, _))) {
            let mut introduced = self.clone();
            while matches!(introduced.goal(), Some(Proposition::Implies(_, _))) {
                let Some(next) =
                    attempt::candidate_outcome(introduced.apply_step(ProofStep::Intro))?
                else {
                    return Ok(None);
                };
                introduced = next;
            }
            return introduced.try_direct_structural_closure_inner(quantified);
        }
        match attempt::candidate_outcome(self.apply_step(ProofStep::Intro))? {
            Some(introduced) => introduced.try_direct_structural_closure_inner(quantified),
            None => Ok(None),
        }
    }

    /// Searches the currently migrated `simp` vocabulary against this proof.
    ///
    /// Direct logical closers remain the cheap first choice. For a pure or
    /// fixed-state signed-order/equality derivation, the kernel-selected edge path
    /// is translated into a candidate made only of checked theorem
    /// applications, rewrites, and nested `have` scopes. The candidate
    /// advances this same `Proof`; no semantic result is produced before
    /// those proof steps have been accepted.
    pub(in crate::surface::proof) fn try_simp_closure(&self) -> Result<Option<Self>, ClickError> {
        // simp reaches the same failing frame question through several of
        // its strategies and candidates; one closure attempt answers each
        // exact failed question once (`with_closure_failure_memo`).
        crate::surface::planning::proposition_search::with_simp_atomic_reduction_cache(|| {
            crate::kernel::with_closure_failure_memo(|| self.try_simp_closure_strategies())
        })
        .map_err(|error| self.attach_step_diagnostic(error))
    }

    /// Close a mathematical `Integer` bound goal with the solver behind
    /// `auto`: refute the goal's negation from the facts connected to it and
    /// apply the resulting certificate as one ordinary checked step. Any
    /// miss leaves the proof unchanged.
    /// The searches `auto` runs besides `simp`: the solver and its bridges,
    /// then a bounded chain of rewrites. A closer that has already tried
    /// `simp` on this goal runs these when it misses.
    pub(in crate::surface::proof) fn try_auto_closure_after_simp(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        if self.scalar_equality_goal_is_refuted() {
            return Ok(None);
        }
        if let Some(closed) = self.try_solver_closure()? {
            return Ok(Some(closed));
        }
        if let Some(closed) = self.try_bridged_solver_closure()? {
            return Ok(Some(closed));
        }
        if let Some(closed) = self.try_machine_goal_solver_closure()? {
            return Ok(Some(closed));
        }
        if let Some(closed) = self.try_solver_equality_closure()? {
            return Ok(Some(closed));
        }
        if let Some(closed) = self.try_definedness_solver_closure()? {
            return Ok(Some(closed));
        }
        if let Some(closed) = self.try_auto_conjunction_closure()? {
            return Ok(Some(closed));
        }
        if let Some(closed) = self.try_definition_condition_closure()? {
            return Ok(Some(closed));
        }
        if let Some(closed) = self.try_auto_equality_chain_closure()? {
            return Ok(Some(closed));
        }
        if let Some(closed) = self.try_constructor_join_closure()? {
            return Ok(Some(closed));
        }
        if let Some(closed) = self.try_wide_equality_solver_closure()? {
            return Ok(Some(closed));
        }
        self.try_native_goal_by_integer_reading()
    }

    /// A known different scalar value or a nonzero mathematical offset
    /// cannot satisfy this equality. Avoid spelling historical equalities
    /// and unfolding functions for that miss. An inconsistent context stays
    /// eligible for ordinary contradiction closure; this is not proof evidence.
    fn scalar_equality_goal_is_refuted(&self) -> bool {
        let Some(Proposition::ConditionIs(condition, wanted)) = self.goal() else {
            return false;
        };
        let assumptions = self.facts().assumptions();
        if let ConditionTerm::IntegerEqual(left, right) = condition {
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
                        || self.facts().contains(&Proposition::ConditionIs(
                            ConditionTerm::IntegerEqual(left.clone(), right.clone()),
                            true,
                        ))
                        || self.facts().contains(&Proposition::ConditionIs(
                            ConditionTerm::IntegerEqual(right.clone(), left.clone()),
                            true,
                        ))
                };
            let refuted = offset_base(right).is_some_and(|base| same_value(left, base))
                || offset_base(left).is_some_and(|base| same_value(right, base));
            if !refuted {
                return false;
            }
            let _scope = crate::kernel::assumptions::PureFactContextIdScope::enter(assumptions);
            return !assumptions.is_inconsistent();
        }
        let (left, right) = match condition {
            ConditionTerm::Bitvector32Equal(left, right)
            | ConditionTerm::Bitvector64Equal(left, right) => (left, right),
            _ => return false,
        };
        let literal = |term: &Bitvector32Term| {
            matches!(
                term,
                Bitvector32Term::Constant(_) | Bitvector32Term::Int64Constant(_)
            )
        };
        if !literal(left) && !literal(right) {
            return false;
        }
        !assumptions.is_inconsistent()
            && assumptions
                .decide(condition)
                .is_some_and(|known| known != *wanted)
    }

    pub(in crate::surface::proof) fn try_solver_closure(&self) -> Result<Option<Self>, ClickError> {
        self.solver_closure(true, &[])
    }

    /// Close a native comparison of exact observations, such as `a < 100`
    /// for an `int`, by proving its Integer reading `to_integer(a) < 100`
    /// with the solver. The Integer fact files its native comparison, so
    /// the goal is then an available fact.
    pub(in crate::surface::proof) fn try_native_goal_by_integer_reading(
        &self,
    ) -> Result<Option<Self>, ClickError> {
        let (Some(goal), Some(surface_goal)) = (self.goal(), self.surface_goal()) else {
            return Ok(None);
        };
        let readings = crate::kernel::assumptions::integer_observations_of_native_comparison(goal);
        if readings.is_empty() {
            return Ok(None);
        }
        let written = written_integer_observations(std::iter::once(surface_goal));
        for reading in readings {
            let Some(spelled) = self.spell_integer_comparison(&reading, &written) else {
                continue;
            };
            let Ok(scope) = self.begin_have(spelled) else {
                continue;
            };
            let Some(closed) = scope.try_solver_closure()? else {
                continue;
            };
            let Ok(proof) = closed.join() else {
                continue;
            };
            if let Some(closed) =
                attempt::candidate_outcome(proof.apply_step(ProofStep::Assumption))?
            {
                return Ok(Some(closed));
            }
        }
        Ok(None)
    }

    /// Refute the goal's negation from the connected facts, then from them
    /// and the type ranges of their machine observations, then, when
    /// `identities`, also from in-range machine `+` and `-` identities.
    ///
    /// `spelled` gives the source spelling of facts the caller just
    /// established, which a cited premise uses before its resolved one.
    pub(in crate::surface::proof) fn solver_closure(
        &self,
        identities: bool,
        spelled: &[(Proposition, ClickProposition)],
    ) -> Result<Option<Self>, ClickError> {
        let (Some(goal), Some(surface_goal)) = (self.goal(), self.surface_goal()) else {
            return Ok(None);
        };
        // A native goal is refuted as its Integer reading, so the certificate
        // spells it observed: `r <= 5` as `to_integer(r) <= 5`.
        let observed_goal = observed_native_surface_comparison(goal, surface_goal);
        let surface_goal = &observed_goal;
        if crate::kernel::proof::integer_arithmetic::integer_affine_claim(goal).is_none() {
            return Ok(None);
        }
        let Some(candidates) =
            crate::surface::planning::proposition_search::solver_connected_premises(
                self.facts().assumptions(),
                goal,
            )
        else {
            return Ok(None);
        };
        check_verification_deadline()?;
        let plan = |premises: &[Proposition], ranges: &[crate::kernel::IntegerTerm]| {
            crate::instrumentation::measure_operation(
                "surface",
                "auto solver",
                "auto solver: integer refutation",
                || plan_integer_refutation_with_ranges(goal, premises, ranges),
            )
        };
        // Native comparisons read as Integer comparisons, and machine type
        // ranges, are added only when the Integer facts alone leave a
        // counterexample, so a proof that needs neither keeps its
        // certificate.
        // A native candidate reads as an Integer fact, so the first plan may
        // cite one with no source spelling (a derived low-word bound); the
        // extended search below then drops it and plans again.
        // The planner reads a native comparison as an Integer one, but the
        // solver cites native facts only through their Integer readings,
        // which it spells by the native fact's own written operands; the
        // native candidates themselves stay out.
        let native = |premise: &Proposition| {
            !crate::kernel::assumptions::integer_observations_of_native_comparison(premise)
                .is_empty()
        };
        // The first plan reads only the native facts that observe a value
        // the goal does; the extended search below reads the rest.
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
            .filter(|premise| !native(premise) || observes_goal(premise))
            .cloned()
            .collect::<Vec<_>>();
        let mut integer_candidates = with_native_comparisons_as_integer(&near);
        integer_candidates.retain(|premise| !native(premise));

        let spellings = SpellingCache::default();
        let first = match plan(&integer_candidates, &[]) {
            IntegerRefutation::Proved {
                certificate,
                premises,
            } => match self.spell_refutation(
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
                            let outcome = self.spell_refutation(
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
                                _ => return Ok(None),
                            }
                            attempts += 1;
                        }
                        IntegerRefutation::Counterexample(_) if identities => {
                            return self.try_operation_identity_closure(
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
        let Some(surface) = integer_plan_to_surface_certificate_with_ranges(
            &certificate,
            &pairs,
            surface_goal,
            &ranges,
        ) else {
            return Ok(None);
        };
        attempt::candidate_outcome(self.apply_step(ProofStep::ArithmeticCertificate(
            ArithmeticCertificate::integer(surface),
        )))
    }

    /// Spell a refutation's cited premises and type ranges. A cited fact
    /// uses `spelled` or its resolved source spelling; a native comparison
    /// read as an Integer one, and a type range, are spelled from the goal's
    /// and cited facts' written observations.
    fn spell_refutation(
        &self,
        certificate: &IntegerArithmeticCertificate,
        premises: &[Proposition],
        candidates: &[Proposition],
        spelled: &[(Proposition, ClickProposition)],
        surface_goal: &ClickProposition,
        spellings: &SpellingCache,
    ) -> Spelling {
        // The source spelling of a fact, resolved once per solver closure:
        // a retried plan cites mostly the same facts.
        let resolve = |fact: &Proposition| -> Option<(Proposition, ClickProposition)> {
            if let Some(known) = spellings.borrow().get(fact) {
                return known.clone();
            }
            let resolved = self
                .resolve_simp_premises(std::slice::from_ref(fact), &[])
                .and_then(|mut spelled| spelled.pop());
            spellings
                .borrow_mut()
                .insert(fact.clone(), resolved.clone());
            resolved
        };
        // A certificate cites its premises by their source spelling; one
        // that needs a fact with none (a conjunct of a written invariant,
        // for one) is not closed by the solver.
        let mut pairs: Vec<Option<(Proposition, ClickProposition)>> =
            Vec::with_capacity(premises.len());
        for premise in premises {
            if !candidates.contains(premise) {
                pairs.push(None);
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
            // fact spelled at a snapshot keeps that snapshot on each.
            let (selector, source) = match source {
                ClickProposition::At {
                    selector,
                    proposition,
                } => (Some(selector), *proposition),
                source => (None, source),
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
        match self.spell_type_ranges(certificate, &written) {
            Ok(ranges) => Spelling::Spelled(pairs, ranges),
            Err(value) => Spelling::UnspelledRange(value),
        }
    }

    /// Close the goal with in-range machine `+` and `-` identities. A
    /// refutation that may assume `to_integer(a op b) == to_integer(a) op
    /// to_integer(b)` for the operations among the facts' and goal's
    /// machine observations selects the identities it needs. Each is then
    /// proved: its two type-range bounds by the solver, the identity by
    /// `integer_operation_identity`, and the goal by the solver from the
    /// facts and identities. Identities are not nested: a bound that needs
    /// one is not proved here.
    fn try_operation_identity_closure(
        &self,
        goal: &Proposition,
        surface_goal: &ClickProposition,
        candidates: &[Proposition],
        written_facts: &[Proposition],
    ) -> Result<Option<Self>, ClickError> {
        use crate::kernel::IntegerTerm;
        use crate::kernel::proof::integer_operation_identity::mathematical;
        let mut identities: Vec<(IntegerTerm, IntegerTerm, Proposition)> = Vec::new();
        // An operand of an observed operation may itself be one, as
        // `available - amount` in `used + (available - amount)`; each
        // identity's operands are observed in turn, once each, so the work
        // follows the operations written.
        let mut pending = machine_observations(goal, candidates);
        let mut seen = std::collections::HashSet::new();
        while let Some(observed) = pending.pop() {
            if !seen.insert(observed.clone()) {
                continue;
            }
            let Some((_, value)) = mathematical(&observed) else {
                continue;
            };
            let (IntegerTerm::Add(left, right) | IntegerTerm::Subtract(left, right)) = &value
            else {
                continue;
            };
            for operand in [left.as_ref(), right.as_ref()] {
                if matches!(operand, IntegerTerm::Machine(_)) {
                    pending.push(operand.clone());
                }
            }
            let identity = Proposition::ConditionIs(
                ConditionTerm::integer_equal(observed.clone(), value.clone()),
                true,
            );
            identities.push((observed, value, identity));
        }
        if identities.is_empty() {
            return Ok(None);
        }
        check_verification_deadline()?;
        let mut assumed = candidates.to_vec();
        assumed.extend(identities.iter().map(|(_, _, identity)| identity.clone()));
        let ranges = machine_observations(goal, &assumed);
        let IntegerRefutation::Proved { premises, .. } = crate::instrumentation::measure_operation(
            "surface",
            "auto solver",
            "auto solver: integer refutation with operation identities",
            || plan_integer_refutation_with_ranges(goal, &assumed, &ranges),
        ) else {
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
            // A native comparison read as an Integer one has no spelling of
            // its own; the goal and the other facts spell the identities.
            if let Some((_, surface)) = self
                .resolve_simp_premises(std::slice::from_ref(premise), &[])
                .and_then(|mut spelled| spelled.pop())
            {
                surfaces.push(surface);
            }
        }
        let mut written = written_integer_observations(surfaces.iter());
        // An operand the cited facts do not spell, such as a capacity the
        // refutation bounds only through a native comparison, may still be
        // spelled by another connected fact as written, such as the native
        // `capacity == used + available` behind a cited Integer reading.
        // Look there only on a miss.
        let spells = |written: &[ContractExpression]| {
            used.iter().all(|(observed, value, _)| {
                let (IntegerTerm::Add(left, right) | IntegerTerm::Subtract(left, right)) = value
                else {
                    return false;
                };
                [observed, left.as_ref(), right.as_ref()]
                    .into_iter()
                    .all(|term| self.spell_integer_observation(term, written).is_some())
            })
        };
        if !spells(&written) {
            for premise in written_facts.iter().take(MAX_SOLVER_SPELLING_FACTS) {
                if let Some((_, surface)) = self
                    .resolve_simp_premises(std::slice::from_ref(premise), &[])
                    .and_then(|mut spelled| spelled.pop())
                {
                    surfaces.push(surface);
                }
            }
            written = written_integer_observations(surfaces.iter());
        }
        let mut proof = self.clone();
        let mut established: Vec<(Proposition, ClickProposition)> = Vec::new();
        for (observed, value, _) in used {
            let (
                IntegerTerm::Machine(machine),
                IntegerTerm::Add(left, right) | IntegerTerm::Subtract(left, right),
            ) = (observed, value)
            else {
                return Ok(None);
            };
            let (Some(spelled_observed), Some(spelled_left), Some(spelled_right)) = (
                self.spell_integer_observation(observed, &written),
                self.spell_integer_observation(left, &written),
                self.spell_integer_observation(right, &written),
            ) else {
                return Ok(None);
            };
            let (left, right) = (Box::new(spelled_left), Box::new(spelled_right));
            let spelled_value = if matches!(value, IntegerTerm::Subtract(..)) {
                ContractExpression::Subtract(left, right)
            } else {
                ContractExpression::Add(left, right)
            };
            let (min, max) = machine.ty().format().bounds();
            let lower = ClickProposition::Comparison {
                left: surface_signed_integer_literal(&min),
                operator: ComparisonOperator::LessEqual,
                right: spelled_value.clone(),
            };
            let upper = ClickProposition::Comparison {
                left: spelled_value.clone(),
                operator: ComparisonOperator::LessEqual,
                right: surface_signed_integer_literal(&max),
            };
            for bound in [&lower, &upper] {
                let scope = proof.begin_have(bound.clone())?;
                let Some(closed) = scope.try_solver_closure_without_identities()? else {
                    return Ok(None);
                };
                proof = closed.join()?;
                established.extend(
                    proof
                        .added_facts()
                        .iter()
                        .map(|fact| (fact.clone(), bound.clone())),
                );
            }
            let identity = ClickProposition::Comparison {
                left: spelled_observed,
                operator: ComparisonOperator::Equal,
                right: spelled_value,
            };
            let identity_surface = identity.clone();
            let scope = proof.begin_have(identity.clone())?;
            let step = ProofStep::ArithmeticCertificate(ArithmeticCertificate::special(
                SpecialArithmeticCertificate {
                    premises: vec![lower, upper],
                    nodes: vec![SpecialArithmeticNode::IntegerOperationIdentity {
                        bounds: vec![0, 1],
                        result: identity,
                    }],
                    conclusion: 0,
                },
            ));
            let Ok(closed) = scope.apply_step(step) else {
                return Ok(None);
            };
            proof = closed.join()?;
            established.extend(
                proof
                    .added_facts()
                    .iter()
                    .map(|fact| (fact.clone(), identity_surface.clone())),
            );
        }
        proof.solver_closure(false, &established)
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
        let (left, operator, right) = match (condition, truth) {
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
            && machine.ty() == crate::kernel::MachineIntegerType::Int32
            && let Some(view) = self.premise_fixed_state_view()
            && let Some(value) = crate::surface::proof::surface_synthesis::synthesize_surface_value(
                &CValue::Int32(machine.value().clone()),
                view.parameter_binding,
                view.fixed_state.state,
            )
        {
            return Some(ContractExpression::Call {
                name: "to_integer".into(),
                arguments: vec![value],
            });
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

    /// The written expression among `written` that lowers to `term`.
    fn spell_written_integer_observation(
        &self,
        term: &crate::kernel::IntegerTerm,
        written: &[ContractExpression],
    ) -> Option<ContractExpression> {
        written
            .iter()
            .find(|expression| {
                let probe = ClickProposition::Comparison {
                    left: (*expression).clone(),
                    operator: ComparisonOperator::LessEqual,
                    right: ContractExpression::IntegerLiteral("0".into()),
                };
                // The probe of an exact observation lowers to its native
                // comparison, which is read back as the Integer one. Zero is
                // the probe's upper side because `0 <= v` of an unsigned `v`
                // folds to true.
                let Ok(lowered) =
                    self.lower_integer_surface_proposition(&probe, "integer observation")
                else {
                    return false;
                };
                let lowered =
                    crate::kernel::assumptions::integer_observations_of_native_comparison(&lowered)
                        .into_iter()
                        .next()
                        .unwrap_or(lowered);
                matches!(
                    lowered,
                    Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(observed, _), true)
                        if observed.as_ref() == term
                )
            })
            .cloned()
    }

    /// Spell the type range of each machine observation a `TypeRange` node
    /// of `certificate` cites, as `MIN <= to_integer(v)` or
    /// `to_integer(v) <= MAX`. The observation is spelled by a written
    /// `to_integer(...)` in the goal or a cited premise that lowers to it;
    /// `None` when one has no such spelling.
    fn spell_type_ranges(
        &self,
        certificate: &IntegerArithmeticCertificate,
        written: &[ContractExpression],
    ) -> Result<Vec<(crate::kernel::IntegerTerm, bool, ClickProposition)>, crate::kernel::IntegerTerm>
    {
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
            let (min, max) = machine.ty().format().bounds();
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
            ranges.push((value.clone(), upper, bound));
        }
        Ok(ranges)
    }

    fn try_flat_simp_conjunction(
        &self,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Self>, ClickError> {
        let Some(surfaces) = self.wide_conjunction_surfaces() else {
            return Ok(None);
        };
        let mut proof = self.clone();
        for surface in surfaces {
            let scope = proof.begin_have(surface)?;
            let Some(closed) = scope.try_simp_closure_with_surfaces(introduced_surfaces)? else {
                return Ok(None);
            };
            proof = closed.join()?;
        }
        attempt::candidate_outcome(proof.apply_step(ProofStep::Assumption))
    }

    fn try_simp_closure_strategies(&self) -> Result<Option<Self>, ClickError> {
        let mut scope = attempt::search_scope("simp closure");
        if let Some(proof) = self.try_flat_simp_conjunction(&[])? {
            scope.succeed();
            return Ok(Some(proof));
        }
        if let Some(proof) = self.try_direct_logical_closure()? {
            scope.succeed();
            return Ok(Some(proof));
        }
        if self.scalar_equality_goal_is_refuted() {
            return Ok(None);
        }
        if let Some(proof) = self.try_direct_structural_closure_under_binders()? {
            scope.succeed();
            return Ok(Some(proof));
        }
        if matches!(self.context.as_ref(), ProofContext::Pure(_))
            && let Some(surface) = self.surface_goal()
            && let Ok(proof) = self.apply_step(ProofStep::Extract(surface.clone()))
            && proof.focused_discharged()
        {
            scope.succeed();
            return Ok(Some(proof));
        }
        if let Some(execution) = self.execution()
            && let Some(anchor) = frontier_premise_anchor(execution)
            && let Some(surface_goal) = self.surface_goal()
            && let Ok(source) =
                surface_at_snapshot(surface_goal, &SnapshotSelector::ProgramPoint(anchor))
            && let Ok(proof) = self.apply_step(ProofStep::Extract(source))
            && proof.is_complete()
        {
            scope.succeed();
            return Ok(Some(proof));
        }
        let result = match self.try_simp_closure_after_direct(false)? {
            Some(proof) => Some(proof),
            None => self.try_restated_constant_upper_bound()?,
        };
        if result.is_some() {
            scope.succeed();
        }
        Ok(result)
    }

    /// Closes `value <= c` over a constant by proving the same bound
    /// written `value < c + 1`. The two are one claim, but an order chain
    /// that ends at `c + 1` concludes the strict form, and the derivation
    /// asked for the non-strict form finds no chain ending at `c`.
    ///
    /// It runs only after every other strategy has missed, on a goal of
    /// exactly this shape, and the restated goal is strict, so it does not
    /// recur.
    fn try_restated_constant_upper_bound(&self) -> Result<Option<Self>, ClickError> {
        let Some(Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessEqual(_, bound),
            true,
        )) = self.goal()
        else {
            return Ok(None);
        };
        // `c + 1` must not wrap in the order the comparison is made in.
        let Some(bound) = bound.as_const().filter(|bound| *bound as i32 != i32::MAX) else {
            return Ok(None);
        };
        let Some(ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::LessEqual,
            right,
        }) = self.surface_goal().cloned()
        else {
            return Ok(None);
        };
        // The source bound is the kernel bound, or its sign-flipped form
        // for an unsigned comparison; the successor is spelled in the
        // operand's own type.
        let successor = match &right {
            ContractExpression::CFragment(CExpression::Value(CValue::UInt32(
                Bitvector32Term::Constant(value),
            ))) if *value == bound ^ 0x8000_0000 => ContractExpression::CFragment(
                CExpression::Value(CValue::UInt32(Bitvector32Term::Constant(value + 1))),
            ),
            ContractExpression::IntegerLiteral(literal)
                if literal.parse::<i32>().ok() == Some(bound as i32) =>
            {
                ContractExpression::IntegerLiteral((i64::from(bound as i32) + 1).to_string())
            }
            _ => return Ok(None),
        };
        let strict = ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::LessThan,
            right: successor,
        };
        let Ok(scope) = self.begin_have(strict.clone()) else {
            return Ok(None);
        };
        let Some(proved) = scope.try_simp_closure()? else {
            return Ok(None);
        };
        let Ok(joined) = proved.join() else {
            return Ok(None);
        };
        Ok(joined
            .apply_step(ProofStep::ArithmeticUsing(vec![strict]))
            .ok()
            .filter(|proof| proof.is_complete() || proof.goal() != self.goal()))
    }

    /// Continues smart closure after direct logical candidates have either
    /// missed or been deliberately rejected as non-checkable. When
    /// `exclude_exact_goal` is true, the atomic derivation query may not cite
    /// the goal's own ambient fact; every selected theorem step is still
    /// checked against this unchanged Proof.
    pub(super) fn try_simp_closure_after_direct(
        &self,
        exclude_exact_goal: bool,
    ) -> Result<Option<Self>, ClickError> {
        let mut scope = attempt::search_scope("simp closure after direct candidates");
        let result = self.try_simp_closure_after_direct_with_surfaces(exclude_exact_goal, &[])?;
        if result.is_some() {
            scope.succeed();
        }
        Ok(result)
    }

    pub(super) fn try_simp_closure_with_surfaces(
        &self,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Self>, ClickError> {
        let mut scope = attempt::search_scope("simp closure with surfaces");
        if let Some(proof) = self.try_direct_logical_closure()? {
            scope.succeed();
            return Ok(Some(proof));
        }
        if let Some(proof) = self.try_direct_structural_closure_under_binders()? {
            scope.succeed();
            return Ok(Some(proof));
        }
        let result =
            self.try_simp_closure_after_direct_with_surfaces(false, introduced_surfaces)?;
        if result.is_some() {
            scope.succeed();
        }
        Ok(result)
    }

    fn try_simp_closure_after_direct_with_surfaces(
        &self,
        exclude_exact_goal: bool,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Self>, ClickError> {
        self.try_simp_closure_after_direct_with_surfaces_and_function_unfold(
            exclude_exact_goal,
            introduced_surfaces,
            true,
        )
    }

    fn try_simp_closure_after_direct_with_surfaces_and_function_unfold(
        &self,
        exclude_exact_goal: bool,
        introduced_surfaces: &[ClickProposition],
        allow_function_unfold: bool,
    ) -> Result<Option<Self>, ClickError> {
        // An unsigned order is the signed order of sign-flipped operands,
        // which the derivation below treats as opaque atoms. The uint32
        // lemmas state the steps, so a goal of one of their shapes is closed
        // by naming the lemma, from the exact premise it requires.
        if let Some(proof) = self.try_unsigned_order_lemma() {
            return Ok(Some(proof));
        }
        // Population bounds are arithmetic on the authority's count, even
        // when that count shares a carrier with a C field. Try its indexed
        // bounds before searching memory equalities and recorded snapshots.
        // Compound signed orders likewise select indexed bounds before
        // spelling historical aliases, including terminal outcomes with
        // many earlier clauses. Simple terminal comparisons retain their
        // result-aware rewrites and named-rule routes first.
        let population_count_comparison = matches!(
            self.surface_goal(),
            Some(
                ClickProposition::Comparison {
                    left: ContractExpression::ResourceCount(_),
                    ..
                } | ClickProposition::Comparison {
                    right: ContractExpression::ResourceCount(_),
                    ..
                }
            )
        );
        let compound_signed_order = matches!(
            self.goal(),
            Some(Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessThan(..)
                    | ConditionTerm::Bitvector32SignedLessEqual(..)
                    | ConditionTerm::Bitvector32SignedGreaterThan(..)
                    | ConditionTerm::Bitvector32SignedGreaterEqual(..),
                _
            ))
        ) && matches!(
            self.surface_goal(),
            Some(ClickProposition::Comparison { left, right, .. })
                if [left, right].into_iter().any(|term| matches!(
                    term,
                    ContractExpression::Add(..)
                        | ContractExpression::Subtract(..)
                        | ContractExpression::Multiply(..)
                ))
        );
        let indexed_arithmetic_tried = population_count_comparison
            || compound_signed_order
            || (self.focused_outcome_data().is_none()
                && matches!(
                    self.goal(),
                    Some(Proposition::ConditionIs(
                        ConditionTerm::Bitvector32SignedLessThan(..)
                            | ConditionTerm::Bitvector32SignedLessEqual(..)
                            | ConditionTerm::Bitvector32SignedGreaterThan(..)
                            | ConditionTerm::Bitvector32SignedGreaterEqual(..),
                        _
                    ))
                ));
        if indexed_arithmetic_tried
            && let Some(proof) = crate::instrumentation::measure_operation(
                "surface",
                "simp closure",
                "simp closure: indexed bounds",
                || self.try_execution_signed_arithmetic(),
            )
        {
            return Ok(Some(proof));
        }
        // Integer arithmetic has its own compact, locally checked evidence
        // path. Keep it ahead of the legacy signed arithmetic derivation so
        // a mathematical Integer goal cannot accidentally enter the machine
        // overflow checker.
        if let Some(surface_goal) = self.surface_goal()
            && let Some(goal) = self.goal()
            && let Some(plan) = plan_integer_affine_certificate(goal, &[])
            && plan.nodes.len() == 1
            && matches!(
                plan.nodes.first(),
                Some(IntegerArithmeticNode::Trivial { .. })
            )
        {
            let certificate = IntegerCertificate {
                nodes: vec![IntegerCertificateNode::Trivial {
                    result: surface_goal.clone(),
                }],
                conclusion: 0,
            };
            if let Ok(proof) = self.apply_step(ProofStep::ArithmeticCertificate(
                ArithmeticCertificate::integer(certificate),
            )) {
                return Ok(Some(proof));
            }
        }
        if let Some(proof) = self.try_goal_conditional_normalization() {
            return Ok(Some(proof));
        }
        if let Some(surface_goal) = self.surface_goal()
            && let Some(proof) = self.try_selected_unchanged_load_forall_goal(surface_goal, &[])
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
        if let Some(flat) = self.try_flat_simp_conjunction(introduced_surfaces)? {
            return Ok(Some(flat));
        }
        let structural_conjunction_tried = if let Some(surface_goal) = self.surface_goal()
            && matches!(surface_goal, ClickProposition::And(_, _))
            && matches!(self.goal(), Some(Proposition::And(_, _)))
        {
            if let Some(structural) = crate::instrumentation::measure_operation(
                "surface",
                "simp closure",
                "simp closure: structural",
                || {
                    self.try_structural_simp_closure_with_surfaces(
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
        if let Some(closed) = self.try_constructor_guard_refutation()? {
            return Ok(Some(closed));
        }
        // Retain the selected premises for the anchored fallbacks. The proof
        // is unchanged by a declined candidate, so repeating derivation
        // discovery here would perform the same search a second time.
        let mut anchored_pairs = Vec::new();
        let atomic = (|| {
            let (goal, derivation, fixed_state_application_closes_goal) =
                self.selected_simp_derivation_plan(exclude_exact_goal)?;
            // A derivation that records the exact path it used names its
            // own premises. Spell only those first: the selection it ran in
            // holds every fact connected to the goal's variables, and
            // spelling them all costs work in the path's length for a
            // closer that cites one or two.
            let cited_pairs = derivation.recorded_path_premises().and_then(|cited| {
                self.resolve_simp_premises(&cited, introduced_surfaces)
                    .filter(|pairs| pairs.len() == cited.len())
            });
            if let Some(pairs) = &cited_pairs
                && let Some(closed) = self.check_typed_atomic_simp_candidate(
                    &goal,
                    &derivation,
                    pairs,
                    fixed_state_application_closes_goal,
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
            // A goal-local checked rewrite may close from one recorded fact.
            // Try that before spelling a whole connected component. This probe
            // never recursively invokes the broad atomic closer for a candidate.
            if let Some(closed) =
                self.try_indexed_goal_equality_rewrite_direct_closure(exclude_exact_goal)
            {
                return Some(closed);
            }
            anchored_pairs =
                self.resolve_simp_premises(&derivation.context_premises(), introduced_surfaces)?;
            let premise_pairs = &anchored_pairs;
            // This rule constructs its checked nonnegative scope directly.
            // Avoid a speculative generic candidate for this same predecessor
            // goal before constructing that scope.
            if let Some(closed) = self.try_selected_predecessor_upper_bound(&goal, premise_pairs) {
                return Some(closed);
            }
            // The same derivation already failed to check over the premises
            // it cites; the wider context does not translate it either.
            let typed_atomic =
                match self.extract_special_conjunct_premises(&derivation, premise_pairs) {
                    Ok(Some(extracted)) if extracted.is_complete() => Some(extracted),
                    _ if cited_pairs.is_some() => None,
                    Ok(Some(extracted)) => extracted.check_typed_atomic_simp_candidate(
                        &goal,
                        &derivation,
                        premise_pairs,
                        fixed_state_application_closes_goal,
                    ),
                    Ok(None) | Err(()) => self.check_typed_atomic_simp_candidate(
                        &goal,
                        &derivation,
                        premise_pairs,
                        fixed_state_application_closes_goal,
                    ),
                };
            typed_atomic
                .or_else(|| self.try_selected_pointer_inequality_rewrite(&goal, premise_pairs))
                .or_else(|| self.try_selected_equality_rewrite_chain(premise_pairs))
                .or_else(|| self.try_selected_constant_bound_weakening(&goal, &derivation))
                .or_else(|| {
                    self.surface_goal().and_then(|surface_goal| {
                        self.try_selected_unchanged_load_forall_goal(surface_goal, premise_pairs)
                            .or_else(|| {
                                self.try_selected_forall_goal(&goal, surface_goal, premise_pairs)
                            })
                    })
                })
                .or_else(|| self.try_selected_forall_instantiation(&goal, premise_pairs))
                .or_else(|| self.try_selected_disjunction_cases(premise_pairs))
        })();
        check_verification_deadline()?;
        if let Some(atomic) = atomic {
            return Ok(Some(atomic));
        }
        if matches!(self.context.as_ref(), ProofContext::Pure(_)) {
            for (_, surface) in &anchored_pairs {
                if let Some(contradiction) = attempt::candidate_outcome(
                    self.apply_step(ProofStep::Contradiction(surface.clone())),
                )? {
                    return Ok(Some(contradiction));
                }
            }
        }
        if let Some(surface_goal) = self.surface_goal()
            && let Some(goal) = self.goal()
            && !anchored_pairs.is_empty()
            && let Some(plan) = plan_integer_affine_certificate(
                goal,
                &anchored_pairs
                    .iter()
                    .map(|(kernel, _)| kernel.clone())
                    .collect::<Vec<_>>(),
            )
            && let Some(certificate) =
                integer_plan_to_surface_certificate(&plan, &anchored_pairs, surface_goal)
            && let Ok(proof) = self.apply_step(ProofStep::ArithmeticCertificate(
                ArithmeticCertificate::integer(certificate),
            ))
        {
            return Ok(Some(proof));
        }
        if let Some(anchored) = self
            .try_outcome_anchored_order_transitivity(&anchored_pairs)
            .or_else(|| self.try_outcome_anchored_increment_order(&anchored_pairs))
        {
            return Ok(Some(anchored));
        }
        if let Some(rewritten) = crate::instrumentation::measure_operation(
            "surface",
            "simp closure",
            "simp closure: indexed goal equality rewrite",
            || {
                self.try_indexed_goal_equality_rewrite_closure_excluding(
                    exclude_exact_goal,
                    allow_function_unfold,
                )
            },
        ) {
            return Ok(Some(rewritten));
        }
        // Indexed rewrite planning uses Option for an ordinary candidate
        // miss; preserve an exhausted budget before trying another closer.
        check_verification_deadline()?;
        if allow_function_unfold
            && let Some(rewritten) =
                self.try_introduced_equality_then_function_unfold_closure(introduced_surfaces)?
        {
            return Ok(Some(rewritten));
        }
        // A goal over a value a fact equates to a constructor, as a proof
        // `match` arm's case states it: evaluate from a rewrite.
        if allow_function_unfold
            && self.facts().assumptions().has_algebraic_constructor_facts()
            && let Some(rewritten) = self.try_constructor_evaluation_closure(introduced_surfaces)?
        {
            return Ok(Some(rewritten));
        }
        if let Some(surface_goal) = self.surface_goal()
            && let Some(proof) = self.try_snapshot_transport_closure(surface_goal)?
        {
            return Ok(Some(proof));
        }
        if let Some(instantiated) =
            self.try_indexed_forall_instantiation_with_surfaces(introduced_surfaces)
        {
            return Ok(Some(instantiated));
        }
        if let Some(defined) = self.try_signed_definedness_closure()? {
            return Ok(Some(defined));
        }
        if let Some(eliminated) = self.try_disjunctive_syllogism_closure() {
            return Ok(Some(eliminated));
        }
        if let Some(guarded) = self.try_guarded_consequent_closure()? {
            return Ok(Some(guarded));
        }
        // The atomic helpers still classify their internal candidate misses
        // as `Option`; surface a deadline that fired inside them here rather
        // than continuing into structural search with it exceeded.
        check_verification_deadline()?;
        if self.surface_goal().is_none() && matches!(self.goal(), Some(Proposition::And(_, _))) {
            return self.try_structural_and_simp_closure(introduced_surfaces);
        }
        let Some(surface_goal) = self.surface_goal().cloned() else {
            return Ok(None);
        };
        if let Some(enumerated) = self.try_finite_forall_enumeration(&surface_goal)? {
            return Ok(Some(enumerated));
        }
        // A pure goal that its own signed bounds already decide gets the one
        // checked arithmetic certificate, not a case split over those same
        // bounds. The certificate reads the goal's own bound buckets and
        // emits a single leaf, while the split searches for a pivot and then
        // owes a proof on each arm — including a dead arm closed only by a
        // contradiction between the pivot and a premise. Keep this ahead of
        // the split so the cheaper, smaller expansion wins whenever it
        // applies; the split still runs for everything the certificate
        // declines.
        if let Some(arithmetic) = self.try_pure_signed_arithmetic() {
            return Ok(Some(arithmetic));
        }
        if let Some(split) = self.try_upper_bound_split_closure(introduced_surfaces)? {
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
                "simp closure",
                "simp closure: structural",
                || {
                    self.try_structural_simp_closure_with_surfaces(
                        &surface_goal,
                        introduced_surfaces,
                    )
                },
            )?
        {
            return Ok(Some(structural));
        }
        if allow_function_unfold
            && let Some(unfolded) = self.try_function_unfold_simp_closure(introduced_surfaces)?
        {
            return Ok(Some(unfolded));
        }
        // A Special fact such as `aligned(p + i, 8)` is not generally a
        // simp-derivation: the kernel's pointer rule consumes a matching
        // alignment/relation fact directly. Use the selected pairs when
        // `simp() using` supplied them; otherwise recover only typed Special
        // candidates from the recorded Surface map for generic `simp()`.
        if let Some(surface_goal) = self.surface_goal()
            && let Some(goal) = self.goal()
        {
            let special_pairs = if !anchored_pairs.is_empty() {
                anchored_pairs.clone()
            } else {
                let (surface_facts, premise_anchor) = match self.context.as_ref() {
                    ProofContext::Pure(context) => {
                        (&context.theorem_context.surface_requirements, None)
                    }
                    ProofContext::FixedState(context) => (
                        context.surface_propositions,
                        context.premise_anchor.as_ref(),
                    ),
                    ProofContext::Execution(_) => {
                        if let Some(data) = self.focused_outcome_data() {
                            (&data.surface_propositions, data.premise_anchor.as_ref())
                        } else {
                            let Some(execution) = self.execution() else {
                                return Ok(None);
                            };
                            (&execution.presentation.surface_propositions, None)
                        }
                    }
                };
                self.facts()
                    .special_candidates_mentioning(goal)
                    .into_iter()
                    .filter(|premise| {
                        matches!(
                            premise,
                            Proposition::ConditionIs(
                                ConditionTerm::Bitvector64Equal(..)
                                    | ConditionTerm::PointerValueEqual(..)
                                    | ConditionTerm::PointerEqual(..)
                                    | ConditionTerm::PointerOffsetEqual(..)
                                    | ConditionTerm::Float32(
                                        CFloatCondition::Classification { .. }
                                    )
                                    | ConditionTerm::Float64(
                                        CFloatCondition::Classification { .. }
                                    ),
                                true
                            )
                        )
                    })
                    .filter_map(|premise| {
                        self.available_surface_fact(surface_facts, premise_anchor, &premise)
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
            if let Some(plan) = plan_special_arithmetic_certificate(goal, &kernels) {
                let certificate =
                    special_plan_to_surface_certificate(&plan, &surfaces, surface_goal);
                if let Ok(proof) = self.apply_step(ProofStep::ArithmeticCertificate(certificate)) {
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
        if let Some(surface_goal) = self.surface_goal()
            && let Some(goal) = self.goal()
            && !anchored_pairs.is_empty()
            && let Some(plan) = plan_signed_arithmetic_certificate(
                goal,
                &anchored_pairs
                    .iter()
                    .map(|(kernel, _)| kernel.clone())
                    .collect::<Vec<_>>(),
            )
            && let Some(certificate) =
                self.signed_plan_to_surface_certificate(&plan, &anchored_pairs, surface_goal)
            && let Ok(proof) =
                self.apply_step(ProofStep::ArithmeticCertificate(ArithmeticCertificate {
                    family: ArithmeticCertificateFamily::SignedInt32(certificate),
                }))
        {
            return Ok(Some(proof));
        }
        if !indexed_arithmetic_tried
            && let Some(arithmetic) = crate::instrumentation::measure_operation(
                "surface",
                "simp closure",
                "simp closure: indexed bounds",
                || self.try_execution_signed_arithmetic(),
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
    fn try_pure_signed_arithmetic(&self) -> Option<Self> {
        let ProofContext::Pure(context) = self.context.as_ref() else {
            return None;
        };
        self.try_indexed_signed_arithmetic(&context.theorem_context.surface_requirements, None)
    }

    /// The same indexed bound selection on an execution proof: at function
    /// exit, at a statement frontier, or inside a loop phase, so simp reads a
    /// variable's bounds the same way wherever it runs. A bound can also be
    /// the negation of a branch condition. A goal that is itself an available
    /// fact is left to `assumption`. Pre-return signed orders and population
    /// bounds run before broad premise spelling, preferring named rules on
    /// the selected premises; other goals retain the final fallback.
    fn try_execution_signed_arithmetic(&self) -> Option<Self> {
        if NamedPremiseClosureScope::active() {
            return None;
        }
        let goal = self.goal()?;
        if std::iter::once(goal.clone())
            .chain(condition_polarity_forms(goal))
            .any(|form| self.facts().contains(&form))
        {
            return None;
        }
        let (surfaces, anchor) = match self.context.as_ref() {
            ProofContext::Pure(_) => return None,
            ProofContext::FixedState(context) => {
                (context.surface_propositions, context.premise_anchor.clone())
            }
            ProofContext::Execution(_) => match self.focused_outcome_data() {
                Some(data) => (&data.surface_propositions, data.premise_anchor.clone()),
                None => (
                    &self.execution()?.surface_propositions,
                    self.execution().and_then(frontier_premise_anchor),
                ),
            },
        };
        self.try_indexed_signed_arithmetic(surfaces, anchor.as_ref())
    }

    /// The facts the indexed signed arithmetic route plans over: the bounds
    /// reachable from the goal's variables, and with `with_equalities` the
    /// equalities naming them too, followed to their own variables. Each
    /// visited variable costs its indexed bound entries and, with
    /// equalities, one indexed lookup of the facts that mention it.
    fn indexed_arithmetic_premises(
        &self,
        goal: &Proposition,
        with_equalities: bool,
    ) -> (Vec<Proposition>, bool) {
        let mut available = BTreeSet::new();
        let mut has_equalities = false;
        let mut visited = BTreeSet::new();
        // Count lowering can leave a read expression where the bounds index
        // names its registered load variable. Seed from that canonical value,
        // not from variables in the read's address or memory snapshot.
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
            for (endpoint, other, strict, forward) in self
                .facts()
                .assumptions()
                .signed_order_bound_entries(&Bitvector32Term::Variable(variable))
            {
                let (left, right) = if forward {
                    (endpoint, other)
                } else {
                    (other, endpoint)
                };
                let condition = if strict {
                    ConditionTerm::Bitvector32SignedLessThan(Box::new(left), Box::new(right))
                } else {
                    ConditionTerm::Bitvector32SignedLessEqual(Box::new(left), Box::new(right))
                };
                let fact = Proposition::ConditionIs(condition, true);
                let mut found = false;
                for form in std::iter::once(fact.clone()).chain(condition_polarity_forms(&fact)) {
                    if self.facts().contains(&form) {
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
            let equalities = self
                .facts()
                .assumptions()
                .condition_facts_mentioning_variable(variable)
                .into_iter()
                .flatten()
                .filter(|(condition, value)| {
                    *value && matches!(condition, ConditionTerm::Bitvector32Equal(..))
                })
                .map(|(condition, _)| Proposition::ConditionIs(condition.clone(), true))
                // A load's defining equation only names that same value.
                // It adds no arithmetic relation, and following its memory
                // term would pull unrelated address variables into the search.
                .filter(|fact| !crate::kernel::is_load_variable_defining_fact(fact))
                .collect::<Vec<_>>();
            for fact in equalities {
                if !self.facts().contains(&fact) {
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
    /// `extract`. Literal bounds on the goal variables are tried first, so
    /// unrelated relational claims do not crowd out those operands' ranges.
    /// The certificate is planned over the kernel facts before any
    /// of them is spelled, so a goal the bounds do not decide is declined
    /// without surface work.
    fn try_indexed_signed_arithmetic(
        &self,
        surfaces: &SurfacePropositionMap,
        anchor: Option<&ProgramPointRef>,
    ) -> Option<Self> {
        let goal = self.goal()?;
        let surface_goal = self.surface_goal()?;
        let is_pure = matches!(self.context.as_ref(), ProofContext::Pure(_));
        // A variable's literal bounds can settle the goal without admitting
        // every earlier relational claim on that variable to the planner's
        // bounded premise slice. Keep that slice local even in a contract
        // with hundreds of independently checked outcomes.
        let mut available = indexed_constant_arithmetic_premises(self.facts().assumptions(), goal);
        let compact_plan = plan_signed_arithmetic_certificate(goal, &available);
        // If the literal bounds miss, retain the existing relational-bound
        // and equality routes.
        if compact_plan.is_none() {
            available = self.indexed_arithmetic_premises(goal, false).0;
        }
        let plan = if let Some(plan) =
            compact_plan.or_else(|| plan_signed_arithmetic_certificate(goal, &available))
        {
            plan
        } else {
            let (expanded, has_equalities) = self.indexed_arithmetic_premises(goal, true);
            // Without a selected equality, the second traversal follows the
            // same bounds graph and cannot change the first planning miss.
            if !has_equalities {
                return None;
            }
            available = expanded;
            plan_signed_arithmetic_certificate(goal, &available)?
        };
        let planned_premises = available.len();
        let mut pairs = Vec::new();
        for fact in available {
            let source = self
                .available_surface_fact(surfaces, anchor, &fact)
                .or_else(|| (!is_pure).then(|| self.spelled_comparison_surface(&fact))?);
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
            && let Some(SimpEvidence::Derivation(derivation)) =
                plan_simp_certificate(goal, &assumptions_from_propositions(&kernels))
            && let Some(closed) = self.check_typed_atomic_simp_candidate(
                goal,
                &derivation,
                &pairs,
                matches!(self.context.as_ref(), ProofContext::FixedState(_)),
            )
        {
            return Some(closed);
        }
        let plan = if kernels.len() == planned_premises {
            plan
        } else {
            plan_signed_arithmetic_certificate(goal, &kernels)?
        };
        let certificate = self.signed_plan_to_surface_certificate(&plan, &pairs, surface_goal)?;
        self.apply_step(ProofStep::ArithmeticCertificate(ArithmeticCertificate {
            family: ArithmeticCertificateFamily::SignedInt32(certificate),
        }))
        .ok()
    }

    /// Select only guards actually occurring in the goal, through indexed
    /// fact/source lookups. The emitted simple step checks every selection.
    fn try_goal_conditional_normalization(&self) -> Option<Self> {
        // The trusted ambient graph may close an equality without any
        // explicit condition premise. Emit the existing simple checker with
        // an empty input list; no fact search or extra theorem premise is
        // needed, and expansion preserves this exact check.
        if matches!(
            self.goal(),
            Some(Proposition::ConditionIs(
                ConditionTerm::PointerEqual(..) | ConditionTerm::PointerValueEqual(..),
                true
            ))
        ) && let Ok(proof) = self.apply_step(ProofStep::NormalizeUsing(Vec::new()))
            && proof.is_complete()
        {
            return Some(proof);
        }
        let guards =
            crate::kernel::proof::term_rewrite::TermRewrite::conditional_guards(self.goal()?);
        let frontier_anchor = match self.context.as_ref() {
            ProofContext::Execution(_) if self.focused_outcome_data().is_none() => {
                self.execution().and_then(frontier_premise_anchor)
            }
            _ => None,
        };
        let (surfaces, anchor) = match self.context.as_ref() {
            ProofContext::Pure(context) => (&context.theorem_context.surface_requirements, None),
            ProofContext::FixedState(context) => (
                context.surface_propositions,
                context.premise_anchor.as_ref(),
            ),
            ProofContext::Execution(_) => match self.focused_outcome_data() {
                Some(data) => (&data.surface_propositions, data.premise_anchor.as_ref()),
                None => (
                    &self.execution()?.surface_propositions,
                    frontier_anchor.as_ref(),
                ),
            },
        };
        // The written goal retains nominal field places that the imported
        // scalar execution expression can spell only as a lowered index.
        // Cite its own conditional guards before reconstructing a premise
        // from execution syntax, so printing preserves that field's type.
        let written_guards = match self.surface_goal() {
            Some(ClickProposition::Comparison { left, right, .. }) => [left, right]
                .into_iter()
                .filter_map(|expression| match expression {
                    ContractExpression::If { condition, .. } => Some(condition.as_ref().clone()),
                    _ => None,
                })
                .flat_map(|condition| {
                    [
                        condition.clone(),
                        ClickProposition::Not(Box::new(condition)),
                    ]
                })
                .filter_map(|surface| {
                    let lowered = self
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
                let fact = Proposition::ConditionIs(condition.clone(), value);
                if !self.facts().contains(&fact)
                    && !condition_polarity_forms(&fact)
                        .iter()
                        .any(|form| self.facts().contains(form))
                {
                    continue;
                }
                let surface = written_guards
                    .iter()
                    .find(|(lowered, _)| {
                        *lowered == fact || condition_polarity_equivalent(lowered, &fact)
                    })
                    .map(|(_, surface)| surface.clone())
                    .or_else(|| self.available_surface_fact(surfaces, anchor, &fact))
                    .or_else(|| {
                        condition_polarity_forms(&fact)
                            .iter()
                            .find_map(|form| self.available_surface_fact(surfaces, anchor, form))
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
        self.apply_step(ProofStep::NormalizeUsing(premises))
            .ok()
            .filter(Proof::is_complete)
    }

    /// Uses one explicitly supplied equality before unfolding applications in
    /// the rewritten goal. Loop preservation supplies its entry invariants in
    /// this list: rewriting through that checked premise first changes a
    /// function-entry comparison into the smaller loop-entry frame that the
    /// defining equation can expose.
    fn try_introduced_equality_then_function_unfold_closure(
        &self,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Self>, ClickError> {
        for surface in introduced_surfaces {
            for oriented in
                std::iter::once(surface.clone()).chain(reverse_surface_equality(surface))
            {
                let Some(rewritten) =
                    attempt::candidate_outcome(self.apply_step(ProofStep::Rewrite(oriented)))?
                else {
                    continue;
                };
                if let Some(closed) = rewritten.try_direct_logical_closure()? {
                    return Ok(Some(closed));
                }
                if let Some(closed) =
                    rewritten.try_function_unfold_simp_closure(introduced_surfaces)?
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
    fn try_function_unfold_simp_closure(
        &self,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Self>, ClickError> {
        // The structural closer introduces these binders and searches their
        // bodies with the guard or fresh variable available. Unfolding the
        // whole binder would repeat that same search for every candidate.
        if matches!(
            self.goal(),
            Some(Proposition::Implies(..) | Proposition::ForAll { .. })
        ) {
            return Ok(None);
        }
        let Some(_scope) = SimpFallbackScope::enter(SimpFallback::FunctionUnfold) else {
            return Ok(None);
        };
        let Some(surface_goal) = self.surface_goal() else {
            return Ok(None);
        };
        let applications =
            pure_theorems::click_function_applications(surface_goal, introduced_surfaces);
        if applications.is_empty() {
            return Ok(None);
        }
        let mut unfolded_any = false;
        let mut proof = self.clone();
        for application in applications {
            let attempted = proof.apply_step(ProofStep::UnfoldFunction(application));
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
            if let Some(closed) = proof.try_direct_logical_closure()? {
                return Ok(Some(closed));
            }
            // A recursive definition over a known constructor exposes its
            // recursive call on a smaller argument. Evaluate those calls to a
            // fixed fuel before searching.
            if let Some(closed) = proof.try_constructor_evaluation_closure(introduced_surfaces)? {
                return Ok(Some(closed));
            }
            if let Some(closed) = proof
                .try_simp_closure_after_direct_with_surfaces_and_function_unfold(
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
            return self.try_constructor_evaluation_closure(introduced_surfaces);
        }
        Ok(None)
    }

    /// Evaluate a goal's recursive applications over known constructors, at
    /// most `CONSTRUCTOR_EVALUATION_FUEL` checked steps. Each step is the
    /// first that applies of: an `unfold` of an application in the goal
    /// (which the kernel accepts only when its argument selects one
    /// definition arm), or a `rewrite` by a supplied equation whose right
    /// side is a constructor, exposing one for the next unfold. There is no
    /// branching: one candidate per step, and the goal is checked for
    /// closure after each. Nothing is kept unless the goal closes.
    fn try_constructor_evaluation_closure(
        &self,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Self>, ClickError> {
        // A fact recorded at a program point keeps its anchor, `at(p, s) ==
        // at(p, Shape::Circle(r))`; the anchored constructor is still one.
        let is_constructor_equation = |surface: &ClickProposition| {
            let ClickProposition::Comparison {
                operator: ComparisonOperator::Equal,
                right,
                ..
            } = surface
            else {
                return false;
            };
            let mut right = right;
            while let ContractExpression::At { expression, .. } = right {
                right = expression;
            }
            matches!(right, ContractExpression::AlgebraicConstructor { .. })
        };
        let mut constructor_equations: Vec<ClickProposition> = introduced_surfaces
            .iter()
            .filter(|surface| is_constructor_equation(surface))
            .cloned()
            .collect();
        let mut fact_equations_gathered = false;
        let mut proof = self.clone();
        for _ in 0..CONSTRUCTOR_EVALUATION_FUEL {
            check_verification_deadline()?;
            let Some(surface_goal) = proof.surface_goal() else {
                return Ok(None);
            };
            let mut next = None;
            for application in pure_theorems::click_function_applications(surface_goal, &[]) {
                if let Some(unfolded) = attempt::candidate_outcome(
                    proof.apply_step(ProofStep::UnfoldFunction(application)),
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
                        crate::surface::planning::proposition_search::solver_connected_equalities(
                            proof.facts().assumptions(),
                            goal,
                        )
                {
                    for equality in equalities.iter().take(CONSTRUCTOR_EVALUATION_FACTS) {
                        if let Some((_, surface)) = proof
                            .resolve_simp_premises(std::slice::from_ref(equality), &[])
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
                        proof.apply_step(ProofStep::Rewrite(equation.clone())),
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
            if let Some(closed) = proof.try_direct_logical_closure()? {
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
    fn try_upper_bound_split_closure(
        &self,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Self>, ClickError> {
        // Each arm of a split runs the whole closure, which reaches this
        // split again on the next bound. Along a chain `x0 <= x1 <= ...`
        // that recursion followed every bound, so a goal no split decides
        // cost closure runs linear in the chain. Nest a fixed number.
        let Some(_scope) = UpperBoundSplitScope::enter() else {
            return Ok(None);
        };
        let Some(goal) = self.goal() else {
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
        if let Some(surface_goal) = self.surface_goal() {
            let mut surface_names = BTreeSet::new();
            collect_current_proposition_variables(surface_goal, &mut surface_names);
            for name in surface_names {
                let expression = ContractExpression::CFragment(CExpression::Variable(name));
                let probe = ClickProposition::Comparison {
                    left: expression.clone(),
                    operator: ComparisonOperator::Equal,
                    right: expression,
                };
                if let Ok(kernel) =
                    self.lower_surface_proposition(&probe, "upper-bound goal variable")
                {
                    goal_variables.extend(crate::kernel::proposition_variables(&kernel));
                }
            }
        }
        if goal_variables.is_empty() {
            return Ok(None);
        }

        let frontier_anchor: Option<ProgramPointRef>;
        let (surface_facts, premise_anchor) = match self.context.as_ref() {
            ProofContext::Pure(context) => (&context.theorem_context.surface_requirements, None),
            ProofContext::FixedState(context) => (
                context.surface_propositions,
                context.premise_anchor.as_ref(),
            ),
            ProofContext::Execution(_) => {
                if let Some(data) = self.focused_outcome_data() {
                    (&data.surface_propositions, data.premise_anchor.as_ref())
                } else {
                    let Some(execution) = self.execution() else {
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
                let bound = self
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
                for (endpoint, other, strict, forward) in self
                    .facts()
                    .assumptions()
                    .signed_order_bound_entries(&Bitvector32Term::Variable(*variable))
                {
                    let (left, right) = if forward {
                        (endpoint, other)
                    } else {
                        (other, endpoint)
                    };
                    let condition = if strict {
                        ConditionTerm::Bitvector32SignedLessThan(Box::new(left), Box::new(right))
                    } else {
                        ConditionTerm::Bitvector32SignedLessEqual(Box::new(left), Box::new(right))
                    };
                    let fact = Proposition::ConditionIs(condition, true);
                    for bound in
                        std::iter::once(fact.clone()).chain(condition_polarity_forms(&fact))
                    {
                        if self.facts().contains(&bound)
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
                    Term::Bitvector32(pivot.clone()),
                    Term::Bitvector32(pivot.clone()),
                );
                if crate::kernel::proposition_variables(&pivot_probe).contains(&variable) {
                    return None;
                }
                let bound_surface = introduced_surface.or_else(|| {
                    self.available_surface_fact(surface_facts, premise_anchor, &bound)
                })?;
                let split_kernel = Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedLessThan(
                        Box::new(Bitvector32Term::Variable(variable)),
                        Box::new(pivot),
                    ),
                    true,
                );
                let direct = surface_upper_bound_direct_condition(&bound_surface)?;
                let direct_surface = std::iter::once(direct.clone())
                    .chain(
                        self.premise_fixed_state_view()
                            .into_iter()
                            .flat_map(|view| {
                                view.fixed_state
                                    .recorded_snapshots
                                    .recent(MAX_TRANSPORT_SOURCE_POINTS)
                                    .into_iter()
                                    .filter_map(|(selector, _)| {
                                        surface_at_snapshot(&direct, selector).ok()
                                    })
                                    .collect::<Vec<_>>()
                            }),
                    )
                    .find(|surface| {
                        self.lower_surface_proposition(surface, "upper-bound premise")
                            .is_ok_and(|lowered| lowered == bound)
                    })?;
                let mut surface_candidates = vec![
                    surface_upper_bound_split_condition(&bound_surface)?,
                    direct.clone(),
                ];
                if let Some(view) = self.premise_fixed_state_view() {
                    surface_candidates.extend(
                        view.fixed_state
                            .recorded_snapshots
                            .recent(MAX_TRANSPORT_SOURCE_POINTS)
                            .into_iter()
                            .filter_map(|(selector, _)| {
                                surface_at_snapshot(&direct, selector).ok()
                            }),
                    );
                }
                let split_surface = surface_candidates.into_iter().find(|surface| {
                    self.lower_surface_proposition(surface, "upper-bound split condition")
                        .is_ok_and(|lowered| lowered == split_kernel)
                })?;
                let split_negation = ClickProposition::Not(Box::new(split_surface.clone()));
                if introduced_surfaces
                    .iter()
                    .any(|surface| surface == &split_surface || surface == &split_negation)
                    || condition_polarity_forms(&split_kernel)
                        .iter()
                        .any(|form| self.facts().contains(form))
                {
                    return None;
                }
                Some((split_surface, direct_surface))
            })
            .collect::<Vec<_>>();
        for (condition, direct_bound) in candidates {
            let (split_proof, split, ids) = self.split_focused_if(condition.clone())?;
            let marker = split_proof.checkpoint();
            let mut then_surfaces = introduced_surfaces.to_vec();
            then_surfaces.push(condition.clone());
            let then_branch = split_proof.focus_branch(ids[0])?;
            let disequality = surface_split_disequality(&condition)
                .expect("an upper-bound split condition is a strict comparison");
            let disequality_scope = then_branch.begin_have(disequality.clone())?;
            let disequality_done = disequality_scope
                .try_simp_closure_with_surfaces(&then_surfaces)?
                .or_else(|| {
                    let (left, right) = surface_strict_parts(&condition)?;
                    disequality_scope
                        .apply_step(ProofStep::ApplyTheoremUsing {
                            application: TheoremApplication {
                                name: "click::machine_integer::int32_less_than_implies_not_equal"
                                    .to_string(),
                                arguments: vec![left, right],
                            },
                            premises: vec![condition.clone()],
                        })
                        .ok()
                });
            let Some(disequality_done) = disequality_done else {
                continue;
            };
            let then_branch = disequality_done.join()?;
            then_surfaces.push(disequality);
            let Some(then_done) = then_branch.try_simp_closure_with_surfaces(&then_surfaces)?
            else {
                continue;
            };
            let negated = ClickProposition::Not(Box::new(condition.clone()));
            let mut else_surfaces = introduced_surfaces.to_vec();
            else_surfaces.push(negated.clone());
            let equality = surface_split_equality(&condition)
                .expect("an upper-bound split condition is a strict comparison");
            let nonstrict = surface_split_nonstrict_bound(&condition)
                .expect("an upper-bound split condition is a strict comparison");
            let else_branch = then_done.focus_branch(ids[1])?;
            let equality_scope = else_branch.begin_have(equality.clone())?;
            let nonstrict_scope = equality_scope.begin_have(nonstrict.clone())?;
            let nonstrict_done = nonstrict_scope
                .try_simp_closure_with_surfaces(&else_surfaces)?
                .or_else(|| {
                    nonstrict_scope
                        .apply_step(ProofStep::ApplyTheoremUsing {
                            application: TheoremApplication {
                                name: "click::machine_integer::int32_less_than_increment_implies_less_equal".to_string(),
                                arguments: surface_nonstrict_parts(&nonstrict)
                                    .map(|(left, right)| vec![left, right])?,
                            },
                            premises: vec![direct_bound.clone()],
                        })
                        .ok()
                });
            let Some(nonstrict_done) = nonstrict_done else {
                continue;
            };
            let equality_scope = equality_scope.join_nested(nonstrict_done)?;
            else_surfaces.push(nonstrict);
            let Some(equality_done) =
                equality_scope.try_simp_closure_with_surfaces(&else_surfaces)?
            else {
                continue;
            };
            let else_branch = equality_done.join()?;
            else_surfaces.push(equality.clone());
            let rewritten_surface_goal =
                surface_strict_parts(&condition).and_then(|(left, right)| {
                    let ContractExpression::CFragment(CExpression::Variable(name)) = left else {
                        return None;
                    };
                    substitute_click_proposition(
                        else_branch.surface_goal()?,
                        &std::iter::once((name, right)).collect(),
                    )
                    .ok()
                });
            let transported_else = else_branch
                .surface_goal()
                .and_then(old_reflexive_transport_source)
                .and_then(|source| {
                    else_branch
                        .try_planned_execution_proposition_fact_transport(
                            &source,
                            else_branch.surface_goal()?,
                        )
                        .ok()
                        .flatten()
                })
                .filter(Proof::focused_discharged);
            let rewritten_else = match else_branch.apply_step(ProofStep::Rewrite(equality.clone()))
            {
                Ok(rewritten) if rewritten.focused_discharged() => Some(rewritten),
                Ok(rewritten) => {
                    let transported = rewritten_surface_goal
                        .as_ref()
                        .and_then(old_reflexive_transport_source)
                        .and_then(|source| {
                            rewritten
                                .try_planned_execution_proposition_fact_transport(
                                    &source,
                                    rewritten_surface_goal.as_ref()?,
                                )
                                .ok()
                                .flatten()
                        })
                        .filter(Proof::focused_discharged);
                    if transported.is_some() {
                        transported
                    } else {
                        rewritten.try_simp_closure_with_surfaces(&else_surfaces)?
                    }
                }
                Err(_) => None,
            };
            let else_done = if transported_else.is_some() {
                transported_else
            } else if rewritten_else.is_some() {
                rewritten_else
            } else {
                else_branch.try_simp_closure_with_surfaces(&else_surfaces)?
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
    pub(super) fn try_outcome_anchored_order_transitivity(
        &self,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        let data = self.focused_outcome_data()?;
        let anchor = data.premise_anchor.as_ref()?;
        let predecessor = match anchor.region {
            CodeRegionRef::Statement(index) if index > 0 => Some(ProgramPointRef {
                region: CodeRegionRef::Statement(index - 1),
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
                    let anchored = surface_at_snapshot(surface, anchor).ok()?;
                    let parts = surface_nonstrict_parts(&anchored)?;
                    Some((anchored, parts))
                })
                .collect::<Vec<_>>();
            for (first_surface, (first, middle)) in &ordered {
                for (second_surface, (second_middle, last)) in &ordered {
                    if middle != second_middle {
                        continue;
                    }
                    let theorem = ProofStep::ApplyTheoremUsing {
                        application: TheoremApplication {
                            name: "click::machine_integer::int32_greater_equal_transitive"
                                .to_string(),
                            arguments: vec![last.clone(), middle.clone(), first.clone()],
                        },
                        premises: vec![second_surface.clone(), first_surface.clone()],
                    };
                    let Ok(applied) = self.apply_step(theorem) else {
                        continue;
                    };
                    if applied.is_complete() {
                        return Some(applied);
                    }
                    if let Some(closed) = applied.try_direct_logical_closure().ok().flatten() {
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
    /// ordinary theorem, nested-`have`, and assumption checkers decide whether
    /// either constant-size historical application establishes the current
    /// result-aware goal.
    pub(super) fn try_outcome_anchored_increment_order(
        &self,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        let data = self.focused_outcome_data()?;
        let anchor = data.premise_anchor.as_ref()?;
        let predecessor = match anchor.region {
            CodeRegionRef::Statement(index) if index > 0 => Some(ProgramPointRef {
                region: CodeRegionRef::Statement(index - 1),
                kind: anchor.kind,
            }),
            _ => None,
        };
        let surface_goal = self.surface_goal()?.clone();
        surface_nonstrict_parts(&surface_goal)?;
        for anchor in predecessor
            .as_ref()
            .into_iter()
            .chain(std::iter::once(anchor))
        {
            let mut lower_bounds = Vec::new();
            let mut upper_bounds = Vec::new();
            for (kernel, surface) in premise_pairs {
                let anchored = surface_at_snapshot(surface, anchor).ok()?;
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
                for (upper_surface, (upper_value, surface_upper), upper_kernel) in &upper_bounds {
                    // Entry requirements and resource observations can spell
                    // the same checked value at different snapshots. Select
                    // by the kernel endpoint as well as identical syntax;
                    // ApplyTheoremUsing still validates both named premises
                    // and the result at the chosen historical boundary.
                    if lower_value != upper_value
                        && !(lower_kernel.is_some() && lower_kernel == upper_kernel)
                    {
                        continue;
                    }
                    let theorem = ProofStep::ApplyTheoremUsing {
                        application: TheoremApplication {
                            name: "click::machine_integer::int32_increment_preserves_order"
                                .to_string(),
                            arguments: vec![
                                lower_value.clone(),
                                surface_lower.clone(),
                                surface_upper.clone(),
                            ],
                        },
                        premises: vec![lower_surface.clone(), upper_surface.clone()],
                    };
                    let Ok(applied) = self.apply_step(theorem) else {
                        continue;
                    };
                    if applied.is_complete() {
                        return Some(applied);
                    }
                    let one = ContractExpression::CFragment(CExpression::Value(int32(1)));
                    let theorem_conclusion = ClickProposition::Comparison {
                        left: ContractExpression::Add(
                            Box::new(surface_lower.clone()),
                            Box::new(one.clone()),
                        ),
                        operator: ComparisonOperator::LessEqual,
                        right: ContractExpression::Add(
                            Box::new(lower_value.clone()),
                            Box::new(one),
                        ),
                    };
                    if let Some(closed) = applied
                        .apply_step(ProofStep::TransportUsing {
                            source: theorem_conclusion,
                            target: surface_goal.clone(),
                            premises: Vec::new(),
                        })
                        .ok()
                        .or_else(|| applied.try_direct_logical_closure().ok().flatten())
                    {
                        return Some(closed);
                    }
                }
            }
        }
        None
    }

    /// Tries the focused branch goal itself as one explicit fact transport from a
    /// recorded program point. This also applies to proposition scopes opened
    /// mid-execution, such as loop-invariant initialization and preservation.
    /// The candidate space is the execution's
    /// recorded-snapshot index, not the ambient fact set; every accepted source
    /// and target is checked by `TransportUsing` on this immutable Proof.
    pub(super) fn try_snapshot_transport_closure(
        &self,
        surface_goal: &ClickProposition,
    ) -> Result<Option<Self>, ClickError> {
        if super::solver_bridges::machine_equality_bridge_active() {
            return Ok(None);
        }
        // Every candidate below lowers the same goal, so a failing question
        // about the goal's own loads repeats per candidate; remember those
        // failures for this closure (`with_closure_failure_memo`).
        crate::instrumentation::measure_operation(
            "surface",
            "simp closure",
            "simp closure: snapshot transport",
            || {
                crate::kernel::with_closure_failure_memo(|| {
                    self.try_snapshot_transport_closure_candidates(surface_goal)
                })
            },
        )
    }

    fn try_snapshot_transport_closure_candidates(
        &self,
        surface_goal: &ClickProposition,
    ) -> Result<Option<Self>, ClickError> {
        if let Some(proof) = self.try_cell_frame_transport_closure(surface_goal)? {
            return Ok(Some(proof));
        }
        // Outcome transport is a general closure. Extending it to fixed-state
        // and mid-execution proposition scopes is needed specifically for
        // opaque Click applications whose snapshot arguments cannot be
        // refreshed by ordinary field rewrites. Keep non-function goals on
        // their established, more local rewrite plans.
        if self.outcome_fixed_state_view().is_none() {
            let mut calls = BTreeSet::new();
            crate::surface::validation::collect_click_function_calls_in_proposition(
                surface_goal,
                &mut calls,
            );
            if calls.is_empty() {
                return Ok(None);
            }
        }
        let Some(view) = self.premise_fixed_state_view() else {
            return Ok(None);
        };
        if let Some(source) = old_reflexive_transport_source(surface_goal) {
            if self.execution_proposition_fixed_state_view().is_some()
                && let Some(proof) =
                    self.try_planned_execution_proposition_fact_transport(&source, surface_goal)?
                && proof.is_complete()
            {
                return Ok(Some(proof));
            }
            match self.try_fixed_state_fact_transport(&source, surface_goal, std::iter::empty()) {
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
        // early-return paths. An older point is still reachable by an
        // explicit `transport`.
        let selectors = std::iter::once(SnapshotSelector::ProgramPoint(first)).chain(
            view.fixed_state
                .recorded_snapshots
                .recent(MAX_TRANSPORT_SOURCE_POINTS)
                .into_iter()
                .map(|(selector, _)| selector.clone()),
        );
        let mut tried = BTreeSet::new();
        for selector in selectors {
            if (names_result && !crate::surface::snapshot_can_name_result(Some(&selector)))
                || !tried.insert(selector.clone())
            {
                continue;
            }
            let source = ClickProposition::At {
                selector,
                proposition: Box::new(surface_goal.clone()),
            };
            match self.try_fixed_state_fact_transport(
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
            if let Some(proof) = self.try_projected_snapshot_transport(&source, surface_goal)? {
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
    /// (`ProofFacts::quantified_conjunct_projection_source`) with the goal
    /// lowered at that point, so a point holding no such fact costs one
    /// lowering and one lookup. The proof is one explicit transport from
    /// the larger fact to the goal, which the checked quantified frame
    /// decides by conjunction elimination; expansion prints it.
    fn try_projected_snapshot_transport(
        &self,
        source: &ClickProposition,
        surface_goal: &ClickProposition,
    ) -> Result<Option<Self>, ClickError> {
        let Ok(lowered) =
            self.lower_surface_proposition_direct(source, "smart projected transport source")
        else {
            check_verification_deadline()?;
            return Ok(None);
        };
        let Some(full) = self.facts().quantified_conjunct_projection_source(&lowered) else {
            return Ok(None);
        };
        let full = full.clone();
        let Some(full_surface) = self
            .resolve_simp_premises(std::slice::from_ref(&full), &[])
            .and_then(|pairs| pairs.into_iter().next())
            .map(|(_, surface)| surface)
        else {
            return Ok(None);
        };
        match self.try_fixed_state_fact_transport(
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

    /// A goal that reads one cell at two snapshots, such as
    /// `owner->cell[0] == owner->phase` right after a store wrote the first
    /// side from the second, holds when nothing in between wrote that cell.
    /// That is a frame fact: carry the cell's reflexive equality from a
    /// recorded point to the goal by `transport`, whose checker takes the
    /// frame evidence (an exact `separate`, say) as its listed premises.
    fn try_cell_frame_transport_closure(
        &self,
        surface_goal: &ClickProposition,
    ) -> Result<Option<Self>, ClickError> {
        let Some(Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true)) =
            self.goal()
        else {
            return Ok(None);
        };
        let load = |term: &Bitvector32Term| match term {
            Bitvector32Term::Variable(variable) => {
                crate::kernel::registered_load_term_for_variable(variable)
            }
            Bitvector32Term::MemoryLoad(..) => Some(term.clone()),
            _ => None,
        };
        let (
            Some(Bitvector32Term::MemoryLoad(left_memory, left_pointer, left_kind)),
            Some(Bitvector32Term::MemoryLoad(right_memory, right_pointer, right_kind)),
        ) = (load(left), load(right))
        else {
            return Ok(None);
        };
        if left_pointer != right_pointer || left_kind != right_kind || left_memory == right_memory {
            return Ok(None);
        }
        let Some(view) = self.premise_fixed_state_view() else {
            return Ok(None);
        };
        // The cell as the current state reads it.
        let current = crate::kernel::intern_c_memory_ref(view.fixed_state.state.memory());
        let current_side = if right_memory == current {
            right
        } else if left_memory == current {
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
        let reflexive = ClickProposition::Comparison {
            left: cell.clone(),
            operator: ComparisonOperator::Equal,
            right: cell,
        };
        let selectors = view
            .fixed_state
            .recorded_snapshots
            .recent(MAX_TRANSPORT_SOURCE_POINTS)
            .into_iter()
            .map(|(selector, _)| selector.clone())
            .collect::<Vec<_>>();
        for selector in selectors {
            let source = ClickProposition::At {
                selector,
                proposition: Box::new(reflexive.clone()),
            };
            match self.try_fixed_state_fact_transport(&source, surface_goal, std::iter::empty()) {
                Ok(Some(proof)) if proof.is_complete() => return Ok(Some(proof)),
                Ok(_) => {}
                Err(_) => check_verification_deadline()?,
            }
        }
        Ok(None)
    }

    /// Close an implication whose algebraic guard is refuted by a checked
    /// rewrite and direct normalization. A miss does not run general simp on
    /// the guard or select the implication's connected fact component.
    fn try_constructor_guard_refutation(&self) -> Result<Option<Self>, ClickError> {
        let Some(Proposition::Implies(guard, _)) = self.goal() else {
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
        let Some(antecedent) = self.surface_goal().and_then(surface_implication_antecedent) else {
            return Ok(None);
        };
        let opposite = negate_click_proposition(&antecedent);
        let Some(scope) = attempt::candidate_outcome(self.begin_have(opposite.clone()))? else {
            return Ok(None);
        };
        let Some(proved) = scope.try_direct_model_equality_rewrite_closure() else {
            check_verification_deadline()?;
            return Ok(None);
        };
        let Some(joined) = attempt::candidate_outcome(proved.join())? else {
            return Ok(None);
        };
        let Some(introduced) = attempt::candidate_outcome(joined.apply_step(ProofStep::Intro))?
        else {
            return Ok(None);
        };
        attempt::candidate_outcome(introduced.apply_step(ProofStep::Contradiction(opposite)))
    }

    // Walk consecutive implication guards without retaining a dispatcher
    // frame for each. Each guard keeps its checked introduction, contradiction
    // probes, and named-premise extraction before the body is simplified.
    #[inline(never)]
    fn try_implication_simp_closure(
        &self,
        surface_antecedent: &ClickProposition,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Self>, ClickError> {
        let mut base = self.clone();
        let mut antecedent = surface_antecedent.clone();
        let mut available_surfaces = introduced_surfaces.to_vec();
        loop {
            let Some(mut introduced) =
                attempt::candidate_outcome(base.apply_step(ProofStep::Intro))?
            else {
                return Ok(None);
            };
            // The introduced antecedent itself is the uniquely selected
            // contradiction candidate. This is a constant-size probe:
            // `Contradiction` checks that exact fact and its indexed
            // opposite, without scanning ambient path facts.
            if let Some(closed) = introduced.try_introduced_antecedent_contradiction(&antecedent)? {
                return Ok(Some(closed));
            }
            // A selected execution path can make the antecedent false through a
            // short derivation rather than an already-indexed exact opposite.
            // Prove and retain that opposite first; after `intro`, ordinary
            // contradiction checks the two explicit facts.
            let negated_antecedent = negate_click_proposition(&antecedent);
            if let Some(scope) =
                attempt::candidate_outcome(base.begin_have(negated_antecedent.clone()))?
                && let Some(proved) = scope.try_simp_closure()?
                && let Some(with_opposite) = attempt::candidate_outcome(proved.join())?
                && let Some(with_antecedent) =
                    attempt::candidate_outcome(with_opposite.apply_step(ProofStep::Intro))?
                && let Some(closed) = attempt::candidate_outcome(
                    with_antecedent.apply_step(ProofStep::Contradiction(negated_antecedent)),
                )?
            {
                return Ok(Some(closed));
            }
            let mut conjuncts = Vec::new();
            if matches!(&antecedent, ClickProposition::And(_, _)) {
                collect_surface_conjunct_leaves(&antecedent, &mut conjuncts);
            }
            for conjunct in &conjuncts {
                let Some(extracted) = attempt::candidate_outcome(
                    introduced.apply_step(ProofStep::Extract(conjunct.clone())),
                )?
                else {
                    return Ok(None);
                };
                introduced = extracted;
                if introduced.is_complete() {
                    return Ok(Some(introduced));
                }
            }
            available_surfaces.push(antecedent.clone());
            available_surfaces.extend(conjuncts.iter().cloned());
            // Introducing this guard can make a previously introduced
            // conditional premise usable. Select its written consequent
            // and let the ordinary checked `extract` rule discharge the
            // guard; do not branch over possible guard values.
            for premise in available_surfaces.clone() {
                let mut current = &premise;
                while let ClickProposition::Implies(_, consequent) = current {
                    let Some(extracted) = attempt::candidate_outcome(
                        introduced.apply_step(ProofStep::Extract(consequent.as_ref().clone())),
                    )?
                    else {
                        break;
                    };
                    introduced = extracted;
                    available_surfaces.push(consequent.as_ref().clone());
                    if introduced.is_complete() {
                        return Ok(Some(introduced));
                    }
                    current = consequent;
                }
            }
            if !conjuncts.is_empty()
                && let Some(surface_goal) = introduced.surface_goal()
                && let Some(source) = old_reflexive_transport_source(surface_goal)
            {
                match introduced.try_fixed_state_fact_transport(
                    &source,
                    surface_goal,
                    conjuncts.iter().cloned(),
                ) {
                    Ok(Some(transported)) if transported.is_complete() => {
                        return Ok(Some(transported));
                    }
                    Ok(_) => {}
                    Err(_) => check_verification_deadline()?,
                }
            }
            if let Some(split) = introduced.try_upper_bound_split_closure(&available_surfaces)? {
                return Ok(Some(split));
            }
            if let Some(closed) = introduced.try_direct_logical_closure()? {
                return Ok(Some(closed));
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
            return introduced.try_simp_closure_with_surfaces(&available_surfaces);
        }
    }

    /// Refines the Proof-owned Surface goal through audited scopes and steps.
    /// The caller cannot supply a second description of the judgment: this
    /// syntax is the view paired with the kernel goal in `PropositionObligation`.
    /// Keep branch-local proof/syntax temporaries out of this recursive frame.
    #[inline(never)]
    fn try_structural_simp_closure_with_surfaces(
        &self,
        surface_goal: &ClickProposition,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Self>, ClickError> {
        let Some(goal) = self.goal() else {
            return Ok(None);
        };
        if matches!(goal, Proposition::And(_, _)) {
            // The split owns the checked Surface-to-kernel correspondence.
            // In particular, a lowered existential body may be a conjunction
            // whose written Surface spelling is only the body; do not gate
            // this on a shape heuristic.
            // A smart closure candidate may encounter a kernel conjunction
            // whose written presentation is not recoverable.  Decline this
            // candidate so the caller can report its ordinary bounded proof
            // failure; the explicit `both` operation still rejects the same
            // mismatch transactionally through the checked split.
            match self.checked_both_surface_children() {
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
            return self.try_structural_and_simp_closure(introduced_surfaces);
        }
        if matches!(goal, Proposition::Or(_, _))
            && let Some((surface_left, surface_right)) =
                surface_logical_children(surface_goal, false)
        {
            return self.try_structural_or_simp_closure(
                &surface_left,
                &surface_right,
                introduced_surfaces,
            );
        }
        if matches!(goal, Proposition::Implies(_, _))
            && let Some(surface_antecedent) = surface_implication_antecedent(surface_goal)
        {
            return self.try_implication_simp_closure(&surface_antecedent, introduced_surfaces);
        }
        match (surface_goal, goal) {
            (ClickProposition::Exists { name, .. }, goal @ Proposition::Exists { .. })
                if quantified_external_range_goal(goal) =>
            {
                self.try_structural_exists_simp_closure(name, introduced_surfaces)
            }
            (ClickProposition::ForAll { .. }, Proposition::ForAll { .. }) => {
                self.try_structural_forall_simp_closure(surface_goal, introduced_surfaces)
            }
            // A predicate-call goal unfolds to its body, which the
            // structural arms and logical closers then work over. Repeat
            // unfolds are refused so recursive predicate bodies cannot loop
            // the search.
            (ClickProposition::PredicateCall { name, .. }, _)
                if !self.focused_branch_unfolds().contains(name) =>
            {
                self.try_structural_predicate_simp_closure(name, introduced_surfaces)
            }
            _ => Ok(None),
        }
    }

    // These helpers preserve the dispatcher's search order and checked steps;
    // their stack storage is needed only for the selected connective.
    #[inline(never)]
    fn try_structural_exists_simp_closure(
        &self,
        name: &str,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Self>, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Ok(None);
        };
        let mut candidates = Vec::new();
        for argument in context.arguments {
            if matches!(argument, CExpression::Value(CValue::Int32(_))) {
                candidates.push(ContractExpression::CFragment(argument.clone()));
            }
        }
        // The range-loadability source slice has no witness in its call
        // arguments, so zero is the deterministic fallback.  It is tried
        // after call arguments to keep this operation useful for other
        // source-backed existential requirements without searching ambient
        // facts.
        candidates.push(ContractExpression::CFragment(CExpression::Value(
            CValue::Int32(Bitvector32Term::Constant(0)),
        )));
        for value in candidates {
            check_verification_deadline()?;
            let witness = ProofWitness::single(name.to_string(), value);
            let Some(introduced) =
                attempt::candidate_outcome(self.apply_step(ProofStep::Witness(witness)))?
            else {
                continue;
            };
            if let Some(closed) = introduced.try_simp_closure_with_surfaces(introduced_surfaces)? {
                return Ok(Some(closed));
            }
        }
        Ok(None)
    }

    #[inline(never)]
    fn try_structural_forall_simp_closure(
        &self,
        surface_goal: &ClickProposition,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Self>, ClickError> {
        if let Some(enumerated) = self.try_finite_forall_enumeration(surface_goal)? {
            return Ok(Some(enumerated));
        }
        match attempt::candidate_outcome(self.apply_step(ProofStep::Intro))? {
            Some(introduced) => introduced.try_simp_closure_with_surfaces(introduced_surfaces),
            None => Ok(None),
        }
    }

    #[inline(never)]
    fn try_structural_and_simp_closure(
        &self,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Self>, ClickError> {
        let (split_proof, split, ids) = self.split_focused_both()?;
        let marker = split_proof.checkpoint();
        let Some(left) = split_proof
            .focus_branch(ids[0])?
            .try_simp_closure_with_surfaces(introduced_surfaces)?
        else {
            return Ok(None);
        };
        let Some(right) = left
            .focus_branch(ids[1])?
            .try_simp_closure_with_surfaces(introduced_surfaces)?
        else {
            return Ok(None);
        };
        attempt::candidate_outcome(right.join_focused_both(&marker, split, ids))
    }

    #[inline(never)]
    fn try_structural_predicate_simp_closure(
        &self,
        name: &str,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Self>, ClickError> {
        match attempt::candidate_outcome(
            self.apply_step(ProofStep::UnfoldPredicate(name.to_string())),
        )? {
            Some(unfolded) => unfolded.try_simp_closure_with_surfaces(introduced_surfaces),
            None => Ok(None),
        }
    }

    #[inline(never)]
    fn try_structural_or_simp_closure(
        &self,
        surface_left: &ClickProposition,
        surface_right: &ClickProposition,
        introduced_surfaces: &[ClickProposition],
    ) -> Result<Option<Self>, ClickError> {
        for surface in [surface_left, surface_right] {
            let selected = (|| {
                let Some(scope) = attempt::candidate_outcome(self.begin_have(surface.clone()))?
                else {
                    return Ok(None);
                };
                let Some(scope) = scope.try_simp_closure_with_surfaces(introduced_surfaces)? else {
                    return Ok(None);
                };
                let Some(joined) = attempt::candidate_outcome(scope.join())? else {
                    return Ok(None);
                };
                attempt::candidate_outcome(joined.apply_step(ProofStep::Assumption))
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
    pub(super) fn try_finite_forall_enumeration(
        &self,
        surface_goal: &ClickProposition,
    ) -> Result<Option<Self>, ClickError> {
        let Some(goal) = self.goal() else {
            return Ok(None);
        };
        let Some(instances) = crate::kernel::finite_forall_goal_instances(goal, true) else {
            return Ok(None);
        };
        // A goal stated as a predicate call binds through the predicate's
        // body; unfold it at the surface to name the binders.
        let predicate_environment = match self.context.as_ref() {
            ProofContext::Pure(context) => context.spec_definitions.predicates,
            ProofContext::FixedState(context) => context.spec_definitions.predicates,
            ProofContext::Execution(context) => context.spec_definitions.predicates,
        };
        let all_predicates = predicate_environment
            .definitions
            .keys()
            .cloned()
            .collect::<Vec<_>>();
        let unfolded = unfold_click_predicates_in_proposition_with_active(
            predicate_environment,
            &all_predicates,
            surface_goal,
            &mut BTreeSet::new(),
        )
        .unwrap_or_else(|_| surface_goal.clone());
        let mut binder_names = Vec::new();
        let mut surface_body = &unfolded;
        while let ClickProposition::ForAll { name, body, .. } = surface_body {
            binder_names.push(name.clone());
            surface_body = body;
        }
        if binder_names.is_empty() {
            return Ok(None);
        }

        let mut proof = self.clone();
        for (values, instance) in instances {
            check_verification_deadline()?;
            if values.len() != binder_names.len() {
                return Ok(None);
            }
            if matches!(normalize_proposition(&instance), SimpProposition::True) {
                continue;
            }
            let Some(value_expressions) = values
                .iter()
                .map(|value| {
                    u32::try_from(*value)
                        .ok()
                        .map(|bits| ContractExpression::CFragment(CExpression::Value(int32(bits))))
                })
                .collect::<Option<Vec<_>>>()
            else {
                return Ok(None);
            };
            let substitutions = binder_names
                .iter()
                .cloned()
                .zip(value_expressions)
                .collect::<BTreeMap<_, _>>();
            let Ok(surface_instance) = substitute_click_proposition(surface_body, &substitutions)
            else {
                return Ok(None);
            };
            // An instance whose guard is constant true is stated as its
            // conclusion: that is the fact a later instance's proof cites, and
            // `enumerate()` reads the table through the same normalization.
            let surface_instance = match (&instance, &surface_instance) {
                (Proposition::Implies(guard, _), ClickProposition::Implies(_, conclusion))
                    if matches!(normalize_proposition(guard), SimpProposition::True) =>
                {
                    conclusion.as_ref().clone()
                }
                _ => surface_instance,
            };
            let Some(scope) = attempt::candidate_outcome(proof.begin_have(surface_instance))?
            else {
                return Ok(None);
            };
            let Some(scope) = scope.try_simp_closure()? else {
                return Ok(None);
            };
            let Some(joined) = attempt::candidate_outcome(scope.join())? else {
                return Ok(None);
            };
            proof = joined;
        }
        attempt::candidate_outcome(proof.apply_step(ProofStep::Enumerate))
    }

    /// Closes from the just-introduced antecedent and one exact indexed
    /// opposite. The antecedent fixes the kernel pair; Surface lookup visits
    /// only forms recorded for those two facts, never the ambient set.
    pub(super) fn try_introduced_antecedent_contradiction(
        &self,
        surface_antecedent: &ClickProposition,
    ) -> Result<Option<Self>, ClickError> {
        let Some(introduced) = self.checked_facts().first() else {
            return Ok(None);
        };
        let opposite = match introduced {
            Proposition::ConditionIs(condition, value) => {
                Proposition::ConditionIs(condition.clone(), !value)
            }
            Proposition::Not(body) => body.as_ref().clone(),
            proposition => Proposition::Not(Box::new(proposition.clone())),
        };
        if !self.facts().contains(&opposite) {
            return Ok(None);
        }
        if let Some(closed) = attempt::candidate_outcome(
            self.apply_step(ProofStep::Contradiction(surface_antecedent.clone())),
        )? {
            return Ok(Some(closed));
        }
        let surfaces = match self.context.as_ref() {
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
            ProofContext::Execution(_) => self
                .outcome_fixed_state_view()
                .into_iter()
                .flat_map(|view| view.surface_propositions.surfaces(&opposite))
                .cloned()
                .collect::<Vec<_>>(),
        };
        for surface in surfaces {
            if let Some(closed) =
                attempt::candidate_outcome(self.apply_step(ProofStep::Contradiction(surface)))?
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
    pub(super) fn selected_simp_derivation(
        &self,
        exclude_exact_goal: bool,
    ) -> Option<(
        Proposition,
        PropositionDerivation,
        Vec<(Proposition, ClickProposition)>,
        bool,
    )> {
        self.selected_simp_derivation_with_surfaces(exclude_exact_goal, &[])
    }

    fn selected_simp_derivation_with_surfaces(
        &self,
        exclude_exact_goal: bool,
        introduced_surfaces: &[ClickProposition],
    ) -> Option<(
        Proposition,
        PropositionDerivation,
        Vec<(Proposition, ClickProposition)>,
        bool,
    )> {
        let (goal, derivation, theorem_application_closes_goal) =
            self.selected_simp_derivation_plan(exclude_exact_goal)?;
        let premise_pairs =
            self.resolve_simp_premises(&derivation.context_premises(), introduced_surfaces)?;
        Some((
            goal,
            derivation,
            premise_pairs,
            theorem_application_closes_goal,
        ))
    }

    /// The derivation simp selected for the focused goal, before any of its
    /// premises is spelled, and whether a theorem application closes the
    /// goal in this context.
    fn selected_simp_derivation_plan(
        &self,
        exclude_exact_goal: bool,
    ) -> Option<(Proposition, PropositionDerivation, bool)> {
        let theorem_application_closes_goal = match self.context.as_ref() {
            ProofContext::Pure(_) | ProofContext::FixedState(_) => true,
            // Entry-anchored premises can add a check-equivalent outcome
            // fact without discharging the exact goal form. Keep the
            // ordinary trailing assumption so the checked successor decides
            // whether it is needed.
            ProofContext::Execution(_) => {
                if self.focused_outcome_data().is_none() {
                    self.execution()?;
                }
                false
            }
        };
        let goal = self.goal()?.clone();
        let derivation = if exclude_exact_goal {
            self.facts()
                .assumptions()
                .derive_simp_proposition_without_exact_goal(&goal)
        } else {
            match plan_simp_certificate(&goal, self.facts().assumptions()) {
                Some(SimpEvidence::Derivation(derivation)) => Some(derivation),
                _ if matches!(self.context.as_ref(), ProofContext::Pure(_)) => {
                    self.facts().assumptions().derive_atomic_proposition(&goal)
                }
                _ => None,
            }
        };
        let Some(derivation) = derivation else {
            if matches!(goal, Proposition::CMemoryLoadable { .. }) {
                attempt::record_search_note(
                    "simp view derivation selection",
                    "no retained-premise derivation was produced for the requested view",
                );
            }
            return None;
        };
        Some((goal, derivation, theorem_application_closes_goal))
    }

    /// Spells each of `premises` in this context's recorded source forms,
    /// leaving out one that has none.
    pub(in crate::surface::proof) fn resolve_simp_premises(
        &self,
        premises: &[Proposition],
        introduced_surfaces: &[ClickProposition],
    ) -> Option<Vec<(Proposition, ClickProposition)>> {
        // Broad atomic derivations may retain a whole connected fact
        // component even when no checkable source spelling exists. Do not
        // render an unbounded component speculatively. The recorded-path
        // candidate is tried first, and explicit `using` lists have their
        // own presentation/checking path.
        if premises.len() > MAX_SIMP_SOURCE_PREMISES {
            if matches!(self.goal(), Some(Proposition::CMemoryLoadable { .. })) {
                attempt::record_search_note(
                    "simp view premise spelling",
                    format!(
                        "budget exhausted: the selected view derivation contains {} premises; source spelling permits at most {MAX_SIMP_SOURCE_PREMISES}",
                        premises.len()
                    ),
                );
            }
            return None;
        }
        crate::instrumentation::measure_operation(
            "surface",
            "simp closure",
            "simp closure: premise spelling",
            || self.resolve_simp_premises_unmeasured(premises, introduced_surfaces),
        )
    }

    fn resolve_simp_premises_unmeasured(
        &self,
        premises: &[Proposition],
        introduced_surfaces: &[ClickProposition],
    ) -> Option<Vec<(Proposition, ClickProposition)>> {
        let frontier_anchor: Option<ProgramPointRef>;
        let (surface_facts, _, premise_anchor) = match self.context.as_ref() {
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
                if let Some(data) = self.focused_outcome_data() {
                    (
                        &data.surface_propositions,
                        // Entry-anchored premises can add a check-equivalent
                        // outcome fact without discharging the exact goal
                        // form. Keep the ordinary trailing assumption so
                        // the checked successor decides whether it is needed.
                        false,
                        data.premise_anchor.as_ref(),
                    )
                } else {
                    // A judgment stated mid-execution (a `have` before
                    // function exit) supplies the frontier's recorded
                    // lowerings and the entry of the last executed
                    // statement, exactly as an outcome data does.
                    let execution = self.execution()?;
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
            if let Some(surface) = self.available_surface_fact(surface_facts, anchor, premise) {
                return Some((premise.clone(), surface));
            }
            if let Some(surface) =
                self.available_surface_fact(self.local_surface_facts(), anchor, premise)
            {
                return Some((premise.clone(), surface));
            }
            if crate::instrumentation::deadline_exceeded() {
                return None;
            }
            if let Some(surface) = introduced_surfaces.iter().find(|surface| {
                self.lower_surface_proposition(surface, "introduced simp premise")
                    .is_ok_and(|lowered| {
                        lowered == *premise || condition_polarity_equivalent(&lowered, premise)
                    })
            }) {
                return Some((premise.clone(), surface.clone()));
            }
            condition_polarity_forms(premise)
                .into_iter()
                .find_map(|form| {
                    let surface = self.available_surface_fact(surface_facts, anchor, &form);
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
                            self.local_surface_facts()
                                .kernels_containing_conjunct(premise),
                        )
                        .find_map(|whole| {
                            if crate::instrumentation::deadline_exceeded() {
                                return None;
                            }
                            self.available_surface_fact(surface_facts, anchor, whole)
                                .or_else(|| {
                                    self.available_surface_fact(
                                        self.local_surface_facts(),
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
            .filter_map(|(_, surface)| match surface_snapshot_selector(surface) {
                Some(SnapshotSelector::ProgramPoint(point)) => Some(point),
                Some(SnapshotSelector::Mark(_)) | None => None,
            })
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
        if !crate::instrumentation::deadline_exceeded() && premise_pairs.len() < premises.len() {
            // Name what has no spelling: a derivation found but not written
            // back is refused for that reason, not for the memory history a
            // supplemental explanation may show.
            let unspelled = premises
                .iter()
                .filter(|premise| !premise_pairs.iter().any(|(spelled, _)| spelled == *premise))
                .collect::<Vec<_>>();
            let strategy = if matches!(self.goal(), Some(Proposition::CMemoryLoadable { .. })) {
                "simp view premise spelling"
            } else {
                "simp premise spelling"
            };
            attempt::record_search_premise_note(
                strategy,
                format!(
                    "{} of {} selected derivation premises have checked source spellings; {} were omitted: ",
                    premise_pairs.len(),
                    premises.len(),
                    premises.len() - premise_pairs.len(),
                ),
                &unspelled,
            );
        }
        (!crate::instrumentation::deadline_exceeded()).then_some(premise_pairs)
    }

    /// Resolves one exact retained fact to a surface form that will lower
    /// back to that same kernel proposition when the selected proof step is
    /// checked. Historical locals are anchored before ordinary forms are
    /// considered, so a same-written newer snapshot cannot be substituted.
    /// The fixed-state view against which a premise lookup is spelled: the
    /// focused branch's outcome data, the frontier's current state for a
    /// judgment stated mid-execution, or a fixed-state proof's own state.
    /// The last is a loop's `initialize` phase, a proof at the loop entry: it
    /// spells the contract's entry-state facts against function entry exactly
    /// as the same judgment stated in the function body does. A fixed-state
    /// proof whose state is its entry state (the same object) needs no such
    /// anchoring, and keeps its plain spellings.
    pub(super) fn premise_fixed_state_view(&self) -> Option<FixedStateOperationView<'_>> {
        self.outcome_fixed_state_view()
            .or_else(|| self.execution_proposition_fixed_state_view())
            .or_else(|| match self.context.as_ref() {
                ProofContext::FixedState(context)
                    if !std::ptr::eq(context.fixed_state.pre_state, context.fixed_state.state) =>
                {
                    Some(FixedStateOperationView::from_fixed_state(context))
                }
                _ => None,
            })
    }

    pub(super) fn available_surface_fact(
        &self,
        surface_facts: &SurfacePropositionMap,
        premise_anchor: Option<&ProgramPointRef>,
        kernel: &Proposition,
    ) -> Option<ClickProposition> {
        let surface = self.available_surface_fact_raw(surface_facts, premise_anchor, kernel)?;
        self.named_returned_pointer_surface_fact(&surface, kernel)
            .or(Some(surface))
    }

    fn named_returned_pointer_surface_fact(
        &self,
        surface: &ClickProposition,
        kernel: &Proposition,
    ) -> Option<ClickProposition> {
        let view = self.premise_fixed_state_view()?;
        let Some(result @ CValue::Pointer(_)) = view.fixed_state.result else {
            return None;
        };
        // Resource witnesses may have no written name but coincide with the
        // checked return value. Name that exact value, then re-lower the
        // candidate so presentation cannot change the cited premise.
        let equality = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(result.clone())),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::Binding("result".to_string()),
        };
        let named =
            crate::surface::rewrite_click_proposition_by_surface_equality(surface, &equality)?;
        self.lower_surface_proposition_direct(&named, "returned pointer premise form")
            .is_ok_and(|lowered| {
                lowered == *kernel || condition_polarity_equivalent(&lowered, kernel)
            })
            .then_some(named)
    }

    fn available_surface_fact_raw(
        &self,
        surface_facts: &SurfacePropositionMap,
        premise_anchor: Option<&ProgramPointRef>,
        kernel: &Proposition,
    ) -> Option<ClickProposition> {
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
                if crate::kernel::is_store_fact(condition, *value)))
            && surface_facts.surfaces(kernel).next().is_none()
            && self.local_surface_facts().surfaces(kernel).next().is_none()
            && surface_facts
                .kernels_containing_conjunct(kernel)
                .next()
                .is_none()
            && self
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
        // the refolded field. Like a snapshot selector recorded again in a
        // loop, that spelling may stop denoting its old checked fact.
        // Re-lower those movable forms below; other live recorded pairs keep
        // their indexed lookup without repeating proposition lowering.
        let constructor_equation = matches!(
            kernel,
            Proposition::Equal(
                Term::Algebraic(_),
                Term::Algebraic(crate::kernel::AlgebraicTerm {
                    node: crate::kernel::AlgebraicTermNode::Constructor { .. },
                    ..
                })
            )
        );
        let matches_kernel = |candidate: &ClickProposition, allow_recorded_pair: bool| {
            if crate::instrumentation::deadline_exceeded() {
                return None;
            }
            // `result` exists only once the function returns: a snapshot
            // before the return that reads it lowers, but does not parse.
            if reads_result_before_return(candidate) {
                return None;
            }
            // Synthesized kernel literals can lower back to this fact yet
            // print as diagnostic-only pointer placeholders. Such a form
            // cannot be cited in an expandable proof; try another spelling.
            let named = self.named_returned_pointer_surface_fact(candidate, kernel);
            if !crate::surface::parser::has_valid_source_tokens(
                &crate::surface::printing::source_click_proposition(
                    named.as_ref().unwrap_or(candidate),
                ),
            ) {
                return None;
            }
            let lower = |candidate: &ClickProposition| {
                self.lower_surface_proposition_direct(candidate, "typed simp premise form")
                    .ok()
            };
            if allow_recorded_pair
                && self.focused_outcome_data().is_some()
                && surface_facts
                    .available_kernel_matching(candidate, |fact| self.facts().contains(fact))
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
                let names_a_dead_local = self.premise_fixed_state_view().is_some_and(|view| {
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
                                .and_then(|anchor| view.fixed_state.recorded_snapshots.get(anchor))
                                .is_some_and(|snapshot| snapshot.locals().contains_name(name))
                            && self.local_binding(name).is_none()
                            && self.local_integer_values().get(name).is_none()
                            && self.local_algebraic_values().get(name).is_none()
                    })
                });
                // A statement selector can be recorded again on a later
                // loop iteration. Its old pair remains a checked fact, but
                // an explicit snapshot spelling must still denote it now.
                let snapshot_spelling = proposition_contains_at_expression(candidate);
                if !constructor_equation && !names_a_dead_local && !snapshot_spelling {
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
                || quantified_equivalent_available_fact(kernel, std::slice::from_ref(&lowered))
                    .is_some())
            .then_some(())
        };
        if let Some(surface) = surface_facts.surfaces(kernel).find(|surface| {
            (proposition_contains_at_expression(surface)
                || proposition_contains_old_expression(surface))
                && matches_kernel(surface, true).is_some()
        }) {
            return Some(surface.clone());
        }
        // A selected fact can instead name a fresh loop-head value in the
        // current state. Recover it there before searching older snapshots
        // which cannot name that value at all.
        let pointer_goal = matches!(
            self.goal(),
            Some(Proposition::ConditionIs(ConditionTerm::PointerEqual(..), _))
        );
        if pointer_goal
            && let Some(surface) = surface_facts
                .surfaces(kernel)
                .find(|surface| matches_kernel(surface, true).is_some())
        {
            return Some(surface.clone());
        }
        if pointer_goal
            && let Some(view) = self.premise_fixed_state_view()
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
        let requirement_surface = if let Some(data) = self.focused_outcome_data() {
            data.requirement_surfaces.get(kernel).cloned()
        } else {
            // A judgment stated mid-execution selects its requirement
            // spellings from the frontier's own contract, as an outcome
            // outcome does from its recorded ones.
            self.execution_proposition_fixed_state_view()
                .and_then(|view| {
                    view.requirement_facts
                        .as_slice()
                        .iter()
                        .zip(view.original_requirements)
                        .find(|(fact, _)| *fact == kernel)
                        .and_then(|(_, requirement)| requirement.proposition().cloned())
                })
        };
        if let Some(surface) = requirement_surface {
            let anchored = ClickProposition::At {
                selector: SnapshotSelector::ProgramPoint(function_entry.clone()),
                proposition: Box::new(surface.clone()),
            };
            if matches_kernel(&anchored, true).is_some() {
                return Some(anchored);
            }
            if let Ok(anchored) = surface_at_snapshot(&surface, &function_entry)
                && matches_kernel(&anchored, true).is_some()
            {
                return Some(anchored);
            }
        }
        if self.premise_fixed_state_view().is_some() {
            if let Some(anchored) = surface_facts.surfaces(kernel).find_map(|surface| {
                let anchored = surface_at_snapshot(surface, &function_entry).ok()?;
                matches_kernel(&anchored, true).map(|()| anchored)
            }) {
                return Some(anchored);
            }
            if let Some(view) = self.premise_fixed_state_view()
                && let Some(surface) = synthesize_surface_proposition(
                    kernel,
                    view.parameter_binding,
                    view.fixed_state.pre_state,
                )
                && let Ok(anchored) = surface_at_snapshot(&surface, &function_entry)
                && matches_kernel(&anchored, true).is_some()
            {
                return Some(anchored);
            }
        }
        if let Some(anchor) = premise_anchor
            && let Some(anchored) = surface_facts.surfaces(kernel).find_map(|surface| {
                let anchored = surface_at_snapshot(surface, anchor).ok()?;
                matches_kernel(&anchored, true).map(|()| anchored)
            })
        {
            return Some(anchored);
        }
        // A selected scalar fact may combine a current value with an entry
        // read, which no single earlier snapshot can spell. Try these named
        // states before walking history. New scalar candidates lower directly: a
        // recorded unanchored form may name an earlier value of the same local.
        if !pointer_goal
            && let Some(view) = self.premise_fixed_state_view()
            && let Some(surface) =
                super::surface_synthesis::synthesize_surface_proposition_at_entry_and_post(
                    kernel,
                    view.parameter_binding,
                    view.fixed_state.pre_state,
                    view.fixed_state.state,
                )
            && matches_kernel(&surface, false).is_some()
        {
            return Some(surface);
        }
        // Before accepting an unanchored recorded form, which may have been
        // stated at an earlier value of a variable that later changed,
        // spell the fact against the recorded snapshot where it was read.
        if let Some(anchor) = premise_anchor
            && let Some((parameters, arguments, recorded_snapshots)) = match self.context.as_ref() {
                ProofContext::Pure(_) => None,
                ProofContext::FixedState(context) => Some((
                    context.parameter_binding.parameters,
                    context.parameter_binding.arguments,
                    context.fixed_state.recorded_snapshots,
                )),
                ProofContext::Execution(_) => self.premise_fixed_state_view().map(|view| {
                    (
                        view.parameter_binding.parameters,
                        view.parameter_binding.arguments,
                        view.fixed_state.recorded_snapshots,
                    )
                }),
            }
            && let Some(anchored) = crate::instrumentation::measure_operation(
                "surface",
                "simp premise",
                "simp premise surface at recorded snapshots",
                || {
                    synthesize_surface_at_recorded_snapshots(
                        kernel,
                        ParameterBinding::new(parameters, arguments),
                        recorded_snapshots,
                        anchor,
                    )
                    .find(|surface| matches_kernel(surface, true).is_some())
                },
            )
        {
            return Some(anchored);
        }
        // A fact can mix states: a call's `ensures` that names its own
        // `old(..)` value holds a value only that call's entry state reads,
        // beside values the current state names. Spell it at the current
        // state with one recorded statement entry as the further snapshot.
        if let Some(anchor) = premise_anchor
            && let Some(view) = self.premise_fixed_state_view()
            && let Some(mixed) = crate::instrumentation::measure_operation(
                "surface",
                "simp premise",
                "simp premise surface across recorded snapshots",
                || {
                    synthesize_surface_with_recorded_snapshot(
                        kernel,
                        view.parameter_binding,
                        view.fixed_state.pre_state,
                        view.fixed_state.state,
                        view.fixed_state.recorded_snapshots,
                        anchor,
                    )
                    .find(|surface| matches_kernel(surface, true).is_some())
                },
            )
        {
            return Some(mixed);
        }
        if crate::instrumentation::deadline_exceeded() {
            return None;
        }
        // A checked branch interface can export a kernel fact whose arm-local
        // Surface recording does not survive as a common map entry. The
        // statement-entry anchor still names the exact retained state. Rebuild
        // only this selected fact at that indexed state, anchor it, and require
        // the ordinary direct lowering to recover the same kernel premise.
        if let Some(anchor) = premise_anchor {
            let synthesis_context = match self.context.as_ref() {
                ProofContext::Pure(_) => None,
                ProofContext::FixedState(context) => Some((
                    context.parameter_binding.parameters,
                    context.parameter_binding.arguments,
                    context.fixed_state.recorded_snapshots,
                )),
                ProofContext::Execution(_) => self.premise_fixed_state_view().map(|view| {
                    (
                        view.parameter_binding.parameters,
                        view.parameter_binding.arguments,
                        view.fixed_state.recorded_snapshots,
                    )
                }),
            };
            if let Some((parameters, arguments, recorded_snapshots)) = synthesis_context
                && let Some(state) = recorded_snapshots.get(anchor)
                && let Some(surface) = synthesize_surface_proposition(
                    kernel,
                    ParameterBinding::new(parameters, arguments),
                    state,
                )
                && let Ok(anchored) = surface_at_snapshot(&surface, anchor)
                && matches_kernel(&anchored, true).is_some()
            {
                return Some(anchored);
            }
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
            && self.focused_outcome_data().is_some()
            && let Some(anchored) = surface_facts.surfaces(kernel).find_map(|surface| {
                surface_facts
                    .available_kernel_matching(surface, |fact| self.facts().contains(fact))
                    .is_some_and(|recorded| {
                        recorded == kernel || condition_polarity_equivalent(recorded, kernel)
                    })
                    .then(|| entry_anchored_constructor_equality(self, surface, kernel))
                    .flatten()
            })
        {
            return Some(anchored);
        }
        // Quantified execution facts may be retained in the canonical memory
        // form used by the kernel while their recorded Surface form lowers to
        // a term carrying a check-equivalent memory snapshot. Probe only the
        // persistent alpha/canonical-form bucket for this selected premise;
        // `InstantiateUsing` validates the same equivalence on check.
        if matches!(kernel, Proposition::ForAll { .. }) {
            for candidate in self.facts().matching_quantified_facts(kernel) {
                for surface in surface_facts.surfaces(&candidate) {
                    let lowered = self
                        .lower_surface_proposition_direct(
                            surface,
                            "typed quantified simp premise form",
                        )
                        .ok()?;
                    if quantified_equivalent_available_fact(kernel, std::slice::from_ref(&lowered))
                        .is_some()
                    {
                        return Some(surface.clone());
                    }
                }
            }
            let predicate_environment = match self.context.as_ref() {
                ProofContext::Pure(context) => context.spec_definitions.predicates,
                ProofContext::FixedState(context) => context.spec_definitions.predicates,
                ProofContext::Execution(context) => context.spec_definitions.predicates,
            };
            let click_function_environment = match self.context.as_ref() {
                ProofContext::Pure(context) => context.spec_definitions.functions,
                ProofContext::FixedState(context) => context.spec_definitions.functions,
                ProofContext::Execution(context) => context.spec_definitions.functions,
            };
            for name in self.focused_branch_unfolds().iter() {
                for opaque in surface_facts.kernels_written_by_predicate(name) {
                    for opaque_surface in surface_facts.surfaces(opaque) {
                        let ClickProposition::PredicateCall {
                            name: surface_name,
                            arguments,
                        } = opaque_surface
                        else {
                            continue;
                        };
                        let Some(definition) = predicate_environment.get(surface_name) else {
                            continue;
                        };
                        let Ok(body_surface) =
                            instantiate_click_predicate_definition(definition, arguments)
                        else {
                            continue;
                        };
                        let unfolds_to_selected = unfold_predicates_in_proposition(
                            SpecDefinitions::new(predicate_environment, click_function_environment),
                            std::slice::from_ref(name),
                            opaque,
                            self.facts().assumptions(),
                        )
                        .is_ok_and(|unfolded| {
                            unfolded == *kernel
                                || quantified_equivalent_available_fact(
                                    kernel,
                                    std::slice::from_ref(&unfolded),
                                )
                                .is_some()
                        });
                        if unfolds_to_selected {
                            if matches_kernel(&body_surface, true).is_some() {
                                return Some(body_surface);
                            }
                            if let Some(view) = self.premise_fixed_state_view()
                                && let Some(anchored) = view
                                    .fixed_state
                                    .recorded_snapshots
                                    .keys()
                                    .rev()
                                    .filter_map(|selector| {
                                        surface_at_snapshot(&body_surface, selector).ok()
                                    })
                                    .find(|surface| matches_kernel(surface, true).is_some())
                            {
                                return Some(anchored);
                            }
                        }
                    }
                }
            }
        }
        // Pure unfolding and induction can add a selected fact without a
        // written requirement entry. Synthesize its presentation from retained
        // binder names, then independently lower it back to this exact fact.
        // This is candidate presentation only; it neither adds facts nor
        // reconstructs a proof context.
        if let ProofContext::Pure(context) = self.context.as_ref() {
            let selected = crate::kernel::proposition_variables(kernel);
            let mut bindings = context
                .theorem_context
                .values
                .iter()
                .filter_map(|(name, value)| {
                    let CValue::Int32(Bitvector32Term::Variable(variable)) = value else {
                        return None;
                    };
                    selected
                        .contains(variable)
                        .then(|| (*variable, name.clone()))
                })
                .collect::<BTreeMap<_, _>>();
            if let Some(goal) = self.proposition_obligation() {
                for (name, value) in goal.surface_bindings.iter() {
                    if let ContractExpression::CFragment(CExpression::Value(CValue::Int32(
                        Bitvector32Term::Variable(variable),
                    ))) = value
                        && selected.contains(variable)
                    {
                        bindings.insert(*variable, name.clone());
                    }
                }
            }
            let state = CState::new().with_memory(context.theorem_context.memory.clone());
            if let Some(surface) = synthesize_surface_proposition_with_bound_variable_names(
                kernel,
                ParameterBinding::default(),
                &state,
                &bindings,
            ) && matches_kernel(&surface, true).is_some()
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
        let synthesis_context = match self.context.as_ref() {
            ProofContext::Pure(_) => None,
            ProofContext::FixedState(context) => Some((
                context.parameter_binding.parameters,
                context.parameter_binding.arguments,
                context.fixed_state.state,
            )),
            ProofContext::Execution(_) => self.premise_fixed_state_view().map(|view| {
                (
                    view.parameter_binding.parameters,
                    view.parameter_binding.arguments,
                    view.fixed_state.state,
                )
            }),
        };
        let (parameters, arguments, state) = synthesis_context?;
        let bound_variable_names = self
            .proposition_obligation()
            .into_iter()
            .flat_map(|goal| goal.surface_bindings.iter())
            .filter_map(|(name, binding)| match binding {
                ContractExpression::CFragment(CExpression::Value(CValue::Int32(
                    Bitvector32Term::Variable(variable),
                ))) => Some((*variable, name.clone())),
                _ => None,
            })
            .collect::<BTreeMap<_, _>>();
        if let Some(surface) = synthesize_surface_proposition_with_bound_variable_names(
            kernel,
            ParameterBinding::new(parameters, arguments),
            state,
            &bound_variable_names,
        ) && matches_kernel(&surface, true).is_some()
        {
            return Some(surface);
        }
        // The same recorded snapshots and matcher already completed their
        // search above. The intervening presentation candidates do not change
        // this proof's state, so repeating that miss cannot find a new source.
        None
    }

    /// Tries equalities attached to terms occurring in the current goal.
    /// This complements the kernel derivation path for arithmetic goals whose
    /// normal form is exposed only after selected historical equalities are
    /// rewritten. Candidate lookup is goal-local and persistently indexed.
    /// Atomic goals may retain a same-width renaming, but each selected
    /// equality is used at most once; structural goals keep only a closing
    /// rewrite so their recursive connective proof remains visible.
    #[cfg(test)]
    pub(super) fn try_indexed_goal_equality_rewrite_closure(&self) -> Option<Self> {
        self.try_indexed_goal_equality_rewrite_closure_excluding(false, true)
    }

    /// The closure above; with `exclude_goal_fact`, the goal's own ambient
    /// fact (in either orientation) is not a rewrite candidate, matching the
    /// atomic derivation's rule when direct closure was rejected as
    /// non-checkable.
    pub(super) fn try_indexed_goal_equality_rewrite_closure_excluding(
        &self,
        exclude_goal_fact: bool,
        allow_function_unfold: bool,
    ) -> Option<Self> {
        self.try_indexed_goal_equality_rewrite_direct_closure(exclude_goal_fact)
            .or_else(|| {
                self.try_indexed_goal_equality_rewrite_with_options(
                    exclude_goal_fact,
                    allow_function_unfold,
                    false,
                )
            })
    }

    pub(super) fn try_indexed_goal_equality_rewrite_direct_closure(
        &self,
        exclude_goal_fact: bool,
    ) -> Option<Self> {
        // Probe the scalar bounds and remainder identities that need folded
        // equality congruence. Memory-frame equalities already have a checked
        // transport path; probing their snapshot aliases first repeats costly
        // premise spelling and changes the intended transport certificate.
        let scalar_goal = match self.goal()? {
            Proposition::ConditionIs(ConditionTerm::PointerEqual(left, right), _)
                if left.block == right.block =>
            {
                true
            }
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessThan(..)
                | ConditionTerm::Bitvector32SignedLessEqual(..)
                | ConditionTerm::Bitvector32SignedGreaterThan(..)
                | ConditionTerm::Bitvector32SignedGreaterEqual(..)
                | ConditionTerm::Bitvector64SignedLessThan(..)
                | ConditionTerm::Bitvector64SignedLessEqual(..)
                | ConditionTerm::Bitvector64SignedGreaterThan(..)
                | ConditionTerm::Bitvector64SignedGreaterEqual(..)
                | ConditionTerm::Bitvector64UnsignedLessThan(..)
                | ConditionTerm::Bitvector64UnsignedLessEqual(..)
                | ConditionTerm::Bitvector64UnsignedGreaterThan(..)
                | ConditionTerm::Bitvector64UnsignedGreaterEqual(..)
                | ConditionTerm::IntegerLessThan(..)
                | ConditionTerm::IntegerLessEqual(..)
                | ConditionTerm::IntegerGreaterThan(..)
                | ConditionTerm::IntegerGreaterEqual(..),
                _,
            ) => true,
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(left, right)
                | ConditionTerm::Bitvector64Equal(left, right),
                _,
            ) => [left.as_ref(), right.as_ref()].into_iter().any(|term| {
                matches!(
                    term,
                    Bitvector32Term::Remainder(..)
                        | Bitvector32Term::UnsignedRemainder(..)
                        | Bitvector32Term::Int64Remainder(..)
                        | Bitvector32Term::UInt64Remainder(..)
                )
            }),
            _ => false,
        };
        if !scalar_goal {
            return None;
        }
        self.try_indexed_goal_equality_rewrite_with_options(exclude_goal_fact, false, true)
    }

    /// One indexed rewrite followed by direct closure of an algebraic
    /// comparison, without general simp or connected-premise discovery.
    pub(super) fn try_direct_model_equality_rewrite_closure(&self) -> Option<Self> {
        let goal = match self.goal()? {
            Proposition::Not(body) => body.as_ref(),
            goal => goal,
        };
        if !matches!(
            goal,
            Proposition::Equal(Term::Algebraic(_), Term::Algebraic(_))
        ) {
            return None;
        }
        self.try_indexed_goal_equality_rewrite_with_options(false, false, true)
    }

    /// A derived call equality need not have a recorded source spelling.
    /// Use only an operand already written in this goal, and check the
    /// resulting equality in an ordinary nested proof before citing it.
    fn try_goal_operand_constant_equality(
        &self,
        equality: &Proposition,
    ) -> Option<(ClickProposition, Self)> {
        let ClickProposition::Comparison {
            left: source_left,
            right: source_right,
            ..
        } = self.surface_goal()?
        else {
            return None;
        };
        let Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessThan(left, right)
            | ConditionTerm::Bitvector32SignedLessEqual(left, right)
            | ConditionTerm::Bitvector32SignedGreaterThan(left, right)
            | ConditionTerm::Bitvector32SignedGreaterEqual(left, right),
            true,
        ) = self.goal()?
        else {
            return None;
        };
        let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(a, b), true) = equality else {
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
            let Bitvector32Term::Constant(value) = literal else {
                continue;
            };
            if matches!(operand, Bitvector32Term::Constant(_)) {
                continue;
            }
            let surface = ClickProposition::Comparison {
                left: source.clone(),
                operator: ComparisonOperator::Equal,
                right: ContractExpression::CFragment(CExpression::Value(CValue::Int32(
                    Bitvector32Term::Constant(*value),
                ))),
            };
            let scope = self.begin_have(surface.clone()).ok()?;
            let closed = scope.try_direct_logical_closure().ok()??;
            return Some((surface, closed.join().ok()?));
        }
        None
    }

    fn try_indexed_goal_equality_rewrite_with_options(
        &self,
        exclude_goal_fact: bool,
        allow_function_unfold: bool,
        direct_only: bool,
    ) -> Option<Self> {
        if matches!(
            self.goal(),
            Some(Proposition::Implies(..) | Proposition::ForAll { .. })
        ) {
            return None;
        }
        if matches!(
            self.goal(),
            Some(Proposition::ConditionIs(
                ConditionTerm::IntegerEqual(..),
                true
            ))
        ) && self.scalar_equality_goal_is_refuted()
        {
            return if exclude_goal_fact {
                None
            } else {
                self.try_direct_logical_closure().ok().flatten()
            };
        }
        // The direct-only chain never enters typed or function-unfold
        // search. It can finish a pointer-offset rewrite inside the outer
        // equality search without restarting that speculative fallback.
        let _scope = if direct_only {
            None
        } else {
            Some(SimpFallbackScope::enter(SimpFallback::EqualityRewrite)?)
        };
        // A judgment stated at an execution frontier (a `have` inside an
        // `open` scope, before the outcome) reads its spellings from the
        // execution's surface map, anchored at the current statement entry.
        let frontier_anchor = match self.context.as_ref() {
            ProofContext::Execution(_) if self.focused_outcome_data().is_none() => {
                self.execution().map(|execution| ProgramPointRef {
                    region: CodeRegionRef::Statement(execution.core.frontier.next_statement_index),
                    kind: ProgramPointKind::Entry,
                })
            }
            _ => None,
        };
        let (surface_facts, premise_anchor) = match self.context.as_ref() {
            ProofContext::Pure(context) => (&context.theorem_context.surface_requirements, None),
            ProofContext::FixedState(context) => (
                context.surface_propositions,
                context.premise_anchor.as_ref(),
            ),
            ProofContext::Execution(_) => match self.focused_outcome_data() {
                Some(data) => (&data.surface_propositions, data.premise_anchor.as_ref()),
                None => (
                    &self.execution()?.surface_propositions,
                    frontier_anchor.as_ref(),
                ),
            },
        };
        // One level of the chain: every candidate equality mentioning the
        // goal is tried as a checked rewrite followed by the closers. Up to
        // `refinement_limit` rewrites that changed the goal are returned for
        // the next level; a closing-only probe asks for none.
        // Different equality paths often reach the same checked obligation.
        // Retry its closers only when the premise context or logical-read
        // generation changed. Keep the rewrite/refinement paths themselves:
        // they may still lead to a different next obligation.
        let attempted_closures = std::cell::RefCell::new(BTreeSet::new());
        let level = |proof: &Self,
                     used: &BTreeSet<Proposition>,
                     refinement_limit: usize|
         -> Result<Option<Self>, Vec<(Proposition, Self)>> {
            let Some(goal) = proof.goal().cloned() else {
                return Err(Vec::new());
            };
            let allows_chain = matches!(goal, Proposition::ConditionIs(_, _))
                || matches!(goal, Proposition::CResourceSeparate { .. })
                || matches!(
                    goal,
                    Proposition::Equal(Term::Algebraic(_), Term::Algebraic(_))
                );
            let mut refinements: Vec<(Proposition, Self)> = Vec::new();
            let goal_variable_count = crate::kernel::proposition_variables(&goal).len();
            // Pointer equalities between scaled offsets are candidates too:
            // `rewrite` carries one through the address of a load, so a
            // goal over `p->q->x` reaches `r->x` under `p->q == r`.
            // Once both pointers have the same base, only their offsets
            // need rewriting. Selecting on the shared base also nominates
            // every historical pointer fact about that object, even when
            // none mentions an offset operand of this comparison.
            let equality_candidates = match &goal {
                Proposition::ConditionIs(ConditionTerm::PointerEqual(left, right), value)
                    if left.block == right.block =>
                {
                    // External arguments share a block and carry the
                    // actual base as an offset prefix: `(base + i) == base`
                    // needs facts about `i`, not old reads through `base`.
                    let zero = crate::kernel::PointerOffsetTerm::Constant(0);
                    let (left, right) = match (&left.offset, &right.offset) {
                        (crate::kernel::PointerOffsetTerm::Add(base, index), right)
                            if base.as_ref() == right =>
                        {
                            (index.as_ref(), &zero)
                        }
                        (left, crate::kernel::PointerOffsetTerm::Add(base, index))
                            if left == base.as_ref() =>
                        {
                            (&zero, index.as_ref())
                        }
                        (
                            crate::kernel::PointerOffsetTerm::Add(left_base, left_index),
                            crate::kernel::PointerOffsetTerm::Add(right_base, right_index),
                        ) if left_base == right_base => (left_index.as_ref(), right_index.as_ref()),
                        (left, right) => (left, right),
                    };
                    proof
                        .facts()
                        .load_equalities_mentioning(&Proposition::ConditionIs(
                            ConditionTerm::PointerOffsetEqual(
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
            for equality in equalities {
                // A reflexive equality cannot change the checked goal.
                // Avoid reconstructing source spellings for these pointer
                // metadata facts at every link of the rewrite chain.
                if is_reflexive_pointer_equality(&equality) {
                    continue;
                }
                // A registered read definition remains available to the
                // kernel, but cannot supply a source rewrite. Do not search
                // recorded snapshots for a spelling of this metadata.
                if crate::kernel::is_verified_load_variable_defining_fact(&equality) {
                    continue;
                }
                let equality_has_literal_endpoint = matches!(
                    &equality,
                    Proposition::ConditionIs(
                        ConditionTerm::Bitvector32Equal(left, right) | ConditionTerm::Bitvector64Equal(left, right),
                        true
                    ) if matches!(left.as_ref(), Bitvector32Term::Constant(_) | Bitvector32Term::Int64Constant(_) | Bitvector32Term::UInt64Constant(_))
                        || matches!(right.as_ref(), Bitvector32Term::Constant(_) | Bitvector32Term::Int64Constant(_) | Bitvector32Term::UInt64Constant(_))
                ) || matches!(
                    &equality,
                    Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), true)
                        if matches!(&**left, crate::kernel::IntegerTerm::Constant(_))
                            || matches!(&**right, crate::kernel::IntegerTerm::Constant(_))
                );
                if used.contains(&equality) {
                    continue;
                }
                if exclude_goal_fact
                    && (equality == goal
                        || swapped_bitvector_equality(&equality)
                            .is_some_and(|swapped| swapped == goal))
                {
                    continue;
                }
                let (surface, candidate_proof) =
                    match proof.available_surface_fact(surface_facts, premise_anchor, &equality) {
                        Some(surface) => (surface, proof.clone()),
                        None => match proof.try_goal_operand_constant_equality(&equality) {
                            Some(candidate) => candidate,
                            None => continue,
                        },
                    };
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
                            matches!(kernel, Proposition::ConditionIs(
                                ConditionTerm::Bitvector32Equal(left, right) | ConditionTerm::Bitvector64Equal(left, right), true
                            ) if matches!(if source { left.as_ref() } else { right.as_ref() },
                                Bitvector32Term::Constant(_) | Bitvector32Term::Int64Constant(_) | Bitvector32Term::UInt64Constant(_)))
                                || matches!(kernel, Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), true)
                                    if matches!(if source { &**left } else { &**right }, crate::kernel::IntegerTerm::Constant(_)))
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
                            .unwrap_or_else(|| matches!(&oriented, ClickProposition::Comparison { left, .. } if surface_expression_is_constant(left)));
                        if source_is_literal {
                            continue;
                        }
                    }
                    // Every candidate is a checked rewrite followed by three
                    // closers, for each equality mentioning the goal, at
                    // each link of the chain. Observe the tactic's deadline
                    // and work budget between candidates, so a search that
                    // cannot close stops when its tactic's bound runs out.
                    if crate::instrumentation::deadline_exceeded() {
                        return Err(Vec::new());
                    }
                    let rewrite = proof.apply_step(ProofStep::Rewrite(oriented));
                    let Ok(rewritten) = rewrite else {
                        continue;
                    };
                    if rewritten.goal() == proof.goal() {
                        continue;
                    }
                    // Checked rewrites preserve this obligation. Once one
                    // reaches a refuted scalar equality, more equivalent
                    // rewrites or function expansions cannot help the search.
                    if matches!(
                        rewritten.goal(),
                        Some(Proposition::ConditionIs(
                            ConditionTerm::IntegerEqual(..),
                            true
                        ))
                    ) && rewritten.scalar_equality_goal_is_refuted()
                    {
                        if !exclude_goal_fact
                            && let Some(closed) =
                                rewritten.try_direct_logical_closure().ok().flatten()
                        {
                            return Ok(Some(closed));
                        }
                        return Err(Vec::new());
                    }
                    let closure_key =
                        rewritten
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
                        && let Some(closed) = rewritten
                            .try_direct_logical_closure()
                            .ok()
                            .flatten()
                            .or_else(|| {
                                (!direct_only
                                    && matches!(
                                        rewritten.goal(),
                                        Some(Proposition::ConditionIs(
                                            ConditionTerm::PointerEqual(..),
                                            _
                                        ))
                                    ))
                                .then(|| {
                                    rewritten.try_indexed_goal_equality_rewrite_direct_closure(
                                        exclude_goal_fact,
                                    )
                                })
                                .flatten()
                            })
                            .or_else(|| {
                                (!direct_only)
                                    .then(|| rewritten.try_typed_atomic_simp_closure())
                                    .flatten()
                            })
                            .or_else(|| {
                                allow_function_unfold
                                    .then(|| {
                                        rewritten
                                            .try_function_unfold_simp_closure(&[])
                                            .ok()
                                            .flatten()
                                    })
                                    .flatten()
                            })
                    {
                        return Ok(Some(closed));
                    }
                    // Do not turn a value already present in the goal into a
                    // fresh symbolic variable merely because the reverse
                    // orientation of an equality happens to match first.
                    // Equal-sized variable-to-variable rewrites remain
                    // available for ordinary equality chains.
                    let does_not_expand_a_literal = !equality_has_literal_endpoint
                        || rewritten.goal().is_some_and(|rewritten_goal| {
                            crate::kernel::proposition_variables(rewritten_goal).len()
                                <= goal_variable_count
                        });
                    if allows_chain
                        && refinements.len() < refinement_limit
                        && rewritten.goal() != Some(&goal)
                        && does_not_expand_a_literal
                        && !refinements
                            .iter()
                            .any(|(_, other)| other.goal() == rewritten.goal())
                    {
                        refinements.push((equality.clone(), rewritten));
                    }
                }
            }
            Err(refinements)
        };
        let mut proof = self.clone();
        let mut used = BTreeSet::new();
        loop {
            let refinements = match level(
                &proof,
                &used,
                if direct_only {
                    0
                } else {
                    MAX_EQUALITY_REWRITE_BRANCHES
                },
            ) {
                Ok(closed) => return closed,
                Err(refinements) => refinements,
            };
            // A link whose own rewrite does not close may be one step from a
            // closing link. The first refinement continues the chain; each
            // other one gets a closing-only probe first, so which change the
            // candidate order happened to find first does not decide whether
            // a chain through the goal's equality classes closes.
            for (equality, rewritten) in refinements.iter().skip(1) {
                let mut probe_used = used.clone();
                probe_used.insert(equality.clone());
                if let Ok(Some(closed)) = level(rewritten, &probe_used, 0) {
                    return Some(closed);
                }
            }
            let (equality, rewritten) = refinements.into_iter().next()?;
            used.insert(equality);
            proof = rewritten;
        }
    }

    /// Rewrites with only the explicitly selected equality premises, at most
    /// once each. Every candidate rewrite is checked transactionally, and
    /// the finite user-written premise list is the entire search space.
    pub(super) fn try_selected_equality_rewrite_chain(
        &self,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        self.try_selected_equality_rewrite_chain_with_scope(premise_pairs, false)
    }

    /// The explicit-premise counterpart of
    /// [`Self::try_selected_equality_rewrite_chain`]. After each checked
    /// rewrite it may normalize without context or run a typed atomic plan
    /// against the same named premises, but it cannot consult ambient facts.
    fn try_restricted_equality_rewrite_chain(
        &self,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        self.try_selected_equality_rewrite_chain_with_scope(premise_pairs, true)
    }

    fn try_selected_equality_rewrite_chain_with_scope(
        &self,
        premise_pairs: &[(Proposition, ClickProposition)],
        restricted: bool,
    ) -> Option<Self> {
        let mut proof = self.clone();
        let mut remaining = premise_pairs
            .iter()
            .filter(|(kernel, _)| {
                matches!(
                    kernel,
                    Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(_, _), true)
                        | Proposition::ConditionIs(ConditionTerm::Bitvector64Equal(_, _), true)
                        | Proposition::ConditionIs(ConditionTerm::PointerEqual(_, _), true)
                        | Proposition::ConditionIs(ConditionTerm::PointerValueEqual(_, _), true)
                        | Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(_, _), true)
                        | Proposition::Equal(Term::Algebraic(_), Term::Algebraic(_))
                )
            })
            .map(|(_, surface)| surface.clone())
            .collect::<Vec<_>>();
        while !remaining.is_empty() {
            let mut selected = None;
            for (index, surface) in remaining.iter().enumerate() {
                // Once an earlier equality applies, a later one is only a
                // probe for the rewrite that closes the goal outright.
                let probing = selected.is_some();
                for oriented in
                    std::iter::once(surface.clone()).chain(reverse_surface_equality(surface))
                {
                    // Each candidate rewrite applies a checked step and a
                    // closure, quadratically in the equalities; observe the
                    // tactic's deadline and budget between candidates.
                    if crate::instrumentation::deadline_exceeded() {
                        return None;
                    }
                    if let Ok(rewritten) = proof.apply_step(ProofStep::Rewrite(oriented)) {
                        let closed = if probing {
                            rewritten.try_direct_logical_closure().ok().flatten()
                        } else if restricted {
                            rewritten.try_typed_atomic_simp_from_selected_premises(premise_pairs)
                        } else {
                            rewritten
                                .try_direct_logical_closure()
                                .ok()
                                .flatten()
                                .or_else(|| rewritten.try_typed_atomic_simp_closure())
                        }
                        // A rewrite can leave a goal over constructors only,
                        // such as `ParentLink::Linked(kid) != ParentLink::Empty`
                        // after rewriting by `link.link == ParentLink::Linked(kid)`;
                        // normalization decides it without consulting context.
                        .or_else(|| {
                            rewritten
                                .apply_step(ProofStep::Normalize)
                                .ok()
                                .filter(Proof::is_complete)
                        });
                        if let Some(closed) = closed {
                            return Some(closed);
                        }
                        selected.get_or_insert((index, rewritten));
                    }
                }
                // Every remaining equality is offered the chance to close
                // the goal before one that merely applies is committed to.
                // A rewrite that applies without closing can move the goal
                // away from the equality that would: with `q == p` stated at
                // two points, rewriting `p` to the older `q` first leaves no
                // rewrite by the newer one that reaches a reflexive goal.
                // The probe asks only the direct logical closer (the
                // reflexive goal is its case): giving every later equality
                // the whole typed simp closure made each round cost that
                // closure once per remaining equality, and took the arena
                // `have` at arena_cells.click:3846 from 208,305 to 957,192
                // units.
            }
            let (index, rewritten) = selected?;
            remaining.remove(index);
            proof = rewritten;
        }
        None
    }

    fn try_typed_atomic_simp_from_selected_premises(
        &self,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        let goal = self.goal()?.clone();
        if premise_pairs
            .iter()
            .any(|(kernel, _)| selected_premise_contains_goal(kernel, &goal))
        {
            return self
                .apply_step(ProofStep::Assumption)
                .ok()
                .filter(Proof::is_complete);
        }
        let restricted = premise_pairs
            .iter()
            .map(|(kernel, _)| kernel.clone())
            .collect::<Vec<_>>();
        match plan_simp_certificate(&goal, &assumptions_from_propositions(&restricted))? {
            SimpEvidence::Normalize => self
                .apply_step(ProofStep::Normalize)
                .ok()
                .filter(Proof::is_complete),
            SimpEvidence::Derivation(derivation) => self.check_typed_atomic_simp_candidate(
                &goal,
                &derivation,
                premise_pairs,
                !matches!(self.context.as_ref(), ProofContext::Execution(_)),
            ),
        }
    }

    /// Weakens a constant bound. A goal `value >= c` (or `value <= c`)
    /// closes from a stronger context bound `value >= C` with `C >= c`
    /// (`value <= C` with `C <= c`), the shape a loop's negated guard leaves
    /// on its counter. The proof cites only facts it establishes itself, two
    /// nested `have`s closed by the direct logical closer, so the context
    /// bound needs no Surface spelling; the transitivity theorem then closes
    /// the goal.
    pub(super) fn try_selected_constant_bound_weakening(
        &self,
        goal: &Proposition,
        derivation: &PropositionDerivation,
    ) -> Option<Self> {
        let surface_goal = self.surface_goal()?.clone();
        let (goal_value, goal_bound, lower_bound) = match goal {
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedGreaterEqual(value, bound),
                true,
            ) => (value, bound, true),
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessEqual(value, bound),
                true,
            ) => (value, bound, false),
            _ => return None,
        };
        let Bitvector32Term::Constant(goal_bits) = goal_bound.as_ref() else {
            return None;
        };
        let goal_constant = *goal_bits as i32;
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
            let bound = match (term, polarity, lower_bound) {
                (ConditionTerm::Bitvector32SignedGreaterEqual(value, bound), true, true)
                | (ConditionTerm::Bitvector32SignedLessThan(value, bound), false, true)
                | (ConditionTerm::Bitvector32SignedLessEqual(value, bound), true, false)
                | (ConditionTerm::Bitvector32SignedGreaterThan(value, bound), false, false)
                    if value == goal_value =>
                {
                    bound
                }
                _ => continue,
            };
            let Bitvector32Term::Constant(bits) = bound.as_ref() else {
                continue;
            };
            let constant = *bits as i32;
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
                ContractExpression::CFragment(CExpression::Value(int32(constant as u32)));
            let bound_surface = ClickProposition::Comparison {
                left: surface_value.clone(),
                operator,
                right: surface_constant.clone(),
            };
            let link_surface = ClickProposition::Comparison {
                left: surface_constant.clone(),
                operator,
                right: surface_goal_constant.clone(),
            };
            let Ok(scope) = self.begin_have(bound_surface.clone()) else {
                continue;
            };
            let Some(scope) = scope.try_direct_logical_closure().ok().flatten() else {
                continue;
            };
            let Ok(proof) = scope.join() else {
                continue;
            };
            let Ok(scope) = proof.begin_have(link_surface.clone()) else {
                continue;
            };
            let Some(scope) = scope.try_direct_logical_closure().ok().flatten() else {
                continue;
            };
            let Ok(proof) = scope.join() else {
                continue;
            };
            let theorem = ProofStep::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: if lower_bound {
                        "click::machine_integer::int32_greater_equal_transitive".to_string()
                    } else {
                        "click::machine_integer::int32_less_equal_transitive".to_string()
                    },
                    arguments: vec![
                        surface_value.clone(),
                        surface_constant.clone(),
                        surface_goal_constant.clone(),
                    ],
                },
                premises: vec![bound_surface, link_surface],
            };
            let Ok(applied) = proof.apply_step(theorem) else {
                continue;
            };
            if applied.is_complete() {
                return Some(applied);
            }
            if let Some(closed) = applied.try_direct_logical_closure().ok().flatten() {
                return Some(closed);
            }
        }
        None
    }

    /// Searches the structured predecessor proof already expressible through
    /// the checked API. The goal itself fixes the value and upper bound, so
    /// this visits only selected equalities connected to that value and one
    /// exact upper-bound premise; it never tries every partially synthesizable
    /// context fact as a candidate step.
    /// The surface spelling of an exact fact, looked up as `simp` resolves
    /// the premises of a derivation it selected.
    fn unsigned_surface_fact(&self, kernel: &Proposition) -> Option<ClickProposition> {
        // A reconstructible spelling is not evidence that the fact is held.
        // In particular, a positive difference may need to be derived from
        // the unsigned guard before the predecessor lemma can use it.
        if !self.facts().contains(kernel) {
            return None;
        }
        match self.context.as_ref() {
            ProofContext::Pure(context) => self.available_surface_fact(
                &context.theorem_context.surface_requirements,
                None,
                kernel,
            ),
            ProofContext::FixedState(context) => self.available_surface_fact(
                context.surface_propositions,
                context.premise_anchor.as_ref(),
                kernel,
            ),
            ProofContext::Execution(_) => {
                if let Some(data) = self.focused_outcome_data() {
                    self.available_surface_fact(
                        &data.surface_propositions,
                        data.premise_anchor.as_ref(),
                        kernel,
                    )
                } else {
                    let execution = self.execution()?;
                    let anchor = frontier_premise_anchor(execution);
                    self.available_surface_fact(
                        &execution.presentation.surface_propositions,
                        anchor.as_ref(),
                        kernel,
                    )
                }
            }
        }
    }

    /// The fact `lower <u upper` as a proof that has it in that spelling,
    /// with the fact's surface and its two operands. The fact may be held
    /// as `upper >u lower`; the lemma that reads it the other way round is
    /// applied first. Both lookups are exact: no fact is scanned.
    fn unsigned_strict_fact(
        &self,
        lower: &Bitvector32Term,
        upper: &Bitvector32Term,
        surface_fact: &dyn Fn(&Proposition) -> Option<ClickProposition>,
    ) -> Option<(
        Self,
        ClickProposition,
        ContractExpression,
        ContractExpression,
    )> {
        let less = Proposition::ConditionIs(
            ConditionTerm::unsigned_less_than(lower.clone(), upper.clone()),
            true,
        );
        if let Some(surface) = surface_fact(&less) {
            let (lower, upper) = surface_strict_parts(&surface)?;
            return Some((self.clone(), surface, lower, upper));
        }
        let greater = Proposition::ConditionIs(
            ConditionTerm::unsigned_greater_than(upper.clone(), lower.clone()),
            true,
        );
        let surface = surface_fact(&greater)?;
        let (lower, upper) = surface_strict_parts(&surface)?;
        let reversed = ClickProposition::Comparison {
            left: lower.clone(),
            operator: ComparisonOperator::LessThan,
            right: upper.clone(),
        };
        let proof = self
            .apply_step(ProofStep::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: "click::machine_integer::uint32_greater_than_implies_reversed_less_than"
                        .to_string(),
                    arguments: vec![upper.clone(), lower.clone()],
                },
                premises: vec![surface],
            })
            .ok()?;
        Some((proof, reversed, lower, upper))
    }

    /// Applies one uint32 lemma and closes the goal with its conclusion.
    fn close_with_unsigned_lemma(
        &self,
        name: &str,
        arguments: Vec<ContractExpression>,
        premise: ClickProposition,
    ) -> Option<Self> {
        let applied = self
            .apply_step(ProofStep::ApplyTheoremUsing {
                application: TheoremApplication {
                    name: name.to_string(),
                    arguments,
                },
                premises: vec![premise],
            })
            .ok()?;
        // The lemma's conclusion is the goal, so applying it discharges the
        // goal where it is stated exactly; the focus then leaves it, though
        // sibling goals (other members of a loop bundle) may remain.
        if applied.is_complete() || applied.goal() != self.goal() {
            return Some(applied);
        }
        applied.try_direct_logical_closure().ok().flatten()
    }

    /// Closes an unsigned order goal that is one step of uint32 arithmetic
    /// from an exact fact, by the lemma that states that step: a
    /// predecessor, a successor under a strict bound, the descent of a
    /// difference, or one comparison read the other way round.
    ///
    /// The goal's shape names the lemma and the one premise it needs, which
    /// is looked up exactly, so the work is a fixed number of lookups
    /// whatever the context holds.
    pub(super) fn try_unsigned_order_lemma(&self) -> Option<Self> {
        self.try_unsigned_order_lemma_from(&|kernel| self.unsigned_surface_fact(kernel))
    }

    /// [`Self::try_unsigned_order_lemma`] with the premise taken from the
    /// surface premises a tactic lists, and from nowhere else: the step
    /// `arithmetic() using { ... }` promises to use exactly those.
    pub(in crate::surface::proof) fn try_unsigned_order_lemma_using(
        &self,
        surface_premises: &[ClickProposition],
    ) -> Option<Self> {
        // Only an unsigned order goal has a lemma, so only then are the
        // listed premises lowered.
        unsigned_order_parts(self.goal()?)?;
        let listed = surface_premises
            .iter()
            .filter_map(|surface| {
                let kernel = self
                    .lower_cited_surface_proposition(surface, "`arithmetic using` premise")
                    .ok()?;
                self.facts()
                    .listed_premise_available(&kernel, &[], false)
                    .then(|| (kernel, surface.clone()))
            })
            .collect::<Vec<_>>();
        self.try_unsigned_order_lemma_from(&|kernel| {
            listed
                .iter()
                .find(|(listed, _)| listed == kernel)
                .map(|(_, surface)| surface.clone())
        })
    }

    fn try_unsigned_order_lemma_from(
        &self,
        surface_fact: &dyn Fn(&Proposition) -> Option<ClickProposition>,
    ) -> Option<Self> {
        let (order, left, right) = unsigned_order_parts(self.goal()?)?;
        let zero = Bitvector32Term::Constant(0);
        let one = Bitvector32Term::Constant(1);
        let reversed_fact = |condition: ConditionTerm, name: &str, strict: bool| {
            let surface = surface_fact(&Proposition::ConditionIs(condition, true))?;
            let (lower, upper) = if strict {
                surface_strict_parts(&surface)?
            } else {
                surface_nonstrict_parts(&surface)?
            };
            // Each reversal lemma takes the operands in the order its
            // premise writes them.
            let arguments = if name
                .rsplit("::")
                .next()
                .is_some_and(|name| name.starts_with("uint32_g"))
            {
                vec![upper, lower]
            } else {
                vec![lower, upper]
            };
            self.close_with_unsigned_lemma(name, arguments, surface)
        };
        match order {
            UnsignedOrder::Less => {
                // `value - 1 <u value` from `0 <u value`.
                if left == Bitvector32Term::Subtract(Box::new(right.clone()), Box::new(one.clone()))
                {
                    if let Some((proof, premise, _, value)) =
                        self.unsigned_strict_fact(&zero, &right, surface_fact)
                    {
                        return proof.close_with_unsigned_lemma(
                            "click::machine_integer::uint32_positive_predecessor_strictly_decreases",
                            vec![value],
                            premise,
                        );
                    }
                    // The value is a difference `upper - lower`, nonzero
                    // because `lower <u upper`.
                    if let Bitvector32Term::Subtract(upper, lower) = &right
                        && let Some((proof, premise, lower, upper)) =
                            self.unsigned_strict_fact(lower, upper, surface_fact)
                    {
                        // The difference is spelled from the premise's own
                        // operands, so it lowers to the goal's term.
                        let difference = ContractExpression::Subtract(
                            Box::new(upper.clone()),
                            Box::new(lower.clone()),
                        );
                        let positive = ClickProposition::Comparison {
                            left: ContractExpression::CFragment(CExpression::Value(
                                CValue::UInt32(Bitvector32Term::Constant(0)),
                            )),
                            operator: ComparisonOperator::LessThan,
                            right: difference.clone(),
                        };
                        let proof = proof
                            .apply_step(ProofStep::ApplyTheoremUsing {
                                application: TheoremApplication {
                                    name: "click::machine_integer::uint32_less_than_implies_positive_difference"
                                        .to_string(),
                                    arguments: vec![lower, upper],
                                },
                                premises: vec![premise],
                            })
                            .ok()?;
                        return proof.close_with_unsigned_lemma(
                            "click::machine_integer::uint32_positive_predecessor_strictly_decreases",
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
                    Bitvector32Term::Add(left_base, left_offset),
                    Bitvector32Term::Add(right_base, right_offset),
                ) = (&left, &right)
                    && left_base == right_base
                    && let Bitvector32Term::Subtract(negated_zero, value) = left_base.as_ref()
                    && negated_zero.as_ref() == &zero
                    && let (Some(lower), Some(bound)) =
                        (left_offset.as_const(), right_offset.as_const())
                    && bound != 0
                    && lower == bound - 1
                    && let Some((proof, premise, value, bound)) =
                        self.unsigned_strict_fact(value, right_offset, surface_fact)
                {
                    return proof.close_with_unsigned_lemma(
                        "click::machine_integer::uint32_difference_decreases_after_increment",
                        vec![value, bound],
                        premise,
                    );
                }
                reversed_fact(
                    ConditionTerm::unsigned_greater_than(right, left),
                    "click::machine_integer::uint32_greater_than_implies_reversed_less_than",
                    true,
                )
            }
            UnsignedOrder::LessEqual => {
                // `value + 1 <=u upper` from `value <u upper`.
                if let Bitvector32Term::Add(value, amount) = &left
                    && amount.as_ref() == &one
                    && let Some((proof, premise, value, upper)) =
                        self.unsigned_strict_fact(value, &right, surface_fact)
                {
                    return proof.close_with_unsigned_lemma(
                        "click::machine_integer::uint32_increment_upper_bound",
                        vec![value, upper],
                        premise,
                    );
                }
                reversed_fact(
                    ConditionTerm::unsigned_greater_equal(right, left),
                    "click::machine_integer::uint32_greater_equal_implies_reversed_less_equal",
                    false,
                )
            }
            UnsignedOrder::Greater => reversed_fact(
                ConditionTerm::unsigned_less_than(right, left),
                "click::machine_integer::uint32_less_than_implies_reversed_greater_than",
                true,
            ),
            UnsignedOrder::GreaterEqual => reversed_fact(
                ConditionTerm::unsigned_less_equal(right, left),
                "click::machine_integer::uint32_less_equal_implies_reversed_greater_equal",
                false,
            ),
        }
    }

    pub(super) fn try_selected_predecessor_upper_bound(
        &self,
        goal: &Proposition,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        if !matches!(self.context.as_ref(), ProofContext::FixedState(_)) {
            return None;
        }
        let Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessEqual(predecessor, goal_upper),
            true,
        ) = goal
        else {
            return None;
        };
        let Bitvector32Term::Subtract(value, amount) = predecessor.as_ref() else {
            return None;
        };
        if amount.as_ref() != &Bitvector32Term::Constant(1) {
            return None;
        }
        let upper_kernel = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessEqual(value.clone(), goal_upper.clone()),
            true,
        );
        let (_, upper_surface) = premise_pairs
            .iter()
            .find(|(kernel, _)| kernel == &upper_kernel)?;
        let (surface_value, surface_upper) = surface_nonstrict_parts(upper_surface)?;
        let nonnegative_surface = ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(int32(0))),
            operator: ComparisonOperator::LessEqual,
            right: surface_value.clone(),
        };
        for (kernel, surface) in premise_pairs {
            let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) =
                kernel
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
            let Bitvector32Term::Constant(bits) = selected_constant else {
                continue;
            };
            if (*bits as i32) < 0 {
                continue;
            }
            let mut orientations = vec![surface.clone()];
            if let Some(reverse) = reverse_surface_equality(surface)
                && reverse != *surface
            {
                orientations.push(reverse);
            }
            for equality in orientations {
                let scope = self.begin_have(nonnegative_surface.clone()).ok()?;
                let Ok(scope) = scope.apply_step(ProofStep::Rewrite(equality)) else {
                    continue;
                };
                let Some(scope) = scope.try_direct_logical_closure().ok().flatten() else {
                    continue;
                };
                let joined = scope.join().ok()?;
                let theorem = ProofStep::ApplyTheoremUsing {
                    application: TheoremApplication {
                        name: "click::machine_integer::int32_nonnegative_predecessor_upper_bound"
                            .to_string(),
                        arguments: vec![surface_value.clone(), surface_upper.clone()],
                    },
                    premises: vec![nonnegative_surface.clone(), upper_surface.clone()],
                };
                let Ok(applied) = joined.apply_step(theorem) else {
                    continue;
                };
                if applied.is_complete() {
                    return Some(applied);
                }
                if let Some(closed) = applied.try_direct_logical_closure().ok().flatten() {
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
    fn try_disjunctive_syllogism_closure(&self) -> Option<Self> {
        let goal = self.goal()?.clone();
        if !matches!(goal, Proposition::ConditionIs(_, _)) {
            return None;
        }
        let assumptions = self.facts().assumptions();
        let refuted = |disjunct: &Proposition| {
            let negated = match disjunct {
                Proposition::ConditionIs(condition, value) => {
                    Proposition::ConditionIs(condition.clone(), !value)
                }
                other => Proposition::Not(Box::new(other.clone())),
            };
            assumptions.states_required_goal(&negated)
        };
        let candidates = assumptions
            .disjunction_fact_propositions()
            .filter(|disjunction| {
                let disjuncts = flattened_disjuncts(disjunction);
                disjuncts.iter().any(|disjunct| **disjunct == goal)
                    && disjuncts
                        .iter()
                        .filter(|disjunct| ***disjunct != goal)
                        .all(|disjunct| refuted(disjunct))
            })
            .cloned()
            .collect::<Vec<_>>();
        let frontier_anchor = match self.context.as_ref() {
            ProofContext::Execution(_) if self.focused_outcome_data().is_none() => {
                self.execution().map(|execution| ProgramPointRef {
                    region: CodeRegionRef::Statement(execution.core.frontier.next_statement_index),
                    kind: ProgramPointKind::Entry,
                })
            }
            _ => None,
        };
        let (surface_facts, premise_anchor) = match self.context.as_ref() {
            ProofContext::Pure(context) => (&context.theorem_context.surface_requirements, None),
            ProofContext::FixedState(context) => (
                context.surface_propositions,
                context.premise_anchor.as_ref(),
            ),
            ProofContext::Execution(_) => match self.focused_outcome_data() {
                Some(data) => (&data.surface_propositions, data.premise_anchor.as_ref()),
                None => (
                    &self.execution()?.surface_propositions,
                    frontier_anchor.as_ref(),
                ),
            },
        };
        candidates.into_iter().find_map(|disjunction| {
            let surface =
                self.available_surface_fact(surface_facts, premise_anchor, &disjunction)?;
            self.try_selected_disjunction_cases(&[(disjunction, surface)])
        })
    }

    /// Eliminates one disjunction selected by the kernel derivation and
    /// proves both arms on their branch-local `Proof`s. The disjunction is
    /// never reopened once either disjunct is already available, which makes
    /// recursive branch search descend through distinct case assumptions.
    pub(super) fn try_selected_disjunction_cases(
        &self,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        for (kernel, surface) in premise_pairs {
            let Proposition::Or(left, right) = kernel else {
                continue;
            };
            if self.facts().contains(left) || self.facts().contains(right) {
                continue;
            }
            let (surface_left, surface_right) = match surface {
                ClickProposition::Or(left, right) => {
                    (left.as_ref().clone(), right.as_ref().clone())
                }
                ClickProposition::At {
                    selector,
                    proposition,
                } => {
                    let ClickProposition::Or(left, right) = proposition.as_ref() else {
                        continue;
                    };
                    (
                        ClickProposition::At {
                            selector: selector.clone(),
                            proposition: Box::new(left.as_ref().clone()),
                        },
                        ClickProposition::At {
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
            let Ok((split_proof, split, ids)) = self.split_focused_cases(surface.clone()) else {
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
                let selected = focused_branch
                    .apply_step(ProofStep::Contradiction(assumed_surface.clone()))
                    .ok()
                    .or_else(|| focused_branch.try_simp_closure().ok().flatten())
                    .or_else(|| {
                        let (goal_left, goal_right) =
                            surface_logical_children(focused_branch.surface_goal()?, false)?;
                        let selected_goal = if index == 0 { goal_left } else { goal_right };
                        let scope = focused_branch.begin_have(selected_goal).ok()?;
                        let rewritten = scope
                            .apply_step(ProofStep::Rewrite(assumed_surface.clone()))
                            .ok()?;
                        let closed = rewritten.try_direct_logical_closure().ok().flatten()?;
                        let joined = closed.join().ok()?;
                        joined.apply_step(ProofStep::Assumption).ok()
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

    /// Applies a planner's flat explicit candidate directly to persistent
    /// `Proof` descendants. Planning may select surface operations, but only
    /// their checked implementations can advance the proof.
    ///
    /// Generated candidates historically retain a final `assumption()` even
    /// when the preceding operation already discharged the goal. Ignore only
    /// that final no-op; any other operation after closure rejects the
    /// candidate. No certificate is materialized or interpreted here.
    pub(super) fn try_planned_explicit_steps(&self, tactics: &[ProofTactic]) -> Option<Self> {
        if tactics.is_empty() {
            return None;
        }
        let mut proof = self.clone();
        for (index, tactic) in tactics.iter().enumerate() {
            if proof.focused_discharged() {
                if index + 1 == tactics.len() && matches!(tactic, ProofTactic::Assumption) {
                    continue;
                }
                return None;
            }
            let step = SourceContext::PureGoal.leaf_step(tactic)?;
            proof = proof.apply_step(step).ok()?;
        }
        proof.focused_discharged().then_some(proof)
    }

    /// Specializes one checkable universal premise selected by the atomic
    /// decision at the current goal. Planning only chooses the explicit
    /// quantified fact, argument, and guards; each selected operation advances
    /// this `Proof` directly.
    pub(super) fn try_selected_forall_instantiation(
        &self,
        goal: &Proposition,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        let tactics = plan_explicit_forall_instantiation(goal, premise_pairs).or_else(|| {
            let surface_goal = self.surface_goal()?;
            let extra_arguments = self
                .proposition_obligation()
                .into_iter()
                .flat_map(|goal| goal.surface_bindings.iter())
                .filter_map(|(name, binding)| match binding {
                    ContractExpression::CFragment(CExpression::Value(CValue::Int32(value))) => {
                        Some((
                            value.clone(),
                            ContractExpression::CFragment(CExpression::Variable(name.clone())),
                        ))
                    }
                    _ => None,
                })
                .collect::<Vec<_>>();
            plan_explicit_forall_instantiation_transport(
                goal,
                surface_goal,
                premise_pairs,
                &extra_arguments,
                &|conclusion| {
                    self.facts()
                        .assumptions()
                        .clone()
                        .assume_proposition(conclusion.clone())
                        .derive_simp_atomic_proposition(goal)
                        .is_some()
                },
            )
        })?;
        self.try_planned_explicit_steps(&tactics)
    }

    /// Tries only universal facts introduced by checked predicate unfolds when
    /// the atomic decision cannot name an instantiated premise. Candidate
    /// discovery is read-only; a specialization is retained only after the
    /// ordinary `InstantiateUsing` operation advances and closes this Proof.
    #[cfg(test)]
    pub(super) fn try_indexed_forall_instantiation(&self) -> Option<Self> {
        self.try_indexed_forall_instantiation_with_surfaces(&[])
    }

    fn try_indexed_forall_instantiation_with_surfaces(
        &self,
        introduced_surfaces: &[ClickProposition],
    ) -> Option<Self> {
        let goal = self.goal()?;
        let execution_view = matches!(self.context.as_ref(), ProofContext::Execution(_))
            .then(|| self.premise_fixed_state_view())
            .flatten();
        let surface_facts = match self.context.as_ref() {
            ProofContext::Pure(context) => &context.theorem_context.surface_requirements,
            ProofContext::FixedState(context) => context.surface_propositions,
            ProofContext::Execution(_) => execution_view.as_ref()?.surface_propositions,
        };
        let bound_variable_names = match self.proposition_obligation() {
            Some(goal) => goal
                .surface_bindings
                .iter()
                .filter_map(|(name, binding)| match binding {
                    ContractExpression::CFragment(CExpression::Value(CValue::Int32(
                        Bitvector32Term::Variable(variable),
                    ))) => Some((*variable, name.clone())),
                    _ => None,
                })
                .collect::<BTreeMap<_, _>>(),
            _ => BTreeMap::new(),
        };
        let surface_form = |fact: &Proposition| {
            if let Some(surface) = introduced_surfaces.iter().find(|surface| {
                self.lower_surface_proposition(surface, "introduced forall premise")
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
            let recorded = match self.context.as_ref() {
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
            let synthesized = match self.context.as_ref() {
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
        let mut quantified_candidates = introduced_surfaces
            .iter()
            .filter_map(|surface| {
                let quantified = surface_facts.available_kernel_matching(surface, |kernel| {
                    matches!(kernel, Proposition::ForAll { .. })
                        && self.facts().quantified_fact_available(kernel)
                })?;
                Some((quantified.clone(), Some(surface.clone())))
            })
            .collect::<Vec<_>>();
        for quantified in self.facts().predicate_unfolded_universal_facts() {
            if !quantified_candidates
                .iter()
                .any(|(candidate, _)| candidate == quantified)
            {
                quantified_candidates.push((quantified.clone(), None));
            }
        }
        for (quantified, introduced_surface) in quantified_candidates {
            // Reject shape-incompatible universals before Surface lookup or
            // synthesis. Candidate extraction is structural and bounded by
            // this one indexed fact and the focused branch goal; the expensive
            // form work is reserved for a specialization that can
            // actually mention the goal's concrete argument.
            let candidate_values =
                crate::kernel::forall_guided_instantiation_candidate_values(&quantified, goal);
            let Proposition::ForAll { var, body, .. } = &quantified else {
                unreachable!("the predicate-unfolded universal index contains only universals")
            };
            if candidate_values.is_empty() {
                continue;
            }
            let recorded_surfaces = match self.context.as_ref() {
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
            let predicate_environment = match self.context.as_ref() {
                ProofContext::Pure(context) => context.spec_definitions.predicates,
                ProofContext::FixedState(context) => context.spec_definitions.predicates,
                ProofContext::Execution(context) => context.spec_definitions.predicates,
            };
            let mut surfaces = introduced_surface.into_iter().collect::<Vec<_>>();
            for recorded in recorded_surfaces {
                let candidate = match recorded {
                    ClickProposition::PredicateCall {
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
            let synthesized = match self.context.as_ref() {
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
            };
            if let Some(synthesized) = synthesized
                && !surfaces.contains(&synthesized)
            {
                surfaces.push(synthesized);
            }
            // Unfolding retains the opaque predicate fact alongside its
            // checked body. Reconstruct that body's exact surface form
            // from only the active predicate indexes when generic synthesis
            // cannot express it (notably byte-indexed loads).
            if surfaces.is_empty() {
                let click_function_environment = match self.context.as_ref() {
                    ProofContext::Pure(context) => context.spec_definitions.functions,
                    ProofContext::FixedState(context) => context.spec_definitions.functions,
                    ProofContext::Execution(context) => context.spec_definitions.functions,
                };
                for name in self.focused_branch_unfolds().iter() {
                    for opaque in self.facts().mentioning_predicate(name) {
                        let opaque_surfaces = match self.context.as_ref() {
                            ProofContext::Pure(context) => context
                                .theorem_context
                                .surface_requirements
                                .surfaces(opaque)
                                .cloned()
                                .collect::<Vec<_>>(),
                            ProofContext::FixedState(context) => context
                                .surface_propositions
                                .surfaces(opaque)
                                .cloned()
                                .collect::<Vec<_>>(),
                            ProofContext::Execution(_) => execution_view?
                                .surface_propositions
                                .surfaces(opaque)
                                .cloned()
                                .collect::<Vec<_>>(),
                        };
                        for opaque_surface in opaque_surfaces {
                            let ClickProposition::PredicateCall {
                                name: surface_name,
                                arguments,
                            } = opaque_surface
                            else {
                                continue;
                            };
                            let Some(definition) = predicate_environment.get(&surface_name) else {
                                continue;
                            };
                            let Ok(body_surface) =
                                instantiate_click_predicate_definition(definition, &arguments)
                            else {
                                continue;
                            };
                            if unfold_predicates_in_proposition(
                                SpecDefinitions::new(
                                    predicate_environment,
                                    click_function_environment,
                                ),
                                std::slice::from_ref(name),
                                opaque,
                                self.facts().assumptions(),
                            )
                            .is_ok_and(|kernel| kernel == quantified)
                                && !surfaces.contains(&body_surface)
                            {
                                surfaces.push(body_surface);
                            }
                        }
                    }
                }
            }
            for surface in surfaces {
                for value in candidate_values.iter() {
                    let argument = match value {
                        Bitvector32Term::Constant(bits) => Some(ContractExpression::CFragment(
                            CExpression::Value(CValue::Int32(Bitvector32Term::Constant(*bits))),
                        )),
                        Bitvector32Term::UInt64Constant(_) => Some(ContractExpression::CFragment(
                            CExpression::Value(CValue::UInt64(value.clone())),
                        )),
                        Bitvector32Term::Int64Constant(_) => Some(ContractExpression::CFragment(
                            CExpression::Value(CValue::Int64(value.clone())),
                        )),
                        Bitvector32Term::Variable(variable) => {
                            let Some(goal) = self.proposition_obligation() else {
                                continue;
                            };
                            goal.surface_bindings.iter().find_map(|(name, binding)| {
                                matches!(
                                    binding,
                                    ContractExpression::CFragment(CExpression::Value(
                                        CValue::Int32(Bitvector32Term::Variable(bound))
                                    )) if bound == variable
                                )
                                .then(|| {
                                    ContractExpression::CFragment(CExpression::Variable(
                                        name.clone(),
                                    ))
                                })
                            })
                        }
                        _ => None,
                    };
                    let Some(argument) = argument else {
                        continue;
                    };
                    let instantiated =
                        substitute_int32_variable_in_proposition(body, *var, value.clone());
                    let mut guard_facts = Vec::new();
                    let mut current = &instantiated;
                    let mut guards_available = true;
                    while let Proposition::Implies(guard, consequent) = current {
                        let mut conjuncts = Vec::new();
                        atomic_conjuncts(guard, &mut conjuncts);
                        for conjunct in conjuncts {
                            if matches!(normalize_proposition(conjunct), SimpProposition::True) {
                                continue;
                            }
                            let exact = std::iter::once(conjunct.clone())
                                .chain(condition_polarity_forms(conjunct))
                                .find(|candidate| self.facts().contains(candidate));
                            let selected = exact.map(|fact| vec![fact]).or_else(|| {
                                self.facts()
                                    .assumptions()
                                    .derive_simp_atomic_proposition(conjunct)
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
                    let instantiated_proof = match self.apply_step(ProofStep::InstantiateUsing {
                        quantified: surface.clone(),
                        argument: argument.clone(),
                        premises: Some(
                            guard_facts
                                .iter()
                                .map(|(_, surface)| surface.clone())
                                .collect(),
                        ),
                    }) {
                        Ok(proof) => proof,
                        Err(_) => continue,
                    };
                    let conclusion = current.clone();
                    if &conclusion == goal || conclusion.clone() == goal.clone() {
                        // The instantiation added the goal, so it closed it.
                        if instantiated_proof.is_complete() {
                            return Some(instantiated_proof);
                        }
                        continue;
                    }

                    let transport_assumptions = self
                        .facts()
                        .assumptions()
                        .clone()
                        .assume_proposition(conclusion.clone());
                    let Some(transport_derivation) =
                        transport_assumptions.derive_simp_atomic_proposition(goal)
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
                            // `InstantiateUsing` has already checked this
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
                        ClickProposition::At {
                            selector,
                            proposition,
                        } => (Some(selector.clone()), proposition.as_ref()),
                        other => (None, other),
                    };
                    let ClickProposition::ForAll {
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
                    while let ClickProposition::Implies(_, body) = source {
                        source = *body;
                    }
                    if let Some(selector) = selector {
                        source = ClickProposition::At {
                            selector,
                            proposition: Box::new(source),
                        };
                    }
                    transport_surfaces.insert(0, source.clone());
                    let target = self.surface_goal()?.clone();
                    match instantiated_proof.try_fact_transport_from_candidates(
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
    pub(super) fn try_selected_forall_goal(
        &self,
        goal: &Proposition,
        surface_goal: &ClickProposition,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        let tactics = plan_explicit_forall_goal_from_premises(goal, surface_goal, premise_pairs)?;
        if tactics
            .iter()
            .any(|tactic| matches!(tactic, ProofTactic::Have(_)))
        {
            self.try_generated_linear_script(&tactics).ok().flatten()
        } else {
            self.try_planned_explicit_steps(&tactics)
        }
    }

    /// Specializes a universal premise from a caller-owned, bounded Surface
    /// list. Loop preservation uses this for the invariants named at the loop
    /// head: their iteration-entry spellings lower to the historical facts
    /// that a back-edge goal may transport pointwise. Every selected premise
    /// must still be available in this Proof, and the resulting instantiate
    /// and transport operations are checked normally.
    pub(super) fn try_named_forall_goal_from_surfaces(
        &self,
        surfaces: &[ClickProposition],
    ) -> Option<Self> {
        let goal = self.goal()?;
        let surface_goal = self.surface_goal()?;
        let premise_pairs = surfaces
            .iter()
            .filter_map(|surface| {
                let lowered = self
                    .lower_surface_proposition(surface, "named universal premise")
                    .ok()?;
                if !matches!(lowered, Proposition::ForAll { .. })
                    || !self.facts().quantified_fact_available(&lowered)
                {
                    return None;
                }
                Some((lowered, surface.clone()))
            })
            .collect::<Vec<_>>();
        let auxiliary_pairs = surfaces
            .iter()
            .filter_map(|surface| {
                let lowered = self
                    .lower_surface_proposition(surface, "named loop transport premise")
                    .ok()?;
                (!matches!(lowered, Proposition::ForAll { .. })
                    && self.facts().exact_available_across_effects(&lowered, &[]))
                .then_some((lowered, surface.clone()))
            })
            .collect::<Vec<_>>();
        for premise in premise_pairs {
            let mut selected = vec![premise];
            selected.extend(auxiliary_pairs.iter().cloned());
            if let Some(closed) = self.try_selected_forall_goal(goal, surface_goal, &selected) {
                return Some(closed);
            }
        }
        None
    }

    /// Retains the pointwise unchanged-load certificate for a guarded
    /// universal outcome. The kernel derivation has already selected the
    /// finite context premises relevant to this goal; after introducing the
    /// binder and guard, transport searches only those forms plus the
    /// freshly extracted guard leaves.
    pub(super) fn try_selected_unchanged_load_forall_goal(
        &self,
        surface_goal: &ClickProposition,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        self.focused_outcome_data()?;
        let mut cursor = surface_goal;
        let mut proof = self.clone();
        let mut introduced_forall = false;
        while let ClickProposition::ForAll { body, .. } = cursor {
            proof = proof.apply_step(ProofStep::Intro).ok()?;
            cursor = body;
            introduced_forall = true;
        }
        if !introduced_forall {
            return None;
        }
        let ClickProposition::Implies(antecedent, _) = cursor else {
            return None;
        };
        proof = proof.apply_step(ProofStep::Intro).ok()?;
        let mut guard_surfaces = Vec::new();
        collect_surface_conjunct_leaves(antecedent, &mut guard_surfaces);
        for guard in &guard_surfaces {
            proof = proof.apply_step(ProofStep::Extract(guard.clone())).ok()?;
        }
        let target = proof.surface_goal()?.clone();
        let source = old_reflexive_transport_source(&target)?;
        let source_pairs = proof
            .lower_surface_proposition(&source, "unchanged-load transport source")
            .ok()
            .and_then(|kernel| {
                proof
                    .facts()
                    .assumptions()
                    .derive_atomic_proposition(&kernel)
            })
            .and_then(|derivation| {
                let data = proof.focused_outcome_data()?;
                let pairs = derivation
                    .context_premises()
                    .into_iter()
                    .filter_map(|premise| {
                        proof
                            .available_surface_fact(
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
        let anchor_state = view.fixed_state.recorded_snapshots.get(anchor)?;
        let mut anchored_candidates = Vec::new();
        for (kernel, _) in premise_pairs.iter().chain(&source_pairs) {
            let Some(surface) =
                synthesize_surface_proposition(kernel, view.parameter_binding, anchor_state)
            else {
                continue;
            };
            let Ok(surface) = surface_at_snapshot(&surface, anchor) else {
                continue;
            };
            let Some((left, right)) = surface_nonstrict_parts(&surface) else {
                continue;
            };
            let left_is_atomic_variable = match &left {
                ContractExpression::CFragment(CExpression::Variable(_)) => true,
                ContractExpression::At { expression, .. } => matches!(
                    expression.as_ref(),
                    ContractExpression::CFragment(CExpression::Variable(_))
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
        let transported = match proof.try_fixed_state_fact_transport(&source, &target, candidates) {
            Ok(Some(transported)) => transported,
            Ok(None) | Err(_) => return None,
        };
        if transported.is_complete() {
            return Some(transported);
        }
        transported.try_direct_logical_closure().ok().flatten()
    }

    pub(super) fn try_typed_atomic_simp_closure(&self) -> Option<Self> {
        let (goal, derivation, premise_pairs, fixed_state_application_closes_goal) =
            self.selected_simp_derivation(false)?;
        // Resource unfolding records the body conjunction as one checked
        // fact.  Special derivations cite the exact relation leaf, so expose
        // that leaf through the ordinary checked `extract` transition before
        // constructing a certificate.  This keeps certificate premises
        // top-level and preserves the source spelling/snapshot that produced
        // the resource fact.
        match self.extract_special_conjunct_premises(&derivation, &premise_pairs) {
            Ok(Some(extracted)) if extracted.is_complete() => Some(extracted),
            Ok(Some(extracted)) => extracted.check_typed_atomic_simp_candidate(
                &goal,
                &derivation,
                &premise_pairs,
                fixed_state_application_closes_goal,
            ),
            Ok(None) => self.check_typed_atomic_simp_candidate(
                &goal,
                &derivation,
                &premise_pairs,
                fixed_state_application_closes_goal,
            ),
            Err(()) => self.check_typed_atomic_simp_candidate(
                &goal,
                &derivation,
                &premise_pairs,
                fixed_state_application_closes_goal,
            ),
        }
    }

    pub(super) fn extract_special_conjunct_premises(
        &self,
        derivation: &PropositionDerivation,
        premise_pairs: &[(Proposition, ClickProposition)],
    ) -> Result<Option<Self>, ()> {
        let exact_sources = premise_pairs
            .iter()
            .map(|(kernel, surface)| (kernel, surface))
            .collect::<BTreeMap<_, _>>();
        let (surface_facts, premise_anchor) = match self.context.as_ref() {
            ProofContext::Pure(context) => (&context.theorem_context.surface_requirements, None),
            ProofContext::FixedState(context) => {
                (context.surface_propositions, context.premise_anchor.clone())
            }
            ProofContext::Execution(_) => match self.focused_outcome_data() {
                Some(data) => (&data.surface_propositions, data.premise_anchor.clone()),
                None => {
                    let execution = self.execution().ok_or(())?;
                    (
                        &execution.presentation.surface_propositions,
                        frontier_premise_anchor(execution),
                    )
                }
            },
        };
        let mut proof = self.clone();
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
            // load may then denote a different memory snapshot.
            let source = exact_sources
                .get(premise)
                .copied()
                .cloned()
                .or_else(|| {
                    proof.available_surface_fact(surface_facts, premise_anchor.as_ref(), premise)
                })
                .or_else(|| {
                    premise_anchor
                        .as_ref()
                        .and_then(|_| proof.available_surface_fact(surface_facts, None, premise))
                })
                .ok_or(())?;
            let successor = proof
                .apply_step(ProofStep::Extract(source))
                .map_err(|_| ())?;
            // `extract(source)` proves only the proposition to which `source`
            // lowers in this successor's context. A stale presentation record
            // can therefore make the step succeed without publishing the
            // exact premise selected above. Exact top-level membership is the
            // progress measure; polarity or snapshot conversion requires its
            // own checked proof step rather than being assumed here.
            if !successor.checked_facts().contains(premise) {
                return Err(());
            }
            // Extracting a premise can also discharge the goal. Its checked
            // completion is sufficient; later premises require an open goal.
            if successor.is_complete() {
                return Ok(Some(successor));
            }
            proof = successor;
            extracted = true;
        }
        Ok(extracted.then_some(proof))
    }

    /// Searches from exactly the Surface premises named by `simp() using`.
    /// This query cannot add facts or close the goal: it returns only the
    /// descendant obtained by checking the typed atomic decision through the
    /// ordinary Proof transitions.
    pub(in crate::surface::proof) fn try_restricted_simp_closure(
        &self,
        surfaces: &[ClickProposition],
    ) -> Option<Self> {
        if matches!(
            self.goal(),
            Some(Proposition::CMemoryLoadable { .. } | Proposition::CMemoryReadDefined { .. })
        ) && let Some(surface_goal) = self.surface_goal()
        {
            for source in surfaces
                .iter()
                .filter(|surface| matches!(surface, ClickProposition::Loadable { .. }))
            {
                if let Ok(closed) = self.apply_step(ProofStep::TransportUsing {
                    source: source.clone(),
                    target: surface_goal.clone(),
                    premises: surfaces.to_vec(),
                }) && closed.is_complete()
                {
                    return Some(closed);
                }
            }
        }
        // A conjunction is proved one conjunct at a time, each as a checked
        // `have` from the same listed premises, and then closed from the
        // conjuncts it added.
        if let (Some(Proposition::And(_, _)), Some(ClickProposition::And(left, right))) =
            (self.goal(), self.surface_goal())
        {
            let mut proof = self.clone();
            for conjunct in [left, right] {
                let scope = proof.begin_have(conjunct.as_ref().clone()).ok()?;
                proof = scope.try_restricted_simp_closure(surfaces)?.join().ok()?;
            }
            return proof
                .apply_step(ProofStep::Assumption)
                .ok()
                .filter(Proof::is_complete);
        }
        // A named restricted premise may be a leaf of one exact available
        // conjunction (commonly after `unfold(predicate)`). Materialize that
        // leaf through the checked `extract` transition before
        // asking the restricted planner to use it. The returned descendant
        // therefore owns both the semantic fact and the Surface provenance;
        // expansion does not need to reconstruct and check a certificate to
        // justify the premise later.
        let mut proof = self.clone();
        for surface in surfaces {
            let kernel = proof
                .lower_surface_proposition(surface, "restricted simp premise")
                .ok()?;
            proof = proof.materialize_selected_resource_separation(&kernel)?;
            if !proof.facts().contains_top_level(&kernel)
                && !normalizes_context_free(&kernel)
                && proof.facts().contains_proper_conjunct(&kernel)
            {
                proof = proof.apply_step(ProofStep::Extract(surface.clone())).ok()?;
                if proof.is_complete() {
                    return Some(proof);
                }
            }
        }
        let goal = proof.goal()?;
        let premise_pairs = surfaces
            .iter()
            .map(|surface| {
                let kernel = proof
                    .lower_surface_proposition(surface, "restricted simp premise")
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
        // A listed equality under a definedness guard the list does not
        // state: prove the guard from the other listed premises, extract the
        // consequent, and continue from the list with the consequent in the
        // implication's place.
        if let Some(closed) = proof.try_restricted_guarded_consequent(surfaces, &premise_pairs) {
            return Some(closed);
        }
        // A listed implication and its listed antecedent justify extracting
        // the consequent. Keep this route explicitly tied to `using`, rather
        // than allowing an unrelated ambient implication to discharge it.
        if premise_pairs.iter().any(|(premise, _)| {
            matches!(premise, Proposition::Implies(antecedent, consequent)
                if consequent.as_ref() == goal
                    && premise_pairs.iter().any(|(selected, _)| selected == antecedent.as_ref()))
        }) && let Some(surface_goal) = proof.surface_goal()
            && let Ok(extracted) = proof.apply_step(ProofStep::Extract(surface_goal.clone()))
        {
            if extracted.is_complete() {
                return Some(extracted);
            }
            if let Ok(closed) = extracted.apply_step(ProofStep::Assumption)
                && closed.is_complete()
            {
                return Some(closed);
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
        let theorem_application_closes_goal =
            !matches!(self.context.as_ref(), ProofContext::Execution(_));
        let try_typed_derivation = || {
            let SimpEvidence::Derivation(derivation) =
                plan_simp_certificate(goal, &assumptions_from_propositions(&restricted))?
            else {
                return None;
            };
            proof.check_typed_atomic_simp_candidate(
                goal,
                &derivation,
                &premise_pairs,
                theorem_application_closes_goal,
            )
        };
        let typed_first = signed_order || signed_definedness_operands(goal).is_some();
        if typed_first && let Some(closed) = try_typed_derivation() {
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
            // NormalizeUsing can query its ambient graph. Restricted search
            // must first establish that this candidate works in the selected
            // context, just as its other planners use `restricted` below.
            // Build only from the explicit input; never scan ambient facts.
            if !conditions.is_empty()
                && crate::kernel::proof::fact_reasoning::normalize_using_conditions(
                    goal,
                    &condition_kernels,
                    &crate::kernel::proof::ProofFacts::from_ordered(&restricted),
                )
                .is_ok()
                && let Ok(closed) = proof.apply_step(ProofStep::NormalizeUsing(conditions))
                && closed.is_complete()
            {
                return Some(closed);
            }
        }
        // A definedness goal is left to the typed candidates and the
        // `int32_defined` / `int64_defined` closer below, so an
        // operand-specific theorem application keeps its priority.
        if let Some(surface_goal) = proof.surface_goal()
            && signed_definedness_operands(goal).is_none()
            && let Some(plan) = plan_special_arithmetic_certificate(goal, &restricted)
        {
            let certificate = special_plan_to_surface_certificate(
                &plan,
                &premise_pairs
                    .iter()
                    .map(|(_, surface)| surface.clone())
                    .collect::<Vec<_>>(),
                surface_goal,
            );
            if let Ok(closed) = proof.apply_step(ProofStep::ArithmeticCertificate(certificate))
                && closed.is_complete()
            {
                return Some(closed);
            }
        }
        if let Some(surface_goal) = proof.surface_goal()
            // The kernel lowering has already established the exact carrier
            // and checked terms for this goal.  Use that fact as the routing
            // predicate so fixed-state and execution proofs receive the same
            // certificate path; source-side guesses would miss converted C
            // values and could route a machine comparison incorrectly.
            && integer_affine_claim(goal).is_some()
            && restricted
                .iter()
                .all(|premise| integer_affine_claim(premise).is_some())
            && let Some(plan) = plan_integer_affine_certificate(goal, &restricted)
            && let Some(certificate) =
                integer_plan_to_surface_certificate(&plan, &premise_pairs, surface_goal)
            && let Ok(closed) = proof.apply_step(ProofStep::ArithmeticCertificate(
                ArithmeticCertificate::integer(certificate),
            ))
            && closed.is_complete()
        {
            return Some(closed);
        }
        // The selected context has not changed, so the ordinary derivation
        // slot need not repeat the early attempt.
        let typed = if typed_first {
            None
        } else {
            try_typed_derivation()
        };
        typed
            .or_else(|| proof.try_restricted_equality_rewrite_chain(&premise_pairs))
            .or_else(|| proof.try_outcome_anchored_order_transitivity(&premise_pairs))
            .or_else(|| proof.try_outcome_anchored_increment_order(&premise_pairs))
            // An exact selected premise or context-free normalization may
            // close directly. An arbitrary ambient `assumption` must remain
            // invisible through this explicitly restricted boundary.
            .or_else(|| proof.try_typed_atomic_simp_from_selected_premises(&premise_pairs))
            // An `int32` or `int64` definedness goal: the listed premises that
            // bound an operand by a constant, checked by the `int32_defined` /
            // `int64_defined` rule. It runs after the operand-specific `int32`
            // theorem applications above, which keep their checked form.
            .or_else(|| {
                proof
                    .try_restricted_signed_definedness_closure(&premise_pairs)
                    .ok()
                    .flatten()
            })
    }

    fn try_selected_pointer_inequality_rewrite(
        &self,
        goal: &Proposition,
        premises: &[(Proposition, ClickProposition)],
    ) -> Option<Self> {
        if !matches!(
            goal,
            Proposition::ConditionIs(ConditionTerm::PointerEqual(_, _), false)
        ) {
            return None;
        }
        for (kernel, source) in premises {
            if !matches!(
                kernel,
                Proposition::ConditionIs(ConditionTerm::PointerEqual(_, _), true)
            ) {
                continue;
            }
            let deanchored = match source {
                ClickProposition::Comparison {
                    left:
                        ContractExpression::At {
                            selector: left_selector,
                            expression: left,
                        },
                    operator: ComparisonOperator::Equal,
                    right:
                        ContractExpression::At {
                            selector: right_selector,
                            expression: right,
                        },
                } if left_selector == right_selector => Some(ClickProposition::Comparison {
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
                    let Ok(rewritten) = self.apply_step(ProofStep::Rewrite(oriented)) else {
                        continue;
                    };
                    if let Ok(Some(closed)) = rewritten.try_direct_logical_closure() {
                        return Some(closed);
                    }
                }
            }
        }
        None
    }

    pub(super) fn check_typed_atomic_simp_candidate(
        &self,
        goal: &Proposition,
        derivation: &PropositionDerivation,
        premise_pairs: &[(Proposition, ClickProposition)],
        fixed_state_application_closes_goal: bool,
    ) -> Option<Self> {
        let surface_goal = self.surface_goal();
        let tactics = recorded_signed_order_pairs(derivation, premise_pairs)
            .and_then(|ordered| {
                plan_recorded_signed_order_path_for_context(
                    goal,
                    &ordered,
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let (unsigned, ordered) = recorded_wide_order_pairs(derivation, premise_pairs)?;
                plan_recorded_wide_order_path(
                    unsigned,
                    &ordered,
                    fixed_state_application_closes_goal,
                )
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
                let plan = plan_signed_arithmetic_certificate(goal, &kernels)?;
                let certificate =
                    self.signed_plan_to_surface_certificate(&plan, premise_pairs, surface_goal?)?;
                Some(vec![ProofTactic::ArithmeticCertificate(
                    ArithmeticCertificate {
                        family: ArithmeticCertificateFamily::SignedInt32(certificate),
                    },
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
            .or_else(|| {
                plan_explicit_loadability_transport(goal, self.surface_goal()?, premise_pairs)
            })
            .or_else(|| plan_pointer_advanced_load_equality(goal, premise_pairs))
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation.int32_increment_upper_bound_step()?.premise()],
                    premise_pairs,
                    false,
                )?;
                for_context(
                    plan_explicit_increment_upper_bound(goal, &recorded),
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation
                        .int32_increment_constant_upper_bound_step()?
                        .premise()],
                    premise_pairs,
                    false,
                )?;
                for_context(
                    plan_explicit_increment_constant_upper_bound(goal, &recorded),
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation
                        .int32_increment_strictly_increases_step()?
                        .premise()],
                    premise_pairs,
                    false,
                )?;
                for_context(
                    plan_explicit_increment_strictly_increases(goal, &recorded),
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation
                        .int32_one_plus_strictly_increases_step()?
                        .premise()],
                    premise_pairs,
                    false,
                )?;
                for_context(
                    plan_explicit_one_plus_strictly_increases(goal, &recorded),
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation
                        .int32_increment_below_max_is_defined_step()?
                        .premise()],
                    premise_pairs,
                    false,
                )?;
                for_context(
                    plan_explicit_increment_below_max_is_defined(goal, &recorded),
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation
                        .int32_one_plus_below_max_is_defined_step()?
                        .premise()],
                    premise_pairs,
                    false,
                )?;
                for_context(
                    plan_explicit_one_plus_below_max_is_defined(goal, &recorded),
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let (first, second) = derivation.int32_nonnegative_add_within_max_steps()?;
                let recorded = recorded_premise_pairs(
                    [first.premise(), second.premise()],
                    premise_pairs,
                    false,
                )?;
                for_context(
                    plan_explicit_nonnegative_add_within_max_is_defined(goal, &recorded),
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let (first, second) = derivation.int32_nonnegative_subtract_within_value_steps()?;
                let recorded = recorded_premise_pairs(
                    [first.premise(), second.premise()],
                    premise_pairs,
                    false,
                )?;
                for_context(
                    plan_explicit_nonnegative_subtract_within_value_is_defined(goal, &recorded),
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let (first, second) = derivation.int32_increment_lower_bound_steps()?;
                let recorded = recorded_premise_pairs(
                    [first.premise(), second.premise()],
                    premise_pairs,
                    false,
                )?;
                for_context(
                    plan_explicit_increment_lower_bound(goal, &recorded),
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let (first, second) =
                    derivation.int32_increment_greater_equal_lower_bound_steps()?;
                let recorded = recorded_premise_pairs(
                    [first.premise(), second.premise()],
                    premise_pairs,
                    false,
                )?;
                for_context(
                    plan_explicit_increment_greater_equal_lower_bound(goal, &recorded),
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let (first, second) =
                    derivation.int32_increment_strict_greater_lower_bound_steps()?;
                let recorded = recorded_premise_pairs(
                    [first.premise(), second.premise()],
                    premise_pairs,
                    false,
                )?;
                for_context(
                    plan_explicit_increment_strict_greater_lower_bound(goal, &recorded),
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let (first, second) =
                    derivation.int32_increment_strict_greater_from_strict_lower_steps()?;
                let recorded = recorded_premise_pairs(
                    [first.premise(), second.premise()],
                    premise_pairs,
                    false,
                )?;
                for_context(
                    plan_explicit_increment_strict_greater_from_strict_lower(goal, &recorded),
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let (first, second) = derivation.int32_increment_preserves_order_steps()?;
                let recorded = recorded_premise_pairs(
                    [first.premise(), second.premise()],
                    premise_pairs,
                    false,
                )?;
                for_context(
                    plan_explicit_increment_preserves_order(goal, &recorded),
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation
                        .int32_positive_predecessor_is_nonnegative_step()?
                        .premise()],
                    premise_pairs,
                    false,
                )?;
                for_context(
                    plan_explicit_positive_predecessor_is_nonnegative(goal, &recorded),
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation
                        .int32_positive_predecessor_strictly_decreases_step()?
                        .premise()],
                    premise_pairs,
                    false,
                )?;
                for_context(
                    plan_explicit_positive_predecessor_strictly_decreases(goal, &recorded),
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let (first, second) =
                    derivation.int32_nonnegative_predecessor_upper_bound_steps()?;
                let recorded = recorded_premise_pairs(
                    [first.premise(), second.premise()],
                    premise_pairs,
                    false,
                )?;
                plan_recorded_int32_nonnegative_predecessor_upper_bound_for_context(
                    goal,
                    &recorded,
                    fixed_state_application_closes_goal,
                )
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
                plan_recorded_int32_equal_one_predecessor_for_context(
                    goal,
                    derivation,
                    &recorded,
                    fixed_state_application_closes_goal,
                )
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
                plan_recorded_int32_one_le_predecessor_for_context(
                    goal,
                    &recorded,
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let (first, second) = derivation.int32_le_and_not_lt_implies_equality_premises()?;
                let recorded = recorded_premise_pairs([first, second], premise_pairs, true)?;
                for_context(
                    plan_explicit_le_and_not_lt_implies_eq(goal, &recorded),
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let (first, second) = derivation.int32_ge_and_not_gt_implies_equality_premises()?;
                let recorded = recorded_premise_pairs([first, second], premise_pairs, true)?;
                for_context(
                    plan_explicit_ge_and_not_gt_implies_eq(goal, &recorded),
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation.int32_positive_is_nonnegative_step()?.premise()],
                    premise_pairs,
                    false,
                )?;
                for_context(
                    plan_explicit_positive_is_nonnegative(goal, &recorded),
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation.int32_successor_le_implies_lt_step()?.premise()],
                    premise_pairs,
                    false,
                )?;
                plan_recorded_int32_successor_le_implies_lt_for_context(
                    goal,
                    &recorded,
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation
                        .int32_constant_lower_bound_weakening_step()?
                        .premise()],
                    premise_pairs,
                    false,
                )?;
                for_context(
                    plan_explicit_le_transitive_constant_lower(goal, &recorded),
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let recorded = recorded_premise_pairs(
                    [derivation
                        .int32_negated_strict_successor_bound_step()?
                        .premise()],
                    premise_pairs,
                    true,
                )?;
                plan_recorded_int32_negated_strict_successor_bound_for_context(
                    goal,
                    &recorded,
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let (first, second) = derivation.int32_le_and_neq_implies_strict_premises()?;
                let recorded = recorded_premise_pairs([first, second], premise_pairs, true)?;
                for_context(
                    plan_explicit_le_and_neq_implies_lt(goal, &recorded),
                    fixed_state_application_closes_goal,
                )
            })
            .or_else(|| {
                let kernels = premise_pairs
                    .iter()
                    .map(|(premise, _)| premise.clone())
                    .collect::<Vec<_>>();
                let surface_goal = self.surface_goal()?;
                let plan = plan_special_arithmetic_certificate(goal, &kernels)?;
                Some(vec![ProofTactic::ArithmeticCertificate(
                    special_plan_to_surface_certificate(
                        &plan,
                        &premise_pairs
                            .iter()
                            .map(|(_, surface)| surface.clone())
                            .collect::<Vec<_>>(),
                        surface_goal,
                    ),
                )])
            });
        let Some(tactics) = tactics else {
            if matches!(goal, Proposition::CMemoryLoadable { .. }) {
                attempt::record_search_note(
                    "simp view certificate planning",
                    "no source certificate plan was produced from the resolved derivation premises",
                );
            }
            return None;
        };
        // The planner selects only Surface-expressible explicit operations.
        // Apply those through the same recursive Proof driver used by
        // authoritative source scripts; the plan is provenance input, not an
        // independently interpreted semantic certificate.
        let checked = self.try_generated_linear_script(&tactics);
        if matches!(goal, Proposition::CMemoryLoadable { .. })
            && let Err(error) = &checked
        {
            attempt::record_search_note("simp view certificate checking", error.raw_summary());
        }
        let proof = attempt::candidate_outcome(checked)
            .ok()
            .flatten()
            .flatten()?;
        proof.focused_discharged().then_some(proof)
    }

    pub(super) fn simp_failure(&self) -> ClickError {
        // A range-loadability goal has a reason a reader can act on, in the
        // spelling they wrote it with. The lowered rendering below would show
        // them a byte extent over an internal pointer name instead.
        if let Some(reason) = self.unproved_loadable_range_goal_reason() {
            return self.step_error(format!(
                "`simp` failed for `{}`: {reason}",
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
                        condition_kind(condition)
                    ),
                    Proposition::ConditionIs(condition, false) => format!(
                        "the negation of an internal {} goal with no Click spelling",
                        condition_kind(condition)
                    ),
                    _ => format!(
                        "the goal {}",
                        describe_pure_fact(goal, ParameterBinding::default())
                    ),
                })
            })
            .unwrap_or_else(|| "a goal that is not a proposition".into());
        self.step_error(format!(
            "`simp` failed for `{}`: could not establish {goal}{}",
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
        (crate::surface::checking::simp_condition_without_assumptions(condition)
            == Some(!*expected))
        .then(|| {
            "it is false at this point: the values its reads resolve to here refute it, so no \
             further fact proves it."
                .to_string()
        })
    }

    /// The one explanation for "the goal and an available fact spell alike
    /// and read different versions", which is what a `simp` over a term that
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
        crate::surface::diagnostics::describe_proposition_version_mismatch(
            goal,
            &premises,
            "the available fact was stated",
            ParameterBinding::new(parameters, arguments),
        )
    }

    /// Plan a numeric induction application against the current checked facts.
    /// Each missing domain premise is a checked have; no source-wide premise
    /// pool or parallel induction executor participates in acceptance.
    fn apply_smart_induction(
        &self,
        hypothesis: &str,
        arguments: &[ContractExpression],
    ) -> Result<Self, ClickError> {
        let ProofContext::Pure(context) = self.context.as_ref() else {
            return Err(self.step_error("induction application requires a pure theorem proof"));
        };
        let Some(setup) = context.induction_setup.as_ref() else {
            return Err(self.step_error("induction hypothesis is not active"));
        };
        if hypothesis != setup.hypothesis {
            return Err(self.step_error(format!("unknown induction hypothesis `{hypothesis}`")));
        }
        let [argument] = arguments else {
            return Err(self.step_error(format!(
                "induction hypothesis `{hypothesis}` expects one argument"
            )));
        };
        let premises = pure_theorems::induction_application_surface_premises(setup, argument)?;
        let mut proof = self.clone();
        for premise in &premises {
            let lowered = proof.lower_cited_surface_proposition(premise, "induction premise")?;
            if proof.facts().contains(&lowered) {
                continue;
            }
            let scope = proof.begin_have(premise.clone())?;
            let Some(checked) = scope.try_simp_closure()? else {
                return Err(proof.step_error(format!(
                    "induction hypothesis `{hypothesis}` could not prove premise `{}`",
                    describe_click_proposition(premise),
                )));
            };
            proof = checked.join()?;
        }
        proof.apply_step(ProofStep::ApplyInduction {
            hypothesis: hypothesis.to_string(),
            arguments: arguments.to_vec(),
            premises,
        })
    }

    /// Checks source whose caller has already selected this Proof driver as
    /// the semantic authority. Explicit operation failures propagate instead
    /// of being converted into a compatibility miss; recursive scopes and
    /// branch arms inherit the same rule.
    pub(in crate::surface::proof) fn try_authoritative_linear_script(
        &self,
        tactics: &[ProofTactic],
    ) -> Result<Option<Self>, ClickError> {
        self.try_authoritative_linear_script_reporting(tactics, &mut None, None)
    }

    /// [`Self::try_authoritative_linear_script`], also reporting why the body
    /// declined. A caller that turns the decline into a user-facing error
    /// needs the written step to name, not only that some route said no.
    pub(in crate::surface::proof) fn try_authoritative_linear_script_reporting(
        &self,
        tactics: &[ProofTactic],
        declined: &mut Option<LinearScriptDecline>,
        unfinished: Option<&mut Option<Self>>,
    ) -> Result<Option<Self>, ClickError> {
        // Address each tactic's diagnostics by its position in the block the
        // user wrote, so a failure inside one `have` body is distinguishable
        // from the same failure inside another.
        let sites = (0..tactics.len())
            .map(|index| self.site().at_block_position(index))
            .collect::<Vec<_>>();
        self.try_addressed_linear_script(tactics, &sites, declined, unfinished)
    }

    /// Checks an explicit planner candidate without attributing its block
    /// positions to a written source body, then restores the caller's site.
    fn try_generated_linear_script(
        &self,
        tactics: &[ProofTactic],
    ) -> Result<Option<Self>, ClickError> {
        self.at_source_tactic(usize::MAX)
            .try_authoritative_linear_script(tactics)
            .map(|proof| proof.map(|proof| proof.at_site(self.site())))
    }

    /// The linear script runner. `sites[index]` is where `tactics[index]`
    /// was written. A proof `if` or `cases` arm is checked together with the
    /// tactics after it, so its script joins the arm's own tactics, addressed
    /// inside that arm, to the continuation, which keeps the addresses it has
    /// in the enclosing block: every written tactic reports its own source
    /// position however many arms check it.
    pub(in crate::surface::proof) fn try_addressed_linear_script(
        &self,
        tactics: &[ProofTactic],
        sites: &[ProofStepSite],
        declined: &mut Option<LinearScriptDecline>,
        unfinished: Option<&mut Option<Self>>,
    ) -> Result<Option<Self>, ClickError> {
        self.run_addressed_linear_script(tactics, sites, declined, unfinished)
    }

    /// [`Self::try_authoritative_linear_script`], also keeping the proof a
    /// body left with its focused goal still open, so a caller refusing the
    /// body can name the goal it stopped at. Only a script that ran every
    /// written step (in its own block or in a proof `if`, `cases` or `both`
    /// arm) leaves one; a declined step leaves none.
    pub(in crate::surface::proof) fn try_authoritative_linear_script_leaving_open(
        &self,
        tactics: &[ProofTactic],
        unfinished: &mut Option<Self>,
    ) -> Result<Option<Self>, ClickError> {
        self.try_authoritative_linear_script_reporting(tactics, &mut None, Some(unfinished))
    }

    /// Runs the arms of one `cases` to completion. The kernel splits a
    /// disjunction in two, so more than two arms split the leading arms'
    /// disjunction against the last arm and recurse into the leading branch;
    /// each arm still runs at the sites of its own source block.
    fn run_case_arms(
        &self,
        arms: &[CaseArmScript<'_>],
        mut unfinished: Option<&mut Option<Self>>,
    ) -> Result<Option<Self>, ClickError> {
        let (last, leading) = arms.split_last().expect("`cases` has arms");
        let disjunction = leading.iter().skip(1).fold(
            leading
                .first()
                .expect("`cases` has at least two arms")
                .assumption
                .clone(),
            |disjunction, arm| {
                ClickProposition::Or(Box::new(disjunction), Box::new(arm.assumption.clone()))
            },
        );
        let disjunction =
            ClickProposition::Or(Box::new(disjunction), Box::new(last.assumption.clone()));
        let (split_proof, split, ids) = self.split_focused_cases(disjunction.clone())?;
        let marker = split_proof.checkpoint();
        let leading_branch = split_proof.focus_branch(ids[0])?;
        let leading_done = match leading {
            [only] => leading_branch.run_addressed_linear_script(
                &only.tactics,
                &only.sites,
                &mut None,
                unfinished.as_deref_mut(),
            )?,
            _ => leading_branch.run_case_arms(leading, unfinished.as_deref_mut())?,
        };
        let Some(leading_done) = leading_done else {
            return Ok(None);
        };
        let Some(all_done) = leading_done
            .focus_branch(ids[1])?
            .run_addressed_linear_script(&last.tactics, &last.sites, &mut None, unfinished)?
        else {
            return Ok(None);
        };
        all_done
            .join_focused_cases(&marker, split, ids, disjunction)
            .map(Some)
    }

    #[allow(clippy::too_many_arguments)]
    fn run_pure_match_group(
        &self,
        plan: &super::proof_object::PureMatchPlan,
        source: &ProofMatch,
        indices: &[usize],
        arm_tactics: &[Vec<ProofTactic>],
        arm_sites: &[Vec<ProofStepSite>],
        certificates: &mut Vec<ProofCertificate>,
        trace: &mut Option<crate::surface::proof_trace::TraceMatch>,
        mut unfinished: Option<&mut Option<Self>>,
    ) -> Result<Option<Self>, ClickError> {
        if let [index] = indices {
            let arm = self.enter_pure_match_case(plan, *index)?;
            let marker = arm.checkpoint();
            let written = source.arms[*index].tactics.len();
            let mut pending = Some(arm.clone());
            let closed = if written == 0 {
                None
            } else {
                arm.run_addressed_linear_script(
                    &arm_tactics[*index][..written],
                    &arm_sites[*index][..written],
                    &mut None,
                    Some(&mut pending),
                )?
            };
            let Some(body_done) = closed.or(pending) else {
                return Ok(None);
            };
            let body_done = body_done.leave_pure_match_case(plan);
            let done = if written < arm_tactics[*index].len() {
                let Some(done) = body_done.run_addressed_linear_script(
                    &arm_tactics[*index][written..],
                    &arm_sites[*index][written..],
                    &mut None,
                    unfinished,
                )?
                else {
                    return Ok(None);
                };
                done
            } else if body_done.focused_discharged() {
                body_done
            } else {
                if let Some(unfinished) = unfinished {
                    *unfinished = Some(body_done);
                }
                return Ok(None);
            };
            certificates.push(done.certificate_since(&marker)?);
            if let Some(trace) = trace {
                trace.arms[*index] = Some(done.pure_match_arm_trace(&arm, &marker, source, *index));
            }
            return Ok(Some(done.leave_pure_match_case(plan)));
        }
        let middle = indices.len() / 2;
        let (split_proof, split, ids) = self.split_pure_match_group()?;
        let marker = split_proof.checkpoint();
        let Some(left_done) = split_proof.focus_branch(ids[0])?.run_pure_match_group(
            plan,
            source,
            &indices[..middle],
            arm_tactics,
            arm_sites,
            certificates,
            trace,
            unfinished.as_deref_mut(),
        )?
        else {
            return Ok(None);
        };
        let Some(done) = left_done.focus_branch(ids[1])?.run_pure_match_group(
            plan,
            source,
            &indices[middle..],
            arm_tactics,
            arm_sites,
            certificates,
            trace,
            unfinished,
        )?
        else {
            return Ok(None);
        };
        done.join_focused_both(&marker, split, ids).map(Some)
    }

    fn run_addressed_linear_script(
        &self,
        tactics: &[ProofTactic],
        sites: &[ProofStepSite],
        declined: &mut Option<LinearScriptDecline>,
        mut unfinished: Option<&mut Option<Self>>,
    ) -> Result<Option<Self>, ClickError> {
        debug_assert_eq!(tactics.len(), sites.len());
        let finish = |proof: Self, unfinished: Option<&mut Option<Self>>| {
            if proof.focused_discharged() {
                Some(proof)
            } else {
                if let Some(unfinished) = unfinished {
                    *unfinished = Some(proof);
                }
                None
            }
        };
        let pure_source = matches!(self.context.as_ref(), ProofContext::Pure(_));
        if tactics.is_empty() {
            *declined = Some(LinearScriptDecline::Shape);
            return Ok(None);
        }
        let arm_sites = |index: usize, arm: usize, name: &'static str, written: usize| {
            (0..written)
                .map(|position| sites[index].in_arm(arm, name, position))
                .chain(sites[index + 1..].iter().cloned())
                .collect::<Vec<_>>()
        };

        let mut proof = self.clone();
        for (index, tactic) in tactics.iter().enumerate() {
            proof = proof.at_site(&sites[index]);
            let _timing = if pure_source {
                proof
                    .site()
                    .written_source_tactic_path()
                    .and_then(|path| TacticTiming::pure_source(proof.claim_label(), path, tactic))
            } else {
                None
            };
            let nested_capture = proof.begin_nested_tactic_capture();
            if proof.focused_discharged() {
                // A closer after a step that already discharged the goal (a
                // `transport` whose target is the goal, an exact theorem
                // conclusion, an `unfold` whose refreshed goal was already
                // an available fact) asserts a closed judgment: a harmless
                // no-op that emits no redundant certificate step. That is
                // `assumption`, `simp`, and the context-free `normalize`,
                // in any position, so `unfold(f(x)); normalize();` means the
                // same whether or not the unfold alone closed the goal. Any
                // other suffix after closure is a declined shape, named with
                // the tactic that closed the goal.
                if matches!(
                    tactic,
                    ProofTactic::Assumption
                        | ProofTactic::Simp
                        | ProofTactic::Normalize
                        | ProofTactic::NormalizeUsing(_)
                ) {
                    // The harmless closer checks nothing: its expansion is
                    // empty.
                    if let Some(capture) = nested_capture {
                        capture.finish(&proof);
                    }
                    continue;
                }
                let closer = index
                    .checked_sub(1)
                    .and_then(|previous| tactics.get(previous))
                    .map_or("an earlier tactic".to_string(), |closer| {
                        format!("`{}`", tactic_name(closer))
                    });
                return Err(proof.step_error(format!(
                    "`{}` follows a goal-closing tactic: {closer} already closed this goal, so only `assumption`, `simp`, or `normalize` may follow it",
                    tactic_name(tactic)
                )));
            }
            // A step that adds a fact can close the goal before a written
            // suffix. Retain that completed step as a checked have, keeping
            // the outer goal open so every remaining explicit step is
            // checked; only a final step, or one followed by a harmless
            // closer, leaves the goal closed.
            let retain_application = matches!(
                tactic,
                ProofTactic::ApplyTheoremUsing { .. }
                    | ProofTactic::ApplyInductionUsing { .. }
                    | ProofTactic::ApplyInduction { .. }
                    | ProofTactic::InstantiateUsing { .. }
                    | ProofTactic::Transport { .. }
                    | ProofTactic::TransportUsing { .. }
                    | ProofTactic::LetSatisfy(_)
            ) && tactics
                .get(index + 1)
                .is_some_and(|next| !matches!(next, ProofTactic::Assumption | ProofTactic::Simp));
            let retain_application = retain_application
                || (matches!(
                    tactic,
                    ProofTactic::Extract(_) | ProofTactic::ApplyTheorem(_)
                ) && tactics.get(index + 1).is_some_and(|next| {
                    !matches!(next, ProofTactic::Assumption | ProofTactic::Simp)
                }));
            let before_application = retain_application.then(|| proof.clone());
            match tactic {
                ProofTactic::ApplyInduction {
                    hypothesis,
                    arguments,
                } => {
                    proof = proof.apply_smart_induction(hypothesis, arguments)?;
                }
                ProofTactic::ApplyTheorem(application) => {
                    proof = proof.apply_theorem_application(application)?;
                }
                ProofTactic::Simp => {
                    let mut search = attempt::search_scope("written simp");
                    let (selected, checks) =
                        crate::surface::proof_diagnostics::capture_check_observations(|| {
                            proof.try_simp_closure()
                        });
                    let selected = match selected {
                        Ok(selected) => selected,
                        Err(error) => {
                            return Err(error
                                .with_check_observations(checks)
                                .with_search_failures(search.finish()));
                        }
                    };
                    let Some(closed) = selected else {
                        if tactics[..index].iter().any(|previous| {
                            matches!(previous, ProofTactic::Witness(_) | ProofTactic::Choose(_))
                        }) {
                            return Err(proof.step_error(
                                "checked `simp` after witness/choose could not close the remaining witness obligations; split conjunctions and discharge each definedness condition explicitly",
                            ).with_search_failures(search.finish()));
                        }
                        return Err(proof
                            .simp_failure()
                            .with_check_observations(checks)
                            .with_search_failures(search.finish()));
                    };
                    search.succeed();
                    proof = closed;
                }
                ProofTactic::SimpUsing(simp) => {
                    let (selected, checks) =
                        crate::surface::proof_diagnostics::capture_check_observations(|| {
                            proof.try_restricted_simp_closure(&simp.premises)
                        });
                    check_verification_deadline()?;
                    let Some(closed) = selected else {
                        if tactics[..index].iter().any(|previous| {
                            matches!(previous, ProofTactic::Witness(_) | ProofTactic::Choose(_))
                        }) {
                            return Err(proof.step_error(
                                "checked `simp` after witness/choose could not close the remaining witness obligations; split conjunctions and discharge each definedness condition explicitly",
                            ));
                        }
                        return Err(proof.step_error("`simp() using` could not prove the current goal from only its listed premises").with_check_observations(checks));
                    };
                    proof = closed;
                }
                ProofTactic::Have(have) => {
                    let scope = proof.begin_have(have.proposition.clone())?;
                    let source_proof = have.checking_proof();
                    let selected = match source_proof.as_ref() {
                        SourceProof::Tactic(SmartTactic::Auto) => scope.try_auto_fact_closure()?,
                        SourceProof::Default | SourceProof::Tactic(SmartTactic::Simp) => {
                            scope.try_simp_closure()?
                        }
                        SourceProof::Script(body) => scope.try_authoritative_linear_script(body)?,
                    };
                    let Some(selected) = selected else {
                        *declined = Some(LinearScriptDecline::Step(index));
                        return Ok(None);
                    };
                    proof = selected.join()?;
                }
                ProofTactic::If(proof_if) => {
                    let then_tactics =
                        script_arm_with_continuation(&proof_if.then_tactics, &tactics[index + 1..]);
                    let else_tactics =
                        script_arm_with_continuation(&proof_if.else_tactics, &tactics[index + 1..]);
                    let then_sites = arm_sites(index, 0, "then", proof_if.then_tactics.len());
                    let else_sites = arm_sites(index, 1, "else", proof_if.else_tactics.len());
                    let (split_proof, split, ids) =
                        proof.split_focused_if(proof_if.condition.clone())?;
                    let marker = split_proof.checkpoint();
                    let Some(then_done) = split_proof
                        .focus_branch(ids[0])?
                        .run_addressed_linear_script(
                            &then_tactics,
                            &then_sites,
                            &mut None,
                            unfinished.as_deref_mut(),
                        )?
                    else {
                        *declined = Some(LinearScriptDecline::Step(index));
                        return Ok(None);
                    };
                    let Some(both_done) = then_done
                        .focus_branch(ids[1])?
                        .run_addressed_linear_script(
                            &else_tactics,
                            &else_sites,
                            &mut None,
                            unfinished.as_deref_mut(),
                        )?
                    else {
                        *declined = Some(LinearScriptDecline::Step(index));
                        return Ok(None);
                    };
                    proof = both_done
                        .join_focused_if(&marker, split, ids, proof_if.condition.clone())?
                        .at_site(&sites[index]);
                    // Both arms checked the tactics after the `if`; a trace
                    // to one of those follows the first arm.
                    proof
                        .note_trace_join_continuation_arm((index + 1 < tactics.len()).then_some(0));
                    return Ok(finish(proof, unfinished));
                }
                ProofTactic::Both(both) => {
                    // A `both` arm proves one conjunct and continues nothing.
                    let own_arm_sites = |arm: usize, name: &'static str, written: usize| {
                        (0..written)
                            .map(|position| sites[index].in_arm(arm, name, position))
                            .collect::<Vec<_>>()
                    };
                    let left_sites = own_arm_sites(0, "left", both.left_tactics.len());
                    let right_sites = own_arm_sites(1, "right", both.right_tactics.len());
                    let (split_proof, split, ids) = proof.split_focused_both()?;
                    let marker = split_proof.checkpoint();
                    let Some(left_done) = split_proof
                        .focus_branch(ids[0])?
                        .run_addressed_linear_script(
                            &both.left_tactics,
                            &left_sites,
                            &mut None,
                            unfinished.as_deref_mut(),
                        )?
                    else {
                        *declined = Some(LinearScriptDecline::Step(index));
                        return Ok(None);
                    };
                    let Some(both_done) = left_done
                        .focus_branch(ids[1])?
                        .run_addressed_linear_script(
                            &both.right_tactics,
                            &right_sites,
                            &mut None,
                            unfinished.as_deref_mut(),
                        )?
                    else {
                        *declined = Some(LinearScriptDecline::Step(index));
                        return Ok(None);
                    };
                    proof = both_done
                        .join_focused_both(&marker, split, ids)?
                        .at_site(&sites[index]);
                }
                ProofTactic::Match(source) if pure_source => {
                    let marker = proof.checkpoint();
                    let (prepared, plan) = proof.prepare_pure_match(source)?;
                    let bodies = source
                        .arms
                        .iter()
                        .map(|arm| {
                            script_arm_with_continuation(&arm.tactics, &tactics[index + 1..])
                                .into_owned()
                        })
                        .collect::<Vec<_>>();
                    let addressed = source
                        .arms
                        .iter()
                        .enumerate()
                        .map(|(arm, body)| arm_sites(index, arm, "case", body.tactics.len()))
                        .collect::<Vec<_>>();
                    let mut certificates = Vec::new();
                    let mut trace = proof.new_pure_match_trace(source);
                    let Some(done) = prepared.run_pure_match_group(
                        &plan,
                        source,
                        &(0..source.arms.len()).collect::<Vec<_>>(),
                        &bodies,
                        &addressed,
                        &mut certificates,
                        &mut trace,
                        unfinished.as_deref_mut(),
                    )?
                    else {
                        *declined = Some(LinearScriptDecline::Step(index));
                        return Ok(None);
                    };
                    proof = done
                        .finish_execution_match(&marker, source, certificates, trace)?
                        .at_site(&sites[index]);
                    proof
                        .note_trace_join_continuation_arm((index + 1 < tactics.len()).then_some(0));
                    return Ok(finish(proof, unfinished));
                }
                ProofTactic::Cases(proof_cases) => {
                    // Each arm runs its own tactics and then the rest of the
                    // script, at the source sites of its own block.
                    let arm_names = if proof_cases.arms().len() == 2 {
                        ["left", "right"].as_slice()
                    } else {
                        ["case"].as_slice()
                    };
                    let arms = proof_cases
                        .arms()
                        .iter()
                        .enumerate()
                        .map(|(arm_index, arm)| CaseArmScript {
                            assumption: arm.assumption(),
                            tactics: script_arm_with_continuation(
                                arm.tactics(),
                                &tactics[index + 1..],
                            ),
                            sites: arm_sites(
                                index,
                                arm_index,
                                arm_names[arm_index.min(arm_names.len() - 1)],
                                arm.tactics().len(),
                            ),
                        })
                        .collect::<Vec<_>>();
                    let Some(done) = proof.run_case_arms(&arms, unfinished.as_deref_mut())? else {
                        *declined = Some(LinearScriptDecline::Step(index));
                        return Ok(None);
                    };
                    proof = done.at_site(&sites[index]);
                    proof
                        .note_trace_join_continuation_arm((index + 1 < tactics.len()).then_some(0));
                    return Ok(finish(proof, unfinished));
                }
                ProofTactic::Transport { source, target } => {
                    // The bare form selects its frame evidence at the
                    // execution frontier this `have` was opened on, exactly
                    // as between top-level steps: the source-local candidates
                    // first, then the premise planner, whose refusal is the
                    // answer. A pure theorem has no frontier to select from.
                    if !matches!(proof.context.as_ref(), ProofContext::Execution(_)) {
                        return Err(proof.step_error(
                            "bare `transport` selects its premises at a C execution frontier, and this proof has none; write `transport(P, Q) using { ... }` with the premises it needs",
                        ));
                    }
                    proof = match proof.try_execution_fact_transport_or_refusal(source, target)? {
                        Ok(transported) => transported,
                        Err(source_refusal) => proof.apply_planned_fact_transport(
                            source,
                            target,
                            index,
                            source_refusal.as_ref(),
                        )?,
                    };
                }
                tactic => {
                    if matches!(tactic, ProofTactic::Sorry) {
                        // Admitted only as a complete body (a `have` body
                        // reaching this runner, or a direct engine call with
                        // a single tactic). A bare `sorry` among other
                        // tactics would cover an unbounded suffix, so it is
                        // rejected to keep holes minimal.
                        if tactics.len() != 1 {
                            return Err(proof.step_error(
                                "`sorry` is only allowed as a complete `have` body or a complete contract proof body; it cannot cover a suffix of other tactics",
                            ));
                        }
                        if !crate::surface::verification::sorry_is_allowed() {
                            return Err(proof.step_error(
                                "`sorry` requires `click verify --allow-sorry`; it is a dev-only proof hole and never verifies in the gate",
                            ));
                        }
                        let label = proof
                            .surface_goal()
                            .map(crate::surface::diagnostics::describe_click_proposition)
                            .map(|goal| format!("have {goal}"))
                            .unwrap_or_else(|| "have (goal unavailable)".to_string());
                        crate::surface::verification::record_sorry_admission(label, String::new());
                        proof = proof.admit_focused_goal_for_sorry()?;
                        continue;
                    }
                    let step = SourceContext::PureGoal
                        .leaf_step(tactic)
                        .ok_or_else(|| proof.unsupported_operation_error(tactic_name(tactic)))?;
                    proof = proof.apply_step(step)?;
                }
            }
            // A written step that checks the goal under another spelling of
            // the same order claim (`0 <= e` for the goal `e >= 0`) has
            // proved the goal. Close it with a recorded `assumption`, which
            // accepts that spelling, so the certificate re-runs on its own;
            // a planned step sequence never reaches this runner and keeps
            // the goal open after such a step.
            if matches!(
                tactic,
                ProofTactic::ApplyTheorem(_)
                    | ProofTactic::ApplyTheoremUsing { .. }
                    | ProofTactic::ApplyInductionUsing { .. }
                    | ProofTactic::ApplyInduction { .. }
                    | ProofTactic::InstantiateUsing { .. }
                    | ProofTactic::Transport { .. }
                    | ProofTactic::TransportUsing { .. }
                    | ProofTactic::LetSatisfy(_)
            ) && !proof.focused_discharged()
                && checked_fact_spells_the_goal(&proof)
            {
                proof = proof.apply_step(ProofStep::Assumption)?;
            }
            if let Some(before) = before_application
                && proof.focused_discharged()
            {
                // An application guarantees every conclusion of its theorem,
                // not only the one that happened to be the goal.
                let conclusions = match tactic {
                    ProofTactic::ApplyTheorem(application)
                    | ProofTactic::ApplyTheoremUsing { application, .. } => {
                        before.theorem_application_surface_conclusions(application)
                    }
                    _ => Vec::new(),
                };
                proof = before.retain_completed_goal(&proof, &conclusions)?;
            }
            if let Some(capture) = nested_capture {
                capture.finish(&proof);
            }
        }

        Ok(finish(proof, unfinished))
    }

    /// Applies one statement step, retaining one newly proved non-load
    /// requirement when the checked step reports it as unavailable.  The
    /// requirement is lowered again at this exact frontier and compared by
    /// the shared alpha-aware identity before any proof operation is accepted.
    /// A failed retry returns the original structured error, allowing the
    /// normal smart caller to preserve its diagnostic and planner behavior.
    fn try_statement_step_with_retries(
        &self,
        step: ProofStep,
        retried_requirements: &mut std::collections::BTreeSet<PropositionIdentityKey>,
    ) -> Result<Self, ClickError> {
        // Smart execution exposes supported missing source-backed
        // prerequisites before contextual compatibility reasoning can
        // discharge them invisibly. The retained proof retries the same
        // ordinary checked step after publishing its `have`.
        // Use the same checked-step entry point as written `step()` so
        // smart execution retains its fact deltas in the opt-in trace too.
        let initial = self.apply_step(step.clone());
        self.retry_statement_after_refusal(step, retried_requirements, initial)
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
                .is_ok_and(|lowered| lowered_states_requirement(&lowered, requirement))
                .then(|| RequirementSpelling {
                    surface: surface.clone(),
                    direct_caller: None,
                }));
        }
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Ok(None);
        };
        let Some(execution) = self.execution() else {
            return Ok(None);
        };
        let execution_view = execution.view(context);
        let _qualified_sources = super::surface_synthesis::QualifiedSynthesisScope::enter(
            execution_view.surface_propositions,
        );
        let admit = |candidate: ClickProposition| match self
            .lower_surface_goal(&candidate, "step obligation")
        {
            Ok(lowered) if lowered_states_requirement(&lowered, requirement) => Some(candidate),
            _ => None,
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
                .then_some(RequirementSpelling {
                    surface,
                    direct_caller: None,
                }));
        }
        if requirement.call_site.is_some()
            && let Some(registry_surface) =
                source_backed_call_requirement_surface(requirement, step, execution, context)
        {
            let direct_caller =
                source_backed_direct_caller_requirement(requirement, step, execution, context);
            let candidate = match &direct_caller {
                Some((predicate_name, _)) => {
                    let mut unfolded = self.active_unfolded_predicates();
                    unfolded.push(predicate_name.clone());
                    unfold_structural_invariant_proposition(
                        context.spec_definitions.predicates,
                        &registry_surface.proposition,
                        &unfolded,
                    )
                    .map_err(|message| self.step_error(message))?
                }
                None => registry_surface.proposition,
            };
            if let Some(surface) = admit(candidate) {
                return Ok(Some(RequirementSpelling {
                    surface,
                    direct_caller,
                }));
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
        .map(|surface| RequirementSpelling {
            surface,
            direct_caller: None,
        }))
    }

    /// `auto`'s automatic opening (design/proof-reuse.md R4): a C operation
    /// refused because the resource it reads or writes lies inside a folded
    /// resource is retried once that resource is unfolded, one layer per
    /// refused access. The certificate records each `unfold`, so expansion
    /// writes it out. A refusal the opening does not resolve is reported as
    /// the original refusal.
    fn retry_statement_after_auto_open(
        &self,
        step: ProofStep,
        retried_requirements: &mut std::collections::BTreeSet<PropositionIdentityKey>,
        error: ClickError,
    ) -> Result<Self, ClickError> {
        let mut proof = self.clone();
        let mut refusal = error.clone();
        for _ in 0..MAX_AUTO_OPENINGS_PER_STATEMENT {
            let Some(missing) = refusal.missing_resource() else {
                break;
            };
            let Some(opened) = proof.auto_open_for_missing_resource(missing)? else {
                break;
            };
            proof = opened;
            match proof.apply_step(step.clone()) {
                Ok(stepped) => return Ok(stepped),
                Err(next) if next.missing_resource().is_some() => refusal = next,
                Err(next) => {
                    return proof
                        .retry_statement_after_refusal(step, retried_requirements, Err(next))
                        .map_err(|_| error);
                }
            }
        }
        Err(error)
    }

    pub(in crate::surface::proof) fn retry_statement_after_refusal(
        &self,
        step: ProofStep,
        retried_requirements: &mut std::collections::BTreeSet<PropositionIdentityKey>,
        initial: Result<Self, ClickError>,
    ) -> Result<Self, ClickError> {
        match initial {
            Ok(proof) => Ok(proof),
            Err(error) if error.missing_resource().is_some() => {
                self.retry_statement_after_auto_open(step, retried_requirements, error)
            }
            Err(error) => {
                let Some(mut requirement) = error.unresolved_requirement().cloned() else {
                    return Err(error);
                };
                let Some(identity) = proposition_identity_key(&requirement.proposition) else {
                    return Err(error);
                };
                if !retried_requirements.insert(identity) {
                    return Err(error);
                }
                let ProofContext::Execution(context) = self.context.as_ref() else {
                    return Err(error);
                };
                let mut proof = self.clone();
                let mut error = error;
                loop {
                    let Some(execution) = proof.execution() else {
                        return Err(error);
                    };
                    let execution_view = execution.view(context);
                    let _qualified_sources =
                        super::surface_synthesis::QualifiedSynthesisScope::enter(
                            execution_view.surface_propositions,
                        );
                    // A call requirement is authoritative only at the call
                    // site that produced it. Resolve its source clause from
                    // the immutable registry/interface definition, after
                    // checking that this proof is still at that exact call.
                    // In particular, do not synthesize from the caller's
                    // reduced snapshot or use the kernel candidate ordinal
                    // as a source selector.
                    // Lower and compare each candidate independently; no
                    // surface is admitted merely because it parses or because
                    // lowering succeeds.  The caller below invokes this at
                    // most twice in a fixed order.
                    let admit_candidate = |candidate: ClickProposition| match proof
                        .lower_surface_goal(&candidate, "smart retained-have requirement")
                    {
                        Ok(lowered) if lowered_states_requirement(&lowered, &requirement) => {
                            Ok(Some(candidate))
                        }
                        Ok(_) | Err(_) => {
                            check_verification_deadline()?;
                            Ok(None)
                        }
                    };
                    let synthesize_candidate = || {
                        synthesize_surface_proposition(
                            &requirement.proposition,
                            context.parameter_binding(),
                            &execution.core.state,
                        )
                    };
                    let mut direct_caller = requirement.call_site.as_ref().and_then(|_| {
                        source_backed_direct_caller_requirement(
                            &requirement,
                            &step,
                            execution,
                            context,
                        )
                    });
                    let surface = if requirement.call_site.is_some() {
                        // A source-backed call may only use the source form
                        // after all carrier/call/frontier/ordinal checks have
                        // passed.  A missing authoritative registry entry is
                        // still a hard refusal; synthesis is only the second
                        // spelling of an admitted source candidate.
                        let Some(registry_surface) = source_backed_call_requirement_surface(
                            &requirement,
                            &step,
                            execution,
                            context,
                        ) else {
                            return Err(error);
                        };
                        let candidate = if let Some((predicate_name, _)) = &direct_caller {
                            let mut unfolded = proof.active_unfolded_predicates();
                            unfolded.push(predicate_name.clone());
                            unfold_structural_invariant_proposition(
                                context.spec_definitions.predicates,
                                &registry_surface.proposition,
                                &unfolded,
                            )
                            .map_err(|message| proof.step_error(message))?
                        } else {
                            registry_surface.proposition
                        };
                        if let Some(surface) = admit_candidate(candidate)? {
                            surface
                        } else {
                            let Some(synthesized) = synthesize_candidate() else {
                                return Err(error);
                            };
                            let Some(surface) = admit_candidate(synthesized)? else {
                                return Err(error);
                            };
                            // A synthesized generated guard is a different
                            // goal from the written predicate's existential.
                            // Its witness must be selected for this goal.
                            direct_caller = None;
                            surface
                        }
                    } else {
                        let Some(synthesized) = synthesize_candidate() else {
                            return Err(error);
                        };
                        let Some(surface) = admit_candidate(synthesized)? else {
                            return Err(error);
                        };
                        surface
                    };
                    if let Some((predicate_name, _)) = &direct_caller {
                        let Some(unfolded) = attempt::candidate_outcome(
                            proof.apply_step(ProofStep::UnfoldPredicate(predicate_name.clone())),
                        )?
                        else {
                            return Err(error);
                        };
                        proof = unfolded;
                    }
                    let have = match proof.begin_have(surface.clone()) {
                        Ok(have) => have,
                        Err(_) => {
                            check_verification_deadline()?;
                            return Err(error);
                        }
                    };
                    let closed = match direct_caller {
                        Some((predicate_name, selection)) => {
                            let _ = predicate_name;
                            match have.try_direct_caller_requirement_closure(&selection) {
                                Ok(closed) => closed,
                                Err(_) => {
                                    check_verification_deadline()?;
                                    return Err(error);
                                }
                            }
                        }
                        None => close_requirement_have_by_auto(have, &surface)?,
                    };
                    let Some(closed) = closed else {
                        return Err(error);
                    };
                    // `join` publishes the checked proposition into the exact
                    // enclosing frontier.  Reapply the original step value so a
                    // future StepContract follows precisely the same contract
                    // selection and certificate provenance as the refused step.
                    proof = closed.join()?;
                    match proof.apply_step(step.clone()) {
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
    pub(in crate::surface::proof) fn try_statement_step(&self) -> Result<Option<Self>, ClickError> {
        self.try_statement_step_with_apply(|proof| proof.apply_step(ProofStep::Step))
    }

    pub(in crate::surface::proof) fn try_smart_statement_step(
        &self,
        step: ProofStep,
        retried_requirements: &mut std::collections::BTreeSet<PropositionIdentityKey>,
    ) -> Result<Option<Self>, ClickError> {
        self.try_statement_step_with_apply(|proof| {
            proof.try_statement_step_with_retries(step.clone(), retried_requirements)
        })
    }

    pub(in crate::surface::proof) fn try_direct_caller_requirement_closure(
        &self,
        selection: &CallerRequirementSelection,
    ) -> Result<Option<Self>, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Ok(None);
        };
        let unfolded = unfold_structural_invariant_proposition(
            context.spec_definitions.predicates,
            &selection.source_proposition,
            &self.active_unfolded_predicates(),
        )
        .map_err(|message| self.step_error(message))?;
        let ClickProposition::Exists {
            click_type,
            name: source_name,
            body,
            ..
        } = unfolded
        else {
            return Ok(None);
        };
        let candidate_names = std::iter::once(source_name.clone()).chain(
            (0..MAX_DIRECT_CALLER_BINDING_NAMES).map(|suffix| {
                format!(
                    "{}_witness_{}_{suffix}",
                    source_name, selection.source_id.outer_ordinal
                )
            }),
        );
        let Some(choice_name) = candidate_names.into_iter().find(|candidate| {
            self.local_binding(candidate).is_none()
                && !context
                    .parsed_function
                    .parameters()
                    .iter()
                    .any(|parameter| parameter.name() == candidate)
                && self
                    .execution()
                    .is_none_or(|execution| !execution.core.state.locals().contains_name(candidate))
        }) else {
            return Ok(None);
        };
        let replacement = match &click_type {
            ClickType::Integer | ClickType::Algebraic(_) => {
                ContractExpression::Binding(choice_name.clone())
            }
            ClickType::C(_) | ClickType::CObjectPointer { .. } => {
                ContractExpression::CFragment(CExpression::Variable(choice_name.clone()))
            }
            ClickType::Parameter(_) => return Ok(None),
        };
        let body =
            substitute_click_proposition(&body, &BTreeMap::from([(source_name, replacement)]))
                .map_err(|message| self.step_error(message))?;
        let source = ClickProposition::At {
            selector: SnapshotSelector::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Function,
                kind: ProgramPointKind::Entry,
            }),
            proposition: Box::new(ClickProposition::Exists {
                click_type: click_type.clone(),
                name: choice_name.clone(),
                written_name: None,
                body: Box::new(body),
            }),
        };
        let Some(chosen) =
            attempt::candidate_outcome(self.apply_step(ProofStep::LetSatisfy(ProofLetSatisfy {
                bindings: vec![(choice_name.clone(), click_type)],
                proposition: source,
            })))?
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
        let Some(ClickProposition::Exists {
            name, written_name, ..
        }) = chosen.surface_goal()
        else {
            return Ok(None);
        };
        let witness_name = written_name.as_ref().unwrap_or(name).clone();
        let Some(witnessed) = attempt::candidate_outcome(chosen.apply_step(ProofStep::Witness(
            ProofWitness::single(
                witness_name,
                ContractExpression::CFragment(CExpression::Variable(choice_name)),
            ),
        )))?
        else {
            return Ok(None);
        };
        let mut proof = witnessed;
        for source in &source_leaves {
            // At the entry snapshot the leaves already close the goal.
            if proof.focused_discharged() {
                return Ok(Some(proof));
            }
            let Some(extracted) =
                attempt::candidate_outcome(proof.apply_step(ProofStep::Extract(source.clone())))?
            else {
                return Ok(None);
            };
            proof = extracted;
        }
        if proof.focused_discharged() {
            return Ok(Some(proof));
        }
        if let Some(closed) = proof.try_simp_closure_with_surfaces(&source_leaves)? {
            return Ok(Some(closed));
        }
        // The leaves hold at function entry. A conjunct this frontier does
        // not state exactly, such as a wide range or a universal over reads,
        // is carried here by one explicit transport of its entry form.
        let Some(goal) = proof.surface_goal().cloned() else {
            return Ok(None);
        };
        let mut conjuncts = Vec::new();
        let mut pending = vec![goal];
        while let Some(proposition) = pending.pop() {
            match proposition {
                ClickProposition::And(left, right) => {
                    pending.push(*right);
                    pending.push(*left);
                }
                conjunct => conjuncts.push(conjunct),
            }
        }
        let mut carried_any = false;
        for conjunct in conjuncts {
            check_verification_deadline()?;
            let Ok(lowered) =
                proof.lower_surface_proposition(&conjunct, "caller requirement conjunct")
            else {
                return Ok(None);
            };
            if proof.facts().pure_assumption_available(&lowered) {
                continue;
            }
            let Some(carried) = proof.try_carry_entry_conjunct(&conjunct)? else {
                return Ok(None);
            };
            proof = carried;
            carried_any = true;
        }
        if !carried_any {
            return Ok(None);
        }
        proof.try_simp_closure_with_surfaces(&source_leaves)
    }

    /// Proves `conjunct` at this frontier from its function-entry form: a
    /// plain fact by one `transport`, and a guarded universal by introducing
    /// its binder and guard, instantiating the entry universal there, and
    /// transporting that one conclusion. Every step is the checked operation.
    fn try_carry_entry_conjunct(
        &self,
        conjunct: &ClickProposition,
    ) -> Result<Option<Self>, ClickError> {
        let entry = |proposition: &ClickProposition| ClickProposition::At {
            selector: SnapshotSelector::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Function,
                kind: ProgramPointKind::Entry,
            }),
            proposition: Box::new(proposition.clone()),
        };
        let transport = |proposition: &ClickProposition| ProofStep::TransportUsing {
            source: entry(proposition),
            target: proposition.clone(),
            premises: vec![entry(proposition)],
        };
        let steps = match conjunct {
            ClickProposition::ForAll { name, body, .. } => {
                let ClickProposition::Implies(guard, consequent) = body.as_ref() else {
                    return Ok(None);
                };
                vec![
                    ProofStep::IntroAs(name.clone()),
                    ProofStep::Intro,
                    ProofStep::InstantiateUsing {
                        quantified: entry(conjunct),
                        argument: ContractExpression::CFragment(CExpression::Variable(
                            name.clone(),
                        )),
                        premises: Some(vec![guard.as_ref().clone()]),
                    },
                    transport(consequent),
                ]
            }
            _ => vec![transport(conjunct)],
        };
        let Some(mut scope) = attempt::candidate_outcome(self.begin_have(conjunct.clone()))? else {
            return Ok(None);
        };
        for step in steps {
            let Some(next) = attempt::candidate_outcome(scope.apply_step(step))? else {
                return Ok(None);
            };
            scope = next;
        }
        attempt::candidate_outcome(scope.join())
    }

    pub(in crate::surface::proof) fn try_statement_step_with_apply(
        &self,
        mut apply: impl FnMut(&Self) -> Result<Self, ClickError>,
    ) -> Result<Option<Self>, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Ok(None);
        };
        let Some(execution) = self.execution() else {
            return Err(self.step_error("execution-frontier proof lost its semantic state"));
        };
        // Structural frontiers belong to the branch and loop operations.
        let (_, _, statement, _) = next_top_level_statement_from_frontier_position(
            execution.view(context),
            &execution.core.state,
            context.function,
            context.arguments,
            context.claim_label,
            context.tactic_index,
            "smart step selection",
        )?;
        if matches!(statement, CStatement::If { .. } | CStatement::Switch { .. }) {
            // A C `if` the context decides is one step into that arm; one it
            // cannot decide is a fork for the driver's branch handling. A
            // symbolic switch likewise belongs to the bounded planner, which
            // materializes its case split before applying one switch theorem
            // per path.
            return match apply(self) {
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
        if self.is_at_call_outcomes_frontier()? {
            return Ok(None);
        }
        // The statement runs in the whole proof context; nothing can supply
        // more than the step already sees, so its failure is the answer,
        // with the step's diagnostic. The exception is a statement whose
        // successors are path cases: a case split on their facts supplies
        // each case's facts, and that split belongs to the planner.
        match apply(self) {
            Ok(proof) => Ok(Some(proof)),
            Err(error) if error.is_path_case_split() => {
                check_verification_deadline()?;
                Ok(None)
            }
            Err(error) => Err(error),
        }
    }
}

/// How many resources `auto` opens for one C statement before it reports
/// the statement's refusal. A statement touches a bounded number of places,
/// and each opening must hold one of them.
const MAX_AUTO_OPENINGS_PER_STATEMENT: usize = 4;

/// How many variables simp's bound selection visits from a goal's own
/// variables before it stops following bounds to further variables.
const MAX_BOUND_VARIABLES: usize = 8;

thread_local! {
    static ACTIVE_SIMP_FALLBACKS: std::cell::Cell<u8> = const { std::cell::Cell::new(0) };
}

#[derive(Clone, Copy)]
enum SimpFallback {
    EqualityRewrite = 1,
    FunctionUnfold = 2,
}

/// A candidate can try the other fallback and descend through logical
/// structure, but cannot restart a fallback already evaluating that candidate.
/// The outer rewrite search still owns its equality chain and closing probes.
struct SimpFallbackScope(SimpFallback);

impl SimpFallbackScope {
    fn enter(fallback: SimpFallback) -> Option<Self> {
        ACTIVE_SIMP_FALLBACKS.with(|active| {
            let bit = fallback as u8;
            if active.get() & bit != 0 {
                return None;
            }
            active.set(active.get() | bit);
            Some(Self(fallback))
        })
    }
}

impl Drop for SimpFallbackScope {
    fn drop(&mut self) {
        ACTIVE_SIMP_FALLBACKS.with(|active| active.set(active.get() & !(self.0 as u8)));
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

/// How many recently recorded program points simp offers, beside function
/// entry, as the source of a transport of its goal.
const MAX_TRANSPORT_SOURCE_POINTS: usize = 8;

thread_local! {
    static NAMED_PREMISE_CLOSURE_DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Marks a closure whose premises are named, not selected from ambient
/// facts: a loop bundle member may cite only the loop head's premises and
/// the contract, so simp's per-variable bound lookup, which reads every
/// available bound, stays out of it.
pub(in crate::surface::proof) struct NamedPremiseClosureScope;

impl NamedPremiseClosureScope {
    pub(in crate::surface::proof) fn enter() -> Self {
        NAMED_PREMISE_CLOSURE_DEPTH.with(|depth| depth.set(depth.get() + 1));
        NamedPremiseClosureScope
    }

    fn active() -> bool {
        NAMED_PREMISE_CLOSURE_DEPTH.with(|depth| depth.get() > 0)
    }
}

impl Drop for NamedPremiseClosureScope {
    fn drop(&mut self) {
        NAMED_PREMISE_CLOSURE_DEPTH.with(|depth| depth.set(depth.get().saturating_sub(1)));
    }
}

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
/// can match the goal's outer connective. `assumption` closes a conjunction
/// or disjunction from facts as well as a goal that is itself a fact, and
/// `enumerate` closes only a universal; on any other goal it is refused
/// before it reads a fact, so omitting it changes no outcome and saves
/// rendering the goal into a refusal once per candidate at every `intro`
/// level.
fn direct_logical_candidates(goal: Option<&Proposition>) -> Vec<ProofStep> {
    let mut steps = vec![ProofStep::Normalize, ProofStep::Assumption];
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
/// slice.  In particular, a generated overflow guard (as in `cstr::readable`)
/// remains on the dynamic snapshot-transport route.  The worklist is bounded
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
            Proposition::CMemoryLoadable { base, .. }
                if matches!(base.block, crate::kernel::PointerBlock::ExternalArgument) =>
            {
                saw_range = true;
            }
            Proposition::ConditionIs(ConditionTerm::Bitvector32SignedAddOverflows(_, _), _) => {
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
            Proposition::CMemoryLoadable { .. } => return false,
            Proposition::ConditionIs(_, _) => {}
            _ => return false,
        }
    }
    saw_range
}

/// Collect conjunction leaves for a retained Have without allowing a deeply
/// nested source proposition to evade the verifier's work bound.  The full
/// proposition remains the first closure surface; each leaf is then offered
/// to the existing checked simp closure.
pub(in crate::surface::proof) fn collect_bounded_surface_conjunct_leaves(
    proposition: &ClickProposition,
) -> Result<Vec<ClickProposition>, ClickError> {
    const MAX_NODES: usize = 4096;
    let mut work = vec![proposition];
    let mut leaves = Vec::new();
    let mut visited = 0usize;
    while let Some(current) = work.pop() {
        visited = visited.saturating_add(1);
        crate::instrumentation::record_deterministic_work(1);
        check_verification_deadline()?;
        if visited > MAX_NODES {
            return Err(ClickError::new(format!(
                "retained-have conjunction exceeded structural limit {MAX_NODES}"
            )));
        }
        match current {
            ClickProposition::And(left, right) => {
                work.push(right);
                work.push(left);
            }
            _ => leaves.push(current.clone()),
        }
    }
    Ok(leaves)
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
    fn asserted_condition_given_context(&self, condition: &CExpression) -> ClickProposition {
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
                            Proposition::ConditionIs(condition, !value)
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
fn asserted_condition_proposition(condition: &CExpression) -> ClickProposition {
    let comparison =
        |left: &CExpression, operator, right: &CExpression| ClickProposition::Comparison {
            left: ContractExpression::CFragment(left.clone()),
            operator,
            right: ContractExpression::CFragment(right.clone()),
        };
    match condition {
        CExpression::And(left, right) => ClickProposition::And(
            Box::new(asserted_condition_proposition(left)),
            Box::new(asserted_condition_proposition(right)),
        ),
        CExpression::Or(left, right) => ClickProposition::Or(
            Box::new(asserted_condition_proposition(left)),
            Box::new(asserted_condition_proposition(right)),
        ),
        CExpression::Not(inner) => {
            ClickProposition::Not(Box::new(asserted_condition_proposition(inner)))
        }
        CExpression::Equal(left, right) => comparison(left, ComparisonOperator::Equal, right),
        CExpression::NotEqual(left, right) => comparison(left, ComparisonOperator::NotEqual, right),
        CExpression::LessThan(left, right) => comparison(left, ComparisonOperator::LessThan, right),
        CExpression::LessEqual(left, right) => {
            comparison(left, ComparisonOperator::LessEqual, right)
        }
        CExpression::GreaterThan(left, right) => {
            comparison(left, ComparisonOperator::GreaterThan, right)
        }
        CExpression::GreaterEqual(left, right) => {
            comparison(left, ComparisonOperator::GreaterEqual, right)
        }
        other => comparison(
            other,
            ComparisonOperator::NotEqual,
            &CExpression::Value(int32(0)),
        ),
    }
}

pub(super) fn lowered_states_requirement(
    lowered: &Proposition,
    requirement: &UnresolvedRequirement,
) -> bool {
    if propositions_match_after_canonical_loads(lowered, &requirement.proposition) {
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

fn propositions_match_after_canonical_loads(left: &Proposition, right: &Proposition) -> bool {
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
            (Proposition::ConditionIs(_, _), Proposition::ConditionIs(_, _)) => {
                let left = crate::kernel::canonical_condition_fact(left);
                let right = crate::kernel::canonical_condition_fact(right);
                if !propositions_are_alpha_equal(&left, &right) {
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

fn source_backed_refusal(
    error: &ClickError,
    current_memory: &crate::kernel::CMemory,
) -> Result<bool, ClickError> {
    let Some(requirement) = error.unresolved_requirement() else {
        return Ok(false);
    };
    let Some(site) = requirement.call_site.as_ref() else {
        return Ok(false);
    };
    if crate::kernel::CMemorySnapshotIdentity::of(current_memory) != site.source_snapshot {
        return Ok(false);
    }
    source_backed_requirement_is_supported(
        &requirement.proposition,
        site.source_requirement_ordinal,
        site.source_requirement_is_state_independent,
        site.source_load_snapshot,
    )
}

/// Recover the written source clause that produced one unresolved call
/// requirement.  This is deliberately a narrow, fail-closed lookup: the
/// carrier's callee, interface, source ordinal, argument expressions, and
/// frontier memory identity all have to agree before a source form is
/// admitted to the retained-have retry.
struct SourceBackedCallSurface {
    arguments: Vec<CExpression>,
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

    if crate::kernel::CMemorySnapshotIdentity::of(execution.core.state.memory())
        != site.source_snapshot
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
    let (callee, arguments) = match statement {
        CStatement::Call {
            function_name,
            arguments,
        }
        | CStatement::CallAssign {
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
    match step {
        ProofStep::StepContract(_) => {
            // A named callback interface still belongs to the exact C call
            // that produced the refusal.  The selected named-contract alias
            // above is the only indirect representation that may differ.
            if callee != site.callee && !named_interface_alias {
                return None;
            }
        }
        ProofStep::StepCall(transport) if transport.is_named_contract() => {
            if callee != site.callee && !named_interface_alias {
                return None;
            }
        }
        ProofStep::StepCall(_) => {
            // StepCall is the concrete-call operation: both the C symbol and
            // the selected interface must be the carrier's concrete callee.
            if callee != site.callee || site.interface.as_ref() != site.callee {
                return None;
            }
        }
        ProofStep::Step => {
            // Even an indirect callback must retain the exact function-pointer
            // expression named by the carrier before routing through its
            // selected interface, except for the named-contract alias above.
            if callee != site.callee && !named_interface_alias {
                return None;
            }
        }
        _ => return None,
    }
    if arguments.as_slice() != site.source_arguments.as_slice() {
        return None;
    }
    let expected_interface = match step {
        ProofStep::StepContract(application) => application.name.as_str(),
        ProofStep::StepCall(transport) if transport.is_named_contract() => transport.callee(),
        ProofStep::Step | ProofStep::StepCall(_) => site.interface.as_ref(),
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
                    .map(|parameter| parameter.name().to_string())
                    .collect::<Vec<_>>(),
                parameters
                    .iter()
                    .map(|parameter| parameter.click_type().c_type().map(C0Type::to_kernel_type))
                    .collect::<Vec<_>>(),
                requirement.proposition()?.clone(),
            )
        } else {
            let source = ordinary_source?.get(source_ordinal)?;
            let proposition = match source {
                FunctionRequirementSource::Proposition(proposition) => proposition.clone(),
                FunctionRequirementSource::LoadableSegment(_) => return None,
            };
            let function = context
                .function_environment
                .get_function(site.callee.as_ref())?;
            (
                function
                    .parameters()
                    .iter()
                    .map(|parameter| parameter.name().to_string())
                    .collect::<Vec<_>>(),
                function
                    .parameters()
                    .iter()
                    .map(|parameter| Some(parameter.c_type()))
                    .collect::<Vec<_>>(),
                proposition,
            )
        };

    if source_parameter_names.len() != site.source_arguments.len() {
        return None;
    }
    let substitutions = source_parameter_names
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
                None => ContractExpression::CFragment(argument.clone()),
            };
            (parameter.clone(), argument)
        })
        .collect::<BTreeMap<_, _>>();
    // Match contract lowering: adapt a signed character argument to the
    // predicate's byte parameter before substituting the call arguments.
    // Keep the original source clause for source-ID and parameter selection.
    let elaborated = crate::surface::lowering::elaborate_character_byte_views(
        &source_proposition,
        context.spec_definitions.predicates,
        &|name| {
            let slot = source_parameter_names
                .iter()
                .position(|parameter| parameter == name)?;
            match source_parameter_types[slot]? {
                crate::kernel::CType::Int8Pointer => Some(C0Type::Int8Pointer),
                crate::kernel::CType::Int8Array(size) => Some(C0Type::Int8Array(size)),
                _ => None,
            }
        },
    );
    // A call step's binder map names the caller instance each callee binder
    // is: the callee's field reads become reads of that caller instance.
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
        _ => BTreeMap::new(),
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
    if !matches!(step, ProofStep::Step | ProofStep::StepCall(_))
        || source.interface.as_ref() != source.callee.as_str()
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
            let ContractExpression::CFragment(CExpression::Variable(callee_name)) = argument else {
                return None;
            };
            let callee_slot = callee
                .parameters()
                .iter()
                .position(|parameter| parameter.name() == callee_name)?;
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
        .get(&predicate_name)
        .and_then(|definition| definition.parameters().get(*predicate_argument_slot))
        .and_then(|parameter| parameter.click_type().c_type())
        .map(C0Type::to_kernel_type);
    *substituted_arguments.get_mut(*predicate_argument_slot)? =
        caller_parameter_as_argument(caller_parameter, predicate_parameter_type);
    let entry_state = context.constants.function_entry_state.as_ref()?;
    let entry_snapshot = crate::kernel::CMemorySnapshotIdentity::of(entry_state.memory());
    // Phase 1 projects entry requirements only across an effect-free prefix.
    // Local declarations change the current snapshot without adding an
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
            entry_snapshot,
        )?;
    Some((predicate_name, selection))
}

/// A caller parameter passed where a value of kernel type `expected` is read:
/// the parameter itself, or, for a signed character pointer read as
/// `uint8` bytes, its explicit byte view.
fn caller_parameter_as_argument(
    parameter: &syntax::C0Parameter,
    expected: Option<crate::kernel::CType>,
) -> ContractExpression {
    match expected {
        Some(expected)
            if crate::surface::lowering::needs_character_byte_view(
                parameter.c_type(),
                expected,
            ) =>
        {
            crate::surface::lowering::character_byte_view(parameter.name())
        }
        _ => ContractExpression::CFragment(CExpression::Variable(parameter.name().to_string())),
    }
}

/// The caller parameter a call argument names, directly or through a cast
/// that leaves the pointer unchanged: the same kernel type, such as `char *`
/// or `unsigned char *` for a `uint8 *` parameter, adding no `volatile`.
/// Constness is a property of the access path, not of the pointer, and a
/// read predicate grants no write permission, so a `const` cast is identity
/// here too.
fn caller_parameter_through_identity_cast(
    argument: &CExpression,
    parameters: &[syntax::C0Parameter],
    state: &crate::kernel::CState,
) -> Option<usize> {
    let (name, cast_type) = match argument {
        CExpression::Variable(name) => (name, None),
        CExpression::Cast {
            expression,
            target_type,
            pointee_volatile: false,
            ..
        } => match expression.as_ref() {
            CExpression::Variable(name) => (name, Some(*target_type)),
            _ => return None,
        },
        _ => return None,
    };
    // A local holding a parameter's own pointer value, as `p = bytes;`
    // leaves it, names the same storage; the caller has already required
    // that no effect separates entry from this call.
    let slot = parameters
        .iter()
        .position(|parameter| parameter.name() == name)
        .or_else(|| {
            let held = state.scalar_local_value(name)?;
            let mut matching = parameters.iter().enumerate().filter(|(_, parameter)| {
                state.scalar_local_value(parameter.name()).as_ref() == Some(&held)
            });
            match (matching.next(), matching.next()) {
                (Some((slot, _)), None) => Some(slot),
                _ => None,
            }
        })?;
    // A cast between character pointer types also names the same storage:
    // one byte has one value, read through either signedness.
    match cast_type {
        Some(target_type)
            if target_type != parameters[slot].c_type().to_kernel_type()
                && !(target_type.is_character_pointer()
                    && parameters[slot]
                        .c_type()
                        .to_kernel_type()
                        .is_character_pointer()) =>
        {
            None
        }
        _ => Some(slot),
    }
}

/// Candidate spellings of one kernel fact from recorded program-point
/// snapshots, nearest first: the fact synthesized from a snapshot where its cells are
/// readable and re-read there (`at(statement(n).entry, ...)`), then, for an
/// equality whose operands were read from different snapshots, one anchor per
/// operand. Callers must re-lower each candidate and accept it only when it
/// denotes exactly `kernel`.
///
/// Seek lazily through the persistent snapshot tree, nearest point first.
/// Both tree traversal and candidate synthesis check the verifier budget;
/// a successful near-anchor candidate costs logarithmic work in history size.
/// Exhaustion is sticky and stops this iterator before any further synthesis.
/// The cross-snapshot equality fallback sees only the already visited points.
pub(super) fn synthesize_surface_at_recorded_snapshots<'a>(
    kernel: &'a Proposition,
    parameter_binding: ParameterBinding<'a>,
    recorded_snapshots: &'a RecordedSnapshots,
    anchor: &ProgramPointRef,
) -> impl Iterator<Item = ClickProposition> + 'a {
    let anchor_index = match &anchor.region {
        CodeRegionRef::Statement(index) => *index,
        _ => usize::MAX,
    };
    // This is speculative premise presentation, not an explicit request to
    // visit the execution history. A missing spelling must not scan every
    // retained state for each equality candidate. Probe a small neighborhood;
    // callers can name an older snapshot explicitly when this search misses.
    const MAX_SNAPSHOT_CANDIDATES: usize = 256;
    let mut entries = recorded_snapshots
        .statement_entries_nearest(anchor_index)
        .take(MAX_SNAPSHOT_CANDIDATES);
    let mut points = Vec::new();
    let mut finished = false;
    std::iter::from_fn(move || {
        if finished || crate::instrumentation::deadline_exceeded() {
            finished = true;
            return None;
        }
        for (point, state) in entries.by_ref() {
            if crate::instrumentation::deadline_exceeded() {
                finished = true;
                return None;
            }
            points.push((point.clone(), state));
            if let Some(surface) = synthesize_surface_proposition(kernel, parameter_binding, state)
                && let Ok(surface) = surface_at_snapshot(&surface, point)
            {
                return Some(surface);
            }
        }
        finished = true;
        if crate::instrumentation::deadline_exceeded() {
            return None;
        }
        synthesize_surface_equality_across_points(kernel, parameter_binding, &points)
    })
}

/// [`synthesize_surface_at_recorded_snapshots`] for a fact that mixes states:
/// spelled at `current`, with each recorded statement entry nearest `anchor`
/// in turn as the one further snapshot for a value only that entry state
/// reads, such as `link.link == ParentLink::Linked(at(statement(3).entry,
/// p->kid))`. The same bounded neighborhood as the whole-fact probe.
fn synthesize_surface_with_recorded_snapshot<'a>(
    kernel: &'a Proposition,
    parameter_binding: ParameterBinding<'a>,
    entry: &'a CState,
    current: &'a CState,
    recorded_snapshots: &'a RecordedSnapshots,
    anchor: &ProgramPointRef,
) -> impl Iterator<Item = ClickProposition> + 'a {
    let anchor_index = match &anchor.region {
        CodeRegionRef::Statement(index) => *index,
        _ => usize::MAX,
    };
    const MAX_SNAPSHOT_CANDIDATES: usize = 256;
    recorded_snapshots
        .statement_entries_nearest(anchor_index)
        .take(MAX_SNAPSHOT_CANDIDATES)
        .take_while(|_| !crate::instrumentation::deadline_exceeded())
        .filter_map(move |(point, state)| {
            let selector = SnapshotSelector::ProgramPoint(point.clone());
            super::surface_synthesis::synthesize_surface_proposition_at_entry_post_and_snapshot(
                kernel,
                parameter_binding,
                entry,
                current,
                Some((state, &selector)),
            )
        })
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

/// `b == a` for the fact `a == b`.
fn swapped_bitvector_equality(fact: &Proposition) -> Option<Proposition> {
    let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), value) = fact else {
        return None;
    };
    Some(Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(right.clone(), left.clone()),
        *value,
    ))
}

/// Whether a goal is explicitly named by a restricted premise, either as
/// the premise itself or as one of its conjunction leaves. Checked fact
/// indexing makes those leaves available to `assumption`; this predicate
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

/// A 32-bit unsigned order and its operands, read from the signed order of
/// sign-flipped operands the kernel states it as. A constant operand arrives
/// already flipped; at least one operand carries the flip itself, so two
/// bare constants are an ordinary signed comparison.
fn unsigned_order_parts(
    proposition: &Proposition,
) -> Option<(UnsignedOrder, Bitvector32Term, Bitvector32Term)> {
    const SIGN_BIT: u32 = 0x8000_0000;
    let Proposition::ConditionIs(condition, true) = proposition else {
        return None;
    };
    let (order, left, right) = match condition {
        ConditionTerm::Bitvector32SignedLessThan(left, right) => (UnsignedOrder::Less, left, right),
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
            (UnsignedOrder::LessEqual, left, right)
        }
        ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
            (UnsignedOrder::Greater, left, right)
        }
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
            (UnsignedOrder::GreaterEqual, left, right)
        }
        _ => return None,
    };
    let flipped = |term: &Bitvector32Term| match term {
        Bitvector32Term::BitwiseXor(value, sign) if sign.as_const() == Some(SIGN_BIT) => {
            Some(value.as_ref().clone())
        }
        Bitvector32Term::BitwiseXor(sign, value) if sign.as_const() == Some(SIGN_BIT) => {
            Some(value.as_ref().clone())
        }
        _ => None,
    };
    let unflipped = |term: &Bitvector32Term| {
        flipped(term).or_else(|| {
            term.as_const()
                .map(|value| Bitvector32Term::Constant(value ^ SIGN_BIT))
        })
    };
    if flipped(left).is_none() && flipped(right).is_none() {
        return None;
    }
    Some((order, unflipped(left)?, unflipped(right)?))
}

/// Closes a `have` of a step requirement the way smart execution does: the
/// bounded simp closure over the requirement and its conjunct leaves, and for
/// an `int32` existential a witness of 0 first. This is the implicit `auto`
/// a step runs for an obligation nothing written proves.
pub(in crate::surface::proof) fn close_requirement_have_by_auto<'a>(
    have: ProofScope<'a>,
    surface: &ClickProposition,
) -> Result<Option<ProofScope<'a>>, ClickError> {
    let mut surfaces = vec![surface.clone()];
    surfaces.extend(collect_bounded_surface_conjunct_leaves(surface)?);
    let closed = have.try_simp_closure_with_surfaces(&surfaces)?;
    if closed.is_some() {
        return Ok(closed);
    }
    let ClickProposition::Exists {
        click_type: ClickType::C(syntax::C0Type::Int32),
        name,
        written_name,
        ..
    } = surface
    else {
        return Ok(None);
    };
    let witnessed =
        attempt::candidate_outcome(have.apply_step(ProofStep::Witness(ProofWitness::single(
            written_name.as_ref().unwrap_or(name).clone(),
            ContractExpression::CFragment(CExpression::Value(CValue::Int32(
                Bitvector32Term::Constant(0),
            ))),
        ))))?;
    match witnessed {
        Some(witnessed) => witnessed.try_simp_closure_with_surfaces(&surfaces),
        None => Ok(None),
    }
}

/// A step requirement spelled in Surface syntax.
pub(in crate::surface::proof) struct RequirementSpelling {
    pub(in crate::surface::proof) surface: ClickProposition,
    /// When the requirement is the caller's own predicate requirement passed
    /// through the call: the predicate to unfold and the requirement to
    /// project, as smart execution's retry proves it.
    pub(in crate::surface::proof) direct_caller: Option<(String, CallerRequirementSelection)>,
}

/// Proves a requirement's `have` by the implicit `auto`: the caller's own
/// requirement by unfolding its predicate and projecting it, anything else by
/// [`close_requirement_have_by_auto`].
pub(in crate::surface::proof) fn close_requirement_spelling_by_auto<'a>(
    have: ProofScope<'a>,
    spelling: &RequirementSpelling,
) -> Result<Option<ProofScope<'a>>, ClickError> {
    let Some((predicate_name, selection)) = &spelling.direct_caller else {
        return close_requirement_have_by_auto(have, &spelling.surface);
    };
    let Some(unfolded) = attempt::candidate_outcome(
        have.apply_step(ProofStep::UnfoldPredicate(predicate_name.clone())),
    )?
    else {
        return Ok(None);
    };
    unfolded.try_direct_caller_requirement_closure(selection)
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
}
