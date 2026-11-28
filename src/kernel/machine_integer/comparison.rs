//! Exact comparison: `to_integer(a) R to_integer(b)` holds exactly when the
//! native comparison of `a` and `b` at their format does. `to_integer` is
//! injective and order-preserving on every format, so the two comparisons
//! have the same truth.

mod fact_identity;
pub(crate) use fact_identity::{FactOperand, fact_operand_identity};

use super::{Relation, identity, range, representation};
use crate::kernel::{
    BooleanOperandView, IntegerComparisonOperator, IntegerTerm, KernelTerm, KernelTermNode,
    MachineIntegerType, OldConditionTerm, OldMachineTerm, Proposition, SharedIntegerTerm,
    SharedMachineIntegerTerm,
};

/// A written comparison for structural matching. Unlike checking views, this
/// preserves direction and performs no arithmetic cancellation or evaluation.
pub(crate) struct StructuralComparisonView<'a> {
    pub(crate) format: MachineIntegerType,
    pub(crate) relation: crate::kernel::CompareRelation,
    pub(crate) negated: bool,
    pub(crate) operands: [ComparisonOperand<'a>; 2],
}

/// Read a retained primitive comparison without exporting its machine operands.
/// Other selected atoms keep the existing structural classifier; connectives
/// are deliberately not opened by that classifier.
pub(crate) fn structural_boolean_comparison_view(
    condition: crate::kernel::BooleanOperandView<'_>,
) -> Option<StructuralComparisonView<'_>> {
    if let Some((format, relation, operands)) = condition.comparison() {
        let [left, right] = operands.map(|operand| match operand {
            crate::kernel::MachineOperandView::Old(value) => {
                Some(ComparisonOperand::Written(value))
            }
            operand => operand
                .try_retain(format)
                .map(ComparisonOperand::Observation),
        });
        return Some(StructuralComparisonView {
            format,
            relation,
            negated: false,
            operands: [left?, right?],
        });
    }
    let (operator, [left, right]) = written_integer_comparison(condition)?;
    structural_integer_comparison_view(operator, [&left, &right])
}

pub(crate) fn structural_comparison_view(
    condition: &OldConditionTerm,
) -> Option<StructuralComparisonView<'_>> {
    if let OldConditionTerm::Compare {
        format,
        relation,
        left,
        right,
    } = condition
    {
        return Some(StructuralComparisonView {
            format: *format,
            relation: *relation,
            negated: false,
            operands: [
                ComparisonOperand::Written(left),
                ComparisonOperand::Written(right),
            ],
        });
    }
    let (operator, operands) = integer_comparison_operands(condition)?;
    structural_integer_comparison_view(operator, operands)
}

/// The written Integer operands, with their original scopes and direction.
pub(crate) fn written_integer_comparison(
    condition: crate::kernel::BooleanOperandView<'_>,
) -> Option<(IntegerComparisonOperator, [SharedIntegerTerm; 2])> {
    use crate::kernel::BooleanOperandView as B;
    match condition {
        B::Native(native) => {
            let (operator, operands) = integer_comparison_operands(native)?;
            Some((operator, operands.map(Clone::clone)))
        }
        B::Shared(root) => {
            if let Some(native) = root.cached_condition_output() {
                return written_integer_comparison(B::Native(native));
            }
            let KernelTermNode::IntegerCompare {
                operator,
                arguments,
            } = root.node()
            else {
                return None;
            };
            Some((
                *operator,
                arguments
                    .each_ref()
                    .map(|root| match root.written_argument() {
                        Some(crate::kernel::PureFunctionArgument::Integer(integer)) => {
                            integer.clone()
                        }
                        _ => SharedIntegerTerm::from_root(root.clone()),
                    }),
            ))
        }
    }
}

pub(crate) fn structural_integer_comparison_view(
    operator: IntegerComparisonOperator,
    operands: [&SharedIntegerTerm; 2],
) -> Option<StructuralComparisonView<'static>> {
    use crate::kernel::CompareRelation as R;
    use IntegerComparisonOperator as Op;
    let (relation, negated) = match operator {
        Op::Equal => (R::Equal, false),
        Op::NotEqual => (R::Equal, true),
        Op::LessThan => (R::LessThan, false),
        Op::LessEqual => (R::LessEqual, false),
        Op::GreaterThan => (R::GreaterThan, false),
        Op::GreaterEqual => (R::GreaterEqual, false),
    };
    let (ordered_relation, left, right) = order_integer_operands(operator, operands, true);
    let mut view = comparison_view_at_format_from_handles(ordered_relation, left, right)?;
    if matches!(relation, R::GreaterThan | R::GreaterEqual) {
        view.operands.swap(0, 1);
    }
    Some(StructuralComparisonView {
        format: view.format,
        relation,
        negated,
        operands: view.operands,
    })
}

fn integer_comparison_operands(
    condition: &OldConditionTerm,
) -> Option<(IntegerComparisonOperator, [&SharedIntegerTerm; 2])> {
    use IntegerComparisonOperator as Op;
    Some(match condition {
        OldConditionTerm::IntegerLessThan(left, right) => (Op::LessThan, [left, right]),
        OldConditionTerm::IntegerLessEqual(left, right) => (Op::LessEqual, [left, right]),
        OldConditionTerm::IntegerGreaterThan(left, right) => (Op::GreaterThan, [left, right]),
        OldConditionTerm::IntegerGreaterEqual(left, right) => (Op::GreaterEqual, [left, right]),
        OldConditionTerm::IntegerEqual(left, right) => (Op::Equal, [left, right]),
        OldConditionTerm::IntegerNotEqual(left, right) => (Op::NotEqual, [left, right]),
        _ => return None,
    })
}

/// An Integer comparison as `left REL right` with its truth folded in:
/// `>`/`>=` swap their operands, and a false comparison is negated.
pub(in crate::kernel) fn integer_relation(
    condition: &OldConditionTerm,
    value: bool,
) -> Option<(Relation, &SharedIntegerTerm, &SharedIntegerTerm)> {
    let (operator, operands) = integer_comparison_operands(condition)?;
    Some(order_integer_operands(operator, operands, value))
}

fn order_integer_operands<T>(
    operator: IntegerComparisonOperator,
    [left, right]: [T; 2],
    value: bool,
) -> (Relation, T, T) {
    use IntegerComparisonOperator as Op;
    let (relation, left, right) = match operator {
        Op::LessThan => (Relation::Less, left, right),
        Op::LessEqual => (Relation::LessEqual, left, right),
        Op::GreaterThan => (Relation::Less, right, left),
        Op::GreaterEqual => (Relation::LessEqual, right, left),
        Op::Equal => (Relation::Equal, left, right),
        Op::NotEqual => (Relation::NotEqual, left, right),
    };
    match (relation, value) {
        (relation, true) => (relation, left, right),
        (Relation::Less, false) => (Relation::LessEqual, right, left),
        (Relation::LessEqual, false) => (Relation::Less, right, left),
        (Relation::Equal, false) => (Relation::NotEqual, left, right),
        (Relation::NotEqual, false) => (Relation::Equal, left, right),
    }
}

/// The native machine comparison equivalent to the Integer comparison
/// `condition` with truth `value`, when both sides observe one machine
/// format exactly: `to_integer(x)` against `to_integer(y)` of the same
/// format, or against a constant that format represents. A constant outside
/// the format's range makes the Integer comparison decided by the range
/// alone; nothing is returned for it, nor for a format whose Integer
/// comparisons keep their Integer spelling
/// (`representation::spells_comparison_natively`).
pub(crate) fn native_comparison_of_integer_observation(
    condition: &OldConditionTerm,
    value: bool,
) -> Option<(OldConditionTerm, bool)> {
    native_comparison_view(condition, value)?.boxed_condition()
}

/// Decide a written machine comparison without assumptions. Wide equality
/// also admits expressions recognized by the native 64-bit constant reader.
pub(crate) fn literal_native_comparison_value(condition: BooleanOperandView<'_>) -> Option<bool> {
    use crate::kernel::{KernelMachineLiteral, MachineOperandView};
    let (format, relation, operands) = condition.comparison()?;
    let [left, right] = operands.map(|operand| match operand {
        MachineOperandView::Shared(root) if let Some(value) = root.written_machine_input() => {
            MachineOperandView::Old(value)
        }
        _ => operand,
    });
    if format.format().bits() > 64 {
        return None;
    }
    let literal_at = |operand: MachineOperandView<'_>, ty: MachineIntegerType| {
        if let Some((destination, value)) = operand.checked_literal_integer_conversion() {
            return KernelMachineLiteral::from_term_bits(destination, value.bits()).constant_at(ty);
        }
        match operand {
            MachineOperandView::Shared(root) => root.machine_literal()?.constant_at(ty),
            MachineOperandView::Old(term) => ty.constant_from_term(term),
        }
    };
    if format == MachineIntegerType::Int64 && relation == crate::kernel::CompareRelation::Equal {
        // Wide equality accepts the bits of either signedness, including
        // constant arithmetic. A top-level Integer conversion must be in range.
        let bits = |operand: MachineOperandView<'_>| {
            if operand.integer_conversion_destination().is_some() {
                let (destination, value) = operand.checked_literal_integer_conversion()?;
                return (destination.format().bits() == 64).then_some(value.bits() as u64);
            }
            operand.int64_constant().map(|n| n as u64)
        };
        return Some(bits(left)? == bits(right)?);
    }
    let left = literal_at(left, format)?;
    let right = literal_at(right, format)?;
    Some(relation.holds(left.to_i128()?, right.to_i128()?))
}

/// The value of a closed machine comparison, floating-point literal comparison,
/// Boolean literal or equality of Boolean literals.
pub(crate) fn closed_condition_value(condition: BooleanOperandView<'_>) -> Option<bool> {
    if let BooleanOperandView::Shared(root) = condition
        && let Some(native) = root.cached_condition_output()
    {
        return closed_condition_value(BooleanOperandView::Native(native));
    }
    if let Some(value) = condition.constant() {
        return Some(value);
    }
    if let Some([left, right]) = condition.equality() {
        return Some(left.constant()? == right.constant()?);
    }
    if let Some((format, operator, [left, right])) = condition.float_comparison() {
        return Some(format.compare_bits(left.literal_bits()?, right.literal_bits()?, operator));
    }
    literal_native_comparison_value(condition)
}

/// Whether a written machine comparison retains a simple int32 match operand.
pub(crate) fn retains_int32_match(
    format: MachineIntegerType,
    operands: [crate::kernel::MachineOperandView<'_>; 2],
) -> bool {
    format == MachineIntegerType::Int32
        && operands.into_iter().any(|operand| {
            matches!(operand, crate::kernel::MachineOperandView::Shared(root)
                if matches!(root.node(), crate::kernel::KernelTermNode::Match(matched)
                    if matched.has_simple_int32_arms()))
        })
}

/// Select a native equality over a retained int32 fold or its immediate sum.
/// Surface raises these operands as explicit Integer observations because
/// direct machine comparison syntax retains a different comparison node.
pub(crate) fn native_int32_fold_equality(
    condition: &OldConditionTerm,
) -> Option<[&OldMachineTerm; 2]> {
    let OldConditionTerm::Compare {
        format: MachineIntegerType::Int32,
        relation: crate::kernel::CompareRelation::Equal,
        left,
        right,
    } = condition
    else {
        return None;
    };
    let operands = [left.as_ref(), right.as_ref()];
    let is_fold = |operand: crate::kernel::MachineOperandView<'_>| operand.fold().is_some();
    operands
        .into_iter()
        .map(crate::kernel::MachineOperandView::Old)
        .any(|operand| {
            is_fold(operand)
                || operand.binary().is_some_and(|(format, operator, terms)| {
                    format == MachineIntegerType::Int32
                        && operator == crate::kernel::MachineBinaryOp::Add
                        && terms.into_iter().any(is_fold)
                })
        })
        .then_some(operands)
}

/// Preserve comparisons over literals, identical variables, and bounded
/// operations during logical lowering. Inspect only operand roots.
pub(crate) fn logical_condition_for_operand_views(
    format: MachineIntegerType,
    relation: crate::kernel::CompareRelation,
    operands: [crate::kernel::MachineOperandView<'_>; 2],
) -> OldConditionTerm {
    logical_comparison(format, relation, operands, false)
}

#[cfg(test)]
pub(in crate::kernel) fn logical_conditional_guard_for_operand_views(
    format: MachineIntegerType,
    relation: crate::kernel::CompareRelation,
    operands: [crate::kernel::MachineOperandView<'_>; 2],
) -> OldConditionTerm {
    logical_comparison(format, relation, operands, true)
}

/// Construct the logical comparison selected by specification lowering, keeping
/// the written operand formats for exact rewriting and condition export.
pub(in crate::kernel) fn stored_logical_comparison(
    format: MachineIntegerType,
    relation: crate::kernel::CompareRelation,
    operands: [crate::kernel::MachineOperandView<'_>; 2],
    in_conditional: bool,
) -> crate::kernel::StoredConditionTerm {
    use crate::kernel::{
        CompareRelation, KernelTermImport, MachineOperandView, StoredConditionTerm,
    };
    if format.format().bits() == 64
        && relation == CompareRelation::Equal
        && let [
            MachineOperandView::Old(left),
            MachineOperandView::Old(right),
        ] = operands
    {
        return StoredConditionTerm::logical_word64_equality(
            format,
            left.clone(),
            right.clone(),
            in_conditional,
        );
    }
    if let Some(words) = retained_comparison_operands(format, operands, in_conditional) {
        let (format, words) = retained_compare_words(format, relation, words);
        let mut import = KernelTermImport::for_exact_field_inputs();
        let arguments = words.each_ref().map(|word| import.machine(format, word));
        return StoredConditionTerm::from_root(KernelTerm::boolean_comparison_raw(
            format, relation, arguments,
        ))
        .expect("logical machine comparison");
    }
    StoredConditionTerm::from_minted(condition_for_operand_views_in(
        format, relation, operands, true,
    ))
}

fn logical_comparison(
    format: MachineIntegerType,
    relation: crate::kernel::CompareRelation,
    operands: [crate::kernel::MachineOperandView<'_>; 2],
    in_conditional: bool,
) -> OldConditionTerm {
    retained_comparison_operands(format, operands, in_conditional)
        .map(|[left, right]| retained_compare(format, relation, left, right))
        .unwrap_or_else(|| condition_for_operand_views_in(format, relation, operands, true))
}

pub(in crate::kernel) fn retained_comparison_operands(
    format: MachineIntegerType,
    operands: [crate::kernel::MachineOperandView<'_>; 2],
    in_conditional: bool,
) -> Option<[OldMachineTerm; 2]> {
    let variables = operands.map(|operand| operand.variable().copied());
    let [left, right] = if matches!(format.format().bits(), 32 | 64)
        && let [Some(left), Some(right)] = variables
        && left == right
    {
        [
            OldMachineTerm::Variable(left),
            OldMachineTerm::Variable(right),
        ]
    } else if format.format().bits() == 64
        && let [Some(left), Some(right)] = operands.map(pointer_address_operand)
        && left == right
    {
        // `address(p) == address(p)` names one address word twice.
        [left, right]
    } else if let [Some(left), Some(right)] = operands.map(|operand| operand.literal()) {
        [left, right]
    } else {
        if !matches!(format.format().bits(), 32 | 64) {
            return None;
        }
        let [left, right] =
            operands.map(|operand| bounded_comparison_operand(format, operand, in_conditional));
        if left.is_none() && right.is_none() {
            return None;
        }
        [
            left.or_else(|| comparison_leaf_operand(operands[0]))?,
            right.or_else(|| comparison_leaf_operand(operands[1]))?,
        ]
    };
    Some([left, right])
}

/// The native comparison of two retained operands, without deciding it.
fn retained_compare(
    format: MachineIntegerType,
    relation: crate::kernel::CompareRelation,
    left: OldMachineTerm,
    right: OldMachineTerm,
) -> OldConditionTerm {
    let (format, [left, right]) = retained_compare_words(format, relation, [left, right]);
    OldConditionTerm::Compare {
        format,
        relation,
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn retained_compare_words(
    format: MachineIntegerType,
    relation: crate::kernel::CompareRelation,
    words: [OldMachineTerm; 2],
) -> (MachineIntegerType, [OldMachineTerm; 2]) {
    // Native 32-bit comparisons read sign-free words; their format carries
    // the signedness. Keep the same operand representation as exact rewriting.
    let words = if format.format().bits() == 32 {
        words.map(OldMachineTerm::into_word32)
    } else {
        words
    };
    // Wide equality compares words, and its established native filing
    // format is Int64 even when the literal operands are unsigned
    // (`OldConditionTerm::int64_equal`). Narrower equality keeps its format.
    let format =
        if relation == crate::kernel::CompareRelation::Equal && format.format().bits() == 64 {
            MachineIntegerType::Int64
        } else {
            format
        };
    (format, words)
}

/// Whether logical lowering retained a comparison containing a bounded machine
/// operation. Conditional evaluation must retain it even when checking can decide
/// its truth intrinsically (a mask bound or reflexive operands, for example).
pub(crate) fn is_bounded_machine_comparison(condition: &crate::kernel::OldConditionTerm) -> bool {
    let crate::kernel::OldConditionTerm::Compare {
        format,
        left,
        right,
        ..
    } = condition
    else {
        return false;
    };
    if !matches!(format.format().bits(), 32 | 64) {
        return false;
    }
    use crate::kernel::MachineOperandView as V;
    let a = bounded_comparison_operand(*format, V::Old(left), true);
    let b = bounded_comparison_operand(*format, V::Old(right), true);
    (a.is_some() || b.is_some())
        && (a.is_some() || comparison_leaf_operand(V::Old(left)).is_some())
        && (b.is_some() || comparison_leaf_operand(V::Old(right)).is_some())
}

/// Read one literal/variable leaf without exporting an arithmetic root.
/// An address word `address(p)` as its comparison atom.
fn pointer_address_operand(
    operand: crate::kernel::MachineOperandView<'_>,
) -> Option<OldMachineTerm> {
    use crate::kernel::MachineOperandView as V;
    match operand {
        V::Shared(root)
            if matches!(
                root.node(),
                crate::kernel::KernelTermNode::IntegerAddress { .. }
            ) =>
        {
            root.machine_conversion_leaf().cloned()
        }
        V::Old(term @ OldMachineTerm::IntegerAddress(..)) => Some(term.clone()),
        _ => None,
    }
}

fn comparison_leaf_operand(
    operand: crate::kernel::MachineOperandView<'_>,
) -> Option<OldMachineTerm> {
    operand
        .literal()
        .or_else(|| operand.variable().copied().map(OldMachineTerm::Variable))
}

/// Read a bounded bitwise, shift, unsigned arithmetic, or word cast operand.
/// Inspect only immediate leaves. Use the established word encoding for
/// unsigned 32-bit arithmetic.
fn bounded_comparison_operand(
    observation: MachineIntegerType,
    operand: crate::kernel::MachineOperandView<'_>,
    in_conditional: bool,
) -> Option<OldMachineTerm> {
    if let Some((format, op @ crate::kernel::MachineUnaryOp::BitwiseNot, child)) = operand.unary()
        && matches!(format.format().bits(), 32 | 64)
    {
        crate::instrumentation::record_deterministic_work(1);
        return Some(OldMachineTerm::Unary {
            format,
            op,
            operand: Box::new(comparison_leaf_operand(child)?),
        });
    }
    if in_conditional
        && let Some((spelling, source, destination, child)) = operand.cast()
        && observation.format().bits() == destination.format().bits()
        && (matches!(
            spelling,
            crate::kernel::MachineCastSpelling::Int64From32
                | crate::kernel::MachineCastSpelling::Int64FromUInt32
                | crate::kernel::MachineCastSpelling::UInt64FromInt32
                | crate::kernel::MachineCastSpelling::UInt64From32
                | crate::kernel::MachineCastSpelling::UInt32From64
        ) || (child.variable().is_some()
            && (spelling == crate::kernel::MachineCastSpelling::UInt64FromInt64
                || (spelling == crate::kernel::MachineCastSpelling::Generic
                    && crate::kernel::is_sign_cast32(source, destination)))))
    {
        crate::instrumentation::record_deterministic_work(1);
        return Some(OldMachineTerm::cast_node(
            spelling,
            source,
            destination,
            comparison_leaf_operand(child)?,
        ));
    }
    let (format, operator, arguments) = operand.binary()?;
    let width = format.format().bits();
    if !matches!(width, 32 | 64) {
        return None;
    }
    use crate::kernel::MachineBinaryOp as O;
    let normalize_word32 = match operator {
        O::BitwiseAnd | O::BitwiseOr | O::BitwiseXor => false,
        O::Add | O::Subtract | O::Multiply if in_conditional => {
            let word32 = observation == MachineIntegerType::UInt32 && width == 32;
            let unsigned = !format.format().is_signed();
            match arguments.map(|argument| argument.variable().is_some()) {
                // Exact rewriting keeps the explicit operator format for
                // two variables. Arithmetic with a literal can use word32.
                [true, true] => false,
                [true, false] | [false, true] if unsigned || word32 => word32,
                _ => return None,
            }
        }
        // Read the literal in the operator's format. Signed -1 can overflow
        // for the minimum dividend, while an unsigned all-ones word is valid.
        O::Divide | O::Remainder
            if in_conditional
                && arguments[0].variable().is_some()
                && ((!format.format().is_signed() && arguments[1].variable().is_some())
                    || arguments[1]
                        .literal()
                        .and_then(|literal| format.constant_from_term(&literal))
                        .and_then(|constant| constant.to_i128())
                        .is_some_and(|divisor| !matches!(divisor, 0 | -1))) =>
        {
            false
        }
        O::ShiftRight | O::ShiftLeft
            if operator == O::ShiftRight || !format.format().is_signed() =>
        {
            let variable_shift = in_conditional
                && arguments
                    .iter()
                    .all(|argument| argument.variable().is_some());
            // Evaluation checks the shift domain before a fact may use it.
            if !variable_shift && super::bounds::constant_shift_count(arguments[1])? >= width {
                return None;
            }
            false
        }
        _ => return None,
    };
    crate::instrumentation::record_deterministic_work(1);
    let [left, right] = arguments.map(comparison_leaf_operand);
    let (left, right) = (left?, right?);
    let (format, left, right) = if normalize_word32 {
        (
            MachineIntegerType::Int32,
            left.into_word32(),
            right.into_word32(),
        )
    } else {
        (format, left, right)
    };
    Some(OldMachineTerm::Binary {
        format,
        op: operator,
        left: Box::new(left),
        right: Box::new(right),
    })
}

/// Read a fixed-size native conditional, including an immediate conditional
/// in either arm or as an immediate operand of its machine comparison guard.
/// The inner reader accepts only bounded operands.
fn conditional_atom(root: &crate::kernel::KernelTerm) -> Option<OldMachineTerm> {
    read_conditional_atom(root, |format, operand| {
        conditional_operand_atom(format, operand)
            .or_else(|| read_conditional_atom(operand, conditional_operand_atom))
    })
}

fn conditional_operand_atom(
    format: MachineIntegerType,
    root: &crate::kernel::KernelTerm,
) -> Option<OldMachineTerm> {
    let operand = crate::kernel::MachineOperandView::Shared(root);
    comparison_leaf_operand(operand).or_else(|| bounded_comparison_operand(format, operand, true))
}

fn read_conditional_atom(
    root: &crate::kernel::KernelTerm,
    operand: impl Fn(MachineIntegerType, &crate::kernel::KernelTerm) -> Option<OldMachineTerm>,
) -> Option<OldMachineTerm> {
    use crate::kernel::KernelTermNode as N;
    let N::MachineIf { arguments } = root.node() else {
        return None;
    };
    use crate::kernel::{KernelType, ProgramType};
    let result_format = match root.ty() {
        KernelType::Program(ProgramType::Int32) => MachineIntegerType::Int32,
        KernelType::Program(ProgramType::UInt32) => MachineIntegerType::UInt32,
        KernelType::Program(ProgramType::Int64) => MachineIntegerType::Int64,
        KernelType::Program(ProgramType::UInt64) => MachineIntegerType::UInt64,
        _ => return None,
    };
    crate::instrumentation::record_deterministic_work(1);
    let condition = match arguments[0].node() {
        N::Variable(variable) => OldConditionTerm::Variable(*variable),
        N::BoolEqual {
            arguments: [left, right],
        } => {
            let (N::Variable(left), N::Variable(right)) = (left.node(), right.node()) else {
                return None;
            };
            OldConditionTerm::BoolEqual(
                Box::new(OldConditionTerm::Variable(*left)),
                Box::new(OldConditionTerm::Variable(*right)),
            )
        }
        N::BoolCompare {
            format,
            relation,
            arguments: guard,
        } if matches!(format.format().bits(), 32 | 64) => {
            let mut left = operand(*format, &guard[0])?;
            let mut right = operand(*format, &guard[1])?;
            if format.format().bits() == 32 {
                left = left.into_word32();
                right = right.into_word32();
            }
            OldConditionTerm::Compare {
                format: *format,
                relation: *relation,
                left: Box::new(left),
                right: Box::new(right),
            }
        }
        _ => return None,
    };
    Some(OldMachineTerm::If {
        condition: Box::new(condition),
        then_term: Box::new(operand(result_format, &arguments[1])?),
        else_term: Box::new(operand(result_format, &arguments[2])?),
    })
}

/// Construct a checking comparison from two borrowed operands. Native inputs
/// and fixed-size atoms keep their written comparison; shared arithmetic stays
/// in exact observations. This never exports a shared arithmetic tree.
pub(crate) fn condition_for_operand_views(
    format: MachineIntegerType,
    relation: crate::kernel::CompareRelation,
    operands: [crate::kernel::MachineOperandView<'_>; 2],
) -> OldConditionTerm {
    condition_for_operand_views_in(format, relation, operands, false)
}

/// [`condition_for_operand_views`]. Under logical lowering (`structural`)
/// a comparison of two atoms the native constructor would decide because
/// they are the same atom or both literals keeps its comparison:
/// lowering `address(p) + 3u64 == address(p) + 3u64` or `(0 + 1) == 2`
/// does not compute its truth; checking does.
fn condition_for_operand_views_in(
    format: MachineIntegerType,
    relation: crate::kernel::CompareRelation,
    operands: [crate::kernel::MachineOperandView<'_>; 2],
    structural: bool,
) -> OldConditionTerm {
    use crate::kernel::{CompareRelation as R, MachineOperandView as V};
    if format == MachineIntegerType::Int64 && relation != R::Equal {
        let holds = |a, b| match relation {
            R::LessThan => a < b,
            R::LessEqual => a <= b,
            R::GreaterThan => a > b,
            R::GreaterEqual => a >= b,
            R::Equal => unreachable!(),
        };
        if let Some(value) = crate::kernel::primitives::int64_signed_order_by_width_views(
            operands[0],
            operands[1],
            holds,
        ) {
            return OldConditionTerm::Constant(value);
        }
    }
    if format == MachineIntegerType::UInt32
        && let Some(bound) = operands[1].literal().and_then(|word| word.constant32())
    {
        let upper = operands[0].unsigned32_upper_bound();
        let result = match relation {
            R::LessThan if upper < bound => Some(true),
            R::LessEqual if upper <= bound => Some(true),
            R::GreaterThan if upper <= bound => Some(false),
            R::GreaterEqual if upper < bound => Some(false),
            _ => None,
        };
        if let Some(result) = result {
            return OldConditionTerm::Constant(result);
        }
    }
    // Calls and pointer addresses remain native comparison atoms. Conversions
    // with an opaque Integer input also have a cached native reading, but
    // cannot be compared as shared machine observations.
    let operands = operands.map(|operand| match operand {
        V::Shared(root)
            if matches!(
                root.node(),
                crate::kernel::KernelTermNode::Call { .. }
                    | crate::kernel::KernelTermNode::IntegerAddress { .. }
            ) || (matches!(
                root.node(),
                crate::kernel::KernelTermNode::IntegerToMachine { .. }
            ) && !root.is_shared_machine_operand()) =>
        {
            V::Old(
                root.machine_conversion_leaf()
                    .expect("machine comparison atom"),
            )
        }
        operand => operand,
    });
    let atoms = operands.map(|operand| match operand {
        V::Shared(root) => root
            .machine_constant_reading()
            .map(|literal| literal.old_term())
            .or_else(|| operand.variable().copied().map(OldMachineTerm::Variable))
            .or_else(|| root.machine_read_leaf().cloned())
            .or_else(|| {
                // A signedness cast of one variable is still a fixed-size
                // atom. Keep the native guard spelling used by cited bounds;
                // never export a shared arithmetic operand here.
                let crate::kernel::KernelTermNode::MachineCast {
                    encoding: crate::kernel::MachineCastSpelling::Generic,
                    source,
                    destination,
                    operand,
                } = root.node()
                else {
                    return None;
                };
                if !crate::kernel::is_sign_cast32(*source, *destination) {
                    return None;
                }
                let crate::kernel::KernelTermNode::Variable(variable) = operand.node() else {
                    return None;
                };
                Some(OldMachineTerm::sign_cast32(
                    *source,
                    *destination,
                    OldMachineTerm::Variable(*variable),
                ))
            })
            .or_else(|| conditional_atom(root)),
        V::Old(_) => None,
    });
    let operands: [V<'_>; 2] =
        std::array::from_fn(|index| atoms[index].as_ref().map(V::Old).unwrap_or(operands[index]));
    if let [V::Old(left), V::Old(right)] = operands {
        let condition =
            OldConditionTerm::machine_compare(format, relation, left.clone(), right.clone());
        // Only identical or literal operands: a comparison the operands'
        // type range decides, such as `0u64 <= k`, keeps its established
        // decision.
        if structural
            && matches!(condition, OldConditionTerm::Constant(_))
            && matches!(format.format().bits(), 32 | 64)
            && (left == right
                || (format.constant_from_term(left).is_some()
                    && format.constant_from_term(right).is_some()))
        {
            return retained_compare(format, relation, left.clone(), right.clone());
        }
        return condition;
    }
    let [left, right] = operands.map(|operand| {
        if let Some(literal) = operand.literal() {
            // Native wide equality uses an Int64 word comparison even when
            // its literals were written as UInt64. Retain the word's bits
            // while giving its Integer observation the comparison's sign.
            let literal = match &literal {
                OldMachineTerm::Constant { format: source, .. }
                    if source.format().bits() == format.format().bits() =>
                {
                    OldMachineTerm::machine_integer_cast(*source, format, literal)
                }
                _ => literal,
            };
            IntegerTerm::from_machine(format, literal).expect("typed comparison literal")
        } else {
            IntegerTerm::Machine(match operand {
                V::Old(value) => SharedMachineIntegerTerm::intern(format, value.clone()),
                V::Shared(root) => SharedMachineIntegerTerm::observe_shared(
                    format,
                    root.with_machine_observation_type(format),
                )
                .expect("typed comparison operand"),
            })
        }
    });
    match relation {
        R::Equal => OldConditionTerm::integer_equal(left, right),
        R::LessThan => OldConditionTerm::integer_less_than(left, right),
        R::LessEqual => OldConditionTerm::integer_less_equal(left, right),
        R::GreaterThan => OldConditionTerm::integer_greater_than(left, right),
        R::GreaterEqual => OldConditionTerm::integer_greater_equal(left, right),
    }
}

/// Retain native arithmetic at an explicit checking boundary. This is a
/// syntax-only reading of the selected comparison, not a lowering policy.
pub(crate) fn retained_arithmetic_comparison(
    condition: &OldConditionTerm,
) -> Option<OldConditionTerm> {
    let OldConditionTerm::Compare {
        format,
        relation,
        left,
        right,
    } = condition
    else {
        return None;
    };
    if !matches!(
        format,
        MachineIntegerType::Int32
            | MachineIntegerType::UInt32
            | MachineIntegerType::Int64
            | MachineIntegerType::UInt64
    ) {
        return None;
    }
    use crate::kernel::{KernelTerm, MachineBinaryOp as O, MachineOperandView as V};
    let operands = [V::Old(left), V::Old(right)];
    let roots = operands.map(|operand| {
        operand
            .binary()
            .filter(|(_, op, _)| {
                matches!(
                    op,
                    O::Add
                        | O::Subtract
                        | O::Multiply
                        | O::Divide
                        | O::Remainder
                        | O::ShiftLeft
                        | O::ShiftRight
                )
            })
            .map(|_| KernelTerm::retained_machine_operand(*format, operand))
    });
    if roots.iter().all(Option::is_none) {
        return None;
    }
    Some(condition_for_operand_views(
        *format,
        *relation,
        std::array::from_fn(|i| roots[i].as_ref().map(V::Shared).unwrap_or(operands[i])),
    ))
}

/// A comparison query retaining its original shared operand identities.
/// Boxed conditions are an explicit compatibility output for unmigrated callers.
#[derive(Clone)]
pub(crate) struct NativeComparisonView<'a> {
    pub(crate) format: MachineIntegerType,
    pub(crate) relation: Relation,
    pub(crate) operands: [ComparisonOperand<'a>; 2],
}

#[derive(Clone)]
pub(crate) enum ComparisonOperand<'a> {
    Observation(SharedMachineIntegerTerm),
    Constant(OldMachineTerm),
    Written(&'a OldMachineTerm),
}

impl ComparisonOperand<'_> {
    pub(crate) fn operand_view(&self) -> crate::kernel::MachineOperandView<'_> {
        match self {
            Self::Observation(machine) => machine.operand_view(),
            Self::Constant(value) => crate::kernel::MachineOperandView::Old(value),
            Self::Written(value) => crate::kernel::MachineOperandView::Old(value),
        }
    }

    pub(super) fn boxed_value(&self) -> &OldMachineTerm {
        match self {
            Self::Observation(machine) => machine.value(),
            Self::Constant(value) => value,
            Self::Written(value) => value,
        }
    }
}

impl NativeComparisonView<'_> {
    /// A shared reading of the existing 32-bit additive cancellation rule.
    /// Only the selected roots and at most four child identities are inspected.
    pub(crate) fn cancelled_equality(&self) -> Option<NativeComparisonView<'static>> {
        use crate::kernel::{KernelTermImport, MachineBinaryOp, MachineOperandView as V};
        if self.format.format().bits() != 32
            || !matches!(self.relation, Relation::Equal | Relation::NotEqual)
        {
            return None;
        }
        let [left, right] = self
            .operands
            .each_ref()
            .map(|operand| operand.operand_view());
        fn sum(view: V<'_>) -> Option<(MachineIntegerType, MachineBinaryOp, [V<'_>; 2])> {
            view.binary().filter(|(format, operation, _)| {
                format.format().bits() == 32 && *operation == MachineBinaryOp::Add
            })
        }
        let same = |format, a: V<'_>, b: V<'_>| match (a, b) {
            (V::Shared(a), V::Shared(b)) => a == b,
            (V::Old(a), V::Old(b)) => a == b,
            (V::Shared(a), V::Old(b)) | (V::Old(b), V::Shared(a)) => {
                KernelTermImport::default()
                    .machine_arithmetic(format, b)
                    .as_ref()
                    == Some(a)
            }
        };
        let owned = |view: V<'_>| match view {
            V::Shared(_) => ComparisonOperand::Observation(view.retain(self.format)),
            V::Old(term) => ComparisonOperand::Constant(term.clone()),
        };
        let result = |a, b| NativeComparisonView {
            format: self.format,
            relation: self.relation,
            operands: [a, b],
        };
        if let (Some((lf, _, [a, b])), Some((rf, _, [c, d]))) = (sum(left), sum(right))
            && lf == rf
        {
            for ((kept, other), (matched, remainder)) in [
                ((a, b), (c, d)),
                ((a, b), (d, c)),
                ((b, a), (c, d)),
                ((b, a), (d, c)),
            ] {
                if same(lf, kept, matched) {
                    return Some(result(owned(other), owned(remainder)));
                }
            }
        }
        for (side, partner, reverse) in [(left, right, false), (right, left, true)] {
            if let Some((format, _, [a, b])) = sum(side) {
                for (kept, other) in [(a, b), (b, a)] {
                    if same(format, kept, partner) {
                        let zero =
                            ComparisonOperand::Constant(OldMachineTerm::constant_at32(format, 0));
                        return Some(if reverse {
                            result(zero, owned(other))
                        } else {
                            result(owned(other), zero)
                        });
                    }
                }
            }
        }
        None
    }

    pub(crate) fn cancelled_form(mut self) -> Self {
        while let Some(next) = self.cancelled_equality() {
            self = next;
        }
        self
    }

    /// The value-preserving 32-bit reading of a narrow comparison, retaining
    /// shared operands. Checking folds only the two cast roots.
    pub(crate) fn widened(&self) -> Option<NativeComparisonView<'static>> {
        if self.format.format().bits() >= 32 {
            return None;
        }
        let destination = MachineIntegerType::Int32;
        let operands = self
            .operands
            .each_ref()
            .map(|operand| match operand.operand_view() {
                crate::kernel::MachineOperandView::Shared(term) => ComparisonOperand::Observation(
                    SharedMachineIntegerTerm::from_shared(
                        destination,
                        term.checking_machine_cast(self.format, destination),
                    )
                    .expect("shared widening"),
                ),
                crate::kernel::MachineOperandView::Old(term) => ComparisonOperand::Constant(
                    super::conversion::convert_term(self.format, destination, term.clone()),
                ),
            });
        Some(NativeComparisonView {
            format: destination,
            relation: self.relation,
            operands,
        })
    }

    /// An exact Integer reading retaining the carrier's shared operands.
    /// This is a checking consequence; the original lowered term is untouched.
    pub(crate) fn integer_condition(&self) -> OldConditionTerm {
        let [left, right] = self.operands.each_ref().map(|operand| match operand {
            ComparisonOperand::Observation(value) => IntegerTerm::Machine(value.clone()).into(),
            other => IntegerTerm::from_machine(self.format, other.boxed_value().clone())
                .expect("comparison carrier has its declared format")
                .into(),
        });
        match self.relation {
            Relation::Equal => OldConditionTerm::IntegerEqual(left, right),
            Relation::NotEqual => OldConditionTerm::IntegerNotEqual(left, right),
            Relation::Less => OldConditionTerm::IntegerLessThan(left, right),
            Relation::LessEqual => OldConditionTerm::IntegerLessEqual(left, right),
        }
    }

    /// Match the native comparison representation's polarity for exact
    /// quantified-body identity: disequality is a false equality.
    pub(crate) fn integer_proposition(&self) -> crate::kernel::Proposition {
        let condition = self.integer_condition();
        if let OldConditionTerm::IntegerNotEqual(left, right) = condition {
            crate::kernel::Proposition::condition_is(
                OldConditionTerm::IntegerEqual(left, right),
                false,
            )
        } else {
            crate::kernel::Proposition::condition_is(condition, true)
        }
    }

    /// A checking reading that retains arithmetic in the shared arena.
    /// Only fixed-size leaves and already-written native operands use Compare.
    pub(crate) fn retained_condition(&self) -> (OldConditionTerm, bool) {
        use crate::kernel::CompareRelation as R;
        let relation = match self.relation {
            Relation::Equal | Relation::NotEqual => R::Equal,
            Relation::Less => R::LessThan,
            Relation::LessEqual => R::LessEqual,
        };
        (
            condition_for_operand_views(
                self.format,
                relation,
                self.operands
                    .each_ref()
                    .map(|operand| operand.operand_view()),
            ),
            self.relation != Relation::NotEqual,
        )
    }

    pub(crate) fn boxed_condition(&self) -> Option<(OldConditionTerm, bool)> {
        representation::comparison(
            self.format,
            self.relation,
            self.operands[0].boxed_value().clone(),
            self.operands[1].boxed_value().clone(),
        )
    }
}

/// One view for written native comparisons and exact Integer observations.
/// Native operands are borrowed; Integer operands retain their shared handles.
pub(crate) fn comparison_view(
    condition: &OldConditionTerm,
    value: bool,
) -> Option<NativeComparisonView<'_>> {
    use crate::kernel::CompareRelation as R;
    let OldConditionTerm::Compare {
        format,
        relation,
        left,
        right,
    } = condition
    else {
        return native_comparison_view(condition, value).map(NativeComparisonView::cancelled_form);
    };
    let (relation, left, right) = match (relation, value) {
        (R::Equal, true) => (Relation::Equal, left, right),
        (R::Equal, false) => (Relation::NotEqual, left, right),
        (R::LessThan, true) | (R::GreaterEqual, false) => (Relation::Less, left, right),
        (R::LessEqual, true) | (R::GreaterThan, false) => (Relation::LessEqual, left, right),
        (R::GreaterThan, true) | (R::LessEqual, false) => (Relation::Less, right, left),
        (R::GreaterEqual, true) | (R::LessThan, false) => (Relation::LessEqual, right, left),
    };
    Some(NativeComparisonView {
        format: *format,
        relation,
        operands: [
            ComparisonOperand::Written(left),
            ComparisonOperand::Written(right),
        ],
    })
}

pub(crate) fn native_comparison_view(
    condition: &OldConditionTerm,
    value: bool,
) -> Option<NativeComparisonView<'static>> {
    let (operator, operands) = integer_comparison_operands(condition)?;
    native_comparison_from_integer_operands(operator, operands, value)
}

/// Read a shared Integer comparison for the memory-erased fact index.
/// The outer option is absent if a compatibility operand is still needed.
/// The inner option is absent when this comparison has only an exact key.
pub(crate) fn retained_integer_observation_comparison(
    operator: IntegerComparisonOperator,
    arguments: &[KernelTerm; 2],
    value: bool,
) -> Option<Option<NativeComparisonView<'static>>> {
    use KernelTermNode as Node;
    if !arguments
        .iter()
        .any(|argument| matches!(argument.node(), Node::MachineObservation { .. }))
        || arguments.iter().any(|argument| {
            matches!(
                argument.node(),
                Node::Variable(_)
                    | Node::Call { .. }
                    | Node::Fold(_)
                    | Node::IntegerIf { .. }
                    | Node::Match(_)
            ) || matches!(argument.node(), Node::IntegerLiteral(value) if value.bits() > 128)
        })
    {
        // Only a machine observation or literal arithmetic can change its
        // outer form. A literal wider than any machine format has no bridge.
        return Some(None);
    }
    let operand = |argument: &KernelTerm| -> Option<SharedIntegerTerm> {
        match argument.node() {
            Node::MachineObservation { format, operand } => Some(
                IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(
                    *format,
                    operand.clone(),
                )?)
                .into(),
            ),
            Node::IntegerLiteral(value) => Some(IntegerTerm::Constant(value.clone()).into()),
            _ => None,
        }
    };
    let [left, right] = arguments.each_ref().map(operand);
    Some(native_comparison_from_integer_operands(
        operator,
        [&left?, &right?],
        value,
    ))
}

pub(crate) fn native_comparison_from_integer_operands(
    operator: IntegerComparisonOperator,
    written: [&SharedIntegerTerm; 2],
    value: bool,
) -> Option<NativeComparisonView<'static>> {
    // Numeric evaluation belongs in the checking comparison form. Surface
    // lowering uses the structural reading below, retaining arithmetic.
    // An observation is read through its value relations (rule W):
    // `to_integer(d as int128) != 0` is `d != 0`.
    let operand = |term: &SharedIntegerTerm| -> Option<SharedIntegerTerm> {
        let read = term.value_read();
        if !std::ptr::eq(read, term.as_ref()) {
            return Some(read.clone().into());
        }
        if !term.is_literal_arithmetic() || term.as_const().is_some() {
            return Some(term.clone());
        }
        crate::kernel::proof::integer_arithmetic::literal_integer_value(term)
            .map(|value| IntegerTerm::constant(value).into())
    };
    let [left, right] = written;
    let (read_left, read_right) = (operand(left)?, operand(right)?);
    let (relation, left, right) =
        order_integer_operands(operator, [read_left.as_ref(), read_right.as_ref()], value);
    // Exact extensions can expose different formats. Retry at the written
    // formats when the value readings no longer share a machine format.
    structural_native_comparison_from_operands(relation, left, right).or_else(|| {
        let (relation, left, right) =
            order_integer_operands(operator, written.map(SharedIntegerTerm::as_ref), value);
        structural_native_comparison_from_operands(relation, left, right)
    })
}

pub(crate) fn structural_native_comparison_of_integer_observation(
    condition: &OldConditionTerm,
    value: bool,
) -> Option<(OldConditionTerm, bool)> {
    structural_native_comparison_view(condition, value)?.boxed_condition()
}

/// The machine spelling of a specification comparison, when its immediate
/// Integer operands observe one machine format and the comparison stays nonconstant.
pub(in crate::kernel) fn stored_machine_spelling(
    operator: IntegerComparisonOperator,
    operands: [&KernelTerm; 2],
) -> Option<(crate::kernel::StoredConditionTerm, bool)> {
    use crate::kernel::{KernelTermImport, StoredConditionTerm};

    match operands.map(KernelTerm::node) {
        [
            KernelTermNode::MachineObservation { .. },
            KernelTermNode::MachineObservation { .. },
        ]
        | [
            KernelTermNode::MachineObservation { .. },
            KernelTermNode::IntegerLiteral(_),
        ]
        | [
            KernelTermNode::IntegerLiteral(_),
            KernelTermNode::MachineObservation { .. },
        ] => {}
        _ => return None,
    }
    let (relation, left, right) = order_integer_operands(operator, operands, true);
    let (native, truth) = structural_native_comparison_from_operands(
        relation,
        left.integer_native_compat()?,
        right.integer_native_compat()?,
    )?
    .boxed_condition()?;
    if matches!(native, OldConditionTerm::Constant(_)) {
        return None;
    }
    if let OldConditionTerm::Compare {
        format,
        relation,
        left: written_left,
        right: written_right,
    } = &native
    {
        // Canonical comparison construction preserves a variable observation
        // and converts a literal to the selected machine format. More complex
        // operands can be rewritten and must come from the canonical output.
        let operand = |root: &KernelTerm, written: &OldMachineTerm| match root.node() {
            KernelTermNode::MachineObservation { operand, .. }
                if matches!(operand.node(), KernelTermNode::Variable(_)) =>
            {
                Some(operand.with_machine_observation_type(*format))
            }
            KernelTermNode::IntegerLiteral(_) => {
                Some(KernelTermImport::for_exact_field_inputs().machine(*format, written))
            }
            _ => None,
        };
        if let (Some(a), Some(b)) = (operand(left, written_left), operand(right, written_right)) {
            let root = KernelTerm::boolean_comparison_raw(*format, *relation, [a, b]);
            root.retain_old_condition_output(native);
            return Some((
                StoredConditionTerm::from_root(root).expect("machine comparison"),
                truth,
            ));
        }
    }
    Some((StoredConditionTerm::from_minted(native), truth))
}

pub(crate) fn structural_native_comparison_view(
    condition: &OldConditionTerm,
    value: bool,
) -> Option<NativeComparisonView<'static>> {
    let (operator, operands) = integer_comparison_operands(condition)?;
    structural_comparison_from_integer_operands(operator, operands, value)
}

pub(crate) fn structural_comparison_from_integer_operands(
    operator: IntegerComparisonOperator,
    operands: [&SharedIntegerTerm; 2],
    value: bool,
) -> Option<NativeComparisonView<'static>> {
    let (relation, left, right) = order_integer_operands(operator, operands, value);
    structural_native_comparison_from_operands(relation, left, right)
}

fn structural_native_comparison_from_operands(
    relation: Relation,
    left: &IntegerTerm,
    right: &IntegerTerm,
) -> Option<NativeComparisonView<'static>> {
    // A 128-bit comparison has a native node, but the kernel's order
    // reasoning (the difference graph, interval bounds) works on its
    // Integer form, so an Integer comparison of 128-bit observations keeps
    // that spelling (`representation::spells_comparison_natively`).
    let spelled_natively = |side: &IntegerTerm| match side {
        IntegerTerm::Machine(machine) => representation::spells_comparison_natively(machine.ty()),
        _ => true,
    };
    if !spelled_natively(left) || !spelled_natively(right) {
        return None;
    }
    comparison_view_at_format_from_operands(relation, left, right)
}

/// Whether `proposition` is an Integer comparison of exact observations of
/// a 128-bit format (or of one and a constant it represents): the reading
/// of that format's native comparison, which keeps its Integer spelling
/// ([`representation::spells_comparison_natively`]). One match on the root
/// and the two sides.
pub(crate) fn reads_wide_integer_observations(proposition: &Proposition) -> bool {
    let Proposition::ConditionIs(condition, value) = proposition else {
        return false;
    };
    comparison_view_at_format(condition.old_form(), *value)
        .is_some_and(|view| !representation::spells_comparison_natively(view.format))
}

/// [`native_comparison_of_integer_observation`] at every format, whatever
/// its spelling: the forward map the converse reading checks against.
fn native_comparison_at_format(
    condition: &OldConditionTerm,
    value: bool,
) -> Option<(OldConditionTerm, bool)> {
    comparison_view_at_format(condition, value)?.boxed_condition()
}

fn comparison_view_at_format(
    condition: &OldConditionTerm,
    value: bool,
) -> Option<NativeComparisonView<'static>> {
    let (relation, left, right) = integer_relation(condition, value)?;
    comparison_view_at_format_from_handles(relation, left, right)
}

fn comparison_view_at_format_from_handles(
    relation: Relation,
    left: &SharedIntegerTerm,
    right: &SharedIntegerTerm,
) -> Option<NativeComparisonView<'static>> {
    if [left, right].iter().any(|operand| {
        !matches!(
            operand.root().node(),
            KernelTermNode::MachineObservation { .. } | KernelTermNode::IntegerLiteral(_)
        )
    }) {
        return None;
    }
    comparison_view_at_format_from_operands(relation, left, right)
}

fn comparison_view_at_format_from_operands(
    relation: Relation,
    left: &IntegerTerm,
    right: &IntegerTerm,
) -> Option<NativeComparisonView<'static>> {
    let ty = match (left, right) {
        (IntegerTerm::Machine(left), IntegerTerm::Machine(right)) if left.ty() == right.ty() => {
            left.ty()
        }
        (IntegerTerm::Machine(machine), IntegerTerm::Constant(_))
        | (IntegerTerm::Constant(_), IntegerTerm::Machine(machine)) => machine.ty(),
        _ => return None,
    };
    // An 8- or 16-bit observation is a native value of its format, compared
    // natively at it; a constant is that format's constant. An observation
    // whose operand is a word of another width (the byte of a 32-bit sum)
    // has no native comparison: its root width, read in O(1), decides.
    let narrow = ty.format().bits() < 32;
    let carrier = |side: &IntegerTerm| -> Option<ComparisonOperand<'static>> {
        match side {
            IntegerTerm::Machine(machine)
                if narrow
                    && machine.operand_view().root_width().is_some_and(|width| {
                        width != crate::kernel::CarrierWidth::of_machine_type(ty)
                    }) =>
            {
                None
            }
            IntegerTerm::Machine(machine) => Some(ComparisonOperand::Observation(machine.clone())),
            IntegerTerm::Constant(constant) => Some(ComparisonOperand::Constant(
                range::constant_word(ty, constant)?,
            )),
            _ => None,
        }
    };
    let left = carrier(left)?;
    let right = carrier(right)?;
    Some(NativeComparisonView {
        format: ty,
        relation,
        operands: [left, right],
    })
}

/// The native comparison an Integer comparison holds exactly when, read
/// through in-range machine operations: each side that is the exact value
/// of a machine `+` or `-` of observations of one format is replaced by
/// that operation's observation
/// (`identity::machine_operation_of_integer_value`), and the result is read
/// as [`native_comparison_of_integer_observation`] reads it.
/// `to_integer(a) <= 4294967295 - to_integer(b)` on `uint32` reads as
/// `a <= 4294967295u32 - b`. The returned bounds are what each replaced
/// operation needs to equal its exact value; the reading holds only with
/// them. A comparison with no operation side, or whose native form folds
/// to a constant, has no such reading. At most one candidate format per
/// observation the two sides name is tried; nothing else is visited.
#[cfg(test)]
pub(crate) fn native_comparison_through_integer_operations(
    condition: &OldConditionTerm,
    value: bool,
) -> Option<(
    OldConditionTerm,
    bool,
    Vec<identity::IntegerOperationRangeBound>,
)> {
    let (view, bounds) = comparison_view_through_integer_operations(condition, value)?;
    match view.boxed_condition()? {
        (OldConditionTerm::Constant(_), _) => None,
        (native, truth) => Some((native, truth, bounds)),
    }
}

/// The operation bridge before any legacy condition is exported. Range
/// premises are explicit outputs, so callers retain the same authority checks.
pub(crate) fn comparison_view_through_integer_operations(
    condition: &OldConditionTerm,
    value: bool,
) -> Option<(
    NativeComparisonView<'static>,
    Vec<identity::IntegerOperationRangeBound>,
)> {
    let (left, right) = match condition {
        OldConditionTerm::IntegerLessThan(left, right)
        | OldConditionTerm::IntegerLessEqual(left, right)
        | OldConditionTerm::IntegerGreaterThan(left, right)
        | OldConditionTerm::IntegerGreaterEqual(left, right)
        | OldConditionTerm::IntegerEqual(left, right)
        | OldConditionTerm::IntegerNotEqual(left, right) => {
            // Each side is read through its observations' value relations
            // (rule W), so `to_integer(x as uint32) + 1` is an operation on
            // `x`'s own format. Both readings are cached on the sides.
            (&**left.read_through_ref(), &**right.read_through_ref())
        }
        _ => return None,
    };
    let operation =
        |side: &IntegerTerm| matches!(side, IntegerTerm::Add(..) | IntegerTerm::Subtract(..));
    if !operation(left) && !operation(right) {
        return None;
    }
    // The machine formats the sides observe, directly or as operands.
    let mut types = Vec::new();
    for side in [left, right] {
        let operands = match side {
            IntegerTerm::Add(a, b) | IntegerTerm::Subtract(a, b) => vec![&**a, &**b],
            other => vec![other],
        };
        for operand in operands {
            if let IntegerTerm::Machine(machine) = operand
                && !types.contains(&machine.ty())
            {
                types.push(machine.ty());
            }
        }
    }
    types.into_iter().find_map(|ty| {
        let mut bounds = Vec::new();
        let mut read = |side: &IntegerTerm| -> Option<IntegerTerm> {
            if !operation(side) {
                return Some(side.clone());
            }
            let (observed, needed) = identity::machine_operation_of_integer_value(side, ty)?;
            bounds.extend(needed);
            Some(observed)
        };
        let (left, right) = (read(left)?, read(right)?);
        let (left, right): (SharedIntegerTerm, SharedIntegerTerm) = (left.into(), right.into());
        let read = match condition {
            OldConditionTerm::IntegerLessThan(..) => OldConditionTerm::IntegerLessThan(left, right),
            OldConditionTerm::IntegerLessEqual(..) => {
                OldConditionTerm::IntegerLessEqual(left, right)
            }
            OldConditionTerm::IntegerGreaterThan(..) => {
                OldConditionTerm::IntegerGreaterThan(left, right)
            }
            OldConditionTerm::IntegerGreaterEqual(..) => {
                OldConditionTerm::IntegerGreaterEqual(left, right)
            }
            OldConditionTerm::IntegerEqual(..) => OldConditionTerm::IntegerEqual(left, right),
            _ => OldConditionTerm::IntegerNotEqual(left, right),
        };
        Some((native_comparison_view(&read, value)?, bounds))
    })
}

/// The Integer readings of a native comparison fact
/// ([`integer_observations_of_native_comparison`]), and of a promoted
/// comparison of widenings ([`integer_comparisons_of_widenings`]). A native
/// 8- or 16-bit comparison is the same fact as the `int32` comparison of
/// its operands' widenings (rule K8, [`narrow_comparison_as_int32`]), so it
/// has that comparison's readings.
pub(crate) fn integer_readings_with_promotions(proposition: &Proposition) -> Vec<Proposition> {
    if let Proposition::ConditionIs(condition, value) = proposition {
        let promoted = narrow_comparison_as_int32(condition.old_form());
        let widened = integer_comparisons_of_widenings(
            promoted.as_ref().unwrap_or(condition.old_form()),
            *value,
        );
        if !widened.is_empty() {
            return widened;
        }
    }
    integer_observations_of_native_comparison(proposition)
}

/// A native 8- or 16-bit comparison as the signed `int32` comparison of its
/// operands' widenings, which hold the same values (rule K8): `a <=_u8 b`
/// holds exactly when `widen(a) <= widen(b)` does. Order and interval
/// reasoning keeps its facts on 32-bit terms; this is its one bridge to a
/// native narrow fact, filed beside it and consulted for a native goal. The
/// comparison is built by the folding constructor, so it is the same term a
/// promoted comparison of the widenings is. `None` for any other condition.
/// One match on the root and two widenings.
pub(crate) fn narrow_comparison_as_int32(condition: &OldConditionTerm) -> Option<OldConditionTerm> {
    let OldConditionTerm::Compare {
        format,
        relation,
        left,
        right,
    } = condition
    else {
        return None;
    };
    if format.format().bits() >= 32 {
        return None;
    }
    let widen = |term: &OldMachineTerm| {
        super::conversion::convert_term(*format, MachineIntegerType::Int32, term.clone())
    };
    Some(OldConditionTerm::machine_compare(
        MachineIntegerType::Int32,
        *relation,
        widen(left),
        widen(right),
    ))
}

/// The `int32` spelling a native 8- or 16-bit comparison fact is also filed
/// under by the 32-bit indexes (order bounds, the `int32` equality graph,
/// scalar evidence, exact constants, truth nodes), which read that
/// spelling: [`narrow_comparison_as_int32`], unless it folds to a constant.
/// Each index files it inside its own adjuster, so assuming, forgetting and
/// rebuilding a fact agree.
pub(crate) fn narrow_fact_widening(condition: &OldConditionTerm) -> Option<OldConditionTerm> {
    narrow_comparison_as_int32(condition)
        .filter(|widened| !matches!(widened, OldConditionTerm::Constant(_)))
}

/// The native 8- or 16-bit comparison a promoted `int32` comparison of
/// widenings from one narrow format is the same fact as (rule K8), spelled
/// natively: the reverse of [`narrow_comparison_as_int32`], read through
/// [`OldConditionTerm::comparison_fact`]. A Rust comparison of two narrow
/// values states this native comparison. `None` for any other condition.
pub(crate) fn native_narrow_comparison(condition: &OldConditionTerm) -> Option<OldConditionTerm> {
    let OldConditionTerm::Compare {
        format: MachineIntegerType::Int32,
        ..
    } = condition
    else {
        return None;
    };
    let (format, relation, left, right) = condition.comparison_fact()?;
    (format.format().bits() < 32).then(|| {
        OldConditionTerm::narrow_compare(
            format,
            relation,
            left.term(format).into_owned(),
            right.term(format).into_owned(),
        )
    })
}

/// [`narrow_comparison_as_int32`] of a condition fact, with its truth.
pub(crate) fn narrow_proposition_as_int32(proposition: &Proposition) -> Option<Proposition> {
    let Proposition::ConditionIs(condition, value) = proposition else {
        return None;
    };
    narrow_comparison_as_int32(condition.old_form())
        .map(|widened| Proposition::condition_is(widened, *value))
}

/// C compares an 8- or 16-bit value through its widening to `int32`
/// (rule C2): a signed 32-bit comparison whose sides are each such a
/// widening or a constant, at least one a widening, is the Integer
/// comparison of the sides' values, which a widening preserves (K8):
/// `0 <= widen(x)` is `0 <= to_integer(x as int32)`, which the Integer
/// engines read as `0 <= to_integer(x)` (rule W: a widening's observation is
/// built as written and read through to its operand's), so there is one
/// reading. One match on the two sides.
fn integer_comparisons_of_widenings(condition: &OldConditionTerm, value: bool) -> Vec<Proposition> {
    use crate::kernel::CompareRelation as R;
    let OldConditionTerm::Compare {
        format: MachineIntegerType::Int32,
        relation,
        left,
        right,
    } = condition
    else {
        return Vec::new();
    };
    let widening = |side: &OldMachineTerm| side.narrow_widening32_operand().is_some();
    if !widening(left) && !widening(right) {
        return Vec::new();
    }
    let side = |term: &OldMachineTerm| -> Option<SharedIntegerTerm> {
        if !widening(term) && term.constant32().is_none() {
            return None;
        }
        IntegerTerm::from_machine(MachineIntegerType::Int32, term.clone()).map(Into::into)
    };
    let (Some(l), Some(r)) = (side(left), side(right)) else {
        return Vec::new();
    };
    let (condition, truth) = match (relation, value) {
        (R::Equal, truth) => (OldConditionTerm::IntegerEqual(l, r), truth),
        (R::LessThan, true) | (R::GreaterEqual, false) => {
            (OldConditionTerm::IntegerLessThan(l, r), true)
        }
        (R::LessEqual, true) | (R::GreaterThan, false) => {
            (OldConditionTerm::IntegerLessEqual(l, r), true)
        }
        (R::GreaterThan, true) | (R::LessEqual, false) => {
            (OldConditionTerm::IntegerLessThan(r, l), true)
        }
        (R::GreaterEqual, true) | (R::LessThan, false) => {
            (OldConditionTerm::IntegerLessEqual(r, l), true)
        }
    };
    vec![Proposition::condition_is(condition, truth)]
}

/// The Integer comparisons of exact observations whose native comparison
/// ([`native_comparison_of_integer_observation`]) is exactly `proposition`,
/// a native comparison fact: `1u32 <= x` gives `1 <= to_integer(x)`. Each
/// candidate is recomputed through the forward map, so only exact
/// converses, up to the fact's equivalent order spellings, are returned. A
/// 32-bit word equality may read as `int32` or as `uint32`
/// (`representation::comparison_readings`).
pub(crate) fn integer_observations_of_native_comparison(
    proposition: &Proposition,
) -> Vec<Proposition> {
    let Proposition::ConditionIs(condition, value) = proposition else {
        return Vec::new();
    };
    if matches!(
        condition.root().map(KernelTerm::node),
        Some(KernelTermNode::IntegerCompare { .. })
    ) {
        return Vec::new();
    }
    let Some((left, right, types)) = representation::comparison_readings(condition.old_form())
    else {
        return Vec::new();
    };
    // A native order has four spellings (`a >= 1` is `1 <= a`, and a false
    // `0 < x` is `x <= 0`) in every order family; the forward map produces
    // one, so compare against all of them.
    let spellings = crate::kernel::proof::fact_reasoning::order_claim_forms(proposition);
    let mut lifted = Vec::new();
    for &ty in types {
        let (Some(left), Some(right)) = (
            IntegerTerm::from_machine(ty, left.clone()),
            IntegerTerm::from_machine(ty, right.clone()),
        ) else {
            continue;
        };
        let (left, right): (SharedIntegerTerm, SharedIntegerTerm) = (left.into(), right.into());
        let candidates = [
            OldConditionTerm::IntegerLessEqual(left.clone(), right.clone()),
            OldConditionTerm::IntegerLessThan(left.clone(), right.clone()),
            OldConditionTerm::IntegerLessEqual(right.clone(), left.clone()),
            OldConditionTerm::IntegerLessThan(right.clone(), left.clone()),
            OldConditionTerm::IntegerEqual(left.clone(), right.clone()),
        ];
        for candidate in candidates {
            let truth = if matches!(candidate, OldConditionTerm::IntegerEqual(..)) {
                *value
            } else {
                true
            };
            if native_comparison_at_format(&candidate, truth).is_some_and(
                |(native, native_truth)| {
                    let native = Proposition::condition_is(native, native_truth);
                    &native == proposition || spellings.contains(&native)
                },
            ) {
                lifted.push(Proposition::condition_is(candidate, truth));
                break;
            }
        }
    }
    lifted
}

#[cfg(test)]
mod borrowed_comparison_tests {
    use super::*;

    mod scaling_tests {
        include!(
            "../../scaling_tests/kernel/machine_integer/comparison/borrowed_comparison_tests.rs"
        );
    }

    use crate::kernel::{CompareRelation as R, MachineOperandView, Variable};

    #[test]
    fn literal_native_orders_are_builtin_truths_without_ambient_facts() {
        for format in [
            MachineIntegerType::Int8,
            MachineIntegerType::UInt8,
            MachineIntegerType::Int16,
            MachineIntegerType::UInt16,
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let signed = format.format().is_signed();
            let value = if signed {
                (-1).into()
            } else {
                format.format().bounds().1
            };
            let left = range::constant_word(format, &value).unwrap();
            let right = range::constant_word(format, &0.into()).unwrap();
            for (relation, expected) in [
                (R::Equal, false),
                (R::LessThan, signed),
                (R::LessEqual, signed),
                (R::GreaterThan, !signed),
                (R::GreaterEqual, !signed),
            ] {
                let condition = OldConditionTerm::Compare {
                    format,
                    relation,
                    left: Box::new(left.clone()),
                    right: Box::new(right.clone()),
                };
                assert_eq!(
                    literal_native_comparison_value(BooleanOperandView::Native(&condition)),
                    Some(expected)
                );
                let shared = crate::kernel::KernelTermImport::default().condition(&condition);
                assert_eq!(
                    closed_condition_value(BooleanOperandView::Shared(&shared)),
                    Some(expected)
                );
                assert!(!shared.has_cached_native_argument());
                for truth in [true, false] {
                    let proposition = Proposition::condition_is(condition.clone(), truth);
                    assert_eq!(
                        crate::kernel::reasoning::path_facts::solve_builtin_prop(&proposition),
                        expected == truth
                    );
                    assert_eq!(
                        crate::kernel::reasoning::path_facts::disprove_builtin_prop(&proposition),
                        expected != truth
                    );
                }
                let symbolic = OldConditionTerm::Compare {
                    format,
                    relation,
                    left: Box::new(OldMachineTerm::Variable(Variable(992597))),
                    right: Box::new(right.clone()),
                };
                assert_eq!(
                    literal_native_comparison_value(BooleanOperandView::Native(&symbolic)),
                    None
                );
            }
        }
    }

    #[test]
    fn shared_wide_equality_keeps_constant_arithmetic_over_null_addresses() {
        use crate::kernel::{Address, AddressObjectClass, KernelTermImport, MachineBinaryOp};
        let sum = OldMachineTerm::Binary {
            format: MachineIntegerType::UInt64,
            op: MachineBinaryOp::Add,
            left: Box::new(OldMachineTerm::IntegerAddress(
                Box::new(Address::null()),
                AddressObjectClass::NONE,
            )),
            right: Box::new(OldMachineTerm::uint64_constant(u64::MAX)),
        };
        let condition = OldConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: R::Equal,
            left: Box::new(sum),
            right: Box::new(OldMachineTerm::int64_constant(-1)),
        };
        let root = KernelTermImport::default().condition(&condition);
        assert_eq!(
            closed_condition_value(BooleanOperandView::Shared(&root)),
            Some(true)
        );
        assert!(!root.has_cached_native_argument());
    }

    #[test]
    fn written_comparison_views_borrow_and_normalize_every_relation() {
        for format in super::super::FORMATS {
            for (relation, truth, expected, swapped) in [
                (R::Equal, true, Relation::Equal, false),
                (R::Equal, false, Relation::NotEqual, false),
                (R::LessThan, true, Relation::Less, false),
                (R::LessThan, false, Relation::LessEqual, true),
                (R::LessEqual, true, Relation::LessEqual, false),
                (R::LessEqual, false, Relation::Less, true),
                (R::GreaterThan, true, Relation::Less, true),
                (R::GreaterThan, false, Relation::LessEqual, false),
                (R::GreaterEqual, true, Relation::LessEqual, true),
                (R::GreaterEqual, false, Relation::Less, false),
            ] {
                let condition = OldConditionTerm::Compare {
                    format,
                    relation,
                    left: Box::new(OldMachineTerm::Variable(Variable(982412))),
                    right: Box::new(OldMachineTerm::Variable(Variable(982413))),
                };
                let OldConditionTerm::Compare { left, right, .. } = &condition else {
                    unreachable!()
                };
                let view = comparison_view(&condition, truth).unwrap();
                assert_eq!(view.format, format);
                assert_eq!(view.relation, expected);
                let written = if swapped {
                    [right.as_ref(), left.as_ref()]
                } else {
                    [left.as_ref(), right.as_ref()]
                };
                for (operand, written) in view.operands.iter().zip(written) {
                    let MachineOperandView::Old(value) = operand.operand_view() else {
                        panic!("borrowed input")
                    };
                    assert!(std::ptr::eq(value, written));
                }
            }
        }
    }
}
