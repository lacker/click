//! The certificate's existing bounded structural identity, read from either
//! operand representation. The payload bound counts occurrences, as before;
//! sharing is not permission to admit a previously refused certificate shape.
use super::*;
use crate::kernel::{MachineCastSpelling as Encoding, MachineOperandView as View};

fn unwrap_leaf(view: View<'_>) -> View<'_> {
    match view {
        View::Shared(root) => root
            .machine_conversion_leaf()
            .map(View::Legacy)
            .unwrap_or(view),
        _ => view,
    }
}

pub(super) fn binary_supported(format: MachineIntegerType, op: MachineBinaryOp) -> bool {
    use MachineBinaryOp::*;
    matches!(
        (format, op),
        (
            MachineIntegerType::Int32,
            Add | Subtract | BitwiseAnd | BitwiseOr | BitwiseXor
        ) | (MachineIntegerType::Int64, Add)
            | (
                MachineIntegerType::UInt64,
                Add | Subtract | Multiply | Divide | Remainder | BitwiseAnd | BitwiseOr
            )
    )
}

fn cast_supported(encoding: Encoding) -> bool {
    matches!(
        encoding,
        Encoding::Generic
            | Encoding::Int64FromUInt32
            | Encoding::UInt64From32
            | Encoding::UInt32From64
    )
}

fn payload(root: View<'_>) -> Option<usize> {
    let mut pending = vec![root];
    let mut total = 0usize;
    while let Some(term) = pending.pop() {
        let term = unwrap_leaf(term);
        if let View::Legacy(term) = term {
            total = total.checked_add(bitvector_payload(term)?)?;
        } else {
            total = total.checked_add(1)?;
            if term.literal().is_some() || term.variable().is_some() || term.read().is_some() {
            } else if let Some((encoding, _, _, operand)) = term.cast() {
                if !cast_supported(encoding) {
                    return None;
                }
                pending.push(operand);
            } else if let Some((format, op, operands)) = term.binary() {
                if !binary_supported(format, op) {
                    return None;
                }
                pending.extend(operands);
            } else {
                return None;
            }
        }
        if total > MAX_TERM_PAYLOAD {
            return None;
        }
    }
    Some(total)
}

// A read is an opaque scalar value, just as its compatibility name was.
// Ignore the observation's format here; the enclosing comparison checks it,
// while the descriptor retains the load kind, state and address.
fn read_identity(view: View<'_>) -> Option<crate::kernel::KernelTerm> {
    match view {
        View::Shared(term) if view.read().is_some() => {
            Some(term.with_machine_observation_type(MachineIntegerType::Int32))
        }
        View::Legacy(MachineTerm::Variable(variable)) => {
            crate::kernel::eval::registered_scalar_read_term(variable, MachineIntegerType::Int32)
        }
        View::Legacy(value @ MachineTerm::MemoryLoad(..)) => {
            crate::kernel::KernelTermImport::default()
                .machine_arithmetic(MachineIntegerType::Int32, value)
        }
        _ => None,
    }
}

/// Structural equality restricted to precisely the certificate fragment.
/// No identity shortcut may bypass unsupported operators or the payload bound.
pub(super) fn equal(left: View<'_>, right: View<'_>) -> bool {
    if let (View::Legacy(left), View::Legacy(right)) = (left, right) {
        return legacy_bitvector_equal(left, right);
    }
    if !payload(left).is_some_and(charge_payload) || !payload(right).is_some_and(charge_payload) {
        return false;
    }
    let mut pending = vec![(left, right)];
    while let Some((left, right)) = pending.pop() {
        let (left, right) = (unwrap_leaf(left), unwrap_leaf(right));
        if let (View::Legacy(left), View::Legacy(right)) = (left, right) {
            if !legacy_bitvector_equal(left, right) {
                return false;
            }
            continue;
        }
        if let (Some(left), Some(right)) = (left.literal(), right.literal()) {
            if !legacy_bitvector_equal(&left, &right) {
                return false;
            }
            continue;
        }
        if left.read().is_some() || right.read().is_some() {
            let (Some(left), Some(right)) = (read_identity(left), read_identity(right)) else {
                return false;
            };
            if left != right {
                return false;
            }
            continue;
        }
        if let (Some(left), Some(right)) = (left.variable(), right.variable()) {
            if left != right {
                return false;
            }
            continue;
        }
        if let (Some((le, ls, ld, l)), Some((re, rs, rd, r))) = (left.cast(), right.cast()) {
            if (le, ls, ld) != (re, rs, rd) || !cast_supported(le) {
                return false;
            }
            pending.push((l, r));
            continue;
        }
        if let (Some((lf, lo, [la, lb])), Some((rf, ro, [ra, rb]))) =
            (left.binary(), right.binary())
        {
            if (lf, lo) != (rf, ro) || !binary_supported(lf, lo) {
                return false;
            }
            pending.push((la, ra));
            pending.push((lb, rb));
            continue;
        }
        return false;
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{KernelTermExport, KernelTermImport, SharedMachineIntegerTerm, Variable};

    #[test]
    fn shared_certificate_read_identity_keeps_state_address_and_kind() {
        use crate::kernel::{LoadKind, Memory, Pointer, ProgramValue, VerificationSession};
        let _session = VerificationSession::enter();
        let address = Pointer::symbolic(Variable(997109));
        let memory = crate::kernel::intern_memory(Memory::new());
        let name = crate::kernel::eval::load_variable_for_exact_cell(
            &memory,
            &address,
            LoadKind::UInt16,
            2,
        );
        let named = MachineTerm::Variable(name);
        let read = KernelTermImport::default()
            .machine_arithmetic(MachineIntegerType::UInt16, &named)
            .unwrap();
        let wrong = |memory, address, kind| {
            KernelTermImport::default()
                .machine_arithmetic(
                    MachineIntegerType::UInt16,
                    &MachineTerm::MemoryLoad(memory, Box::new(address), kind),
                )
                .unwrap()
        };
        let other_address = wrong(memory.clone(), address.offset_by_bytes(2), LoadKind::UInt16);
        let other_kind = wrong(memory.clone(), address.clone(), LoadKind::Int16);
        let raw =
            MachineTerm::MemoryLoad(memory.clone(), Box::new(address.clone()), LoadKind::UInt16);
        let other_memory_state = wrong(
            crate::kernel::intern_memory(memory.memory().clone().store(
                address.clone(),
                ProgramValue::UInt16(MachineTerm::narrow_constant(MachineIntegerType::UInt16, 7)),
            )),
            address,
            LoadKind::UInt16,
        );
        let exports = KernelTermExport::machine_export_count();
        assert!(equal(View::Shared(&read), View::Legacy(&named)));
        assert!(equal(View::Shared(&read), View::Legacy(&raw)));
        assert!(equal(View::Legacy(&raw), View::Shared(&read)));
        for other in [&other_address, &other_kind, &other_memory_state] {
            assert!(!equal(View::Shared(&read), View::Shared(other)));
        }
        crate::kernel::eval::clear_load_variable_registry();
        assert!(equal(View::Shared(&read), View::Shared(&read)));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn shared_certificate_operand_identity_preserves_supported_and_refused_shapes() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            for op in [
                MachineBinaryOp::Add,
                MachineBinaryOp::Subtract,
                MachineBinaryOp::Multiply,
                MachineBinaryOp::Divide,
                MachineBinaryOp::Remainder,
                MachineBinaryOp::BitwiseAnd,
                MachineBinaryOp::BitwiseOr,
                MachineBinaryOp::BitwiseXor,
            ] {
                let native = MachineTerm::Binary {
                    format,
                    op,
                    left: Box::new(MachineTerm::Variable(Variable(997101))),
                    right: Box::new(MachineTerm::Variable(Variable(997102))),
                };
                let Some(root) = KernelTermImport::default().machine_arithmetic(format, &native)
                else {
                    continue;
                };
                let shared = SharedMachineIntegerTerm::from_shared(format, root).unwrap();
                let exports = KernelTermExport::machine_export_count();
                let expected = legacy_bitvector_equal(&native, &native);
                assert_eq!(
                    equal(shared.operand_view(), shared.operand_view()),
                    expected,
                    "{format:?} {op:?}"
                );
                assert_eq!(
                    equal(shared.operand_view(), View::Legacy(&native)),
                    expected,
                    "mixed {format:?} {op:?}"
                );
                assert_eq!(KernelTermExport::machine_export_count(), exports);
                assert!(!shared.has_boxed_operand());
            }
        }
    }
}

use crate::kernel::machine_integer::Relation;
use crate::kernel::machine_integer::comparison::{
    NativeComparisonView, condition_for_operand_views, native_comparison_view,
};
use std::borrow::Cow;

enum ConditionRead<'a> {
    Written(Cow<'a, ConditionTerm>),
    Observation(NativeComparisonView<'static>),
}
impl<'a> ConditionRead<'a> {
    fn read(condition: &'a ConditionTerm) -> Self {
        let Some(mut view) = native_comparison_view(condition, true) else {
            return Self::Written(Cow::Borrowed(condition));
        };
        let relation = match view.relation {
            Relation::Equal => CompareRelation::Equal,
            Relation::Less => CompareRelation::LessThan,
            Relation::LessEqual => CompareRelation::LessEqual,
            Relation::NotEqual => return Self::Written(Cow::Borrowed(condition)),
        };
        let operands = view.operands.each_ref().map(|v| v.operand_view());
        // The native 64-bit equality constructor folds reflexivity before
        // inspecting the operand fragment. Preserve that rule by root identity.
        if view.format.format().bits() == 64 && relation == CompareRelation::Equal {
            use crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey as Key;
            if Key::for_format(view.format, operands[0])
                == Key::for_format(view.format, operands[1])
            {
                return Self::Written(Cow::Owned(ConditionTerm::Constant(true)));
            }
        }
        let converted = condition_for_operand_views(view.format, relation, operands);
        if !matches!(
            converted,
            crate::kernel::integer_comparison_condition!(_, _)
        ) {
            return Self::Written(Cow::Owned(converted));
        }
        // The native constructor files 64-bit word equality at Int64.
        if relation == CompareRelation::Equal && view.format == MachineIntegerType::UInt64 {
            view.format = MachineIntegerType::Int64;
        }
        Self::Observation(view)
    }
    fn comparison(&self) -> Option<(MachineIntegerType, CompareRelation, [View<'_>; 2])> {
        match self {
            Self::Written(condition) => {
                let ConditionTerm::Compare {
                    format,
                    relation,
                    left,
                    right,
                } = condition.as_ref()
                else {
                    return None;
                };
                Some((
                    *format,
                    *relation,
                    [View::Legacy(left), View::Legacy(right)],
                ))
            }
            Self::Observation(view) => Some((
                view.format,
                match view.relation {
                    Relation::Equal => CompareRelation::Equal,
                    Relation::Less => CompareRelation::LessThan,
                    Relation::LessEqual => CompareRelation::LessEqual,
                    Relation::NotEqual => unreachable!(),
                },
                view.operands.each_ref().map(|v| v.operand_view()),
            )),
        }
    }
}

use crate::kernel::machine_integer::comparison::{
    FactOperand as Side, fact_operand_identity as narrow_identity,
};

pub(super) fn condition_equal(left: &ConditionTerm, right: &ConditionTerm) -> bool {
    let (left, right) = (ConditionRead::read(left), ConditionRead::read(right));
    if let (ConditionRead::Written(left), ConditionRead::Written(right)) = (&left, &right) {
        return condition_identity_native(left, right);
    }
    let (Some((lf, lr, ls)), Some((rf, rr, rs))) = (left.comparison(), right.comparison()) else {
        return false;
    };
    let ((ln, lside), (rn, rside)) = (narrow_identity(lf, lr, ls), narrow_identity(rf, rr, rs));
    if ln.format().bits() < 32 || rn.format().bits() < 32 {
        let side_equal = |a, b| match (a, b) {
            (Side::Value(a), Side::Value(b)) => a == b,
            (Side::Term(a), Side::Term(b)) => equal(a, b),
            _ => false,
        };
        return ln == rn
            && lr == rr
            && side_equal(lside[0], rside[0])
            && side_equal(lside[1], rside[1]);
    }
    let supported = match (lf, rf, lr, rr) {
        (
            MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            CompareRelation::Equal,
            CompareRelation::Equal,
        ) => true,
        (MachineIntegerType::Int32, MachineIntegerType::Int32, a, b)
        | (MachineIntegerType::UInt32, MachineIntegerType::UInt32, a, b) => a == b,
        (MachineIntegerType::Int64, MachineIntegerType::Int64, a, b) => {
            a == b && matches!(a, CompareRelation::Equal | CompareRelation::LessEqual)
        }
        _ => false,
    };
    supported && equal(ls[0], rs[0]) && equal(ls[1], rs[1])
}

#[cfg(test)]
mod condition_tests {
    use super::*;
    use crate::kernel::{
        IntegerTerm, KernelTermExport, KernelTermImport, SharedMachineIntegerTerm, Variable,
    };

    fn shared(format: MachineIntegerType, native: &MachineTerm) -> SharedMachineIntegerTerm {
        SharedMachineIntegerTerm::from_shared(
            format,
            KernelTermImport::default()
                .machine_arithmetic(format, native)
                .unwrap(),
        )
        .unwrap()
    }

    #[test]
    fn observed_certificate_conditions_preserve_the_native_fragment() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            for op in [
                MachineBinaryOp::Add,
                MachineBinaryOp::Subtract,
                MachineBinaryOp::Multiply,
                MachineBinaryOp::Divide,
                MachineBinaryOp::BitwiseAnd,
                MachineBinaryOp::BitwiseXor,
            ] {
                let a = MachineTerm::Binary {
                    format,
                    op,
                    left: Box::new(MachineTerm::Variable(Variable(997111))),
                    right: Box::new(MachineTerm::Variable(Variable(997112))),
                };
                let b = MachineTerm::Variable(Variable(997113));
                let (sa, sb) = (shared(format, &a), shared(format, &b));
                for relation in [
                    CompareRelation::Equal,
                    CompareRelation::LessThan,
                    CompareRelation::LessEqual,
                ] {
                    let native =
                        ConditionTerm::machine_compare(format, relation, a.clone(), b.clone());
                    let expected = condition_identity_native(&native, &native);
                    let observed = condition_for_operand_views(
                        format,
                        relation,
                        [sa.operand_view(), sb.operand_view()],
                    );
                    let exports = KernelTermExport::machine_export_count();
                    assert_eq!(
                        condition_equal(&observed, &native),
                        expected,
                        "mixed {format:?} {op:?} {relation:?}"
                    );
                    assert_eq!(
                        condition_equal(&observed, &observed),
                        expected,
                        "shared {format:?} {op:?} {relation:?}"
                    );
                    let wrong = ConditionTerm::machine_compare(
                        format,
                        relation,
                        a.clone(),
                        MachineTerm::Variable(Variable(997114)),
                    );
                    assert!(!condition_equal(&observed, &wrong));
                    assert_eq!(KernelTermExport::machine_export_count(), exports);
                    assert!(!sa.has_boxed_operand());
                }
                for (written, normalized) in [
                    (CompareRelation::GreaterThan, CompareRelation::LessThan),
                    (CompareRelation::GreaterEqual, CompareRelation::LessEqual),
                ] {
                    let observed = condition_for_operand_views(
                        format,
                        written,
                        [sa.operand_view(), sb.operand_view()],
                    );
                    let native =
                        ConditionTerm::machine_compare(format, normalized, b.clone(), a.clone());
                    let original_direction =
                        ConditionTerm::machine_compare(format, written, a.clone(), b.clone());
                    let expected = condition_identity_native(&native, &native);
                    let exports = KernelTermExport::machine_export_count();
                    assert_eq!(condition_equal(&observed, &native), expected);
                    assert_eq!(
                        condition_equal(&observed, &original_direction),
                        condition_identity_native(&native, &original_direction)
                    );
                    assert_eq!(KernelTermExport::machine_export_count(), exports);
                }
            }
        }
    }

    #[test]
    fn retained_cast_identity_preserves_encoding_and_narrow_comparisons() {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = MachineTerm::Variable(Variable(997141));
        let casts = [
            (
                MachineIntegerType::Int32,
                MachineTerm::Cast {
                    spelling: MachineCastSpelling::Generic,
                    from: MachineIntegerType::UInt8,
                    to: MachineIntegerType::Int32,
                    value: Box::new(variable.clone()),
                },
            ),
            (
                MachineIntegerType::Int64,
                MachineTerm::legacy_cast(
                    MachineCastSpelling::Int64FromUInt32,
                    Box::new(variable.clone()),
                ),
            ),
            (
                MachineIntegerType::Int64,
                MachineTerm::legacy_cast(
                    MachineCastSpelling::Int64From32,
                    Box::new(variable.clone()),
                ),
            ),
            (
                MachineIntegerType::UInt64,
                MachineTerm::legacy_cast(
                    MachineCastSpelling::UInt64From32,
                    Box::new(variable.clone()),
                ),
            ),
            (
                MachineIntegerType::UInt32,
                MachineTerm::legacy_cast(MachineCastSpelling::UInt32From64, Box::new(variable)),
            ),
        ];
        for (format, native) in casts {
            let operand = shared(format, &native);
            let exports = KernelTermExport::machine_export_count();
            assert_eq!(
                equal(operand.operand_view(), View::Legacy(&native)),
                legacy_bitvector_equal(&native, &native)
            );
            if format == MachineIntegerType::Int32 {
                let written = ConditionTerm::machine_compare(
                    format,
                    CompareRelation::LessEqual,
                    native,
                    MachineTerm::constant_at32(MachineIntegerType::Int32, 1),
                );
                let observed = ConditionTerm::integer_less_equal(
                    IntegerTerm::Machine(operand.clone()),
                    IntegerTerm::constant(1.into()),
                );
                assert!(condition_equal(&observed, &written));
            }
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(!operand.has_boxed_operand());
        }
    }

    #[test]
    fn wide_reflexivity_keeps_the_native_constructor_rule() {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int64;
        let native = MachineTerm::Binary {
            format,
            op: MachineBinaryOp::Multiply,
            left: Box::new(MachineTerm::Variable(Variable(997121))),
            right: Box::new(MachineTerm::Variable(Variable(997122))),
        };
        let operand = shared(format, &native);
        let observed = ConditionTerm::integer_equal(
            IntegerTerm::Machine(operand.clone()),
            IntegerTerm::Machine(operand.clone()),
        );
        let exports = KernelTermExport::machine_export_count();
        assert!(condition_equal(&observed, &ConditionTerm::Constant(true)));
        assert!(!condition_equal(&observed, &ConditionTerm::Constant(false)));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(!operand.has_boxed_operand());
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/proof/arithmetic_special/operand_identity/tests.rs");
}
