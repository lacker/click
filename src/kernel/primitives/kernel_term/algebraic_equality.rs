//! Native algebraic syntax equality over common constructor and match fields.
//! Producer metadata remains exact; only this observation uses native value equality.
use super::*;

impl KernelTerm {
    pub(crate) fn algebraic_equal_raw(arguments: [Self; 2]) -> Self {
        Self::intern(
            KernelType::Bool,
            KernelTermNode::AlgebraicEqual { arguments },
        )
    }

    pub(crate) fn algebraic_syntax_equal(&self, other: &Self) -> bool {
        self.algebraic_syntax_equal_while(other, || true)
            .expect("unbounded syntax comparison")
    }

    pub(crate) fn algebraic_syntax_equal_while(
        &self,
        other: &Self,
        mut visit: impl FnMut() -> bool,
    ) -> Option<bool> {
        fn expand(root: KernelTerm) -> KernelTerm {
            let Some(PureFunctionArgument::Algebraic(value)) = root.written_argument() else {
                return root;
            };
            KernelTermImport::default().algebraic(value)
        }
        let mut pending = vec![(self.clone(), other.clone())];
        let mut seen = std::collections::HashSet::new();
        let mut export = KernelTermExport::default();
        while let Some((left, right)) = pending.pop() {
            if !visit() {
                return None;
            }
            crate::instrumentation::record_deterministic_work(1);
            if left.ty() != right.ty() {
                return Some(false);
            }
            if left == right || !seen.insert((left.id(), right.id())) {
                continue;
            }
            if let (KernelTermNode::ImportedScalar(a), KernelTermNode::ImportedScalar(b)) =
                (left.node(), right.node())
            {
                if a.carrier() != b.carrier() || a.value() != b.value() {
                    return Some(false);
                }
                continue;
            }
            if let (Some(a), Some(b)) = (left.written_argument(), right.written_argument()) {
                if a != b {
                    return Some(false);
                }
                continue;
            }
            let left = expand(left);
            let right = expand(right);
            if let KernelType::Program(ty) = left.ty()
                && MachineIntegerType::from_program_type(*ty).is_some()
            {
                if !crate::kernel::machine_operand_syntax_cmp(
                    MachineOperandView::Shared(&left),
                    MachineOperandView::Shared(&right),
                )
                .is_eq()
                {
                    return Some(false);
                }
                continue;
            }
            if left.ty() == &KernelType::Bool {
                if !BooleanOperandView::Shared(&left)
                    .syntax_equal(BooleanOperandView::Shared(&right))
                {
                    return Some(false);
                }
                continue;
            }
            match (left.node(), right.node()) {
                (KernelTermNode::Variable(a), KernelTermNode::Variable(b)) if a == b => {}
                (KernelTermNode::IntegerLiteral(a), KernelTermNode::IntegerLiteral(b))
                    if a == b => {}
                (
                    KernelTermNode::AlgebraicIf { arguments: a },
                    KernelTermNode::AlgebraicIf { arguments: b },
                ) => pending.extend(a.iter().cloned().zip(b.iter().cloned())),
                (KernelTermNode::AlgebraicRead(a), KernelTermNode::AlgebraicRead(b)) => {
                    let (am, aa) = a.parts();
                    let (bm, ba) = b.parts();
                    if am != bm || !aa.syntax_equal(ba) {
                        return Some(false);
                    }
                }
                (KernelTermNode::AlgebraicCall(a), KernelTermNode::AlgebraicCall(b))
                    if a.name == b.name
                        && a.shared_machine_arguments == b.shared_machine_arguments
                        && a.arguments.len() == b.arguments.len() =>
                {
                    // SharedMachine arguments compare their original carrier IDs,
                    // not their exported machine syntax or pointer annotations.
                    pending.extend(
                        a.arguments
                            .iter()
                            .zip(&b.arguments)
                            .zip(&a.shared_machine_arguments)
                            .filter(|(_, carrier)| carrier.is_none())
                            .map(|((a, b), _)| (a.clone(), b.clone())),
                    );
                }
                (KernelTermNode::Constructor(a), KernelTermNode::Constructor(b))
                    if a.variant == b.variant && a.fields.len() == b.fields.len() =>
                {
                    pending.extend(a.fields.iter().cloned().zip(b.fields.iter().cloned()));
                }
                (KernelTermNode::Match(a), KernelTermNode::Match(b))
                    if a.arms.len() == b.arms.len() && a.arguments.len() == b.arguments.len() =>
                {
                    for (a, b) in a.arms.iter().zip(&b.arms) {
                        if a.variant != b.variant || a.bindings.len() != b.bindings.len() {
                            return Some(false);
                        }
                        pending.extend(a.bindings.iter().cloned().zip(b.bindings.iter().cloned()));
                    }
                    pending.extend(a.arguments.iter().cloned().zip(b.arguments.iter().cloned()));
                }
                (
                    KernelTermNode::IntegerOperation {
                        operator: a,
                        arguments: aa,
                    },
                    KernelTermNode::IntegerOperation {
                        operator: b,
                        arguments: ba,
                    },
                ) if a == b && aa.len() == ba.len() => {
                    pending.extend(aa.iter().cloned().zip(ba.iter().cloned()));
                }
                (
                    KernelTermNode::IntegerIf { arguments: a },
                    KernelTermNode::IntegerIf { arguments: b },
                ) => pending.extend(a.iter().cloned().zip(b.iter().cloned())),
                (
                    KernelTermNode::Call {
                        name: a,
                        arguments: aa,
                    },
                    KernelTermNode::Call {
                        name: b,
                        arguments: ba,
                    },
                ) if a == b && aa.len() == ba.len() => {
                    pending.extend(aa.iter().cloned().zip(ba.iter().cloned()))
                }
                (KernelTermNode::Fold(a), KernelTermNode::Fold(b))
                    if a.index == b.index && a.accumulator == b.accumulator && a.item == b.item =>
                {
                    pending.extend(a.arguments.iter().cloned().zip(b.arguments.iter().cloned()))
                }
                // Unmigrated field carriers retain their existing native value
                // identity, including pointer annotations ignored by equality.
                _ if left.requires_native_argument_input()
                    || right.requires_native_argument_input()
                    || left.written_argument().is_some()
                    || right.written_argument().is_some() =>
                {
                    if export.argument(&left).ok()? != export.argument(&right).ok()? {
                        return Some(false);
                    }
                }
                _ if left.old_pointer_value().is_some() && right.old_pointer_value().is_some() => {
                    if left.old_pointer_value() != right.old_pointer_value() {
                        return Some(false);
                    }
                }
                _ => return Some(false),
            }
        }
        Some(true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn constructor(pointer: Pointer) -> AlgebraicTerm {
        let mut value = KernelMatch::test_scrutinee(vec![
            AlgebraicValueType::Program(ProgramType::Int32Pointer),
            AlgebraicValueType::Program(ProgramType::Int32),
        ]);
        value.node = AlgebraicTermNode::Constructor {
            variant: "Arm".into(),
            fields: vec![
                AlgebraicValue::Program(ProgramValue::Pointer(pointer)),
                AlgebraicValue::Program(ProgramValue::Int32(OldMachineTerm::add(
                    OldMachineTerm::Variable(Variable(999671)),
                    OldMachineTerm::constant(1),
                ))),
            ],
        };
        value
    }

    #[test]
    fn common_algebraic_equality_preserves_native_identity_and_exact_payloads() {
        let _session = crate::kernel::VerificationSession::enter();
        // Two producers of one logical pointer: distinct handles.
        let pointer = || {
            Pointer::new(
                Address::symbolic(Variable(999670)),
                ProgramType::Int32Pointer,
            )
        };
        let a = constructor(pointer());
        let b = constructor(pointer());
        let ar = KernelTermImport::default().algebraic(&a);
        let br = KernelTermImport::default().algebraic(&b);
        assert_ne!(ar, br);
        let exports = KernelTermExport::machine_export_count();
        assert!(ar.algebraic_syntax_equal(&br));
        let conditions = [
            OldConditionTerm::AlgebraicEqual(Box::new(a.clone()), Box::new(b.clone())),
            OldConditionTerm::AlgebraicEqual(Box::new(b.clone()), Box::new(a.clone())),
        ];
        let roots = conditions
            .each_ref()
            .map(|c| KernelTermImport::default().condition(c));
        assert!(matches!(
            roots[0].node(),
            KernelTermNode::AlgebraicEqual { .. }
        ));
        assert!(
            BooleanOperandView::Shared(&roots[0])
                .syntax_equal(BooleanOperandView::Shared(&roots[1]))
        );
        assert!(
            BooleanOperandView::Shared(&roots[0])
                .syntax_equal(BooleanOperandView::Native(&conditions[1]))
        );
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        for (root, condition) in roots.iter().zip(&conditions) {
            assert_eq!(
                format!("{:?}", KernelTermExport::condition(root).unwrap()),
                format!("{condition:?}")
            );
        }
        let mut different = a.clone();
        different.algebraic_type.name = "OtherType".into();
        assert!(!ar.algebraic_syntax_equal(&KernelTermImport::default().algebraic(&different)));
        different = a;
        if let AlgebraicTermNode::Constructor { variant, .. } = &mut different.node {
            *variant = "OtherVariant".into();
        }
        assert!(!ar.algebraic_syntax_equal(&KernelTermImport::default().algebraic(&different)));
    }

    #[test]
    fn stored_constructor_equality_keeps_boolean_call_argument_spelling() {
        let _session = crate::kernel::VerificationSession::enter();
        let word = OldMachineTerm::Variable(Variable(999674));
        let arguments = [
            PureFunctionArgument::Value(ProgramValue::Int32(word.clone())),
            PureFunctionArgument::SharedMachine(SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int32,
                word,
            )),
        ];
        let conditions = arguments.map(|arg| {
            let mut model =
                KernelMatch::test_scrutinee(vec![AlgebraicValueType::Program(ProgramType::Bool)]);
            let variable = model.clone();
            let call = OldConditionTerm::BoolApplication(SharedPureApplication::intern(
                "constructor_boolean_field".into(),
                vec![arg],
            ));
            model.node = AlgebraicTermNode::Constructor {
                variant: "Arm".into(),
                fields: vec![AlgebraicValue::Program(ProgramValue::Bool(
                    OldMachineTerm::BoolCast {
                        to: MachineIntegerType::UInt8,
                        value: Box::new(call),
                    },
                ))],
            };
            StoredConditionTerm::algebraic_equal(&model, &variable)
        });
        assert_eq!(conditions[0], conditions[1]);
        for (condition, shared) in conditions.iter().zip([false, true]) {
            let root = condition.root().expect("shared constructor equality");
            let exported = KernelTermExport::condition(root).unwrap();
            for written in [condition.old_form(), &exported] {
                let OldConditionTerm::AlgebraicEqual(left, _) = written else {
                    panic!("expected equality")
                };
                let AlgebraicTermNode::Constructor { fields, .. } = &left.node else {
                    panic!("expected constructor")
                };
                let [
                    AlgebraicValue::Program(ProgramValue::Bool(OldMachineTerm::BoolCast {
                        value,
                        ..
                    })),
                ] = fields.as_slice()
                else {
                    panic!("expected Boolean field")
                };
                let OldConditionTerm::BoolApplication(call) = value.as_ref() else {
                    panic!("expected Boolean call")
                };
                assert!(matches!(
                    (shared, call.arguments()),
                    (true, [PureFunctionArgument::SharedMachine(_)])
                        | (false, [PureFunctionArgument::Value(ProgramValue::Int32(_))])
                ));
            }
        }
    }

    #[test]
    fn common_algebraic_equality_keeps_operand_order_and_legacy_views() {
        let a = KernelMatch::test_scrutinee(vec![]);
        let mut b = a.clone();
        b.node = AlgebraicTermNode::Variable(Variable(999673));
        let condition = OldConditionTerm::AlgebraicEqual(Box::new(a.clone()), Box::new(b.clone()));
        let reversed = OldConditionTerm::AlgebraicEqual(Box::new(b), Box::new(a));
        assert_ne!(condition, reversed);
        let root = KernelTermImport::default().condition(&condition);
        let reverse = KernelTermImport::default().condition(&reversed);
        assert!(
            !BooleanOperandView::Shared(&root).syntax_equal(BooleanOperandView::Shared(&reverse))
        );
        let native = BooleanOperandView::Native(&condition);
        let retained = BooleanOperandView::Shared(&root);
        assert!(retained.syntax_equal(native));
        assert!(native.syntax_equal(retained));
    }

    #[test]
    fn common_algebraic_equality_observation_matches_native_guard_keys() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Pointer::new(
            Address::symbolic(Variable(999672)),
            ProgramType::Int32Pointer,
        );
        let native = OldConditionTerm::AlgebraicEqual(
            Box::new(constructor(pointer.clone())),
            Box::new(constructor(pointer)),
        );
        let condition = KernelTermImport::default().condition(&native);
        let format = MachineIntegerType::Int32;
        let branches = [OldMachineTerm::constant(1), OldMachineTerm::constant(2)];
        let common = KernelTerm::machine_if_shared(
            format,
            [
                condition,
                KernelTermImport::default().machine(format, &branches[0]),
                KernelTermImport::default().machine(format, &branches[1]),
            ],
        );
        let exports = KernelTermExport::machine_export_count();
        let observed = SharedMachineIntegerTerm::observe_shared(format, common).unwrap();
        let native = SharedMachineIntegerTerm::intern(
            format,
            OldMachineTerm::If {
                condition: Box::new(native),
                then_term: Box::new(branches[0].clone()),
                else_term: Box::new(branches[1].clone()),
            },
        );
        assert_eq!(observed, native);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}

#[cfg(test)]
mod scaling_tests {
    use super::*;
    include!("../../../scaling_tests/kernel/primitives/kernel_term/algebraic_equality.rs");
}
