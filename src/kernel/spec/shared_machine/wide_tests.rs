use super::*;
use crate::kernel::VerificationSession;

const FORMATS: [MachineIntegerType; 10] = [
    MachineIntegerType::Int8,
    MachineIntegerType::UInt8,
    MachineIntegerType::Int16,
    MachineIntegerType::UInt16,
    MachineIntegerType::Int32,
    MachineIntegerType::UInt32,
    MachineIntegerType::Int64,
    MachineIntegerType::UInt64,
    MachineIntegerType::Int128,
    MachineIntegerType::UInt128,
];

fn word(format: MachineIntegerType, n: num_bigint::BigInt) -> MachineTerm {
    crate::kernel::machine_integer::range::constant_word(format, &n).unwrap()
}
fn root(format: MachineIntegerType, value: &MachineTerm) -> KernelTerm {
    KernelTerm::retained_machine_operand(format, MachineOperandView::Legacy(value))
}
fn integer(value: &SharedIntegerTerm) -> IntegerTerm {
    use IntegerTerm as I;
    match value.as_ref() {
        I::Machine(m) => IntegerTerm::from_machine(m.ty(), native_term(m.value())).unwrap(),
        I::Add(a, b) => I::add(integer(a), integer(b)),
        I::Subtract(a, b) => I::subtract(integer(a), integer(b)),
        I::Multiply(a, b) => I::multiply(integer(a), integer(b)),
        I::TruncatingQuotient(a, b) => I::truncating_quotient(integer(a), integer(b)),
        I::TruncatingRemainder(a, b) => I::truncating_remainder(integer(a), integer(b)),
        value => value.clone(),
    }
}
fn native_term(term: &MachineTerm) -> MachineTerm {
    match term {
        MachineTerm::IntegerToMachine { value, destination } => MachineTerm::IntegerToMachine {
            value: integer(value).into(),
            destination: *destination,
        },
        term => term.clone(),
    }
}
fn domain(value: &Proposition) -> Proposition {
    match value {
        Proposition::And(a, b) => Proposition::And(Box::new(domain(a)), Box::new(domain(b))),
        Proposition::Or(a, b) => Proposition::Or(Box::new(domain(a)), Box::new(domain(b))),
        Proposition::ConditionIs(c, t) => Proposition::ConditionIs(
            match c {
                ConditionTerm::IntegerEqual(a, b) => {
                    ConditionTerm::integer_equal(integer(a), integer(b))
                }
                ConditionTerm::IntegerLessEqual(a, b) => {
                    ConditionTerm::integer_less_equal(integer(a), integer(b))
                }
                ConditionTerm::IntegerGreaterEqual(a, b) => {
                    ConditionTerm::integer_greater_equal(integer(a), integer(b))
                }
                c => c.clone(),
            },
            *t,
        ),
        p => p.clone(),
    }
}

#[test]
fn wide_casts_match_all_existing_integer_directions() {
    let _session = VerificationSession::enter();
    for source in FORMATS {
        for destination in FORMATS {
            if source.format().bits() != 128 && destination.format().bits() != 128 {
                continue;
            }
            let (min, max) = source.format().bounds();
            let mut leaves = vec![
                MachineTerm::Variable(Variable(995700)),
                word(source, 0.into()),
                word(source, min),
                word(source, max),
            ];
            if source.format().bits() <= 64 {
                leaves.push(MachineTerm::opaque_conversion(
                    "wide_cast",
                    MachineTerm::Variable(Variable(995701)),
                ));
            }
            leaves.push(MachineTerm::IntegerToMachine {
                destination: source,
                value: IntegerTerm::constant_i64(7).into(),
            });
            for leaf in leaves {
                super::super::super::signedness_cast_tests::check_native_parity(
                    root(source, &leaf),
                    destination,
                );
            }
            let initial = root(source, &MachineTerm::Variable(Variable(995702)));
            let intermediate = if source == destination {
                initial
            } else {
                cast(&initial.into(), destination.program_type()).unwrap()
            };
            super::super::super::signedness_cast_tests::check_native_parity(intermediate, source);
        }
    }
}

#[test]
fn wide_reads_keep_type_and_state_in_casts_and_observations() {
    let _session = VerificationSession::enter();
    let address = Pointer::symbolic(Variable(995703));
    let before = crate::kernel::intern_memory(Memory::new());
    let after = crate::kernel::intern_memory(
        Memory::new().store(address.clone(), ProgramValue::Int32(7u32.into())),
    );
    for format in [MachineIntegerType::Int128, MachineIntegerType::UInt128] {
        let kind = crate::kernel::LoadKind::of_type(format.program_type()).unwrap();
        let roots = [before.clone(), after.clone()].map(|memory| {
            KernelTermImport::default().machine(
                format,
                &MachineTerm::MemoryLoad(memory, Box::new(address.clone()), kind),
            )
        });
        assert_ne!(roots[0], roots[1]);
        for read in roots {
            let exports = KernelTermExport::machine_export_count();
            assert!(MachineOperandView::Shared(&read).observe(format).is_some());
            assert!(MachineOperandView::Shared(&read).accepts_cast_operand(format));
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            for destination in FORMATS {
                super::super::super::signedness_cast_tests::check_native_parity(
                    read.clone(),
                    destination,
                );
            }
        }
        let bad = KernelTermImport::default().machine(
            format,
            &MachineTerm::MemoryLoad(
                before.clone(),
                Box::new(address.clone()),
                crate::kernel::LoadKind::Int32,
            ),
        );
        assert!(MachineOperandView::Shared(&bad).observe(format).is_none());
        assert!(cast(&bad.into(), ProgramType::Int32).is_none());
    }
}

#[test]
fn supported_wide_arithmetic_matches_native_values_and_domains() {
    let _session = VerificationSession::enter();
    for a in FORMATS {
        for b in FORMATS {
            if a.format().bits() != 128 && b.format().bits() != 128 {
                continue;
            }
            for op in [
                MachineBinaryOp::Multiply,
                MachineBinaryOp::Divide,
                MachineBinaryOp::Remainder,
            ] {
                for defined in [false, true] {
                    let mut execution = ExecutionBudget::new();
                    let mut budget = SpecEvaluation::logical(&mut execution);
                    budget.program_definedness = defined;
                    for case in 0..6 {
                        let operand = |format: MachineIntegerType, id| match case {
                            0 => MachineTerm::Variable(Variable(id)),
                            1 => word(format, 0.into()),
                            2 => word(format, format.format().bounds().1),
                            3 if id == 995710 => word(format, format.format().bounds().0),
                            3 if format.format().is_signed() => word(format, (-1).into()),
                            5 if format.format().bits() <= 64 => MachineTerm::opaque_conversion(
                                "wide_operand",
                                MachineTerm::Variable(Variable(id)),
                            ),
                            5 => MachineTerm::MemoryLoad(
                                crate::kernel::intern_memory(Memory::new()),
                                Box::new(Pointer::symbolic(Variable(id))),
                                crate::kernel::LoadKind::of_type(format.program_type()).unwrap(),
                            ),
                            _ => word(format, 2.into()),
                        };
                        let left = operand(a, 995710);
                        let right = operand(b, 995711);
                        let expected = crate::kernel::eval::apply_spec_machine_arithmetic(
                            op,
                            if defined {
                                SpecDivision::CDefined
                            } else {
                                SpecDivision::Total
                            },
                            &a.value_from_term(left.clone()),
                            &b.value_from_term(right.clone()),
                            &ExecutionFacts::default(),
                            &[],
                        );
                        for (ls, rs) in [(false, false), (true, false), (false, true), (true, true)]
                        {
                            let make = |format, term: &MachineTerm, shared| {
                                if shared {
                                    SpecValue::Shared(root(format, term))
                                } else {
                                    SpecValue::Native(MachineIntegerType::value_from_term(
                                        format,
                                        term.clone(),
                                    ))
                                }
                            };
                            let l = make(a, &left, ls);
                            let r = make(b, &right, rs);
                            let exports = KernelTermExport::machine_export_count();
                            let actual = apply_values(Some(op), &l, &r, &budget);
                            assert_eq!(KernelTermExport::machine_export_count(), exports);
                            assert_eq!(actual.is_some(), expected.is_some(), "{a:?} {b:?} {op:?}");
                            if let (Some(actual), Some(expected)) = (actual, &expected) {
                                let ExpressionOutcome::Value(expected_value) = &expected.outcome
                                else {
                                    panic!()
                                };
                                let actual_value = SpecValue::Shared(actual.value).into_native();
                                let normalize = |value: &ProgramValue| {
                                    let format =
                                        MachineIntegerType::from_program_type(value.program_type()).unwrap();
                                    let crate::kernel::integer_c_value!(term) = value else {
                                        panic!()
                                    };
                                    format.value_from_term(native_term(term))
                                };
                                assert_eq!(
                                    normalize(&actual_value),
                                    normalize(expected_value),
                                    "{a:?} {b:?} {op:?} case{case}"
                                );
                                let normalize_debts = |debts: &[ProofObligation]| {
                                    debts
                                        .iter()
                                        .map(|o| {
                                            assert!(!o.is_assumable());
                                            let mut o = o.clone();
                                            o.proposition = domain(o.proposition());
                                            o
                                        })
                                        .collect::<Vec<_>>()
                                };
                                assert_eq!(
                                    normalize_debts(&actual.obligations),
                                    normalize_debts(&expected.obligations),
                                    "{a:?} {b:?} {op:?} case{case} defined{defined}"
                                );
                            }
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn wide_producer_keeps_unsupported_operators_and_untyped_words_out() {
    let _session = VerificationSession::enter();
    let mut execution = ExecutionBudget::new();
    let budget = SpecEvaluation::logical(&mut execution);
    for format in [MachineIntegerType::Int128, MachineIntegerType::UInt128] {
        let value: SpecValue = root(format, &MachineTerm::Variable(Variable(995712))).into();
        for op in [
            MachineBinaryOp::Add,
            MachineBinaryOp::Subtract,
            MachineBinaryOp::BitwiseAnd,
            MachineBinaryOp::BitwiseOr,
            MachineBinaryOp::BitwiseXor,
            MachineBinaryOp::ShiftLeft,
            MachineBinaryOp::ShiftRight,
        ] {
            assert!(apply_values(Some(op), &value, &value, &budget).is_none());
        }
        assert!(bitwise_not(&value, None).is_none());
        let invalid = KernelTerm::machine_binary_shared(
            format,
            MachineBinaryOp::Add,
            [
                root(format, &MachineTerm::Variable(Variable(995713))),
                root(format, &MachineTerm::Variable(Variable(995714))),
            ],
        );
        assert!(cast(&invalid.clone().into(), ProgramType::Int32).is_none());
        assert!(
            apply_values(
                Some(MachineBinaryOp::Divide),
                &invalid.into(),
                &value,
                &budget
            )
            .is_none()
        );
    }
}

#[test]
fn nested_wide_evaluation_retains_results_and_inherited_debts() {
    let _session = VerificationSession::enter();
    let leaf = |id| {
        Box::new(SpecExpression::Value(ProgramValue::Int128(
            MachineTerm::Variable(Variable(id)),
        )))
    };
    let expression = SpecExpression::Remainder(
        Box::new(SpecExpression::Multiply(leaf(995715), leaf(995716))),
        leaf(995717),
    );
    let mut execution = ExecutionBudget::new();
    let mut budget = SpecEvaluation::logical(&mut execution);
    let exports = KernelTermExport::machine_export_count();
    let actual = evaluate_spec_expression_paths_with_algebraic_bindings_in(
        SpecScope::unbound(&ExecutionState::new(), None),
        &expression,
        &PureFactContext::new(),
        &mut budget,
    )
    .unwrap();
    assert_eq!(KernelTermExport::machine_export_count(), exports);
    assert_eq!(actual.len(), 1);
    assert!(matches!(actual[0].value, SpecValue::Shared(_)));
    assert!(actual[0].facts.is_empty());
    let expected = evaluate(&expression, true);
    assert_eq!(
        actual[0]
            .obligations
            .iter()
            .map(|o| domain(o.proposition()))
            .collect::<Vec<_>>(),
        expected[0]
            .obligations
            .iter()
            .map(|o| domain(o.proposition()))
            .collect::<Vec<_>>()
    );
}

mod scaling_tests {
    include!("../../../scaling_tests/kernel/spec/shared_machine_wide.rs");
}
