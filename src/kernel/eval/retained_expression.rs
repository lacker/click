//! Execution arithmetic retains produced operands across expression paths.
//! Native operators remain explicit boundaries for unmigrated operations and
//! value families; they retain their original metadata and definedness.
use super::*;
use crate::kernel::execution_value::ExecutionValue;
type ExecutionValuePath = ExpressionPath<ExecutionValue>;
use crate::kernel::MachineBinaryOp as Op;

#[derive(Clone, Copy)]
enum Binary {
    Machine(Op),
    RustShift(Op),
    Narrow(MachineIntegerType, Op),
    Comparison(ComparisonOperator),
}

pub(in crate::kernel) fn evaluate_expression_value_paths(
    state: &ExecutionState,
    expression: &ProgramExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ExecutionValuePath>> {
    match expression {
        ProgramExpression::EnumConstruct {
            enum_type,
            variant,
            fields,
        } => {
            budget.consume_expression_step()?;
            return super::expression::evaluate_program_enum_construct_paths(
                state,
                *enum_type,
                variant,
                fields,
                assumptions,
                budget,
            );
        }
        ProgramExpression::EnumField {
            value,
            variant,
            index,
        } => {
            budget.consume_expression_step()?;
            return super::expression::evaluate_program_enum_field_paths(
                state,
                value,
                variant,
                *index,
                assumptions,
                budget,
            );
        }
        _ => {}
    }
    if let ProgramExpression::StepResult { step, .. } = expression
        && let Some(value) = state
            .step_results
            .as_ref()
            .and_then(|results| results.get(step))
        && value.shared().is_some()
    {
        budget.consume_expression_step()?;
        budget.check_path_width(1)?;
        return Ok(vec![ExpressionPath {
            outcome: ExpressionOutcome::Value(value.clone().into_value()),
            facts: ExecutionFacts::new(),
            obligations: vec![],
        }]);
    }
    if let ProgramExpression::Variable(name) = expression
        && !state.locals.is_array_object(name)
        && !state.locals.is_aggregate_object(name)
        && !matches!(
            state.locals.object_type(name),
            Some(ProgramType::Int128 | ProgramType::UInt128)
        )
    {
        budget.consume_expression_step()?;
        return super::expression::read_retained_lvalue_expression_paths(
            state,
            expression,
            assumptions,
            budget,
        );
    }
    if let ProgramExpression::Ternary {
        condition,
        then_branch,
        else_branch,
    } = expression
    {
        budget.consume_expression_step()?;
        return conditional_paths(
            state,
            condition,
            then_branch,
            else_branch,
            assumptions,
            budget,
        );
    }
    if let ProgramExpression::PointerOffsetBytes { pointer, bytes } = expression {
        budget.consume_expression_step()?;
        let mut paths = Vec::new();
        for mut path in evaluate_expression_value_paths(state, pointer, assumptions, budget)? {
            let ExpressionOutcome::Value(value) = &path.outcome else {
                paths.push(path);
                continue;
            };
            let Some(pointer) = value.pointer() else {
                path.outcome = ExpressionOutcome::RuntimeError(RuntimeError::TypeMismatch);
                paths.push(path);
                continue;
            };
            let pointer = pointer.clone();
            let operands = [
                value.common_operand(),
                KernelTerm::retained_native_machine_operand(
                    MachineIntegerType::UInt64,
                    &MachineTerm::uint64_constant(u64::from(*bytes)),
                ),
            ];
            paths.extend(
                super::operators::pointer_offset_by_bytes_paths(
                    state,
                    pointer,
                    *bytes,
                    path.facts,
                    path.obligations,
                    assumptions,
                )
                .into_iter()
                .map(|path| retain_pointer_arithmetic_path(path, Op::Add, 1, &operands)),
            );
        }
        budget.check_path_width(paths.len())?;
        return Ok(paths);
    }
    let narrow = if let ProgramExpression::Cast {
        expression,
        target_type,
        integer_mode: IntegerCastMode::NarrowArithmetic,
        ..
    } = expression
    {
        MachineIntegerType::from_program_type(*target_type)
            .filter(|format| super::operators::is_narrow_format(*format))
            .and_then(|format| {
                let (op, left, right) = match expression.as_ref() {
                    ProgramExpression::Add(a, b) => (Op::Add, a, b),
                    ProgramExpression::Subtract(a, b) => (Op::Subtract, a, b),
                    ProgramExpression::Multiply(a, b) => (Op::Multiply, a, b),
                    ProgramExpression::BitwiseAnd(a, b) => (Op::BitwiseAnd, a, b),
                    ProgramExpression::BitwiseOr(a, b) => (Op::BitwiseOr, a, b),
                    ProgramExpression::BitwiseXor(a, b) => (Op::BitwiseXor, a, b),
                    _ => return None,
                };
                Some((Binary::Narrow(format, op), left, right))
            })
    } else {
        None
    };
    let (operation, left, right) = if let Some(narrow) = narrow {
        narrow
    } else {
        match expression {
            ProgramExpression::RustShiftLeft(left, right) => {
                (Binary::RustShift(Op::ShiftLeft), left, right)
            }
            ProgramExpression::RustShiftRight(left, right) => {
                (Binary::RustShift(Op::ShiftRight), left, right)
            }
            ProgramExpression::Add(left, right) => (Binary::Machine(Op::Add), left, right),
            ProgramExpression::Subtract(left, right) => {
                (Binary::Machine(Op::Subtract), left, right)
            }
            ProgramExpression::Multiply(left, right) => {
                (Binary::Machine(Op::Multiply), left, right)
            }
            ProgramExpression::Divide(left, right) => (Binary::Machine(Op::Divide), left, right),
            ProgramExpression::BitwiseAnd(left, right) => {
                (Binary::Machine(Op::BitwiseAnd), left, right)
            }
            ProgramExpression::BitwiseOr(left, right) => {
                (Binary::Machine(Op::BitwiseOr), left, right)
            }
            ProgramExpression::BitwiseXor(left, right) => {
                (Binary::Machine(Op::BitwiseXor), left, right)
            }
            ProgramExpression::LessThan(left, right) => (
                Binary::Comparison(ComparisonOperator::LessThan),
                left,
                right,
            ),
            ProgramExpression::LessEqual(left, right) => (
                Binary::Comparison(ComparisonOperator::LessEqual),
                left,
                right,
            ),
            ProgramExpression::GreaterThan(left, right) => (
                Binary::Comparison(ComparisonOperator::GreaterThan),
                left,
                right,
            ),
            ProgramExpression::GreaterEqual(left, right) => (
                Binary::Comparison(ComparisonOperator::GreaterEqual),
                left,
                right,
            ),
            _ => {
                return Ok(super::expression::evaluate_native_expression_paths(
                    state,
                    expression,
                    assumptions,
                    budget,
                )?
                .into_iter()
                .map(|path| {
                    if matches!(
                        expression,
                        ProgramExpression::Value(ProgramValue::Pointer(_))
                            | ProgramExpression::Variable(_)
                            | ProgramExpression::FunctionAddress(_)
                            | ProgramExpression::AddressOf(_)
                            | ProgramExpression::CheckedObjectAddress(_)
                            | ProgramExpression::Subobject { .. }
                            | ProgramExpression::Cast { .. }
                    ) {
                        path.map_value(ExecutionValue::retain_formed_pointer)
                    } else {
                        path.into()
                    }
                })
                .collect());
            }
        }
    };
    budget.consume_expression_step()?;
    let (left_step_width, right_step_width) = if matches!(
        operation,
        Binary::Machine(Op::Add | Op::Subtract) | Binary::Comparison(_)
    ) {
        (
            program_expression_pointer_step_width(state, left),
            program_expression_pointer_step_width(state, right),
        )
    } else {
        (None, None)
    };
    let mut paths = Vec::new();
    for mut left_path in evaluate_expression_value_paths(state, left, assumptions, budget)? {
        refuse_freed_pointer(state, &mut left_path, assumptions);
        let ExpressionOutcome::Value(left_value) = left_path.outcome else {
            paths.push(left_path);
            continue;
        };
        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_path.facts, &left_path.obligations);
        for mut right_path in
            evaluate_expression_value_paths(state, right, &right_assumptions, budget)?
        {
            // Match the native binary evaluator: pointer validity uses the
            // incoming context, while the right expression sees left debts.
            refuse_freed_pointer(state, &mut right_path, assumptions);
            let Some((mut facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &left_path.facts,
                &left_path.obligations,
                &right_path.facts,
                &right_path.obligations,
                assumptions,
            ) else {
                continue;
            };
            let ExpressionOutcome::Value(right_value) = right_path.outcome else {
                paths.push(ExecutionValuePath {
                    facts,
                    obligations,
                    ..right_path
                });
                continue;
            };
            if let Binary::RustShift(op) = operation {
                if let Some((root, required)) =
                    crate::kernel::spec::execution_rust_shift(op, &left_value, &right_value)
                {
                    let context = assumptions_with_path_context(assumptions, &facts, &[]);
                    let mut obligations = obligations;
                    obligations.extend(required.into_iter().filter(|obligation| {
                        !crate::kernel::reasoning::path_facts::required_obligation_is_exactly_discharged(
                            &context, obligation.proposition(),
                        )
                    }));
                    paths.push(ExecutionValuePath {
                        outcome: ExpressionOutcome::Value(root.into()),
                        facts,
                        obligations,
                    });
                } else {
                    let apply = if op == Op::ShiftLeft {
                        apply_rust_shift_left
                    } else {
                        apply_rust_shift_right
                    };
                    paths.extend(
                        apply(
                            left_value.clone().into_native(),
                            right_value.into_native(),
                            facts,
                            obligations,
                            assumptions,
                        )
                        .into_iter()
                        .map(ExecutionValuePath::from),
                    );
                }
                continue;
            }
            if let Binary::Narrow(format, op) = operation {
                let outcome = crate::kernel::spec::execution_narrow_binary(
                    format,
                    op,
                    &left_value,
                    &right_value,
                )
                .map(|value| ExpressionOutcome::Value(value.into()))
                .unwrap_or(ExpressionOutcome::RuntimeError(RuntimeError::TypeMismatch));
                paths.push(ExecutionValuePath {
                    outcome,
                    facts,
                    obligations,
                });
                continue;
            }
            if let Binary::Comparison(operator) = operation {
                let native_paths = if let Some(condition) =
                    retained_comparison(operator, &left_value, &right_value)
                {
                    condition_as_program_int32_paths(condition, facts, obligations, assumptions)
                } else {
                    super::operators::apply_program_comparison(
                        state,
                        operator,
                        left_value.clone().into_native(),
                        right_value.into_native(),
                        left_step_width,
                        right_step_width,
                        facts,
                        obligations,
                        assumptions,
                    )
                };
                paths.extend(native_paths.into_iter().map(ExecutionValuePath::from));
                continue;
            }
            let Binary::Machine(op) = operation else {
                unreachable!()
            };
            if let Some(value) = retained_binary(op, &left_value, &right_value) {
                if op == Op::BitwiseAnd
                    && let ExecutionValue::Shared(root) = &value
                    && let Some(equation) =
                        crate::kernel::spec::bitwise_tag_equation(root, assumptions)
                {
                    facts.push(ExecutionPureFact::new(Proposition::ConditionIs(
                        equation, true,
                    )));
                }
                paths.push(ExecutionValuePath {
                    outcome: ExpressionOutcome::Value(value),
                    facts,
                    obligations,
                });
                continue;
            }
            // Preserve the exact produced operands before native formation
            // checking reads them. The result keeps that syntax independently
            // of its native address normalization and compatibility cache.
            let pointer_arithmetic = if matches!(op, Op::Add | Op::Subtract) {
                let width = match (left_value.pointer(), right_value.pointer()) {
                    (Some(pointer), None) => {
                        super::operators::pointer_value_step_width(pointer, left_step_width)
                    }
                    (None, Some(pointer)) if op == Op::Add => {
                        super::operators::pointer_value_step_width(pointer, right_step_width)
                    }
                    _ => None,
                };
                width.map(|width| {
                    (
                        width,
                        [left_value.common_operand(), right_value.common_operand()],
                    )
                })
            } else {
                None
            };
            // Full ProgramValue payloads cross this boundary, including pointer
            // provenance and qualifications. No numeric projection is used.
            let left_value = left_value.clone().into_native();
            let right_value = right_value.into_native();
            let native = match op {
                Op::Add => apply_program_add(
                    state,
                    left_value,
                    right_value,
                    left_step_width,
                    right_step_width,
                    facts,
                    obligations,
                    assumptions,
                )
                .into_iter()
                .map(super::operators::fold_program_int32_constant_increment)
                .collect(),
                Op::Subtract => apply_program_subtract(
                    state,
                    left_value,
                    right_value,
                    left_step_width,
                    right_step_width,
                    facts,
                    obligations,
                    assumptions,
                ),
                Op::Multiply => {
                    apply_program_multiply(left_value, right_value, facts, obligations, assumptions)
                }
                Op::Divide => {
                    apply_program_divide(left_value, right_value, facts, obligations, assumptions)
                }
                Op::BitwiseAnd | Op::BitwiseOr | Op::BitwiseXor => apply_program_bitwise_binary(
                    left_value,
                    right_value,
                    facts,
                    obligations,
                    assumptions,
                    match op {
                        Op::BitwiseAnd => BitwiseOperation::And,
                        Op::BitwiseOr => BitwiseOperation::Or,
                        Op::BitwiseXor => BitwiseOperation::Xor,
                        _ => unreachable!(),
                    },
                ),
                _ => unreachable!(),
            };
            paths.extend(native.into_iter().map(|path| match &pointer_arithmetic {
                Some((width, operands)) => {
                    retain_pointer_arithmetic_path(path, op, *width, operands)
                }
                None => path.into(),
            }));
        }
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn retain_pointer_arithmetic_path(
    path: ExpressionPath,
    operation: Op,
    byte_width: u32,
    operands: &[KernelTerm; 2],
) -> ExecutionValuePath {
    path.map_value(|value| match value {
        ProgramValue::Pointer(pointer) => KernelTerm::shared_pointer_arithmetic(
            operation,
            byte_width,
            operands.clone(),
            SharedPointerValue::import_produced(&pointer),
        )
        .into(),
        value => ExecutionValue::retain_native(value),
    })
}

fn retained_comparison(
    operator: ComparisonOperator,
    left: &ExecutionValue,
    right: &ExecutionValue,
) -> Option<ConditionTerm> {
    let (format, left) = left.machine()?;
    let (right_format, right) = right.machine()?;
    if format != right_format
        || !matches!(
            format,
            MachineIntegerType::Int32
                | MachineIntegerType::UInt32
                | MachineIntegerType::Int64
                | MachineIntegerType::UInt64
        )
    {
        return None;
    }
    let relation = match operator {
        ComparisonOperator::LessThan => CompareRelation::LessThan,
        ComparisonOperator::LessEqual => CompareRelation::LessEqual,
        ComparisonOperator::GreaterThan => CompareRelation::GreaterThan,
        ComparisonOperator::GreaterEqual => CompareRelation::GreaterEqual,
        _ => return None,
    };
    Some(
        crate::kernel::machine_integer::comparison::condition_for_operand_views(
            format,
            relation,
            [left, right],
        ),
    )
}

fn conditional_paths(
    state: &ExecutionState,
    condition: &ProgramExpression,
    then_branch: &ProgramExpression,
    else_branch: &ProgramExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ExecutionValuePath>> {
    let mut paths = Vec::new();
    for path in evaluate_program_condition_paths(state, condition, assumptions, budget)? {
        let ExpressionOutcome::Value(value) = path.outcome else {
            paths.push(path.into());
            continue;
        };
        for truthiness in program_truthiness_paths(value, path.facts, path.obligations, assumptions)
        {
            let branch = if truthiness.is_true {
                then_branch
            } else {
                else_branch
            };
            let branch_assumptions = assumptions_with_path_context(
                assumptions,
                &truthiness.facts,
                &truthiness.obligations,
            );
            for path in evaluate_expression_value_paths(state, branch, &branch_assumptions, budget)?
            {
                let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                    &truthiness.facts,
                    &truthiness.obligations,
                    &path.facts,
                    &path.obligations,
                    assumptions,
                ) else {
                    continue;
                };
                paths.push(ExecutionValuePath {
                    facts,
                    obligations,
                    ..path.map_value(ExecutionValue::retain_pointer_result)
                });
            }
        }
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(super) fn freed_expression_value_pointer_use(
    state: &ExecutionState,
    value: &ExecutionValue,
    assumptions: &PureFactContext,
) -> Option<UndefinedBehavior> {
    value
        .native_payload()
        .and_then(|native| freed_pointer_use(state, native, assumptions))
}

fn refuse_freed_pointer(
    state: &ExecutionState,
    path: &mut ExecutionValuePath,
    assumptions: &PureFactContext,
) {
    if let ExpressionOutcome::Value(value) = &path.outcome
        && let Some(undefined) = freed_expression_value_pointer_use(state, value, assumptions)
    {
        path.outcome = ExpressionOutcome::UndefinedBehavior(undefined);
    }
}

fn retained_binary(
    op: Op,
    left: &ExecutionValue,
    right: &ExecutionValue,
) -> Option<ExecutionValue> {
    if !matches!(
        op,
        Op::Add | Op::Subtract | Op::Multiply | Op::BitwiseAnd | Op::BitwiseOr | Op::BitwiseXor
    ) {
        return None;
    }
    let (format, left) = left.machine()?;
    let (right_format, right) = right.machine()?;
    if format != right_format
        || !matches!(
            format,
            MachineIntegerType::UInt32 | MachineIntegerType::UInt64
        ) && !(matches!(op, Op::BitwiseAnd | Op::BitwiseOr | Op::BitwiseXor)
            && matches!(
                format,
                MachineIntegerType::Int32 | MachineIntegerType::Int64
            ))
    {
        return None;
    }
    let children = [
        KernelTerm::retained_machine_operand(format, left),
        KernelTerm::retained_machine_operand(format, right),
    ];
    let raw = KernelTerm::machine_binary_shared(format, op, children.clone());
    // These constructors reproduce MachineTerm's native root reductions, not
    // an equality/fact-driven choice of the result representation.
    let value =
        crate::kernel::proof::equality_rewrite::rebuild_normalized_machine_node(&raw, &children)?;
    Some(ExecutionValue::from(value))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn retained_pointer_numeric_results_match_native_casts_and_differences() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = ProgramExpression::Value(ProgramValue::Pointer(
            PointerValue::new(
                Pointer::symbolic(Variable(1024100)),
                ProgramType::Int32Pointer,
            )
            .with_pointee_constant(true)
            .with_pointee_volatile(true),
        ));
        let cast = |expression: ProgramExpression, target_type| ProgramExpression::Cast {
            expression: Box::new(expression),
            target_type,
            integer_mode: IntegerCastMode::Standard,
            pointee_struct: None,
            pointee_volatile: false,
            pointee_constant: false,
            explicit_qualification: false,
        };
        let mut expressions = Vec::new();
        for ty in [ProgramType::Int64, ProgramType::UInt64, ProgramType::Int32] {
            expressions.push(cast(pointer.clone(), ty));
            expressions.push(cast(ProgramExpression::FunctionAddress("f".into()), ty));
            expressions.push(cast(
                ProgramExpression::Value(ProgramValue::typed_pointer(
                    Pointer::null(),
                    ProgramType::Int32Pointer,
                )),
                ty,
            ));
        }
        expressions.push(cast(
            cast(pointer.clone(), ProgramType::UInt64),
            ProgramType::Int32Pointer,
        ));
        expressions.push(ProgramExpression::Subtract(
            Box::new(pointer.clone()),
            Box::new(pointer.clone()),
        ));
        expressions.push(ProgramExpression::Subtract(
            Box::new(pointer),
            Box::new(ProgramExpression::Value(ProgramValue::typed_pointer(
                Pointer::symbolic(Variable(1024101)),
                ProgramType::Int32Pointer,
            ))),
        ));
        for expression in expressions {
            let expected = super::super::expression::evaluate_native_expression_paths(
                &ExecutionState::new(),
                &expression,
                &PureFactContext::new(),
                &mut ExecutionBudget::new(),
            )
            .unwrap();
            let actual = evaluate(&expression);
            assert_eq!(actual.len(), expected.len());
            for (actual, expected) in actual.into_iter().zip(expected) {
                if matches!(
                    expected.outcome,
                    ExpressionOutcome::Value(ProgramValue::PointerInteger(_))
                ) {
                    let ExpressionOutcome::Value(value) = &actual.outcome else {
                        panic!("value");
                    };
                    assert!(
                        matches!(
                            value,
                            ExecutionValue::Native(ProgramValue::PointerInteger(_))
                        ),
                        "complete conversion records remain execution metadata"
                    );
                }
                assert_eq!(actual.into_native(), expected, "{expression:?}");
            }
        }
    }

    #[test]
    fn retained_pointer_arithmetic_preserves_operands_metadata_and_refusals() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = ProgramExpression::Value(ProgramValue::Pointer(
            PointerValue::new(
                Pointer::symbolic(Variable(1023000)),
                ProgramType::Int32Pointer,
            )
            .with_pointee_constant(true)
            .with_pointee_volatile(true),
        ));
        let index = ProgramExpression::Add(
            Box::new(ProgramExpression::Value(ProgramValue::Int32(
                MachineTerm::Variable(Variable(1023001)),
            ))),
            Box::new(ProgramExpression::Value(ProgramValue::Int32(
                MachineTerm::constant(2),
            ))),
        );
        let index_paths = evaluate(&index);
        let ExpressionOutcome::Value(index_value) = &index_paths[0].outcome else {
            panic!("index value");
        };
        let index_root = index_value.shared().unwrap();
        let wide = ProgramExpression::Value(ProgramValue::UInt64(MachineTerm::Variable(Variable(
            1023002,
        ))));
        let expressions = vec![
            ProgramExpression::Add(Box::new(pointer.clone()), Box::new(index.clone())),
            ProgramExpression::Add(Box::new(index), Box::new(pointer.clone())),
            ProgramExpression::Subtract(Box::new(pointer.clone()), Box::new(wide.clone())),
            ProgramExpression::Add(Box::new(pointer.clone()), Box::new(wide)),
            ProgramExpression::PointerOffsetBytes {
                pointer: Box::new(pointer),
                bytes: 8,
            },
            ProgramExpression::Add(
                Box::new(ProgramExpression::Value(ProgramValue::typed_pointer(
                    Pointer::null(),
                    ProgramType::Int32Pointer,
                ))),
                Box::new(ProgramExpression::Value(ProgramValue::Int32(
                    MachineTerm::constant(1),
                ))),
            ),
            ProgramExpression::Add(
                Box::new(ProgramExpression::FunctionAddress("f".into())),
                Box::new(ProgramExpression::Value(ProgramValue::Int32(
                    MachineTerm::constant(1),
                ))),
            ),
        ];
        let state = ExecutionState::new();
        let assumptions = PureFactContext::new();
        for (position, expression) in expressions.into_iter().enumerate() {
            let expected = super::super::expression::evaluate_native_expression_paths(
                &state,
                &expression,
                &assumptions,
                &mut ExecutionBudget::new(),
            )
            .unwrap();
            let actual = evaluate(&expression);
            assert_eq!(actual.len(), expected.len());
            for (actual, expected) in actual.into_iter().zip(expected) {
                if let ExpressionOutcome::Value(ProgramValue::Pointer(pointer)) = &expected.outcome
                {
                    let ExpressionOutcome::Value(value) = &actual.outcome else {
                        panic!("pointer result");
                    };
                    let root = value.shared().expect("retained arithmetic");
                    let KernelTermNode::PointerArithmetic {
                        byte_width,
                        operands,
                        value,
                        ..
                    } = root.node()
                    else {
                        panic!("arithmetic root");
                    };
                    assert_eq!(*byte_width, if position == 4 { 1 } else { 4 });
                    assert!(value.same_source_payload(&SharedPointerValue::import(pointer)));
                    if position < 2 {
                        assert_eq!(&operands[1 - position], index_root);
                    }
                }
                assert_eq!(actual.into_native(), expected, "{expression:?}");
            }
        }
    }

    #[test]
    fn formed_pointer_roots_match_native_values_qualifiers_and_obligations() {
        let _session = crate::kernel::VerificationSession::enter();
        let mut state = ExecutionState::new();
        state
            .locals
            .set("x", ProgramValue::Int32(MachineTerm::constant(7)));
        let array = Pointer::symbolic(Variable(1022001));
        state
            .locals
            .set_array_object_at("array", ProgramType::Int32, 4, array.clone());
        state.set_memory(Memory::new().with_block(array.block, 16));
        let pointer = PointerValue::new(
            Pointer::symbolic(Variable(1022000)),
            ProgramType::Int32Pointer,
        )
        .with_pointee_constant(true)
        .with_pointee_volatile(true);
        let source = ProgramExpression::Value(ProgramValue::Pointer(pointer));
        let mut expressions = vec![
            ProgramExpression::Value(ProgramValue::typed_pointer(
                Pointer::null(),
                ProgramType::VoidPointer,
            )),
            source.clone(),
            ProgramExpression::Variable("array".into()),
            ProgramExpression::FunctionAddress("callback".into()),
            ProgramExpression::AddressOf(Box::new(ProgramExpression::Variable("x".into()))),
            ProgramExpression::CheckedObjectAddress(Box::new(ProgramExpression::Variable(
                "x".into(),
            ))),
            ProgramExpression::Subobject {
                pointer: Box::new(source.clone()),
                width: 4,
            },
            ProgramExpression::PointerOffsetBytes {
                pointer: Box::new(source.clone()),
                bytes: 0,
            },
        ];
        for explicit_qualification in [false, true] {
            expressions.push(ProgramExpression::Cast {
                expression: Box::new(source.clone()),
                target_type: ProgramType::UInt8Pointer,
                integer_mode: IntegerCastMode::Standard,
                pointee_struct: None,
                pointee_volatile: false,
                pointee_constant: false,
                explicit_qualification,
            });
        }
        let assumptions = PureFactContext::new();
        for expression in expressions {
            let expected = super::super::expression::evaluate_native_expression_paths(
                &state,
                &expression,
                &assumptions,
                &mut ExecutionBudget::new(),
            )
            .unwrap();
            let actual = evaluate_expression_value_paths(
                &state,
                &expression,
                &assumptions,
                &mut ExecutionBudget::new(),
            )
            .unwrap();
            assert_eq!(actual.len(), expected.len());
            for (actual, expected) in actual.into_iter().zip(expected) {
                if let ExpressionOutcome::Value(ProgramValue::Pointer(expected_pointer)) =
                    &expected.outcome
                {
                    let ExpressionOutcome::Value(value) = &actual.outcome else {
                        panic!("formed pointer");
                    };
                    let retained = value
                        .shared()
                        .and_then(KernelTerm::pointer_payload)
                        .expect("formed common root");
                    assert!(
                        retained.same_source_payload(&SharedPointerValue::import(expected_pointer)),
                        "{expression:?}"
                    );
                }
                assert_eq!(actual.into_native(), expected, "{expression:?}");
            }
        }
    }

    #[test]
    fn retained_pointer_reads_preserve_freed_value_refusal() {
        let _session = crate::kernel::VerificationSession::enter();
        let cell = Pointer::symbolic(Variable(1021001));
        let assumptions = PureFactContext::new();
        let memory = Memory::new();
        let native = memory.symbolic_pointer_load(&cell, ProgramType::Int32Pointer);
        let ProgramValue::Pointer(pointer) = &native else {
            unreachable!()
        };
        // Allocation contracts can name a retained read as their exact base.
        // Value-use refusal consults that base's own freed-block record.
        let base = pointer.pointer().clone();
        let retained = ExecutionValue::retain_native(native.clone());
        assert!(matches!(
            retained.shared().map(KernelTerm::node),
            Some(KernelTermNode::PointerRead { .. })
        ));
        let memory = memory
            .with_heap_allocation_claim(base.clone(), HeapExtent::int32(4))
            .unwrap();
        let freed = memory.free_heap_block(&base, &assumptions).unwrap();
        let state = ExecutionState::new().with_memory(freed);
        assert_eq!(
            freed_pointer_use(&state, &native, &assumptions),
            Some(UndefinedBehavior::FreedPointerUse)
        );
        let mut path = ExecutionValuePath {
            outcome: ExpressionOutcome::Value(retained),
            facts: Default::default(),
            obligations: vec![],
        };
        refuse_freed_pointer(&state, &mut path, &assumptions);
        assert!(matches!(
            path.outcome,
            ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::FreedPointerUse)
        ));
    }

    fn evaluate(expression: &ProgramExpression) -> Vec<ExecutionValuePath> {
        evaluate_expression_value_paths(
            &ExecutionState::new(),
            expression,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
        )
        .unwrap()
    }
    #[test]
    fn retained_execution_unsigned_operators_match_native_roots() {
        for format in [MachineIntegerType::UInt32, MachineIntegerType::UInt64] {
            let wrap = |term| match format {
                MachineIntegerType::UInt32 => ProgramValue::UInt32(term),
                MachineIntegerType::UInt64 => ProgramValue::UInt64(term),
                _ => unreachable!(),
            };
            let constant = |n| {
                if format == MachineIntegerType::UInt32 {
                    MachineTerm::uint32_constant(n as u32)
                } else {
                    MachineTerm::uint64_constant(n)
                }
            };
            let variable = MachineTerm::Variable(Variable(991101));
            let terms = [
                constant(0),
                constant(1),
                constant(u64::MAX),
                variable.clone(),
                MachineTerm::machine_binary(format, Op::Add, variable.clone(), constant(2)),
                MachineTerm::machine_binary(format, Op::Subtract, variable.clone(), constant(2)),
            ];
            for op in [Op::Add, Op::Subtract, Op::Multiply] {
                for left in &terms {
                    for right in &terms {
                        let a = ExecutionValue::from(wrap(left.clone()));
                        let b = ExecutionValue::from(wrap(right.clone()));
                        let result = retained_binary(op, &a, &b).unwrap();
                        assert_eq!(
                            result.into_native(),
                            wrap(MachineTerm::machine_binary(
                                format,
                                op,
                                left.clone(),
                                right.clone()
                            )),
                            "{format:?} {op:?}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn retained_execution_conditional_keeps_selected_value_without_export() {
        let expression = ProgramExpression::Ternary {
            condition: Box::new(ProgramExpression::Value(ProgramValue::Int32(
                MachineTerm::constant(1),
            ))),
            then_branch: Box::new(ProgramExpression::BitwiseXor(
                Box::new(ProgramExpression::Value(ProgramValue::UInt32(
                    MachineTerm::Variable(Variable(991103)),
                ))),
                Box::new(ProgramExpression::Value(ProgramValue::UInt32(
                    MachineTerm::uint32_constant(7),
                ))),
            )),
            else_branch: Box::new(ProgramExpression::Variable("not_evaluated".into())),
        };
        let exports = KernelTermExport::machine_export_count();
        let paths = evaluate(&expression);
        assert_eq!(paths.len(), 1);
        assert!(matches!(
            paths[0].outcome,
            ExpressionOutcome::Value(ref value) if matches!(value, ExecutionValue::Shared(_))
        ));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn pointer_conditional_paths_keep_scoped_facts_and_complete_values() {
        let _session = crate::kernel::VerificationSession::enter();
        let left = ProgramValue::Pointer(
            PointerValue::new(
                Pointer::symbolic(Variable(1026200)),
                ProgramType::Int32Pointer,
            )
            .with_pointee_constant(true),
        );
        let right = ProgramValue::Pointer(
            PointerValue::new(
                Pointer::symbolic(Variable(1026201)),
                ProgramType::Int32Pointer,
            )
            .with_pointee_volatile(true),
        );
        let expression = ProgramExpression::Ternary {
            condition: Box::new(ProgramExpression::Value(ProgramValue::Int32(
                MachineTerm::Variable(Variable(1026202)),
            ))),
            then_branch: Box::new(ProgramExpression::Value(left)),
            else_branch: Box::new(ProgramExpression::Value(right)),
        };
        let actual = evaluate(&expression);
        let expected = evaluate_program_expression_paths(
            &ExecutionState::new(),
            &expression,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
        )
        .unwrap();
        assert_eq!(actual.len(), 2);
        for (path, native) in actual.into_iter().zip(expected) {
            let ExpressionOutcome::Value(value) = &path.outcome else {
                panic!("pointer result")
            };
            assert!(value.shared().is_some());
            let ExpressionOutcome::Value(ProgramValue::Pointer(pointer)) = &native.outcome else {
                panic!("native pointer")
            };
            assert_eq!(
                value.pointer().unwrap().pointee_constant(),
                pointer.pointee_constant()
            );
            assert_eq!(
                value.pointer().unwrap().pointee_volatile(),
                pointer.pointee_volatile()
            );
            assert_eq!(path.into_native(), native);
        }
    }

    #[test]
    fn retained_execution_bitwise_formats_match_native() {
        for format in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let left = format.symbolic_value(Variable(991104));
            let right = format.symbolic_value(Variable(991105));
            for (op, operation) in [
                (Op::BitwiseAnd, BitwiseOperation::And),
                (Op::BitwiseOr, BitwiseOperation::Or),
                (Op::BitwiseXor, BitwiseOperation::Xor),
            ] {
                let retained =
                    retained_binary(op, &left.clone().into(), &right.clone().into()).unwrap();
                let expected = apply_program_bitwise_binary(
                    left.clone(),
                    right.clone(),
                    ExecutionFacts::new(),
                    Vec::new(),
                    &PureFactContext::new(),
                    operation,
                );
                assert_eq!(
                    ExpressionOutcome::Value(retained.into_native()),
                    expected[0].outcome
                );
            }
        }
    }

    #[test]
    fn retained_execution_order_comparisons_match_native_paths() {
        for (left, right) in [(0, 1), (1, 0), (u32::MAX, 0), (7, 7)] {
            for (operator, expression) in [
                (
                    ComparisonOperator::LessThan,
                    ProgramExpression::LessThan as fn(_, _) -> _,
                ),
                (ComparisonOperator::LessEqual, ProgramExpression::LessEqual),
                (
                    ComparisonOperator::GreaterThan,
                    ProgramExpression::GreaterThan,
                ),
                (
                    ComparisonOperator::GreaterEqual,
                    ProgramExpression::GreaterEqual,
                ),
            ] {
                let left = ProgramValue::UInt32(MachineTerm::uint32_constant(left));
                let right = ProgramValue::UInt32(MachineTerm::uint32_constant(right));
                let result = evaluate(&expression(
                    Box::new(ProgramExpression::Value(left.clone())),
                    Box::new(ProgramExpression::Value(right.clone())),
                ));
                let expected = super::super::operators::apply_program_comparison(
                    &ExecutionState::new(),
                    operator,
                    left,
                    right,
                    None,
                    None,
                    ExecutionFacts::new(),
                    Vec::new(),
                    &PureFactContext::new(),
                );
                assert_eq!(
                    result
                        .into_iter()
                        .map(|path| path.map_value(ExecutionValue::into_native))
                        .collect::<Vec<_>>(),
                    expected
                );
            }
        }
    }

    #[test]
    fn retained_execution_comparison_reads_shared_operands_without_export() {
        let format = MachineIntegerType::UInt32;
        let mut left = ExecutionValue::from(format.symbolic_value(Variable(991106)));
        for _ in 0..32 {
            left = retained_binary(
                Op::Multiply,
                &left,
                &ExecutionValue::from(ProgramValue::UInt32(MachineTerm::uint32_constant(3))),
            )
            .unwrap();
        }
        let exports = KernelTermExport::machine_export_count();
        assert!(
            retained_comparison(
                ComparisonOperator::LessThan,
                &left,
                &ExecutionValue::from(ProgramValue::UInt32(MachineTerm::uint32_constant(10)))
            )
            .is_some()
        );
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn retained_execution_preserves_signed_overflow_and_unbound_errors() {
        let overflow = ProgramExpression::Add(
            Box::new(ProgramExpression::Value(ProgramValue::Int32(
                MachineTerm::constant(i32::MAX as u32),
            ))),
            Box::new(ProgramExpression::Value(ProgramValue::Int32(
                MachineTerm::constant(1),
            ))),
        );
        assert!(
            evaluate(&overflow)
                .iter()
                .any(|path| matches!(path.outcome, ExpressionOutcome::UndefinedBehavior(_)))
        );
        let missing = ProgramExpression::Multiply(
            Box::new(ProgramExpression::Variable("missing".into())),
            Box::new(ProgramExpression::Value(ProgramValue::UInt32(
                MachineTerm::uint32_constant(2),
            ))),
        );
        assert!(matches!(&evaluate(&missing)[0].outcome,
            ExpressionOutcome::RuntimeError(RuntimeError::UnboundVariable(name)) if name == "missing"));
        assert!(
            retained_binary(
                Op::Add,
                &ProgramValue::Int32(MachineTerm::constant(1)).into(),
                &ProgramValue::UInt32(MachineTerm::uint32_constant(1)).into()
            )
            .is_none()
        );
    }

    #[test]
    fn retained_bitwise_and_preserves_tag_facts_and_missing_bound_refusals() {
        let _session = crate::kernel::VerificationSession::enter();
        let word = MachineTerm::Variable(Variable(998272));
        let tag = MachineTerm::Variable(Variable(998273));
        let lower = ConditionTerm::signed_less_equal(0u32.into(), tag.clone());
        let upper = ConditionTerm::signed_less_equal(tag.clone(), 1u32.into());
        let empty = PureFactContext::new();
        let nonnegative = empty.clone().assume_condition(lower, true);
        let bounded = nonnegative.clone().assume_condition(upper.clone(), true);
        let upper_only = empty.clone().assume_condition(upper, true);
        let left = ProgramValue::UInt64(MachineTerm::uint64_bitwise_or(
            word.clone(),
            MachineTerm::uint64_from_int32(tag),
        ));
        let right = ProgramValue::UInt64(MachineTerm::uint64_constant(!3));
        let added = ProgramValue::UInt64(MachineTerm::uint64_add(
            word.clone(),
            MachineTerm::uint64_constant(1),
        ));
        let clear = empty.clone().assume_condition(
            ConditionTerm::uint64_equal(
                MachineTerm::uint64_bitwise_and(word, MachineTerm::uint64_constant(1)),
                MachineTerm::uint64_constant(0),
            ),
            true,
        );
        for (left, context, count) in [
            (left.clone(), &empty, 0),
            (left.clone(), &nonnegative, 0),
            (left.clone(), &upper_only, 0),
            (left, &bounded, 1),
            (added.clone(), &empty, 0),
            (added, &clear, 1),
        ] {
            let expression = ProgramExpression::BitwiseAnd(
                Box::new(ProgramExpression::Value(left.clone())),
                Box::new(ProgramExpression::Value(right.clone())),
            );
            let expected = apply_program_bitwise_binary(
                left.clone(),
                right.clone(),
                ExecutionFacts::new(),
                Vec::new(),
                context,
                BitwiseOperation::And,
            );
            let exports = KernelTermExport::machine_export_count();
            let actual = evaluate_expression_value_paths(
                &ExecutionState::new(),
                &expression,
                context,
                &mut ExecutionBudget::new(),
            )
            .unwrap();
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert_eq!(actual.len(), 1);
            assert_eq!(actual[0].facts.len(), count);
            assert_eq!(actual[0].facts.len(), expected[0].facts.len());
            assert_eq!(
                actual[0]
                    .outcome
                    .clone()
                    .map_value(ExecutionValue::into_native),
                expected[0].outcome
            );
            for (actual, expected) in actual[0].facts.iter().zip(expected[0].facts.iter()) {
                let actual =
                    crate::kernel::proof::proposition_identity_key(actual.proposition()).unwrap();
                let expected =
                    crate::kernel::proof::proposition_identity_key(expected.proposition()).unwrap();
                assert_eq!(actual, expected);
            }
        }
    }

    fn narrow_expression(
        expression: ProgramExpression,
        target_type: ProgramType,
    ) -> ProgramExpression {
        ProgramExpression::Cast {
            expression: Box::new(expression),
            target_type,
            integer_mode: IntegerCastMode::NarrowArithmetic,
            pointee_struct: None,
            pointee_volatile: false,
            pointee_constant: false,
            explicit_qualification: false,
        }
    }

    #[test]
    fn rust_execution_handoffs_preserve_original_widths_and_refusals() {
        let _session = crate::kernel::VerificationSession::enter();
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
            let left = ProgramExpression::Value(
                format.value_from_term(MachineTerm::Variable(Variable(998300))),
            );
            for count in [-1i32, 0, 1, 7, 8, 16, 32, 64] {
                let right = ProgramExpression::Value(ProgramValue::Int32(MachineTerm::constant(
                    count as u32,
                )));
                for expression in [
                    ProgramExpression::RustShiftLeft(
                        Box::new(left.clone()),
                        Box::new(right.clone()),
                    ),
                    ProgramExpression::RustShiftRight(
                        Box::new(left.clone()),
                        Box::new(right.clone()),
                    ),
                ] {
                    let actual = evaluate(&expression);
                    let expected = super::super::expression::evaluate_native_expression_paths(
                        &ExecutionState::new(),
                        &expression,
                        &PureFactContext::new(),
                        &mut ExecutionBudget::new(),
                    )
                    .unwrap();
                    assert_eq!(actual.len(), expected.len());
                    for (actual, expected) in actual.into_iter().zip(expected) {
                        assert_eq!(
                            actual.outcome.map_value(ExecutionValue::into_native),
                            expected.outcome
                        );
                        assert_eq!(actual.facts, expected.facts);
                        assert_eq!(actual.obligations.len(), expected.obligations.len());
                        assert!(actual.obligations.iter().all(|debt| !debt.is_assumable()));
                    }
                }
            }
        }
        for format in [
            MachineIntegerType::Int8,
            MachineIntegerType::UInt8,
            MachineIntegerType::Int16,
            MachineIntegerType::UInt16,
        ] {
            for right in [
                format.value_from_term(MachineTerm::Variable(Variable(998301))),
                ProgramValue::Int32(MachineTerm::constant(3)),
                ProgramValue::Int32(MachineTerm::constant(70000)),
                ProgramValue::UInt64(MachineTerm::uint64_constant(3)),
            ] {
                let expression = narrow_expression(
                    ProgramExpression::Add(
                        Box::new(ProgramExpression::Value(
                            format.value_from_term(MachineTerm::Variable(Variable(998300))),
                        )),
                        Box::new(ProgramExpression::Value(right)),
                    ),
                    format.program_type(),
                );
                let actual = evaluate(&expression);
                let expected = super::super::expression::evaluate_native_expression_paths(
                    &ExecutionState::new(),
                    &expression,
                    &PureFactContext::new(),
                    &mut ExecutionBudget::new(),
                )
                .unwrap();
                assert_eq!(
                    actual
                        .into_iter()
                        .map(|p| p.map_value(ExecutionValue::into_native))
                        .collect::<Vec<_>>(),
                    expected
                );
            }
        }
    }

    #[test]
    fn retained_rust_shift_discharges_only_established_count_domains() {
        let _session = crate::kernel::VerificationSession::enter();
        let count = MachineTerm::Variable(Variable(998302));
        let bound =
            ConditionTerm::unsigned_less_than(count.clone(), MachineTerm::uint32_constant(8));
        let expression = ProgramExpression::RustShiftLeft(
            Box::new(ProgramExpression::Value(ProgramValue::Int8(
                MachineTerm::Variable(Variable(998303)),
            ))),
            Box::new(ProgramExpression::Value(ProgramValue::UInt32(count))),
        );
        let empty = PureFactContext::new();
        let valid = empty.clone().assume_condition(bound.clone(), true);
        let invalid = empty.clone().assume_condition(bound, false);
        let mut roots = Vec::new();
        for (context, pending) in [(&empty, 1), (&valid, 0), (&invalid, 1)] {
            let paths = evaluate_expression_value_paths(
                &ExecutionState::new(),
                &expression,
                context,
                &mut ExecutionBudget::new(),
            )
            .unwrap();
            assert_eq!(paths.len(), 1);
            assert_eq!(paths[0].obligations.len(), pending);
            roots.push(paths[0].outcome.clone());
        }
        assert!(roots.windows(2).all(|pair| pair[0] == pair[1]));
    }

    fn machine_handoff_caller(rust: bool) -> ExecutionState {
        let format = if rust {
            MachineIntegerType::UInt8
        } else {
            MachineIntegerType::UInt32
        };
        let zero = if rust {
            MachineTerm::narrow_constant(format, 0)
        } else {
            MachineTerm::uint32_constant(0)
        };
        ExecutionState::new().with_local("received", format.value_from_term(zero))
    }

    fn complete_machine_handoff_program(
        rust: bool,
        size: usize,
        declared: bool,
    ) -> (ExecutionEnvironment, ProgramStatement) {
        let format = if rust {
            MachineIntegerType::UInt8
        } else {
            MachineIntegerType::UInt32
        };
        let program_type = format.program_type();
        let three = if rust {
            MachineTerm::narrow_constant(format, 3)
        } else {
            MachineTerm::uint32_constant(3)
        };
        let multiply = ProgramExpression::Multiply(
            Box::new(crate::kernel::program_expression::variable("held")),
            Box::new(ProgramExpression::Value(format.value_from_term(three))),
        );
        let expression = if rust {
            narrow_expression(multiply, program_type)
        } else {
            multiply
        };
        let mut body = program_return(crate::kernel::program_expression::variable("held"));
        for _ in 0..size {
            body = program_seq(program_assign("held", expression.clone()), body);
        }
        if declared {
            body = program_seq(
                program_declare("held", program_type),
                program_seq(
                    program_assign("held", crate::kernel::program_expression::variable("x")),
                    body,
                ),
            );
        }
        let helper = program_function(
            program_type,
            "machine_handoff",
            vec![program_parameter(
                if declared { "x" } else { "held" },
                program_type,
            )],
            body,
        );
        let environment = ExecutionEnvironment::new().with_function(helper);
        let (mut call, result) = program_call_value(
            0,
            "machine_handoff",
            vec![ProgramExpression::Value(
                format.value_from_term(MachineTerm::Variable(Variable(998341))),
            )],
        );
        if !rust && let ProgramStatement::CallResult { result_type, .. } = &mut call {
            // C states its declared return type; Rust retains the callee's.
            *result_type = Some(program_type);
        }
        let statement = program_seq(
            call,
            program_seq(
                program_assign("received", result),
                program_return(crate::kernel::program_expression::variable("received")),
            ),
        );
        (environment, statement)
    }

    #[test]
    fn complete_machine_handoffs_keep_roots_across_native_memory_cells() {
        for rust in [false, true] {
            for size in [16, 64, 256] {
                let _session = crate::kernel::VerificationSession::enter();
                let (environment, statement) = complete_machine_handoff_program(rust, size, true);
                let exports = KernelTermExport::machine_export_count();
                let paths = super::super::statements::execute_execution_statement_paths(
                    &machine_handoff_caller(rust),
                    &statement,
                    &PureFactContext::new(),
                    ExecutionContext::execute_bodies(&environment),
                    &mut ExecutionBudget::new(),
                )
                .unwrap();
                let [path] = paths.as_slice() else {
                    panic!("one complete declared-local path");
                };
                let StatementOutcome::Return { value, state } = &path.outcome else {
                    panic!("return: {:?}", path.outcome);
                };
                assert!(path.obligations.is_empty());
                assert!(value.shared().is_some());
                assert_eq!(
                    value.shared(),
                    state.locals.get("received").unwrap().shared()
                );
                // Declared slots still synchronize through the native memory-cell boundary.
                assert!(KernelTermExport::machine_export_count() > exports);
            }
        }
    }

    #[test]
    fn retained_execution_return_and_function_handoff_keep_the_root() {
        let _session = crate::kernel::VerificationSession::enter();
        let statement = ProgramStatement::Return(ProgramExpression::Multiply(
            Box::new(ProgramExpression::Value(ProgramValue::UInt32(
                MachineTerm::Variable(Variable(998330)),
            ))),
            Box::new(ProgramExpression::Value(ProgramValue::UInt32(
                MachineTerm::uint32_constant(3),
            ))),
        ));
        let exports = KernelTermExport::machine_export_count();
        let outcome = super::super::statements::execute_execution_statement(
            &ExecutionState::new(),
            &statement,
            &PureFactContext::new(),
        )
        .unwrap();
        let StatementOutcome::Return { value, .. } = outcome else {
            panic!("return result");
        };
        let root = value.shared().expect("retained return root").clone();
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        let function = program_function(
            ProgramType::UInt32,
            "retained_return",
            Vec::new(),
            statement,
        );
        let environment = ExecutionEnvironment::new();
        let paths = execute_program_function_paths(
            &ExecutionState::new(),
            &function,
            &[],
            &PureFactContext::new(),
            ExecutionContext::execute_bodies(&environment),
            &mut ExecutionBudget::new(),
        )
        .unwrap();
        let FunctionOutcome::Return { value, .. } = &paths[0].outcome else {
            panic!("function result");
        };
        assert_eq!(value.shared(), Some(&root));
        let mut caller = ExecutionState::new();
        let mut obligations = Vec::new();
        crate::kernel::loops::assign_call_result(
            &mut caller,
            "received",
            value.clone(),
            &mut obligations,
            &PureFactContext::new(),
        )
        .unwrap();
        assert_eq!(caller.locals.get("received").unwrap().shared(), Some(&root));
        assert!(obligations.is_empty());
    }

    #[test]
    fn retained_local_reads_restore_roots_and_preserve_const_refusal() {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::UInt32;
        let root = KernelTerm::machine_binary_shared(
            format,
            Op::Multiply,
            [
                KernelTerm::variable(KernelType::Program(ProgramType::UInt32), Variable(998322)),
                KernelTerm::retained_native_machine_operand(
                    format,
                    &MachineTerm::uint32_constant(3),
                ),
            ],
        );
        let mut state = ExecutionState::new();
        let exports = KernelTermExport::machine_export_count();
        state.locals.set_retained_typed_with_all_qualifiers(
            "source",
            ExecutionValue::from(root.clone()),
            ProgramType::UInt32,
            false,
            false,
            false,
            false,
        );
        let saved = state.locals.binding("source").unwrap().clone();
        state.locals.set(
            "source",
            ProgramValue::UInt32(MachineTerm::uint32_constant(7)),
        );
        state.locals.restore_binding("source", saved);
        let paths = evaluate_expression_value_paths(
            &state,
            &ProgramExpression::Variable("source".into()),
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
        )
        .unwrap();
        let ExpressionOutcome::Value(value) = &paths[0].outcome else {
            panic!("local read");
        };
        assert_eq!(value.shared(), Some(&root));
        assert_eq!(
            state
                .locals
                .names_holding_kernel_integer(&root)
                .collect::<Vec<_>>(),
            vec!["source"]
        );
        state.locals.set_typed_with_all_qualifiers(
            "target",
            ProgramValue::UInt32(MachineTerm::uint32_constant(0)),
            ProgramType::UInt32,
            false,
            false,
            true,
            false,
        );
        let assignment = ProgramStatement::Assign {
            name: "target".into(),
            expression: ProgramExpression::Variable("source".into()),
            source: Default::default(),
            prior_result: None,
        };
        let outcome = super::super::statements::execute_execution_statement(
            &state,
            &assignment,
            &PureFactContext::new(),
        )
        .unwrap();
        assert!(matches!(
            outcome,
            StatementOutcome::UndefinedBehavior(UndefinedBehavior::InvalidMemory)
        ));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn retained_local_call_and_conditional_names_use_the_existing_index() {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::UInt32;
        let value =
            KernelTerm::variable(KernelType::Program(ProgramType::UInt32), Variable(998323));
        let call = KernelTerm::checked_call(
            KernelType::Program(ProgramType::UInt32),
            "held_call".into(),
            vec![value.clone()],
        );
        let conditional = KernelTerm::machine_if_shared(
            format,
            [
                KernelTerm::variable(KernelType::Bool, Variable(998324)),
                call.clone(),
                value,
            ],
        );
        let mut state = ExecutionState::new();
        let exports = KernelTermExport::machine_export_count();
        for (name, root) in [("call", call), ("conditional", conditional)] {
            state.locals.set_retained_typed_with_all_qualifiers(
                name,
                ExecutionValue::from(root.clone()),
                ProgramType::UInt32,
                false,
                false,
                false,
                false,
            );
            assert_eq!(
                state
                    .locals
                    .names_holding_kernel_integer(&root)
                    .collect::<Vec<_>>(),
                vec![name]
            );
        }
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn retained_local_bool_cast_keeps_its_original_range_facts() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [
            MachineIntegerType::UInt8,
            MachineIntegerType::Int16,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
        ] {
            let term = MachineTerm::bool_cast(format, ConditionTerm::Variable(Variable(998325)));
            let expected =
                crate::kernel::program_bool_cast_range_facts(&format.value_from_term(term.clone()))
                    .unwrap();
            let root = KernelTermImport::default().machine(format, &term);
            let mut state = ExecutionState::new();
            state.locals.set_retained_typed_with_all_qualifiers(
                "flag",
                ExecutionValue::from(root),
                format.program_type(),
                false,
                false,
                false,
                false,
            );
            let exports = KernelTermExport::machine_export_count();
            let paths = evaluate_expression_value_paths(
                &state,
                &ProgramExpression::Variable("flag".into()),
                &PureFactContext::new(),
                &mut ExecutionBudget::new(),
            )
            .unwrap();
            let actual = paths[0]
                .facts
                .iter()
                .map(|fact| {
                    crate::kernel::proof::proposition_identity_key(fact.proposition()).unwrap()
                })
                .collect::<Vec<_>>();
            let expected = expected
                .iter()
                .map(|fact| crate::kernel::proof::proposition_identity_key(fact).unwrap())
                .collect::<Vec<_>>();
            assert_eq!(actual, expected);
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }

    mod scaling_tests {
        include!("../../scaling_tests/kernel/eval/retained_expression/tests.rs");
    }
    #[test]
    fn boolean_temporary_results_keep_the_producer_root() {
        let _session = crate::kernel::VerificationSession::enter();
        let root = KernelTermImport::default().boolean_call(&SharedPureApplication::intern(
            "boolean_step".into(),
            vec![],
        ));
        for value_type in [None, Some(ProgramType::Bool)] {
            let mut state = ExecutionState::new();
            state.locals.set_retained_typed_with_all_qualifiers(
                "b",
                ExecutionValue::Shared(root.clone()),
                ProgramType::Bool,
                false,
                false,
                false,
                false,
            );
            let statement = ProgramStatement::StepValue {
                steps: vec![11],
                expression: ProgramExpression::Variable("b".into()),
                value_type,
                pointee_constant: false,
            };
            let outcome = super::super::statements::execute_execution_statement(
                &state,
                &statement,
                &PureFactContext::new(),
            )
            .unwrap();
            let StatementOutcome::Normal(after) = outcome else {
                panic!("{outcome:?}")
            };
            let paths = evaluate_expression_value_paths(
                &after,
                &ProgramExpression::StepResult {
                    step: 11,
                    origin: crate::kernel::StepOrigin::Operator(
                        crate::kernel::OperatorKind::Ternary,
                    ),
                },
                &PureFactContext::new(),
                &mut ExecutionBudget::new(),
            )
            .unwrap();
            let ExpressionOutcome::Value(value) = &paths[0].outcome else {
                panic!()
            };
            assert_eq!(value.shared(), Some(&root));
            let address = Memory::local_pointer("boolean_step_cell");
            let memory = Memory::new()
                .with_block(address.block.clone(), 1)
                .store_retained(address.clone(), value.clone());
            let loaded = super::super::memory_loads::evaluate_retained_memory_load_paths(
                &memory,
                address,
                ProgramType::Bool,
                ExecutionFacts::new(),
                vec![],
                &PureFactContext::new(),
                false,
                false,
                None,
                None,
            );
            let ExpressionOutcome::Value(loaded) = &loaded[0].outcome else {
                panic!("memory receipt")
            };
            assert_eq!(loaded.shared(), Some(&root));
            let mut store_state = (*after).clone();
            let address = Memory::local_pointer("boolean_statement_cell");
            store_state.set_memory(Memory::new().with_block(address.block.clone(), 1));
            let statement = ProgramStatement::TypedStore {
                pointer: ProgramExpression::Value(ProgramValue::typed_pointer(
                    address.clone(),
                    ProgramType::VoidPointer,
                )),
                value: ProgramExpression::Variable("b".into()),
                value_type: ProgramType::Bool,
                access_class: None,
                volatile: false,
                pointee_constant: false,
                source: Default::default(),
            };
            let stored = super::super::statements::execute_execution_statement(
                &store_state,
                &statement,
                &PureFactContext::new(),
            )
            .unwrap();
            let StatementOutcome::Normal(stored) = stored else {
                panic!("Boolean store: {stored:?}")
            };
            assert_eq!(
                stored
                    .memory
                    .known_retained_value(&address)
                    .unwrap()
                    .shared(),
                Some(&root)
            );
        }
    }

    #[test]
    fn pointer_steps_keep_nested_read_call_and_arithmetic_roots_through_storage() {
        let _session = crate::kernel::VerificationSession::enter();
        let source_memory = Memory::new();
        let source_address = Pointer::symbolic(Variable(1027900));
        let read = ExecutionValue::retain_native(
            source_memory.symbolic_pointer_load(&source_address, ProgramType::Int32Pointer),
        );
        let read_root = read.shared().unwrap().clone();
        let call_root = KernelTerm::shared_pointer_call(
            KernelTerm::checked_call(
                KernelType::Program(ProgramType::Int32Pointer),
                "nested".into(),
                vec![read_root.clone()],
            ),
            SharedPointerValue::import(&PointerValue::new(
                Memory::local_pointer("pointer_step_pointee"),
                ProgramType::Int32Pointer,
            )),
        );
        let mut state = ExecutionState::new();
        state.set_memory(
            Memory::new().with_block(Memory::local_pointer("pointer_step_pointee").block, 16),
        );
        state.locals.set_retained_typed_with_all_qualifiers(
            "p",
            ExecutionValue::Shared(call_root.clone()),
            ProgramType::Int32Pointer,
            false,
            false,
            false,
            false,
        );
        let statement = ProgramStatement::StepValue {
            steps: vec![11],
            expression: ProgramExpression::Add(
                Box::new(ProgramExpression::Variable("p".into())),
                Box::new(ProgramExpression::Value(ProgramValue::Int32(
                    MachineTerm::constant(1),
                ))),
            ),
            value_type: Some(ProgramType::Int32Pointer),
            pointee_constant: false,
        };
        let result = super::super::statements::execute_execution_statement(
            &state,
            &statement,
            &PureFactContext::new(),
        )
        .unwrap();
        let StatementOutcome::Normal(after) = result else {
            panic!("pointer step: {result:?}")
        };
        let expression = ProgramExpression::StepResult {
            step: 11,
            origin: crate::kernel::StepOrigin::Operator(crate::kernel::OperatorKind::Ternary),
        };
        let paths = evaluate_expression_value_paths(
            &after,
            &expression,
            &PureFactContext::new(),
            &mut ExecutionBudget::new(),
        )
        .unwrap();
        let ExpressionOutcome::Value(value) = &paths[0].outcome else {
            panic!("step receipt")
        };
        let root = value.shared().unwrap();
        let KernelTermNode::PointerArithmetic { operands, .. } = root.node() else {
            panic!("arithmetic root")
        };
        assert_eq!(operands[0], call_root);
        let KernelTermNode::PointerCall { call, .. } = operands[0].node() else {
            panic!("call root")
        };
        let KernelTermNode::Call { arguments, .. } = call.node() else {
            panic!("call arguments")
        };
        assert_eq!(arguments[0], read_root);
        let KernelTermNode::PointerRead { memory, .. } = arguments[0].node() else {
            panic!("state read")
        };
        assert_eq!(memory, &crate::kernel::intern_memory_ref(&source_memory));
        let address = Memory::local_pointer("pointer_step_cell");
        let stored = after
            .memory
            .clone()
            .with_block(address.block.clone(), 8)
            .store_retained(address.clone(), value.clone());
        let loaded = super::super::memory_loads::evaluate_retained_memory_load_paths(
            &stored,
            address,
            ProgramType::Int32Pointer,
            ExecutionFacts::new(),
            vec![],
            &PureFactContext::new(),
            false,
            false,
            None,
            None,
        );
        let ExpressionOutcome::Value(loaded) = &loaded[0].outcome else {
            panic!("memory receipt")
        };
        assert_eq!(loaded.shared(), Some(root));
        assert_eq!(
            after
                .step_result(11)
                .map(|value| value.native().into_owned()),
            Some(value.native().into_owned())
        );
    }
}
