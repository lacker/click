use super::*;

type ValidShiftCountEvaluator = fn(
    Bitvector32Term,
    Bitvector32Term,
    Vec<ExecutionPureFact>,
    Vec<ProofObligation>,
    &PureFactContext,
) -> Vec<CExpressionPath>;

fn c_type_mismatch_expression_path(
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
) -> CExpressionPath {
    CExpressionPath {
        outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
        facts,
        obligations,
    }
}

pub(in crate::kernel) fn evaluate_c_add_paths(
    state: &CState,
    left: &CExpression,
    right: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    let left_step_width = c_expression_pointer_step_width(state, left);
    let right_step_width = c_expression_pointer_step_width(state, right);
    for left_path in evaluate_c_expression_paths(state, left, assumptions, budget)? {
        let CExpressionPath {
            outcome: left_outcome,
            facts: left_facts,
            obligations: left_obligations,
        } = left_path;

        let left = match left_outcome {
            CExpressionOutcome::Value(value) => value,
            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                    facts: left_facts,
                    obligations: left_obligations,
                });
                continue;
            }
            CExpressionOutcome::RuntimeError(error) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::RuntimeError(error),
                    facts: left_facts,
                    obligations: left_obligations,
                });
                continue;
            }
        };

        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_facts, &left_obligations);
        for right_path in evaluate_c_expression_paths(state, right, &right_assumptions, budget)? {
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &left_facts,
                &left_obligations,
                &right_path.facts,
                &right_path.obligations,
                assumptions,
            ) else {
                continue;
            };

            let right = match right_path.outcome {
                CExpressionOutcome::Value(value) => value,
                CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                    paths.push(CExpressionPath {
                        outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                        facts,
                        obligations,
                    });
                    continue;
                }
                CExpressionOutcome::RuntimeError(error) => {
                    paths.push(CExpressionPath {
                        outcome: CExpressionOutcome::RuntimeError(error),
                        facts,
                        obligations,
                    });
                    continue;
                }
            };

            paths.extend(apply_c_add(
                state,
                left.clone(),
                right,
                left_step_width,
                right_step_width,
                facts,
                obligations,
                assumptions,
            ));
        }
    }

    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(in crate::kernel) fn apply_c_add(
    state: &CState,
    left: CValue,
    right: CValue,
    left_step_width: Option<u32>,
    right_step_width: Option<u32>,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    match (left, right) {
        (
            left @ (CValue::Int32(_) | CValue::UInt8(_)),
            right @ (CValue::Int32(_) | CValue::UInt8(_)),
        ) => {
            let mut facts = facts;
            let Some(left) = promote_c_int32_path_value(left, &mut facts, assumptions) else {
                return Vec::new();
            };
            let Some(right) = promote_c_int32_path_value(right, &mut facts, assumptions) else {
                return Vec::new();
            };
            apply_c_int32_add(left, right, facts, obligations, assumptions)
        }
        (CValue::Pointer(pointer), offset @ (CValue::Int32(_) | CValue::UInt8(_))) => {
            let mut facts = facts;
            let Some(offset) = promote_c_int32_path_value(offset, &mut facts, assumptions) else {
                return Vec::new();
            };
            let Some(byte_width) = left_step_width else {
                return vec![CExpressionPath {
                    outcome: CExpressionOutcome::RuntimeError(
                        CRuntimeError::IndeterminatePointeeType,
                    ),
                    facts,
                    obligations,
                }];
            };
            let offset = canonicalized_offset_index_term(offset, &mut facts);
            pointer_offset_by_elements_paths(
                state,
                pointer,
                offset,
                byte_width,
                facts,
                obligations,
                assumptions,
            )
        }
        (offset @ (CValue::Int32(_) | CValue::UInt8(_)), CValue::Pointer(pointer)) => {
            let mut facts = facts;
            let Some(offset) = promote_c_int32_path_value(offset, &mut facts, assumptions) else {
                return Vec::new();
            };
            let Some(byte_width) = right_step_width else {
                return vec![CExpressionPath {
                    outcome: CExpressionOutcome::RuntimeError(
                        CRuntimeError::IndeterminatePointeeType,
                    ),
                    facts,
                    obligations,
                }];
            };
            let offset = canonicalized_offset_index_term(offset, &mut facts);
            pointer_offset_by_elements_paths(
                state,
                pointer,
                offset,
                byte_width,
                facts,
                obligations,
                assumptions,
            )
        }
        _ => vec![c_type_mismatch_expression_path(facts, obligations)],
    }
}

#[derive(Clone)]
struct PointerFormationGuard {
    condition: ConditionTerm,
    value: bool,
}

fn pointer_offset_by_elements_paths(
    state: &CState,
    pointer: Pointer,
    offset: Bitvector32Term,
    byte_width: u32,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let result = pointer.offset_by_elements(offset.clone(), byte_width);
    let mut guards = Vec::new();

    // Pointer offsets are exact i64 terms, but the source index is a signed
    // int32. Once a pointer has a known element index, the next addition must
    // stay in that signed domain. This catches the cumulative case
    // `data + INT_MAX + 1`, even though each individual source operand is a
    // valid int32.
    if let Some(index) = pointer_index_from_offset(&pointer, byte_width)
        && index != Bitvector32Term::Constant(0)
        && offset != Bitvector32Term::Constant(0)
    {
        guards.push(PointerFormationGuard {
            condition: ConditionTerm::signed_add_overflows(index, offset),
            value: false,
        });
    }

    // A resource-backed read may legitimately refer to storage that has not
    // been materialized in the byte map yet. Let that explicit memory range
    // extend the concrete materialization bound; it is still only consulted
    // when the result (including a range endpoint) is provably in the range.
    let resource_backed =
        pointer_is_in_memory_resource(state.resources(), assumptions, &facts, &result, byte_width);
    if !resource_backed {
        guards.extend(pointer_block_bounds(state, &result, byte_width));
    }

    apply_pointer_formation_guards(result, guards, facts, obligations, assumptions)
}

pub(in crate::kernel) fn pointer_offset_by_bytes_paths(
    state: &CState,
    pointer: Pointer,
    bytes: u32,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let result = pointer.offset_by_bytes(bytes);
    let guards = pointer_block_bounds(state, &result, 1);
    apply_pointer_formation_guards(result, guards, facts, obligations, assumptions)
}

fn pointer_index_from_offset(pointer: &Pointer, byte_width: u32) -> Option<Bitvector32Term> {
    if pointer.block != PointerBlock::ExternalArgument {
        return pointer_index_from_offset_term(&pointer.offset, byte_width);
    }

    // External argument pointers carry a symbolic shared-memory offset, not
    // an element index from the beginning of an object. Only the additions
    // structurally introduced after that opaque base participate in the
    // cumulative-index check. Concrete zero-based test pointers retain the
    // direct fallback so their first large addition is checked on the next
    // operation as well.
    pointer
        .offset
        .as_const()
        .and_then(|offset| pointer_index_from_concrete_offset(offset, byte_width))
        .or_else(|| pointer_arithmetic_index(&pointer.offset, byte_width))
}

fn pointer_index_from_offset_term(
    offset: &PointerOffsetTerm,
    byte_width: u32,
) -> Option<Bitvector32Term> {
    match byte_width {
        4 => int32_element_index_from_offset(offset),
        1 => byte_offset_from_pointer_offset(offset),
        _ => None,
    }
}

fn pointer_index_from_concrete_offset(offset: i64, byte_width: u32) -> Option<Bitvector32Term> {
    match byte_width {
        4 if offset % 4 == 0 => {
            let index = offset / 4;
            (i32::MIN as i64..=i32::MAX as i64)
                .contains(&index)
                .then_some(Bitvector32Term::Constant((index as i32) as u32))
        }
        1 if (i32::MIN as i64..=i32::MAX as i64).contains(&offset) => {
            Some(Bitvector32Term::Constant((offset as i32) as u32))
        }
        _ => None,
    }
}

fn pointer_arithmetic_index(
    offset: &PointerOffsetTerm,
    byte_width: u32,
) -> Option<Bitvector32Term> {
    let PointerOffsetTerm::Add(left, right) = offset else {
        return None;
    };
    let right = pointer_index_from_offset_term(right, byte_width)?;
    let left = match left.as_ref() {
        PointerOffsetTerm::Add(..) => pointer_arithmetic_index(left, byte_width)?,
        // The first addend is the pointer's opaque base. It is not an
        // element displacement, even if its byte representation happens to
        // be aligned.
        _ => Bitvector32Term::Constant(0),
    };
    Some(Bitvector32Term::add(left, right))
}

fn pointer_block_bounds(
    state: &CState,
    pointer: &Pointer,
    byte_width: u32,
) -> Vec<PointerFormationGuard> {
    let Some(block_size) = state.memory().block_size(&pointer.block).cloned() else {
        return Vec::new();
    };

    // Concrete offsets can exceed the signed bitvector representation. Check
    // those directly against the byte-sized block instead of silently
    // rebuilding them through a wrapping int32 term.
    if let (Some(offset), Some(size)) = (pointer.offset.as_const(), block_size.as_const()) {
        if offset < 0 || offset > i64::from(size) {
            return vec![PointerFormationGuard {
                condition: ConditionTerm::signed_less_equal(
                    Bitvector32Term::Constant(1),
                    Bitvector32Term::Constant(0),
                ),
                value: true,
            }];
        }
        return Vec::new();
    }

    let (offset, size) = match byte_width {
        4 => {
            let Some(offset) = int32_element_index_from_offset(&pointer.offset) else {
                return Vec::new();
            };
            let Some(size) = int32_element_count_from_bytes(&block_size) else {
                return Vec::new();
            };
            (offset, size)
        }
        1 => {
            let Some(offset) = byte_offset_from_pointer_offset(&pointer.offset) else {
                return Vec::new();
            };
            (offset, block_size)
        }
        _ => return Vec::new(),
    };

    vec![
        PointerFormationGuard {
            condition: ConditionTerm::signed_greater_equal(
                offset.clone(),
                Bitvector32Term::Constant(0),
            ),
            value: true,
        },
        PointerFormationGuard {
            condition: ConditionTerm::signed_less_equal(offset, size),
            value: true,
        },
    ]
}

fn pointer_is_in_memory_resource(
    resources: &ResourceContext,
    assumptions: &PureFactContext,
    facts: &[ExecutionPureFact],
    pointer: &Pointer,
    byte_width: u32,
) -> bool {
    let decide =
        |condition: ConditionTerm| decide_with_facts(assumptions, facts, &condition) == Some(true);
    // This is intentionally a small, structural query. It recognizes the
    // range shape produced by pointer arithmetic without asking the resource
    // algebra to search unrelated resources.
    let contains_range = |resources: &ResourceContext| {
        resources.facts().iter().any(|fact| {
            let Some(range) = fact.memory_range() else {
                return false;
            };
            if range.element_width() != byte_width {
                return false;
            }
            let Some(index) = pointer_index_from_base(pointer, range.base(), byte_width) else {
                return false;
            };
            decide(ConditionTerm::signed_less_equal(
                range.start().clone(),
                index.clone(),
            )) && decide(ConditionTerm::signed_less_equal(index, range.end().clone()))
        })
    };
    contains_range(resources) || assumptions.resource_compositions.iter().any(contains_range)
}

fn pointer_index_from_base(
    pointer: &Pointer,
    base: &Pointer,
    byte_width: u32,
) -> Option<Bitvector32Term> {
    match byte_width {
        4 => pointer.element_index_from_base(base),
        1 => pointer_byte_offset_from_base(pointer, base),
        _ => None,
    }
}

fn apply_pointer_formation_guards(
    pointer: Pointer,
    guards: Vec<PointerFormationGuard>,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let mut normal = vec![CExpressionPath {
        outcome: CExpressionOutcome::Value(CValue::Pointer(pointer)),
        facts,
        obligations,
    }];
    let mut paths = Vec::new();

    for guard in guards {
        let mut next = Vec::new();
        for path in normal {
            match decide_with_facts(assumptions, &path.facts, &guard.condition) {
                Some(known) if known == guard.value => next.push(path),
                Some(_) => paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(
                        CUndefinedBehavior::PointerArithmetic,
                    ),
                    facts: path.facts,
                    obligations: path.obligations,
                }),
                None => {
                    let mut valid_facts = path.facts.clone();
                    add_condition_path_fact(
                        &mut valid_facts,
                        assumptions,
                        guard.condition.clone(),
                        guard.value,
                    )
                    .expect("pointer formation guard should be consistent");
                    next.push(CExpressionPath {
                        outcome: path.outcome.clone(),
                        facts: valid_facts,
                        obligations: path.obligations.clone(),
                    });

                    let invalid_value = !guard.value;
                    let mut invalid_facts = path.facts;
                    add_condition_path_fact(
                        &mut invalid_facts,
                        assumptions,
                        guard.condition.clone(),
                        invalid_value,
                    )
                    .expect("pointer formation guard should be consistent");
                    paths.push(CExpressionPath {
                        outcome: CExpressionOutcome::UndefinedBehavior(
                            CUndefinedBehavior::PointerArithmetic,
                        ),
                        facts: invalid_facts,
                        obligations: path.obligations,
                    });
                }
            }
        }
        normal = next;
    }

    paths.extend(normal);
    paths
}

pub(in crate::kernel) fn apply_c_int32_add(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let overflow = ConditionTerm::signed_add_overflows(left.clone(), right.clone());
    match crate::instrumentation::measure_operation(
        "kernel",
        "independent kernel execution",
        "int32 add overflow decision",
        || decide_with_facts(assumptions, &facts, &overflow),
    ) {
        Some(true) => vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow),
            facts,
            obligations,
        }],
        Some(false) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(int32(Bitvector32Term::add(left, right))),
            facts,
            obligations,
        }],
        None => {
            let mut normal_facts = facts.clone();
            add_condition_path_fact(&mut normal_facts, assumptions, overflow.clone(), false)
                .expect("unknown overflow fact should be consistent");

            let mut overflow_facts = facts;
            add_condition_path_fact(&mut overflow_facts, assumptions, overflow, true)
                .expect("unknown overflow fact should be consistent");

            vec![
                CExpressionPath {
                    outcome: CExpressionOutcome::Value(int32(Bitvector32Term::add(left, right))),
                    facts: normal_facts,
                    obligations: obligations.clone(),
                },
                CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(
                        CUndefinedBehavior::SignedOverflow,
                    ),
                    facts: overflow_facts,
                    obligations,
                },
            ]
        }
    }
}

pub(in crate::kernel) fn apply_c_int32_subtract(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let overflow = ConditionTerm::signed_subtract_overflows(left.clone(), right.clone());
    match decide_with_facts(assumptions, &facts, &overflow) {
        Some(true) => vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow),
            facts,
            obligations,
        }],
        Some(false) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(int32(Bitvector32Term::subtract(left, right))),
            facts,
            obligations,
        }],
        None => {
            let mut normal_facts = facts.clone();
            add_condition_path_fact(&mut normal_facts, assumptions, overflow.clone(), false)
                .expect("unknown overflow fact should be consistent");

            let mut overflow_facts = facts;
            add_condition_path_fact(&mut overflow_facts, assumptions, overflow, true)
                .expect("unknown overflow fact should be consistent");

            vec![
                CExpressionPath {
                    outcome: CExpressionOutcome::Value(int32(Bitvector32Term::subtract(
                        left, right,
                    ))),
                    facts: normal_facts,
                    obligations: obligations.clone(),
                },
                CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(
                        CUndefinedBehavior::SignedOverflow,
                    ),
                    facts: overflow_facts,
                    obligations,
                },
            ]
        }
    }
}

pub(in crate::kernel) fn apply_c_int32_multiply(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let overflow = ConditionTerm::signed_multiply_overflows(
        normalize_exact_memory_loads_in_bitvector(&left, assumptions, 0),
        normalize_exact_memory_loads_in_bitvector(&right, assumptions, 0),
    );
    match decide_with_facts(assumptions, &facts, &overflow) {
        Some(true) => vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow),
            facts,
            obligations,
        }],
        Some(false) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(int32(Bitvector32Term::multiply(left, right))),
            facts,
            obligations,
        }],
        None => {
            let mut normal_facts = facts.clone();
            add_condition_path_fact(&mut normal_facts, assumptions, overflow.clone(), false)
                .expect("unknown overflow fact should be consistent");

            let mut overflow_facts = facts;
            add_condition_path_fact(&mut overflow_facts, assumptions, overflow, true)
                .expect("unknown overflow fact should be consistent");

            vec![
                CExpressionPath {
                    outcome: CExpressionOutcome::Value(int32(Bitvector32Term::multiply(
                        left, right,
                    ))),
                    facts: normal_facts,
                    obligations: obligations.clone(),
                },
                CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(
                        CUndefinedBehavior::SignedOverflow,
                    ),
                    facts: overflow_facts,
                    obligations,
                },
            ]
        }
    }
}

pub(in crate::kernel) fn apply_c_int32_divide(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    apply_c_int32_division_like(
        left,
        right,
        facts,
        obligations,
        assumptions,
        Bitvector32Term::divide,
    )
}

pub(in crate::kernel) fn apply_c_int32_remainder(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    apply_c_int32_division_like(
        left,
        right,
        facts,
        obligations,
        assumptions,
        Bitvector32Term::remainder,
    )
}

fn apply_c_int32_division_like(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    result: fn(Bitvector32Term, Bitvector32Term) -> Bitvector32Term,
) -> Vec<CExpressionPath> {
    let zero = Bitvector32Term::Constant(0);
    let divides_by_zero = ConditionTerm::equal(right.clone(), zero);
    match decide_with_facts(assumptions, &facts, &divides_by_zero) {
        Some(true) => {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::DivisionByZero),
                facts,
                obligations,
            }];
        }
        Some(false) => {
            return apply_c_int32_division_nonzero(
                left,
                right,
                facts,
                obligations,
                assumptions,
                result,
            );
        }
        None => {}
    }

    let mut normal_facts = facts.clone();
    add_condition_path_fact(
        &mut normal_facts,
        assumptions,
        divides_by_zero.clone(),
        false,
    )
    .expect("unknown zero-divisor fact should be consistent");

    let mut zero_facts = facts;
    add_condition_path_fact(&mut zero_facts, assumptions, divides_by_zero, true)
        .expect("unknown zero-divisor fact should be consistent");

    let mut paths = apply_c_int32_division_nonzero(
        left,
        right,
        normal_facts,
        obligations.clone(),
        assumptions,
        result,
    );
    paths.push(CExpressionPath {
        outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::DivisionByZero),
        facts: zero_facts,
        obligations,
    });
    paths
}

fn apply_c_int32_division_nonzero(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    result: fn(Bitvector32Term, Bitvector32Term) -> Bitvector32Term,
) -> Vec<CExpressionPath> {
    let overflow = ConditionTerm::signed_divide_overflows(left.clone(), right.clone());
    match decide_with_facts(assumptions, &facts, &overflow) {
        Some(true) => vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow),
            facts,
            obligations,
        }],
        Some(false) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(int32(result(left, right))),
            facts,
            obligations,
        }],
        None => {
            let mut normal_facts = facts.clone();
            add_condition_path_fact(&mut normal_facts, assumptions, overflow.clone(), false)
                .expect("unknown divide-overflow fact should be consistent");

            let mut overflow_facts = facts;
            add_condition_path_fact(&mut overflow_facts, assumptions, overflow, true)
                .expect("unknown divide-overflow fact should be consistent");

            vec![
                CExpressionPath {
                    outcome: CExpressionOutcome::Value(int32(result(left, right))),
                    facts: normal_facts,
                    obligations: obligations.clone(),
                },
                CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(
                        CUndefinedBehavior::SignedOverflow,
                    ),
                    facts: overflow_facts,
                    obligations,
                },
            ]
        }
    }
}

pub(in crate::kernel) fn apply_c_int32_shift_left(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    apply_c_int32_with_valid_shift_count(
        left,
        right,
        facts,
        obligations,
        assumptions,
        apply_c_int32_shift_left_valid_count,
    )
}

pub(in crate::kernel) fn apply_c_int32_shift_right(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    apply_c_int32_with_valid_shift_count(
        left,
        right,
        facts,
        obligations,
        assumptions,
        |left, right, facts, obligations, _| {
            vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(int32(Bitvector32Term::arithmetic_shift_right(
                    left, right,
                ))),
                facts,
                obligations,
            }]
        },
    )
}

fn apply_c_int32_with_valid_shift_count(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    apply_valid_count: ValidShiftCountEvaluator,
) -> Vec<CExpressionPath> {
    let negative_count =
        ConditionTerm::signed_less_than(right.clone(), Bitvector32Term::Constant(0));
    match decide_with_facts(assumptions, &facts, &negative_count) {
        Some(true) => {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidShift),
                facts,
                obligations,
            }];
        }
        Some(false) => {
            return apply_c_int32_with_nonnegative_shift_count(
                left,
                right,
                facts,
                obligations,
                assumptions,
                apply_valid_count,
            );
        }
        None => {}
    }

    let mut normal_facts = facts.clone();
    add_condition_path_fact(
        &mut normal_facts,
        assumptions,
        negative_count.clone(),
        false,
    )
    .expect("unknown negative shift-count fact should be consistent");

    let mut invalid_facts = facts;
    add_condition_path_fact(&mut invalid_facts, assumptions, negative_count, true)
        .expect("unknown negative shift-count fact should be consistent");

    let mut paths = apply_c_int32_with_nonnegative_shift_count(
        left,
        right,
        normal_facts,
        obligations.clone(),
        assumptions,
        apply_valid_count,
    );
    paths.push(CExpressionPath {
        outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidShift),
        facts: invalid_facts,
        obligations,
    });
    paths
}

fn apply_c_int32_with_nonnegative_shift_count(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    apply_valid_count: ValidShiftCountEvaluator,
) -> Vec<CExpressionPath> {
    let too_large_count =
        ConditionTerm::signed_greater_equal(right.clone(), Bitvector32Term::Constant(32));
    match decide_with_facts(assumptions, &facts, &too_large_count) {
        Some(true) => vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidShift),
            facts,
            obligations,
        }],
        Some(false) => apply_valid_count(left, right, facts, obligations, assumptions),
        None => {
            let mut normal_facts = facts.clone();
            add_condition_path_fact(
                &mut normal_facts,
                assumptions,
                too_large_count.clone(),
                false,
            )
            .expect("unknown large shift-count fact should be consistent");

            let mut invalid_facts = facts;
            add_condition_path_fact(&mut invalid_facts, assumptions, too_large_count, true)
                .expect("unknown large shift-count fact should be consistent");

            let mut paths =
                apply_valid_count(left, right, normal_facts, obligations.clone(), assumptions);
            paths.push(CExpressionPath {
                outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidShift),
                facts: invalid_facts,
                obligations,
            });
            paths
        }
    }
}

fn apply_c_int32_shift_left_valid_count(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let negative_left = ConditionTerm::signed_less_than(left.clone(), Bitvector32Term::Constant(0));
    match decide_with_facts(assumptions, &facts, &negative_left) {
        Some(true) => {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidShift),
                facts,
                obligations,
            }];
        }
        Some(false) => {
            return apply_c_int32_shift_left_nonnegative(
                left,
                right,
                facts,
                obligations,
                assumptions,
            );
        }
        None => {}
    }

    let mut normal_facts = facts.clone();
    add_condition_path_fact(&mut normal_facts, assumptions, negative_left.clone(), false)
        .expect("unknown negative left-shift operand fact should be consistent");

    let mut invalid_facts = facts;
    add_condition_path_fact(&mut invalid_facts, assumptions, negative_left, true)
        .expect("unknown negative left-shift operand fact should be consistent");

    let mut paths = apply_c_int32_shift_left_nonnegative(
        left,
        right,
        normal_facts,
        obligations.clone(),
        assumptions,
    );
    paths.push(CExpressionPath {
        outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidShift),
        facts: invalid_facts,
        obligations,
    });
    paths
}

fn apply_c_int32_shift_left_nonnegative(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let overflow = ConditionTerm::signed_shift_left_overflows(left.clone(), right.clone());
    match decide_with_facts(assumptions, &facts, &overflow) {
        Some(true) => vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow),
            facts,
            obligations,
        }],
        Some(false) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(int32(Bitvector32Term::shift_left(left, right))),
            facts,
            obligations,
        }],
        None => {
            let mut normal_facts = facts.clone();
            add_condition_path_fact(&mut normal_facts, assumptions, overflow.clone(), false)
                .expect("unknown left-shift overflow fact should be consistent");

            let mut overflow_facts = facts;
            add_condition_path_fact(&mut overflow_facts, assumptions, overflow, true)
                .expect("unknown left-shift overflow fact should be consistent");

            vec![
                CExpressionPath {
                    outcome: CExpressionOutcome::Value(int32(Bitvector32Term::shift_left(
                        left, right,
                    ))),
                    facts: normal_facts,
                    obligations: obligations.clone(),
                },
                CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(
                        CUndefinedBehavior::SignedOverflow,
                    ),
                    facts: overflow_facts,
                    obligations,
                },
            ]
        }
    }
}

pub(in crate::kernel) fn evaluate_c_equal_paths(
    state: &CState,
    left: &CExpression,
    right: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for left_path in evaluate_c_expression_paths(state, left, assumptions, budget)? {
        let CExpressionPath {
            outcome: left_outcome,
            facts: left_facts,
            obligations: left_obligations,
        } = left_path;

        let left = match left_outcome {
            CExpressionOutcome::Value(left) => left,
            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                    facts: left_facts,
                    obligations: left_obligations,
                });
                continue;
            }
            CExpressionOutcome::RuntimeError(error) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::RuntimeError(error),
                    facts: left_facts,
                    obligations: left_obligations,
                });
                continue;
            }
        };

        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_facts, &left_obligations);
        for right_path in evaluate_c_expression_paths(state, right, &right_assumptions, budget)? {
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &left_facts,
                &left_obligations,
                &right_path.facts,
                &right_path.obligations,
                assumptions,
            ) else {
                continue;
            };

            match right_path.outcome {
                CExpressionOutcome::Value(right) => {
                    paths.extend(apply_c_equal(
                        left.clone(),
                        right,
                        facts,
                        obligations,
                        assumptions,
                    ));
                }
                CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                    paths.push(CExpressionPath {
                        outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                        facts,
                        obligations,
                    })
                }
                CExpressionOutcome::RuntimeError(error) => paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::RuntimeError(error),
                    facts,
                    obligations,
                }),
            }
        }
    }

    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(in crate::kernel) fn apply_c_equal(
    left: CValue,
    right: CValue,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    match (left, right) {
        (CValue::Pointer(left), CValue::Pointer(right)) => condition_as_c_int32_paths(
            pointer_equality_condition(left, right),
            facts,
            obligations,
            assumptions,
        ),
        (CValue::Pointer(pointer), CValue::Int32(bits))
        | (CValue::Int32(bits), CValue::Pointer(pointer))
            if bits.as_const() == Some(0) =>
        {
            condition_as_c_int32_paths(
                pointer_is_null_condition(pointer),
                facts,
                obligations,
                assumptions,
            )
        }
        (
            left @ (CValue::Int32(_) | CValue::UInt8(_)),
            right @ (CValue::Int32(_) | CValue::UInt8(_)),
        ) => {
            let mut facts = facts;
            let Some(left) = promote_c_int32_path_value(left, &mut facts, assumptions) else {
                return Vec::new();
            };
            let Some(right) = promote_c_int32_path_value(right, &mut facts, assumptions) else {
                return Vec::new();
            };
            condition_as_c_int32_paths(
                ConditionTerm::equal(left, right),
                facts,
                obligations,
                assumptions,
            )
        }
        _ => vec![c_type_mismatch_expression_path(facts, obligations)],
    }
}

pub(in crate::kernel) fn evaluate_c_not_equal_paths(
    state: &CState,
    left: &CExpression,
    right: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for left_path in evaluate_c_expression_paths(state, left, assumptions, budget)? {
        let CExpressionPath {
            outcome: left_outcome,
            facts: left_facts,
            obligations: left_obligations,
        } = left_path;

        let left = match left_outcome {
            CExpressionOutcome::Value(left) => left,
            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                    facts: left_facts,
                    obligations: left_obligations,
                });
                continue;
            }
            CExpressionOutcome::RuntimeError(error) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::RuntimeError(error),
                    facts: left_facts,
                    obligations: left_obligations,
                });
                continue;
            }
        };

        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_facts, &left_obligations);
        for right_path in evaluate_c_expression_paths(state, right, &right_assumptions, budget)? {
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &left_facts,
                &left_obligations,
                &right_path.facts,
                &right_path.obligations,
                assumptions,
            ) else {
                continue;
            };

            match right_path.outcome {
                CExpressionOutcome::Value(right) => {
                    paths.extend(apply_c_not_equal(
                        left.clone(),
                        right,
                        facts,
                        obligations,
                        assumptions,
                    ));
                }
                CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                    paths.push(CExpressionPath {
                        outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                        facts,
                        obligations,
                    })
                }
                CExpressionOutcome::RuntimeError(error) => paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::RuntimeError(error),
                    facts,
                    obligations,
                }),
            }
        }
    }

    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(in crate::kernel) fn apply_c_not_equal(
    left: CValue,
    right: CValue,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    match (left, right) {
        (CValue::Pointer(left), CValue::Pointer(right)) => condition_as_c_int32_not_paths(
            pointer_equality_condition(left, right),
            facts,
            obligations,
            assumptions,
        ),
        (CValue::Pointer(pointer), CValue::Int32(bits))
        | (CValue::Int32(bits), CValue::Pointer(pointer))
            if bits.as_const() == Some(0) =>
        {
            condition_as_c_int32_not_paths(
                pointer_is_null_condition(pointer),
                facts,
                obligations,
                assumptions,
            )
        }
        (
            left @ (CValue::Int32(_) | CValue::UInt8(_)),
            right @ (CValue::Int32(_) | CValue::UInt8(_)),
        ) => {
            let mut facts = facts;
            let Some(left) = promote_c_int32_path_value(left, &mut facts, assumptions) else {
                return Vec::new();
            };
            let Some(right) = promote_c_int32_path_value(right, &mut facts, assumptions) else {
                return Vec::new();
            };
            condition_as_c_int32_not_paths(
                ConditionTerm::equal(left, right),
                facts,
                obligations,
                assumptions,
            )
        }
        _ => vec![c_type_mismatch_expression_path(facts, obligations)],
    }
}

pub(in crate::kernel) fn evaluate_c_not_paths(
    state: &CState,
    expression: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for path in evaluate_c_expression_paths(state, expression, assumptions, budget)? {
        match path.outcome {
            CExpressionOutcome::Value(value) => {
                paths.extend(
                    c_truthiness_paths(value, path.facts, path.obligations, assumptions)
                        .into_iter()
                        .map(|truthiness| CExpressionPath {
                            outcome: CExpressionOutcome::Value(int32(if truthiness.is_true {
                                0
                            } else {
                                1
                            })),
                            facts: truthiness.facts,
                            obligations: truthiness.obligations,
                        }),
                );
            }
            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                    facts: path.facts,
                    obligations: path.obligations,
                })
            }
            CExpressionOutcome::RuntimeError(error) => paths.push(CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(error),
                facts: path.facts,
                obligations: path.obligations,
            }),
        }
    }

    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(in crate::kernel) fn evaluate_c_logical_and_paths(
    state: &CState,
    left: &CExpression,
    right: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for left_path in evaluate_c_expression_paths(state, left, assumptions, budget)? {
        match left_path.outcome {
            CExpressionOutcome::Value(left_value) => {
                for left_truthiness in c_truthiness_paths(
                    left_value,
                    left_path.facts,
                    left_path.obligations,
                    assumptions,
                ) {
                    if !left_truthiness.is_true {
                        paths.push(CExpressionPath {
                            outcome: CExpressionOutcome::Value(int32(0)),
                            facts: left_truthiness.facts,
                            obligations: left_truthiness.obligations,
                        });
                        continue;
                    }

                    let right_assumptions = assumptions_with_path_context(
                        assumptions,
                        &left_truthiness.facts,
                        &left_truthiness.obligations,
                    );
                    for right_path in
                        evaluate_c_expression_paths(state, right, &right_assumptions, budget)?
                    {
                        let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                            &left_truthiness.facts,
                            &left_truthiness.obligations,
                            &right_path.facts,
                            &right_path.obligations,
                            assumptions,
                        ) else {
                            continue;
                        };

                        match right_path.outcome {
                            CExpressionOutcome::Value(value) => {
                                paths.extend(c_truthiness_as_c_int32_paths(
                                    value,
                                    facts,
                                    obligations,
                                    assumptions,
                                ))
                            }
                            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => paths
                                .push(CExpressionPath {
                                    outcome: CExpressionOutcome::UndefinedBehavior(
                                        undefined_behavior,
                                    ),
                                    facts,
                                    obligations,
                                }),
                            CExpressionOutcome::RuntimeError(error) => {
                                paths.push(CExpressionPath {
                                    outcome: CExpressionOutcome::RuntimeError(error),
                                    facts,
                                    obligations,
                                })
                            }
                        }
                    }
                }
            }
            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                    facts: left_path.facts,
                    obligations: left_path.obligations,
                })
            }
            CExpressionOutcome::RuntimeError(error) => paths.push(CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(error),
                facts: left_path.facts,
                obligations: left_path.obligations,
            }),
        }
    }

    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(in crate::kernel) fn evaluate_c_logical_or_paths(
    state: &CState,
    left: &CExpression,
    right: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for left_path in evaluate_c_expression_paths(state, left, assumptions, budget)? {
        match left_path.outcome {
            CExpressionOutcome::Value(left_value) => {
                for left_truthiness in c_truthiness_paths(
                    left_value,
                    left_path.facts,
                    left_path.obligations,
                    assumptions,
                ) {
                    if left_truthiness.is_true {
                        paths.push(CExpressionPath {
                            outcome: CExpressionOutcome::Value(int32(1)),
                            facts: left_truthiness.facts,
                            obligations: left_truthiness.obligations,
                        });
                        continue;
                    }

                    let right_assumptions = assumptions_with_path_context(
                        assumptions,
                        &left_truthiness.facts,
                        &left_truthiness.obligations,
                    );
                    for right_path in
                        evaluate_c_expression_paths(state, right, &right_assumptions, budget)?
                    {
                        let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                            &left_truthiness.facts,
                            &left_truthiness.obligations,
                            &right_path.facts,
                            &right_path.obligations,
                            assumptions,
                        ) else {
                            continue;
                        };

                        match right_path.outcome {
                            CExpressionOutcome::Value(value) => {
                                paths.extend(c_truthiness_as_c_int32_paths(
                                    value,
                                    facts,
                                    obligations,
                                    assumptions,
                                ))
                            }
                            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => paths
                                .push(CExpressionPath {
                                    outcome: CExpressionOutcome::UndefinedBehavior(
                                        undefined_behavior,
                                    ),
                                    facts,
                                    obligations,
                                }),
                            CExpressionOutcome::RuntimeError(error) => {
                                paths.push(CExpressionPath {
                                    outcome: CExpressionOutcome::RuntimeError(error),
                                    facts,
                                    obligations,
                                })
                            }
                        }
                    }
                }
            }
            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                    facts: left_path.facts,
                    obligations: left_path.obligations,
                })
            }
            CExpressionOutcome::RuntimeError(error) => paths.push(CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(error),
                facts: left_path.facts,
                obligations: left_path.obligations,
            }),
        }
    }

    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(in crate::kernel) fn pointer_equality_condition(
    left: Pointer,
    right: Pointer,
) -> ConditionTerm {
    if left.block == right.block {
        ConditionTerm::pointer_offset_equal(left.offset, right.offset)
    } else {
        ConditionTerm::pointer_equal(left, right)
    }
}

pub(in crate::kernel) fn pointer_is_null_condition(pointer: Pointer) -> ConditionTerm {
    pointer_equality_condition(pointer, Pointer::null())
}

pub(in crate::kernel) fn evaluate_c_int32_binary_paths(
    state: &CState,
    left: &CExpression,
    right: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    apply: impl Fn(
        Bitvector32Term,
        Bitvector32Term,
        Vec<ExecutionPureFact>,
        Vec<ProofObligation>,
    ) -> Vec<CExpressionPath>,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for left_path in evaluate_c_expression_paths(state, left, assumptions, budget)? {
        let CExpressionPath {
            outcome: left_outcome,
            facts: left_facts,
            obligations: left_obligations,
        } = left_path;

        let mut left_facts = left_facts;
        let left = match left_outcome {
            CExpressionOutcome::Value(left) => {
                let Some(left) = promote_c_int32_path_value(left, &mut left_facts, assumptions)
                else {
                    paths.push(c_type_mismatch_expression_path(
                        left_facts,
                        left_obligations,
                    ));
                    continue;
                };
                left
            }
            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                    facts: left_facts,
                    obligations: left_obligations,
                });
                continue;
            }
            CExpressionOutcome::RuntimeError(error) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::RuntimeError(error),
                    facts: left_facts,
                    obligations: left_obligations,
                });
                continue;
            }
        };

        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_facts, &left_obligations);
        for right_path in evaluate_c_expression_paths(state, right, &right_assumptions, budget)? {
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &left_facts,
                &left_obligations,
                &right_path.facts,
                &right_path.obligations,
                assumptions,
            ) else {
                continue;
            };

            match right_path.outcome {
                CExpressionOutcome::Value(right) => {
                    let mut facts = facts;
                    let Some(right) = promote_c_int32_path_value(right, &mut facts, assumptions)
                    else {
                        paths.push(c_type_mismatch_expression_path(facts, obligations));
                        continue;
                    };
                    paths.extend(apply(left.clone(), right, facts, obligations));
                }
                CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                    paths.push(CExpressionPath {
                        outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                        facts,
                        obligations,
                    })
                }
                CExpressionOutcome::RuntimeError(error) => paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::RuntimeError(error),
                    facts,
                    obligations,
                }),
            }
        }
    }

    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(in crate::kernel) fn apply_c_int32_total_binary(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    apply: fn(Bitvector32Term, Bitvector32Term) -> Bitvector32Term,
) -> Vec<CExpressionPath> {
    vec![CExpressionPath {
        outcome: CExpressionOutcome::Value(int32(apply(left, right))),
        facts,
        obligations,
    }]
}

pub(in crate::kernel) fn evaluate_c_int32_total_unary_paths(
    state: &CState,
    expression: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    apply: fn(Bitvector32Term) -> Bitvector32Term,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for path in evaluate_c_expression_paths(state, expression, assumptions, budget)? {
        match path.outcome {
            CExpressionOutcome::Value(value) => {
                let mut facts = path.facts;
                let Some(value) = promote_c_int32_path_value(value, &mut facts, assumptions) else {
                    paths.push(c_type_mismatch_expression_path(facts, path.obligations));
                    continue;
                };
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::Value(int32(apply(value))),
                    facts,
                    obligations: path.obligations,
                });
            }
            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                    facts: path.facts,
                    obligations: path.obligations,
                })
            }
            CExpressionOutcome::RuntimeError(error) => paths.push(CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(error),
                facts: path.facts,
                obligations: path.obligations,
            }),
        }
    }

    budget.check_path_width(paths.len())?;
    Ok(paths)
}
