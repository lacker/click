use super::*;

const SURFACE_SYNTHESIS_WORK_LIMIT: usize = 16_384;
pub(super) const SURFACE_SYNTHESIS_DEPTH_LIMIT: usize = 128;

#[derive(Clone, Copy)]
struct SurfaceSynthesisBudget {
    remaining_work: usize,
    depth: usize,
    exhausted_category: Option<&'static str>,
}

thread_local! {
    static SURFACE_SYNTHESIS_BUDGET: std::cell::RefCell<Option<SurfaceSynthesisBudget>> =
        const { std::cell::RefCell::new(None) };
    static LAST_SURFACE_SYNTHESIS_EXHAUSTION: std::cell::Cell<Option<&'static str>> =
        const { std::cell::Cell::new(None) };
}

struct SurfaceSynthesisScope(Option<SurfaceSynthesisBudget>);

impl SurfaceSynthesisScope {
    fn enter() -> Self {
        LAST_SURFACE_SYNTHESIS_EXHAUSTION.with(|last| last.set(None));
        let previous = SURFACE_SYNTHESIS_BUDGET.with(|slot| {
            slot.replace(Some(SurfaceSynthesisBudget {
                remaining_work: SURFACE_SYNTHESIS_WORK_LIMIT,
                depth: 0,
                exhausted_category: None,
            }))
        });
        Self(previous)
    }
}

impl Drop for SurfaceSynthesisScope {
    fn drop(&mut self) {
        let exhausted = SURFACE_SYNTHESIS_BUDGET.with(|slot| {
            let current = slot.replace(self.0.take());
            current.and_then(|budget| budget.exhausted_category)
        });
        if exhausted.is_some() {
            LAST_SURFACE_SYNTHESIS_EXHAUSTION.with(|last| last.set(exhausted));
        }
    }
}

struct SurfaceSynthesisFrame {
    counted: bool,
}

impl SurfaceSynthesisFrame {
    fn enter(category: &'static str) -> Option<Self> {
        let counted = SURFACE_SYNTHESIS_BUDGET.with(|slot| {
            let mut slot = slot.borrow_mut();
            let Some(budget) = slot.as_mut() else {
                return Some(false);
            };
            if budget.remaining_work == 0 || budget.depth >= SURFACE_SYNTHESIS_DEPTH_LIMIT {
                budget.exhausted_category.get_or_insert(category);
                return None;
            }
            budget.remaining_work -= 1;
            budget.depth += 1;
            Some(true)
        })?;
        Some(Self { counted })
    }
}

impl Drop for SurfaceSynthesisFrame {
    fn drop(&mut self) {
        if self.counted {
            SURFACE_SYNTHESIS_BUDGET.with(|slot| {
                if let Some(budget) = slot.borrow_mut().as_mut() {
                    budget.depth = budget.depth.saturating_sub(1);
                }
            });
        }
    }
}

fn consume_surface_synthesis_work(category: &'static str) -> bool {
    SURFACE_SYNTHESIS_BUDGET.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(budget) = slot.as_mut() else {
            return true;
        };
        if budget.remaining_work == 0 {
            budget.exhausted_category.get_or_insert(category);
            return false;
        }
        budget.remaining_work -= 1;
        true
    })
}

pub(super) fn surface_synthesis_exhaustion_description() -> Option<String> {
    LAST_SURFACE_SYNTHESIS_EXHAUSTION.with(|last| {
        last.get().map(|category| {
            format!("Surface Click reconstruction exhausted its bounded {category} search")
        })
    })
}

pub(super) fn surface_synthesis_failure(prefix: &str, kernel: &Proposition) -> String {
    surface_synthesis_exhaustion_description()
        .map(|exhaustion| format!("{prefix}: {exhaustion}"))
        .unwrap_or_else(|| format!("{prefix}: {kernel:?}"))
}

pub(in crate::lang::click) fn synthesize_surface_proposition(
    proposition: &Proposition,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
) -> Option<ClickProposition> {
    let _scope = SurfaceSynthesisScope::enter();
    synthesize_surface_proposition_with_bound_variables(
        proposition,
        parameters,
        arguments,
        state,
        &BTreeMap::new(),
    )
}

fn synthesize_surface_proposition_with_bound_variables(
    proposition: &Proposition,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ClickProposition> {
    let _frame = SurfaceSynthesisFrame::enter("proposition")?;
    match proposition {
        Proposition::And(left, right) => {
            return Some(ClickProposition::And(
                Box::new(synthesize_surface_proposition_with_bound_variables(
                    left,
                    parameters,
                    arguments,
                    state,
                    bound_variables,
                )?),
                Box::new(synthesize_surface_proposition_with_bound_variables(
                    right,
                    parameters,
                    arguments,
                    state,
                    bound_variables,
                )?),
            ));
        }
        Proposition::Or(left, right) => {
            return Some(ClickProposition::Or(
                Box::new(synthesize_surface_proposition_with_bound_variables(
                    left,
                    parameters,
                    arguments,
                    state,
                    bound_variables,
                )?),
                Box::new(synthesize_surface_proposition_with_bound_variables(
                    right,
                    parameters,
                    arguments,
                    state,
                    bound_variables,
                )?),
            ));
        }
        Proposition::Implies(left, right) => {
            return Some(ClickProposition::Implies(
                Box::new(synthesize_surface_proposition_with_bound_variables(
                    left,
                    parameters,
                    arguments,
                    state,
                    bound_variables,
                )?),
                Box::new(synthesize_surface_proposition_with_bound_variables(
                    right,
                    parameters,
                    arguments,
                    state,
                    bound_variables,
                )?),
            ));
        }
        Proposition::ForAll { var, sort, body }
        | Proposition::Exists {
            var, sort, body, ..
        } => {
            if *sort != Sort::CInt32 {
                return None;
            }
            let mut suffix = bound_variables.len();
            let name = loop {
                let candidate = format!("__click_q{suffix}");
                let conflicts = parameters
                    .iter()
                    .any(|parameter| parameter.name() == candidate)
                    || state
                        .locals()
                        .object_values()
                        .any(|(name, _)| name == candidate)
                    || bound_variables.values().any(|name| name == &candidate);
                if !conflicts {
                    break candidate;
                }
                suffix += 1;
            };
            let mut body_variables = bound_variables.clone();
            body_variables.insert(*var, name.clone());
            let body = Box::new(synthesize_surface_proposition_with_bound_variables(
                body,
                parameters,
                arguments,
                state,
                &body_variables,
            )?);
            return Some(match proposition {
                Proposition::ForAll { .. } => ClickProposition::ForAll {
                    c_type: C0Type::Int32,
                    name,
                    body,
                },
                Proposition::Exists { .. } => ClickProposition::Exists {
                    c_type: C0Type::Int32,
                    name,
                    body,
                },
                _ => unreachable!(),
            });
        }
        _ => {}
    }
    // A predicate call lowers each array-ref argument to a (memory, pointer)
    // term pair and each value argument to a single value term, so the kernel
    // argument list reads back unambiguously: a `CMemory` term always opens an
    // array-ref pair. The snapshot the pair names is not spelled here — the
    // current memory needs no spelling, and every caller re-lowers the
    // candidate and compares it to the kernel fact, so a candidate built
    // against the wrong snapshot is rejected by that round trip rather than by
    // a guess made here.
    if let Proposition::Predicate {
        name,
        arguments: kernel_arguments,
    } = proposition
    {
        let mut call_arguments = Vec::new();
        let mut index = 0;
        while index < kernel_arguments.len() {
            match &kernel_arguments[index] {
                Term::CMemory(_) => {
                    let Some(Term::CValue(CValue::Pointer(pointer))) =
                        kernel_arguments.get(index + 1)
                    else {
                        return None;
                    };
                    call_arguments.push(ContractExpression::CFragment(synthesize_surface_pointer(
                        pointer,
                        parameters,
                        arguments,
                        state,
                        bound_variables,
                    )?));
                    index += 2;
                }
                Term::CValue(CValue::Pointer(pointer)) => {
                    call_arguments.push(ContractExpression::CFragment(synthesize_surface_pointer(
                        pointer,
                        parameters,
                        arguments,
                        state,
                        bound_variables,
                    )?));
                    index += 1;
                }
                Term::CValue(CValue::Int32(value) | CValue::UInt8(value)) => {
                    call_arguments.push(synthesize_surface_bitvector(
                        value,
                        parameters,
                        arguments,
                        state,
                        bound_variables,
                    )?);
                    index += 1;
                }
                _ => return None,
            }
        }
        return Some(ClickProposition::PredicateCall {
            name: name.clone(),
            arguments: call_arguments,
        });
    }
    if let Proposition::CResourceSeparate { left, right } = proposition {
        return Some(ClickProposition::Separate {
            left: synthesize_surface_resource_subject(
                left,
                parameters,
                arguments,
                state,
                bound_variables,
            )?,
            right: synthesize_surface_resource_subject(
                right,
                parameters,
                arguments,
                state,
                bound_variables,
            )?,
        });
    }
    if let Proposition::CMemoryLoadable { base, bytes, .. } = proposition {
        let element_count = if let Some(byte_count) = bytes.as_const() {
            if !byte_count.is_multiple_of(4) {
                return None;
            }
            CExpression::Value(int32(byte_count / 4))
        } else if let Bitvector32Term::Multiply(left, right) = bytes {
            let elements = if right.as_const() == Some(4) {
                left.as_ref()
            } else if left.as_const() == Some(4) {
                right.as_ref()
            } else {
                return None;
            };
            contract_expression_to_c_fragment(&synthesize_surface_bitvector(
                elements,
                parameters,
                arguments,
                state,
                bound_variables,
            )?)?
        } else {
            return None;
        };
        let semantic_base =
            synthesize_surface_pointer(base, parameters, arguments, state, bound_variables)?;
        let surface_base = synthesize_surface_pointer_offset(
            &base.offset,
            parameters,
            arguments,
            state,
            bound_variables,
        )
        .unwrap_or_else(|| ContractExpression::CFragment(semantic_base.clone()));
        return Some(ClickProposition::Loadable {
            segment: ContractSegment {
                state: ContractSegmentState::Current,
                base: semantic_base,
                start: CExpression::Value(int32(0)),
                end: element_count.clone(),
                surface: ContractSegmentSurface::Range {
                    base: surface_base,
                    start: ContractExpression::CFragment(CExpression::Value(int32(0))),
                    end: ContractExpression::CFragment(element_count),
                },
            },
        });
    }
    if let Proposition::Not(body) = proposition {
        return Some(ClickProposition::Not(Box::new(
            synthesize_surface_proposition_with_bound_variables(
                body,
                parameters,
                arguments,
                state,
                bound_variables,
            )?,
        )));
    }
    let Proposition::ConditionIs(condition, value) = proposition else {
        return None;
    };
    if let ConditionTerm::Constant(condition) = condition {
        return Some(ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(int32(0))),
            operator: if condition == value {
                ComparisonOperator::Equal
            } else {
                ComparisonOperator::NotEqual
            },
            right: ContractExpression::CFragment(CExpression::Value(int32(0))),
        });
    }
    if let ConditionTerm::PointerOffsetEqual(left, right) = condition {
        return Some(ClickProposition::Comparison {
            left: synthesize_surface_pointer_offset(
                left,
                parameters,
                arguments,
                state,
                bound_variables,
            )?,
            operator: if *value {
                ComparisonOperator::Equal
            } else {
                ComparisonOperator::NotEqual
            },
            right: synthesize_surface_pointer_offset(
                right,
                parameters,
                arguments,
                state,
                bound_variables,
            )?,
        });
    }
    if let ConditionTerm::PointerEqual(left, right) = condition {
        return Some(ClickProposition::Comparison {
            left: synthesize_surface_pointer_expression(
                left,
                parameters,
                arguments,
                state,
                bound_variables,
            )?,
            operator: if *value {
                ComparisonOperator::Equal
            } else {
                ComparisonOperator::NotEqual
            },
            right: synthesize_surface_pointer_expression(
                right,
                parameters,
                arguments,
                state,
                bound_variables,
            )?,
        });
    }
    let (left, operator, right) = match condition {
        ConditionTerm::Bitvector32SignedLessThan(left, right) => {
            (left, ComparisonOperator::LessThan, right)
        }
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
            (left, ComparisonOperator::LessEqual, right)
        }
        ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
            (left, ComparisonOperator::GreaterThan, right)
        }
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
            (left, ComparisonOperator::GreaterEqual, right)
        }
        ConditionTerm::Bitvector32Equal(left, right) => (left, ComparisonOperator::Equal, right),
        _ => return None,
    };
    let surface_left =
        synthesize_surface_bitvector(left, parameters, arguments, state, bound_variables);
    let surface_right =
        synthesize_surface_bitvector(right, parameters, arguments, state, bound_variables);
    let comparison = ClickProposition::Comparison {
        left: surface_left?,
        operator,
        right: surface_right?,
    };
    if *value {
        Some(comparison)
    } else if operator == ComparisonOperator::Equal {
        let ClickProposition::Comparison { left, right, .. } = comparison else {
            unreachable!()
        };
        Some(ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::NotEqual,
            right,
        })
    } else {
        Some(ClickProposition::Not(Box::new(comparison)))
    }
}

fn synthesize_surface_resource_subject(
    resource: &CResource,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ResourceSubject> {
    let _frame = SurfaceSynthesisFrame::enter("resource")?;
    let CResource::Memory(range) = resource else {
        return None;
    };
    let semantic_base =
        synthesize_surface_pointer(range.base(), parameters, arguments, state, bound_variables)?;
    let surface_base = synthesize_surface_pointer_offset(
        &range.base().offset,
        parameters,
        arguments,
        state,
        bound_variables,
    )
    .unwrap_or_else(|| ContractExpression::CFragment(semantic_base.clone()));
    let surface_start =
        synthesize_surface_bitvector(range.start(), parameters, arguments, state, bound_variables)?;
    let surface_end =
        synthesize_surface_bitvector(range.end(), parameters, arguments, state, bound_variables)?;
    let start = contract_expression_to_c_fragment(&surface_start)?;
    let end = contract_expression_to_c_fragment(&surface_end)?;
    Some(ResourceSubject::Memory(ContractSegment {
        state: ContractSegmentState::Current,
        base: semantic_base,
        start,
        end,
        surface: ContractSegmentSurface::Range {
            base: surface_base,
            start: surface_start,
            end: surface_end,
        },
    }))
}

fn synthesize_surface_pointer_offset(
    term: &PointerOffsetTerm,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ContractExpression> {
    let _frame = SurfaceSynthesisFrame::enter("pointer-offset")?;
    for (parameter, argument) in parameters.iter().zip(arguments) {
        if let CExpression::Value(CValue::Pointer(pointer)) = argument
            && pointer.offset == *term
        {
            return Some(ContractExpression::CFragment(CExpression::Variable(
                parameter.name().to_string(),
            )));
        }
    }
    match term {
        PointerOffsetTerm::Int32Scaled {
            value,
            byte_width: 4,
        } if matches!(value.as_ref(), Bitvector32Term::MemoryLoad(_, _)) => {
            let Bitvector32Term::MemoryLoad(_, pointer) = value.as_ref() else {
                unreachable!()
            };
            if let Some(field) =
                synthesize_parameter_field_load(pointer, CType::Int32Pointer, parameters, arguments)
            {
                Some(field)
            } else {
                Some(ContractExpression::CFragment(CExpression::TypedLoad {
                    pointer: Box::new(synthesize_surface_pointer(
                        pointer,
                        parameters,
                        arguments,
                        state,
                        bound_variables,
                    )?),
                    value_type: CType::Int32Pointer,
                }))
            }
        }
        PointerOffsetTerm::Add(left, right) => {
            let indexed_pointer = |base: &PointerOffsetTerm, byte_offset: &PointerOffsetTerm| {
                let PointerOffsetTerm::Constant(byte_offset) = byte_offset else {
                    return None;
                };
                if byte_offset % 4 != 0 {
                    return None;
                }
                let ContractExpression::CFragment(base) = synthesize_surface_pointer_offset(
                    base,
                    parameters,
                    arguments,
                    state,
                    bound_variables,
                )?
                else {
                    return None;
                };
                Some(ContractExpression::CFragment(CExpression::Add(
                    Box::new(base),
                    Box::new(CExpression::Value(CValue::Int32(
                        Bitvector32Term::Constant((byte_offset / 4) as u32),
                    ))),
                )))
            };
            let dynamically_indexed_pointer =
                |base: &PointerOffsetTerm, index: &PointerOffsetTerm| {
                    let PointerOffsetTerm::Int32Scaled {
                        value: index,
                        byte_width: 4,
                    } = index
                    else {
                        return None;
                    };
                    let base =
                        contract_expression_to_c_fragment(&synthesize_surface_pointer_offset(
                            base,
                            parameters,
                            arguments,
                            state,
                            bound_variables,
                        )?)?;
                    let index = contract_expression_to_c_fragment(&synthesize_surface_bitvector(
                        index,
                        parameters,
                        arguments,
                        state,
                        bound_variables,
                    )?)?;
                    Some(ContractExpression::CFragment(CExpression::Add(
                        Box::new(base),
                        Box::new(index),
                    )))
                };
            indexed_pointer(left, right)
                .or_else(|| indexed_pointer(right, left))
                .or_else(|| dynamically_indexed_pointer(left, right))
                .or_else(|| dynamically_indexed_pointer(right, left))
        }
        PointerOffsetTerm::Int32Scaled { value, byte_width } if matches!(*byte_width, 1 | 4) => {
            synthesize_surface_bitvector(value, parameters, arguments, state, bound_variables)
        }
        PointerOffsetTerm::Constant(_)
        | PointerOffsetTerm::Variable(_)
        | PointerOffsetTerm::Int32Scaled { .. } => None,
    }
}

fn synthesize_surface_bitvector(
    term: &Bitvector32Term,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ContractExpression> {
    let _frame = SurfaceSynthesisFrame::enter("bitvector")?;
    if let Bitvector32Term::Variable(variable) = term
        && let Some(name) = bound_variables.get(variable)
    {
        return Some(ContractExpression::CFragment(CExpression::Variable(
            name.clone(),
        )));
    }
    if let Bitvector32Term::Constant(_) = term {
        return Some(ContractExpression::CFragment(CExpression::Value(
            CValue::Int32(term.clone()),
        )));
    }
    if let Some((name, _)) = state.locals().object_values().find(
        |(_, value)| matches!(value, CValue::Int32(local) | CValue::UInt8(local) if local == term),
    ) {
        return Some(if name == "result" {
            ContractExpression::CBinding(name.to_string())
        } else {
            ContractExpression::CFragment(CExpression::Variable(name.to_string()))
        });
    }
    if let Some(name) = describe_parameter_bitvector(term, parameters, arguments) {
        return Some(if name == "result" {
            ContractExpression::CBinding(name)
        } else {
            ContractExpression::CFragment(CExpression::Variable(name))
        });
    }
    let binary = |left: &Bitvector32Term, right: &Bitvector32Term| {
        Some((
            Box::new(synthesize_surface_bitvector(
                left,
                parameters,
                arguments,
                state,
                bound_variables,
            )?),
            Box::new(synthesize_surface_bitvector(
                right,
                parameters,
                arguments,
                state,
                bound_variables,
            )?),
        ))
    };
    match term {
        Bitvector32Term::Constant(_) => unreachable!("constants returned above"),
        Bitvector32Term::Add(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Add(left, right))
        }
        Bitvector32Term::Subtract(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Subtract(left, right))
        }
        Bitvector32Term::Multiply(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Multiply(left, right))
        }
        Bitvector32Term::Divide(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Divide(left, right))
        }
        Bitvector32Term::Remainder(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Remainder(left, right))
        }
        Bitvector32Term::ShiftLeft(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::ShiftLeft(left, right))
        }
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::ShiftRight(left, right))
        }
        Bitvector32Term::BitwiseAnd(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::BitwiseAnd(left, right))
        }
        Bitvector32Term::BitwiseOr(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::BitwiseOr(left, right))
        }
        Bitvector32Term::BitwiseXor(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::BitwiseXor(left, right))
        }
        Bitvector32Term::BitwiseNot(value) => Some(ContractExpression::BitwiseNot(Box::new(
            synthesize_surface_bitvector(value, parameters, arguments, state, bound_variables)?,
        ))),
        Bitvector32Term::MemoryLoad(_, kernel_pointer) => {
            if let Some(field) =
                synthesize_parameter_field_load(kernel_pointer, CType::Int32, parameters, arguments)
            {
                Some(field)
            } else if let Some(indexed_field) = synthesize_parameter_field_indexed_int32_load(
                kernel_pointer,
                parameters,
                arguments,
                state,
                bound_variables,
            ) {
                Some(indexed_field)
            } else if let Some(indexed_local) = synthesize_local_indexed_int32_load(
                kernel_pointer,
                parameters,
                arguments,
                state,
                bound_variables,
            ) {
                Some(indexed_local)
            } else {
                let value_type =
                    parameters
                        .iter()
                        .zip(arguments)
                        .find_map(|(parameter, argument)| {
                            let CExpression::Value(CValue::Pointer(base)) = argument else {
                                return None;
                            };
                            kernel_pointer.element_index_from_base(base)?;
                            match parameter.c_type() {
                                C0Type::UInt8Pointer | C0Type::UInt8Array(_) => Some(CType::UInt8),
                                C0Type::Int32Pointer | C0Type::Int32Array(_) => Some(CType::Int32),
                                C0Type::Int32 | C0Type::UInt8 => None,
                                C0Type::Void => None,
                            }
                        });
                let pointer = synthesize_surface_pointer(
                    kernel_pointer,
                    parameters,
                    arguments,
                    state,
                    bound_variables,
                );
                let pointer = pointer?;
                Some(ContractExpression::CFragment(match value_type {
                    Some(CType::UInt8) => CExpression::TypedLoad {
                        pointer: Box::new(pointer),
                        value_type: CType::UInt8,
                    },
                    _ => CExpression::Load(Box::new(pointer)),
                }))
            }
        }
        Bitvector32Term::Variable(_)
        | Bitvector32Term::If { .. }
        | Bitvector32Term::RangeFold { .. } => None,
        Bitvector32Term::PureFunctionApplication {
            name,
            arguments: values,
        } => Some(ContractExpression::Call {
            name: name.clone(),
            arguments: values
                .iter()
                .map(|value| {
                    synthesize_surface_bitvector(
                        value,
                        parameters,
                        arguments,
                        state,
                        bound_variables,
                    )
                })
                .collect::<Option<Vec<_>>>()?,
        }),
    }
}

fn synthesize_parameter_field_indexed_int32_load(
    pointer: &Pointer,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ContractExpression> {
    let _frame = SurfaceSynthesisFrame::enter("indexed-field")?;
    let pointer_field_and_index = |base: &PointerOffsetTerm,
                                   index: Option<&PointerOffsetTerm>|
     -> Option<(ContractExpression, ContractExpression)> {
        let PointerOffsetTerm::Int32Scaled {
            value,
            byte_width: 4,
        } = base
        else {
            return None;
        };
        let Bitvector32Term::MemoryLoad(_, field_pointer) = value.as_ref() else {
            return None;
        };
        let field = synthesize_parameter_field_load(
            field_pointer,
            CType::Int32Pointer,
            parameters,
            arguments,
        )?;
        let index = match index {
            None => ContractExpression::CFragment(CExpression::Value(int32(0))),
            Some(PointerOffsetTerm::Int32Scaled {
                value,
                byte_width: 4,
            }) => {
                synthesize_surface_bitvector(value, parameters, arguments, state, bound_variables)?
            }
            Some(_) => return None,
        };
        Some((field, index))
    };
    let (field, index) = match &pointer.offset {
        base @ PointerOffsetTerm::Int32Scaled { .. } => pointer_field_and_index(base, None)?,
        PointerOffsetTerm::Add(left, right) => pointer_field_and_index(left, Some(right))
            .or_else(|| pointer_field_and_index(right, Some(left)))?,
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => return None,
    };
    Some(ContractExpression::Index(Box::new(field), Box::new(index)))
}

pub(super) fn bitvector_term_is_load_free(term: &Bitvector32Term) -> bool {
    let mut pending = vec![term];
    while let Some(term) = pending.pop() {
        if !consume_surface_synthesis_work("local-index") {
            return false;
        }
        match term {
            Bitvector32Term::MemoryLoad(_, _) => return false,
            Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_) => {}
            Bitvector32Term::Add(left, right)
            | Bitvector32Term::Subtract(left, right)
            | Bitvector32Term::Multiply(left, right)
            | Bitvector32Term::Divide(left, right)
            | Bitvector32Term::Remainder(left, right)
            | Bitvector32Term::ShiftLeft(left, right)
            | Bitvector32Term::ArithmeticShiftRight(left, right)
            | Bitvector32Term::BitwiseAnd(left, right)
            | Bitvector32Term::BitwiseOr(left, right)
            | Bitvector32Term::BitwiseXor(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            Bitvector32Term::BitwiseNot(value) => pending.push(value),
            Bitvector32Term::If {
                then_term,
                else_term,
                ..
            } => {
                pending.push(then_term);
                pending.push(else_term);
            }
            Bitvector32Term::RangeFold {
                start,
                end,
                initial,
                body,
                ..
            } => {
                pending.push(start);
                pending.push(end);
                pending.push(initial);
                pending.push(body);
            }
            Bitvector32Term::PureFunctionApplication { arguments, .. } => {
                pending.extend(arguments);
            }
        }
    }
    true
}

fn synthesize_local_indexed_int32_load(
    pointer: &Pointer,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ContractExpression> {
    let _frame = SurfaceSynthesisFrame::enter("local-index")?;
    state.locals().object_values().find_map(|(name, value)| {
        let CValue::Pointer(base) = value else {
            return None;
        };
        let index = pointer.element_index_from_base(base)?;
        if index == Bitvector32Term::Constant(0) {
            return None;
        }
        // This candidate is for ordinary `local[index]` spellings. If the
        // derived index itself reads memory, trying to synthesize that load
        // can rediscover another local-relative spelling with a still larger
        // index indefinitely. More specific field and pointer spellings are
        // tried by the surrounding reconstruction logic.
        if !bitvector_term_is_load_free(&index) {
            return None;
        }
        Some(ContractExpression::Index(
            Box::new(ContractExpression::CFragment(CExpression::Variable(
                name.to_string(),
            ))),
            Box::new(synthesize_surface_bitvector(
                &index,
                parameters,
                arguments,
                state,
                bound_variables,
            )?),
        ))
    })
}

fn synthesize_parameter_field_load(
    pointer: &Pointer,
    value_type: CType,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Option<ContractExpression> {
    for (parameter, argument) in parameters.iter().zip(arguments) {
        let (Some(layout), CExpression::Value(CValue::Pointer(base))) =
            (parameter.struct_layout(), argument)
        else {
            continue;
        };
        let Some(element_offset) = pointer
            .element_index_from_base(base)
            .and_then(|offset| offset.as_const())
        else {
            continue;
        };
        let offset_bytes = element_offset.checked_mul(4)?;
        let Some((field_name, field)) = layout
            .fields()
            .iter()
            .find(|(_, field)| field.offset_bytes() == offset_bytes)
        else {
            continue;
        };
        if field.c_type().to_kernel_type() != value_type {
            continue;
        }
        let base = CExpression::Variable(parameter.name().to_string());
        let field_pointer = if offset_bytes == 0 {
            base.clone()
        } else {
            CExpression::PointerOffsetBytes {
                pointer: Box::new(base.clone()),
                bytes: offset_bytes,
            }
        };
        return Some(ContractExpression::Field {
            base: Box::new(ContractExpression::CFragment(base)),
            field: field_name.clone(),
            lowered: CExpression::TypedLoad {
                pointer: Box::new(field_pointer),
                value_type,
            },
        });
    }
    None
}

fn synthesize_surface_pointer(
    pointer: &Pointer,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<CExpression> {
    let _frame = SurfaceSynthesisFrame::enter("pointer")?;
    if pointer == &Pointer::null() {
        return Some(CExpression::Value(int32(0)));
    }
    if let Some(expression) = parameters
        .iter()
        .zip(arguments)
        .find_map(|(parameter, argument)| {
            let CExpression::Value(CValue::Pointer(base)) = argument else {
                return None;
            };
            let index = pointer.element_index_from_base(base)?;
            let base = CExpression::Variable(parameter.name().to_string());
            if index == Bitvector32Term::Constant(0) {
                return Some(base);
            }
            let index = synthesize_surface_bitvector(
                &index,
                parameters,
                arguments,
                state,
                bound_variables,
            )?;
            let ContractExpression::CFragment(index) = index else {
                return None;
            };
            Some(CExpression::Add(Box::new(base), Box::new(index)))
        })
    {
        return Some(expression);
    }
    if let Some(expression) = state.locals().object_values().find_map(|(name, value)| {
        let CValue::Pointer(base) = value else {
            return None;
        };
        let index = pointer.element_index_from_base(base)?;
        let base = CExpression::Variable(name.to_string());
        if index == Bitvector32Term::Constant(0) {
            return Some(base);
        }
        let index =
            synthesize_surface_bitvector(&index, parameters, arguments, state, bound_variables)?;
        let ContractExpression::CFragment(index) = index else {
            return None;
        };
        Some(CExpression::Add(Box::new(base), Box::new(index)))
    }) {
        return Some(expression);
    }
    if !arguments.iter().any(|argument| {
        matches!(
            argument,
            CExpression::Value(CValue::Pointer(base)) if base.block == pointer.block
        )
    }) {
        return None;
    }
    let ContractExpression::CFragment(expression) = synthesize_surface_pointer_offset(
        &pointer.offset,
        parameters,
        arguments,
        state,
        bound_variables,
    )?
    else {
        return None;
    };
    Some(expression)
}

fn synthesize_surface_pointer_expression(
    pointer: &Pointer,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ContractExpression> {
    let _frame = SurfaceSynthesisFrame::enter("pointer-expression")?;
    if let Some(pointer) =
        synthesize_surface_pointer(pointer, parameters, arguments, state, bound_variables)
    {
        return Some(ContractExpression::CFragment(pointer));
    }
    if !arguments.iter().any(|argument| {
        matches!(
            argument,
            CExpression::Value(CValue::Pointer(base)) if base.block == pointer.block
        )
    }) {
        return None;
    }
    synthesize_surface_pointer_offset(
        &pointer.offset,
        parameters,
        arguments,
        state,
        bound_variables,
    )
}
