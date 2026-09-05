use super::*;

pub(super) fn function_signature_type_environment(
    signature: &FunctionSignature,
    include_result: bool,
) -> BTreeMap<String, C0Type> {
    let mut variables = signature
        .parameters()
        .iter()
        .map(|parameter| (parameter.name().to_string(), parameter.c_type()))
        .collect::<BTreeMap<_, _>>();
    if include_result && signature.return_type() != C0Type::Void {
        variables.insert("result".to_string(), signature.return_type());
    }
    variables
}

pub(super) fn theorem_type_environment(theorem: &TheoremDefinition) -> BTreeMap<String, C0Type> {
    theorem
        .parameters()
        .iter()
        .map(|parameter| (parameter.name().to_string(), parameter.c_type()))
        .collect()
}

pub(super) fn validate_proposition_expression_types(
    proposition: &ClickProposition,
    variables: &BTreeMap<String, C0Type>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    context: &str,
) -> Result<(), ClickError> {
    match proposition {
        ClickProposition::Comparison { left, right, .. } => {
            let _ = infer_contract_expression_type(left, variables, click_functions, context)?;
            let _ = infer_contract_expression_type(right, variables, click_functions, context)?;
            Ok(())
        }
        ClickProposition::FloatClassification { expression, .. } => {
            let actual =
                infer_contract_expression_type(expression, variables, click_functions, context)?;
            if let Some(actual) = actual
                && !type_is_float(actual)
            {
                return Err(ClickError::new(format!(
                    "float classification expects a float expression in {context}, got {}",
                    describe_c0_type(actual)
                )));
            }
            Ok(())
        }
        ClickProposition::Separate { left, right } => {
            validate_resource_subject_expression_types(left, variables, click_functions, context)?;
            validate_resource_subject_expression_types(right, variables, click_functions, context)
        }
        ClickProposition::Contains { parent, child } => {
            validate_resource_subject_expression_types(
                parent,
                variables,
                click_functions,
                context,
            )?;
            validate_resource_subject_expression_types(child, variables, click_functions, context)
        }
        ClickProposition::Loadable { segment } => {
            validate_contract_segment_expression_types(segment, variables, click_functions, context)
        }
        ClickProposition::Defined { expression } => {
            let _ =
                infer_contract_expression_type(expression, variables, click_functions, context)?;
            Ok(())
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            validate_proposition_expression_types(left, variables, click_functions, context)?;
            validate_proposition_expression_types(right, variables, click_functions, context)
        }
        ClickProposition::Not(body)
        | ClickProposition::At {
            proposition: body, ..
        } => validate_proposition_expression_types(body, variables, click_functions, context),
        ClickProposition::ForAll { c_type, name, body }
        | ClickProposition::Exists { c_type, name, body } => {
            let mut body_variables = variables.clone();
            body_variables.insert(name.clone(), *c_type);
            validate_proposition_expression_types(body, &body_variables, click_functions, context)
        }
        ClickProposition::RangeAll {
            start,
            end,
            item,
            body,
        }
        | ClickProposition::RangeAny {
            start,
            end,
            item,
            body,
        } => {
            let _ = infer_contract_expression_type(start, variables, click_functions, context)?;
            let _ = infer_contract_expression_type(end, variables, click_functions, context)?;
            let mut body_variables = variables.clone();
            body_variables.insert(item.clone(), C0Type::Int32);
            validate_proposition_expression_types(body, &body_variables, click_functions, context)
        }
        ClickProposition::PredicateCall { arguments, .. } => {
            for argument in arguments {
                let _ =
                    infer_contract_expression_type(argument, variables, click_functions, context)?;
            }
            Ok(())
        }
    }
}

fn validate_resource_subject_expression_types(
    resource: &ResourceSubject,
    variables: &BTreeMap<String, C0Type>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    context: &str,
) -> Result<(), ClickError> {
    match resource {
        ResourceSubject::Memory(segment) => {
            validate_contract_segment_expression_types(segment, variables, click_functions, context)
        }
        ResourceSubject::Declared {
            name,
            arguments,
            parameter_types,
            ..
        } => {
            for (index, argument) in arguments.iter().enumerate() {
                let actual =
                    infer_contract_expression_type(argument, variables, click_functions, context)?;
                if let (Some(actual), Some(expected)) = (actual, parameter_types.get(index))
                    && !resource_types_compatible(name, index, actual, *expected)
                {
                    return Err(ClickError::new(format!(
                        "resource `{name}` argument {index} expects {}, got {} in {context}",
                        describe_c0_type(*expected),
                        describe_c0_type(actual)
                    )));
                }
            }
            Ok(())
        }
    }
}

pub(super) fn validate_pure_theorem_proof(
    theorem_name: &str,
    proof: &SourceProof,
) -> Result<(), ClickError> {
    match proof {
        SourceProof::Default => Ok(()),
        SourceProof::Tactic(SmartTactic::Auto | SmartTactic::Simp) => Ok(()),
        SourceProof::Tactic(SmartTactic::Frame) => Err(ClickError::new(format!(
            "`frame` is not available in the pure proof for theorem `{theorem_name}`"
        ))),
        SourceProof::Script(tactics) => validate_pure_theorem_tactics(theorem_name, tactics),
    }
}

fn validate_pure_theorem_tactics(
    theorem_name: &str,
    tactics: &[ProofTactic],
) -> Result<(), ClickError> {
    for tactic in tactics {
        match tactic {
            ProofTactic::UnfoldPredicate(_)
            | ProofTactic::UnfoldFunction(_)
            | ProofTactic::Induct { .. }
            | ProofTactic::ApplyInduction { .. }
            | ProofTactic::ApplyInductionUsing { .. }
            | ProofTactic::ApplyTheorem(_)
            | ProofTactic::ApplyTheoremUsing { .. }
            | ProofTactic::Assumption
            | ProofTactic::Extract(_)
            | ProofTactic::Normalize
            | ProofTactic::ArithmeticUsing(_)
            | ProofTactic::Intro
            | ProofTactic::Split
            | ProofTactic::Left
            | ProofTactic::Right
            | ProofTactic::Enumerate
            | ProofTactic::Contradiction(_)
            | ProofTactic::Rewrite(_)
            | ProofTactic::InstantiateUsing { .. }
            | ProofTactic::Simp
            | ProofTactic::SimpUsing(_) => {}
            ProofTactic::If(proof_if) => {
                validate_pure_theorem_tactics(theorem_name, &proof_if.then_tactics)?;
                validate_pure_theorem_tactics(theorem_name, &proof_if.else_tactics)?;
            }
            ProofTactic::Cases(proof_cases) => {
                validate_pure_theorem_tactics(theorem_name, &proof_cases.left_tactics)?;
                validate_pure_theorem_tactics(theorem_name, &proof_cases.right_tactics)?;
            }
            ProofTactic::Have(proof_have) => {
                validate_pure_theorem_proof(theorem_name, &proof_have.proof)?;
            }
            ProofTactic::Branch(_)
            | ProofTactic::Loop(_)
            | ProofTactic::Open(_)
            | ProofTactic::Mark(_) => {
                return Err(ClickError::new(format!(
                    "execution tactic `{}` is not available in the pure proof for theorem `{theorem_name}`",
                    tactic_name(tactic)
                )));
            }
            ProofTactic::CloseInvariants
            | ProofTactic::Step
            | ProofTactic::SmartExecute
            | ProofTactic::SmartExecuteAllPaths
            | ProofTactic::ExecuteUntil(_)
            | ProofTactic::SmartFrame(_)
            | ProofTactic::FrameUsing { .. }
            | ProofTactic::ObserveResource(_)
            | ProofTactic::Transport { .. }
            | ProofTactic::TransportUsing { .. }
            | ProofTactic::UnfoldResource(_)
            | ProofTactic::FoldResource(_)
            | ProofTactic::ConstructResource(_)
            | ProofTactic::Witness(_)
            | ProofTactic::Choose(_) => {
                return Err(ClickError::new(format!(
                    "tactic `{}` is not available in the pure proof for theorem `{theorem_name}`",
                    tactic_name(tactic)
                )));
            }
        }
    }
    Ok(())
}

pub(in crate::surface) fn tactic_name(tactic: &ProofTactic) -> &'static str {
    match tactic {
        ProofTactic::Mark(_) => "mark",
        ProofTactic::Step => "step",
        ProofTactic::SmartExecute => "execute",
        ProofTactic::SmartExecuteAllPaths => "execute",
        ProofTactic::ExecuteUntil(_) => "execute_until",
        ProofTactic::SmartFrame(_) => "frame",
        ProofTactic::FrameUsing { .. } => "frame",
        ProofTactic::UnfoldPredicate(_)
        | ProofTactic::UnfoldFunction(_)
        | ProofTactic::UnfoldResource(_) => "unfold",
        ProofTactic::FoldResource(_) => "fold",
        ProofTactic::ConstructResource(_) => "construct",
        ProofTactic::Induct { .. } => "induct",
        ProofTactic::ApplyInduction { .. } => "apply",
        ProofTactic::ApplyInductionUsing { .. } => "apply",
        ProofTactic::ApplyTheorem(_) | ProofTactic::ApplyTheoremUsing { .. } => "apply",
        ProofTactic::Have(_) => "have",
        ProofTactic::Open(_) => "open",
        ProofTactic::If(_) => "if",
        ProofTactic::Cases(_) => "cases",
        ProofTactic::Branch(_) => "branch",
        ProofTactic::Loop(_) => "loop",
        ProofTactic::ObserveResource(_) => "observe",
        ProofTactic::Witness(_) => "witness",
        ProofTactic::Choose(_) => "choose",
        ProofTactic::Assumption => "assumption",
        ProofTactic::Extract(_) => "extract",
        ProofTactic::Normalize => "normalize",
        ProofTactic::ArithmeticUsing(_) => "arithmetic",
        ProofTactic::Intro => "intro",
        ProofTactic::Split => "split",
        ProofTactic::Left => "left",
        ProofTactic::Right => "right",
        ProofTactic::Enumerate => "enumerate",
        ProofTactic::Contradiction(_) => "contradiction",
        ProofTactic::CloseInvariants => "close_invariants",
        ProofTactic::Rewrite(_) => "rewrite",
        ProofTactic::Transport { .. } | ProofTactic::TransportUsing { .. } => "transport",
        ProofTactic::InstantiateUsing { .. } => "instantiate",
        ProofTactic::Simp => "simp",
        ProofTactic::SimpUsing(_) => "simp",
    }
}

pub(super) fn reject_duplicate_owned_declared_resource_clauses<'a>(
    _resources: impl IntoIterator<Item = &'a ResourceClause>,
    _context: &str,
) -> Result<(), ClickError> {
    // Declared resources are quantitative. Repeated owned clauses require or
    // provide repeated units; they are not malformed declarations. Raw memory
    // retains its separate overlap validity rules in the kernel algebra.
    Ok(())
}

pub(in crate::surface) fn describe_resource_clause(resource: &ResourceClause) -> String {
    match resource {
        ResourceClause::Quantified { quantity, resource } => format!(
            "{} of {}",
            describe_contract_expression(quantity),
            describe_resource_clause(resource)
        ),
        ResourceClause::ViewMemory(segment) => format!(
            "views {}[{}..{}]",
            describe_c_expression(&segment.base),
            describe_c_expression(&segment.start),
            describe_c_expression(&segment.end)
        ),
        ResourceClause::OwnMemory(segment) => format!(
            "owns {}[{}..{}]",
            describe_c_expression(&segment.base),
            describe_c_expression(&segment.start),
            describe_c_expression(&segment.end)
        ),
        ResourceClause::MemoryAggregate { access, segments } => {
            let verb = match access {
                ResourceAccessMode::Own => "owns",
                ResourceAccessMode::View => "views",
            };
            format!(
                "{verb} aggregate {{{}}}",
                segments
                    .iter()
                    .map(describe_contract_segment)
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        }
        ResourceClause::Declared {
            access,
            name,
            arguments,
            ..
        } => {
            let resource = format!(
                "{name}({})",
                arguments
                    .iter()
                    .map(describe_contract_expression)
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            match access {
                ResourceAccessMode::Own => resource,
                ResourceAccessMode::View => format!("view {resource}"),
            }
        }
    }
}

pub(in crate::surface) fn describe_c0_type(c_type: C0Type) -> String {
    match c_type {
        C0Type::Void => "void".to_string(),
        C0Type::Int16 => "int16".to_string(),
        C0Type::Int32 => "int32".to_string(),
        C0Type::UInt8 => "uint8".to_string(),
        C0Type::UInt16 => "uint16".to_string(),
        C0Type::UInt32 => "uint32".to_string(),
        C0Type::Int64 => "int64".to_string(),
        C0Type::UInt64 => "uint64".to_string(),
        C0Type::Float32 => "float".to_string(),
        C0Type::Float64 => "double".to_string(),
        C0Type::Int16Pointer | C0Type::Int16Array(_) => "int16*".to_string(),
        C0Type::UInt16Pointer | C0Type::UInt16Array(_) => "uint16*".to_string(),
        C0Type::Int32Pointer | C0Type::Int32Array(_) => "int32*".to_string(),
        C0Type::UInt8Pointer | C0Type::UInt8Array(_) => "uint8*".to_string(),
        C0Type::UInt32Pointer | C0Type::UInt32Array(_) => "uint32*".to_string(),
        C0Type::Int64Pointer | C0Type::Int64Array(_) => "int64*".to_string(),
        C0Type::UInt64Pointer | C0Type::UInt64Array(_) => "uint64*".to_string(),
        C0Type::Float32Pointer | C0Type::Float32Array(_) => "float*".to_string(),
        C0Type::Float64Pointer | C0Type::Float64Array(_) => "double*".to_string(),
        C0Type::Int16PointerPointer => "int16**".to_string(),
        C0Type::UInt16PointerPointer => "uint16**".to_string(),
        C0Type::Int32PointerPointer => "int32**".to_string(),
        C0Type::UInt8PointerPointer => "uint8**".to_string(),
        C0Type::UInt32PointerPointer => "uint32**".to_string(),
        C0Type::Int64PointerPointer => "int64**".to_string(),
        C0Type::UInt64PointerPointer => "uint64**".to_string(),
        C0Type::Float32PointerPointer => "float**".to_string(),
        C0Type::Float64PointerPointer => "double**".to_string(),
        C0Type::FunctionPointer(signature) => format!("function-pointer({signature})"),
    }
}

fn click_types_compatible(actual: C0Type, expected: C0Type) -> bool {
    match (actual, expected) {
        (C0Type::Int32Array(_), C0Type::Int32Pointer)
        | (C0Type::Int32Pointer, C0Type::Int32Array(_)) => true,
        (C0Type::UInt8Array(_), C0Type::UInt8Pointer)
        | (C0Type::UInt8Pointer, C0Type::UInt8Array(_))
        | (C0Type::Int16Array(_), C0Type::Int16Pointer)
        | (C0Type::Int16Pointer, C0Type::Int16Array(_))
        | (C0Type::UInt16Array(_), C0Type::UInt16Pointer)
        | (C0Type::UInt16Pointer, C0Type::UInt16Array(_))
        | (C0Type::UInt32Array(_), C0Type::UInt32Pointer)
        | (C0Type::UInt32Pointer, C0Type::UInt32Array(_))
        | (C0Type::Int64Array(_), C0Type::Int64Pointer)
        | (C0Type::Int64Pointer, C0Type::Int64Array(_))
        | (C0Type::UInt64Array(_), C0Type::UInt64Pointer)
        | (C0Type::UInt64Pointer, C0Type::UInt64Array(_))
        | (C0Type::Float32Array(_), C0Type::Float32Pointer)
        | (C0Type::Float32Pointer, C0Type::Float32Array(_))
        | (C0Type::Float64Array(_), C0Type::Float64Pointer)
        | (C0Type::Float64Pointer, C0Type::Float64Array(_)) => true,
        (C0Type::Int16 | C0Type::Int32 | C0Type::UInt8 | C0Type::UInt16, C0Type::UInt32) => true,
        (actual, expected) if type_is_arithmetic(actual) && type_is_arithmetic(expected) => true,
        _ => actual == expected,
    }
}

fn resource_types_compatible(name: &str, index: usize, actual: C0Type, expected: C0Type) -> bool {
    if name == CResourceFact::ALLOCATION_RESOURCE_NAME
        && index == 0
        && expected == C0Type::Int32Pointer
    {
        return matches!(
            actual,
            C0Type::Int16Pointer
                | C0Type::UInt16Pointer
                | C0Type::Int32Pointer
                | C0Type::UInt8Pointer
                | C0Type::UInt32Pointer
                | C0Type::Int64Pointer
                | C0Type::UInt64Pointer
                | C0Type::Int16PointerPointer
                | C0Type::UInt16PointerPointer
                | C0Type::Int32PointerPointer
                | C0Type::UInt8PointerPointer
                | C0Type::UInt32PointerPointer
                | C0Type::Int64PointerPointer
                | C0Type::UInt64PointerPointer
                | C0Type::Float32Pointer
                | C0Type::Float64Pointer
                | C0Type::Float32PointerPointer
                | C0Type::Float64PointerPointer
                | C0Type::Int32Array(_)
                | C0Type::UInt8Array(_)
                | C0Type::Int16Array(_)
                | C0Type::UInt16Array(_)
                | C0Type::UInt32Array(_)
                | C0Type::Int64Array(_)
                | C0Type::UInt64Array(_)
                | C0Type::Float32Array(_)
                | C0Type::Float64Array(_)
        );
    }
    click_types_compatible(actual, expected)
}

fn infer_contract_expression_type(
    expression: &ContractExpression,
    variables: &BTreeMap<String, C0Type>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    context: &str,
) -> Result<Option<C0Type>, ClickError> {
    match expression {
        ContractExpression::CFragment(expression)
        | ContractExpression::Field {
            lowered: expression,
            ..
        } => {
            if !variables.contains_key("result") && c_expression_uses_variable(expression, "result")
            {
                return Err(ClickError::new(format!(
                    "`result` is not available in {context}"
                )));
            }
            Ok(infer_c_expression_type(expression, variables))
        }
        // C locals are resolved against the concrete program state during
        // lowering, not against the contract namespace used here. In
        // particular, `c(result)` must not inherit the type of built-in
        // contract `result`.
        ContractExpression::CBinding(_) => Ok(None),
        ContractExpression::ResourceCount(_) => Ok(Some(C0Type::Int32)),
        ContractExpression::ResourceWildcard => Err(ClickError::new(
            "`_` is only valid inside a `count(...)` resource pattern",
        )),
        ContractExpression::Old(expression) | ContractExpression::At { expression, .. } => {
            infer_contract_expression_type(expression, variables, click_functions, context)
        }
        ContractExpression::Add(left, right) => {
            infer_add_expression_type(left, right, variables, click_functions, context)
        }
        ContractExpression::Subtract(left, right) => {
            infer_subtract_expression_type(left, right, variables, click_functions, context)
        }
        ContractExpression::Multiply(left, right) | ContractExpression::Divide(left, right) => {
            let left = infer_contract_expression_type(left, variables, click_functions, context)?;
            let right = infer_contract_expression_type(right, variables, click_functions, context)?;
            Ok(arithmetic_result_type(left, right))
        }
        ContractExpression::Remainder(left, right)
        | ContractExpression::BitwiseAnd(left, right)
        | ContractExpression::BitwiseOr(left, right)
        | ContractExpression::BitwiseXor(left, right) => {
            let left = infer_contract_expression_type(left, variables, click_functions, context)?;
            let right = infer_contract_expression_type(right, variables, click_functions, context)?;
            Ok(match (left, right) {
                (Some(left), Some(right)) if type_is_scalar(left) && type_is_scalar(right) => {
                    Some(scalar_arithmetic_result_type(left, right))
                }
                _ => None,
            })
        }
        ContractExpression::ShiftLeft(left, right)
        | ContractExpression::ShiftRight(left, right) => {
            infer_contract_shift_type(left, right, variables, click_functions, context)
        }
        ContractExpression::BitwiseNot(expression) => {
            let expression =
                infer_contract_expression_type(expression, variables, click_functions, context)?;
            Ok(expression
                .filter(|c_type| type_is_scalar(*c_type))
                .map(|c_type| scalar_arithmetic_result_type(c_type, c_type)))
        }
        ContractExpression::Index(base, index) => {
            let _ = infer_contract_expression_type(index, variables, click_functions, context)?;
            Ok(
                infer_contract_expression_type(base, variables, click_functions, context)?
                    .and_then(pointer_element_type),
            )
        }
        ContractExpression::If {
            then_branch,
            else_branch,
            ..
        } => {
            let then_type =
                infer_contract_expression_type(then_branch, variables, click_functions, context)?;
            let else_type =
                infer_contract_expression_type(else_branch, variables, click_functions, context)?;
            Ok(match (then_type, else_type) {
                (Some(then_type), Some(else_type))
                    if click_types_compatible(then_type, else_type) =>
                {
                    Some(then_type)
                }
                (Some(_), Some(_)) => None,
                (Some(c_type), None) | (None, Some(c_type)) => Some(c_type),
                (None, None) => None,
            })
        }
        ContractExpression::RangeFold {
            initial,
            accumulator,
            item,
            body,
            ..
        } => {
            let initial_type =
                infer_contract_expression_type(initial, variables, click_functions, context)?;
            let mut body_variables = variables.clone();
            if let Some(initial_type) = initial_type {
                body_variables.insert(accumulator.clone(), initial_type);
            }
            body_variables.insert(item.clone(), C0Type::Int32);
            infer_contract_expression_type(body, &body_variables, click_functions, context)
                .map(|body_type| body_type.or(initial_type))
        }
        ContractExpression::Let {
            name,
            c_type,
            value,
            body,
        } => {
            let value_type =
                infer_contract_expression_type(value, variables, click_functions, context)?;
            if let (Some(expected), Some(actual)) = (*c_type, value_type)
                && !click_types_compatible(actual, expected)
            {
                return Err(ClickError::new(format!(
                    "let binding `{name}` expects {}, got {} in {context}",
                    describe_c0_type(expected),
                    describe_c0_type(actual)
                )));
            }
            let mut body_variables = variables.clone();
            if let Some(binding_type) = c_type.or(value_type) {
                body_variables.insert(name.clone(), binding_type);
            }
            infer_contract_expression_type(body, &body_variables, click_functions, context)
        }
        ContractExpression::Call { name, arguments } => {
            let Some(function) = click_functions.get(name) else {
                return Ok(None);
            };
            for (index, (parameter, argument)) in
                function.parameters.iter().zip(arguments).enumerate()
            {
                if let Some(actual) =
                    infer_contract_expression_type(argument, variables, click_functions, context)?
                {
                    let expected = parameter.c_type();
                    if !click_types_compatible(actual, expected) {
                        return Err(ClickError::new(format!(
                            "function `{name}` argument {index} expects {}, got {} in {context}",
                            describe_c0_type(expected),
                            describe_c0_type(actual)
                        )));
                    }
                }
            }
            Ok(Some(function.return_type))
        }
    }
}

fn infer_c_expression_type(
    expression: &CExpression,
    variables: &BTreeMap<String, C0Type>,
) -> Option<C0Type> {
    match expression {
        CExpression::Value(CValue::Void) => Some(C0Type::Void),
        CExpression::Value(CValue::Int16(_)) => Some(C0Type::Int16),
        CExpression::Value(CValue::Int32(_)) => Some(C0Type::Int32),
        CExpression::Value(CValue::UInt8(_)) => Some(C0Type::UInt8),
        CExpression::Value(CValue::UInt16(_)) => Some(C0Type::UInt16),
        CExpression::Value(CValue::UInt32(_)) => Some(C0Type::UInt32),
        CExpression::Value(CValue::Int64(_)) => Some(C0Type::Int64),
        CExpression::Value(CValue::UInt64(_)) => Some(C0Type::UInt64),
        CExpression::Value(CValue::Float32(_)) => Some(C0Type::Float32),
        CExpression::Value(CValue::Float64(_)) => Some(C0Type::Float64),
        CExpression::Value(CValue::Pointer(_)) => None,
        CExpression::Variable(name) => variables.get(name).copied(),
        CExpression::Cast {
            expression: _,
            target_type,
        } => match target_type {
            CType::Int16 => Some(C0Type::Int16),
            CType::Int32 => Some(C0Type::Int32),
            CType::UInt8 => Some(C0Type::UInt8),
            CType::UInt16 => Some(C0Type::UInt16),
            CType::UInt32 => Some(C0Type::UInt32),
            CType::Int32Pointer => Some(C0Type::Int32Pointer),
            CType::UInt8Pointer => Some(C0Type::UInt8Pointer),
            CType::Int32PointerPointer => Some(C0Type::Int32PointerPointer),
            CType::UInt8PointerPointer => Some(C0Type::UInt8PointerPointer),
            CType::FunctionPointer(signature) => Some(C0Type::FunctionPointer(*signature)),
            CType::Void | CType::Int32Array(_) | CType::UInt8Array(_) => None,
            CType::Int64 => Some(C0Type::Int64),
            CType::UInt64 => Some(C0Type::UInt64),
            CType::Float32 => Some(C0Type::Float32),
            CType::Float64 => Some(C0Type::Float64),
            CType::Int16Pointer => Some(C0Type::Int16Pointer),
            CType::UInt16Pointer => Some(C0Type::UInt16Pointer),
            CType::UInt32Pointer => Some(C0Type::UInt32Pointer),
            CType::Int64Pointer => Some(C0Type::Int64Pointer),
            CType::UInt64Pointer => Some(C0Type::UInt64Pointer),
            CType::Int16PointerPointer => Some(C0Type::Int16PointerPointer),
            CType::UInt16PointerPointer => Some(C0Type::UInt16PointerPointer),
            CType::UInt32PointerPointer => Some(C0Type::UInt32PointerPointer),
            CType::Int64PointerPointer => Some(C0Type::Int64PointerPointer),
            CType::UInt64PointerPointer => Some(C0Type::UInt64PointerPointer),
            CType::Float32Pointer => Some(C0Type::Float32Pointer),
            CType::Float64Pointer => Some(C0Type::Float64Pointer),
            CType::Float32PointerPointer => Some(C0Type::Float32PointerPointer),
            CType::Float64PointerPointer => Some(C0Type::Float64PointerPointer),
            CType::Int16Array(_)
            | CType::UInt16Array(_)
            | CType::UInt32Array(_)
            | CType::Int64Array(_)
            | CType::UInt64Array(_)
            | CType::Float32Array(_)
            | CType::Float64Array(_) => None,
        },
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            let _ = infer_c_expression_type(condition, variables)?;
            let then_type = infer_c_expression_type(then_branch, variables);
            let else_type = infer_c_expression_type(else_branch, variables);
            match (then_type, else_type) {
                (Some(left), Some(right)) => arithmetic_result_type(Some(left), Some(right)),
                _ => None,
            }
        }
        CExpression::FloatNegate(expression) => {
            infer_c_expression_type(expression, variables).filter(|c_type| type_is_float(*c_type))
        }
        CExpression::FloatClassification { expression, .. } => matches!(
            infer_c_expression_type(expression, variables),
            Some(C0Type::Float32 | C0Type::Float64)
        )
        .then_some(C0Type::Int32),
        CExpression::AddressOf(_) | CExpression::FunctionAddress(_) => None,
        CExpression::PointerOffsetBytes { pointer, .. } => {
            infer_c_expression_type(pointer, variables)
        }
        CExpression::LessThan(_, _)
        | CExpression::LessEqual(_, _)
        | CExpression::GreaterThan(_, _)
        | CExpression::GreaterEqual(_, _)
        | CExpression::Equal(_, _)
        | CExpression::NotEqual(_, _)
        | CExpression::Not(_)
        | CExpression::And(_, _)
        | CExpression::Or(_, _) => Some(C0Type::Int32),
        CExpression::Add(left, right) => infer_c_add_type(left, right, variables),
        CExpression::Subtract(left, right) => infer_c_subtract_type(left, right, variables),
        CExpression::Multiply(left, right) | CExpression::Divide(left, right) => {
            let left = infer_c_expression_type(left, variables);
            let right = infer_c_expression_type(right, variables);
            arithmetic_result_type(left, right)
        }
        CExpression::Remainder(left, right)
        | CExpression::BitwiseAnd(left, right)
        | CExpression::BitwiseOr(left, right)
        | CExpression::BitwiseXor(left, right) => {
            let left = infer_c_expression_type(left, variables);
            let right = infer_c_expression_type(right, variables);
            match (left, right) {
                (Some(left), Some(right)) if type_is_scalar(left) && type_is_scalar(right) => {
                    Some(scalar_arithmetic_result_type(left, right))
                }
                _ => None,
            }
        }
        CExpression::ShiftLeft(left, right) | CExpression::ShiftRight(left, right) => {
            infer_c_shift_type(left, right, variables)
        }
        CExpression::BitwiseNot(expression) => infer_c_expression_type(expression, variables)
            .filter(|c_type| type_is_scalar(*c_type))
            .map(|c_type| scalar_arithmetic_result_type(c_type, c_type)),
        CExpression::Load(pointer) => {
            infer_c_expression_type(pointer, variables).and_then(pointer_element_type)
        }
        CExpression::TypedLoad { value_type, .. } => Some(match value_type {
            CType::Void => return None,
            CType::Int16 => C0Type::Int16,
            CType::Int32 => C0Type::Int32,
            CType::UInt8 => C0Type::UInt8,
            CType::UInt16 => C0Type::UInt16,
            CType::UInt32 => C0Type::UInt32,
            CType::Int64 => C0Type::Int64,
            CType::UInt64 => C0Type::UInt64,
            CType::Float32 => C0Type::Float32,
            CType::Float64 => C0Type::Float64,
            CType::Int32Pointer => C0Type::Int32Pointer,
            CType::UInt8Pointer => C0Type::UInt8Pointer,
            CType::Int16Pointer => C0Type::Int16Pointer,
            CType::UInt16Pointer => C0Type::UInt16Pointer,
            CType::UInt32Pointer => C0Type::UInt32Pointer,
            CType::Int64Pointer => C0Type::Int64Pointer,
            CType::UInt64Pointer => C0Type::UInt64Pointer,
            CType::Int16PointerPointer => C0Type::Int16PointerPointer,
            CType::UInt16PointerPointer => C0Type::UInt16PointerPointer,
            CType::Int32PointerPointer => C0Type::Int32PointerPointer,
            CType::UInt8PointerPointer => C0Type::UInt8PointerPointer,
            CType::UInt32PointerPointer => C0Type::UInt32PointerPointer,
            CType::Int64PointerPointer => C0Type::Int64PointerPointer,
            CType::UInt64PointerPointer => C0Type::UInt64PointerPointer,
            CType::Float32Pointer => C0Type::Float32Pointer,
            CType::Float64Pointer => C0Type::Float64Pointer,
            CType::Float32PointerPointer => C0Type::Float32PointerPointer,
            CType::Float64PointerPointer => C0Type::Float64PointerPointer,
            CType::FunctionPointer(signature) => C0Type::FunctionPointer(*signature),
            CType::Int32Array(length) => C0Type::Int32Array(*length),
            CType::UInt8Array(length) => C0Type::UInt8Array(*length),
            CType::Int16Array(length) => C0Type::Int16Array(*length),
            CType::UInt16Array(length) => C0Type::UInt16Array(*length),
            CType::UInt32Array(length) => C0Type::UInt32Array(*length),
            CType::Int64Array(length) => C0Type::Int64Array(*length),
            CType::UInt64Array(length) => C0Type::UInt64Array(*length),
            CType::Float32Array(length) => C0Type::Float32Array(*length),
            CType::Float64Array(length) => C0Type::Float64Array(*length),
        }),
        CExpression::Index(base, _) => {
            infer_c_expression_type(base, variables).and_then(pointer_element_type)
        }
    }
}

fn infer_add_expression_type(
    left: &ContractExpression,
    right: &ContractExpression,
    variables: &BTreeMap<String, C0Type>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    context: &str,
) -> Result<Option<C0Type>, ClickError> {
    let left = infer_contract_expression_type(left, variables, click_functions, context)?;
    let right = infer_contract_expression_type(right, variables, click_functions, context)?;
    Ok(pointer_arithmetic_type(left, right).or_else(|| arithmetic_result_type(left, right)))
}

fn infer_subtract_expression_type(
    left: &ContractExpression,
    right: &ContractExpression,
    variables: &BTreeMap<String, C0Type>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    context: &str,
) -> Result<Option<C0Type>, ClickError> {
    let left = infer_contract_expression_type(left, variables, click_functions, context)?;
    let right = infer_contract_expression_type(right, variables, click_functions, context)?;
    Ok(match (left, right) {
        (Some(left), Some(right)) if type_is_data_pointer(left) && type_is_scalar(right) => {
            Some(left)
        }
        _ => arithmetic_result_type(left, right),
    })
}

fn infer_c_add_type(
    left: &CExpression,
    right: &CExpression,
    variables: &BTreeMap<String, C0Type>,
) -> Option<C0Type> {
    let left = infer_c_expression_type(left, variables);
    let right = infer_c_expression_type(right, variables);
    pointer_arithmetic_type(left, right).or_else(|| arithmetic_result_type(left, right))
}

fn infer_c_subtract_type(
    left: &CExpression,
    right: &CExpression,
    variables: &BTreeMap<String, C0Type>,
) -> Option<C0Type> {
    let left = infer_c_expression_type(left, variables);
    let right = infer_c_expression_type(right, variables);
    match (left, right) {
        (Some(left), Some(right)) if type_is_data_pointer(left) && type_is_scalar(right) => {
            Some(left)
        }
        _ => arithmetic_result_type(left, right),
    }
}

fn pointer_arithmetic_type(left: Option<C0Type>, right: Option<C0Type>) -> Option<C0Type> {
    match (left, right) {
        (Some(left), Some(right)) if type_is_data_pointer(left) && type_is_scalar(right) => {
            Some(left)
        }
        (Some(left), Some(right)) if type_is_scalar(left) && type_is_data_pointer(right) => {
            Some(right)
        }
        _ => None,
    }
}

fn type_is_float(c_type: C0Type) -> bool {
    matches!(c_type, C0Type::Float32 | C0Type::Float64)
}

fn arithmetic_result_type(left: Option<C0Type>, right: Option<C0Type>) -> Option<C0Type> {
    match (left, right) {
        (Some(left), Some(right)) if type_is_arithmetic(left) && type_is_arithmetic(right) => {
            if matches!(left, C0Type::Float64) || matches!(right, C0Type::Float64) {
                Some(C0Type::Float64)
            } else if matches!(left, C0Type::Float32) || matches!(right, C0Type::Float32) {
                Some(C0Type::Float32)
            } else {
                Some(scalar_arithmetic_result_type(left, right))
            }
        }
        _ => None,
    }
}

fn infer_c_shift_type(
    left: &CExpression,
    right: &CExpression,
    variables: &BTreeMap<String, C0Type>,
) -> Option<C0Type> {
    let left_type = infer_c_expression_type(left, variables)?;
    let right_type = infer_c_expression_type(right, variables)?;
    if !type_is_scalar(left_type) || !type_is_scalar(right_type) {
        return None;
    }
    Some(match left_type {
        C0Type::UInt64 => C0Type::UInt64,
        C0Type::Int64 => C0Type::Int64,
        C0Type::UInt32 => C0Type::UInt32,
        _ => C0Type::Int32,
    })
}

fn infer_contract_shift_type(
    left: &ContractExpression,
    right: &ContractExpression,
    variables: &BTreeMap<String, C0Type>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    context: &str,
) -> Result<Option<C0Type>, ClickError> {
    let left_type = infer_contract_expression_type(left, variables, click_functions, context)?;
    let right_type = infer_contract_expression_type(right, variables, click_functions, context)?;
    Ok(match (left_type, right_type) {
        (Some(left), Some(right)) if type_is_scalar(left) && type_is_scalar(right) => {
            Some(match left {
                C0Type::UInt64 => C0Type::UInt64,
                C0Type::Int64 => C0Type::Int64,
                C0Type::UInt32 => C0Type::UInt32,
                _ => C0Type::Int32,
            })
        }
        _ => None,
    })
}

fn type_is_scalar(c_type: C0Type) -> bool {
    matches!(
        c_type,
        C0Type::Int16
            | C0Type::Int32
            | C0Type::UInt8
            | C0Type::UInt16
            | C0Type::UInt32
            | C0Type::Int64
            | C0Type::UInt64
    )
}

fn type_is_arithmetic(c_type: C0Type) -> bool {
    type_is_scalar(c_type) || type_is_float(c_type)
}

fn scalar_arithmetic_result_type(left: C0Type, right: C0Type) -> C0Type {
    if matches!(left, C0Type::UInt64) || matches!(right, C0Type::UInt64) {
        C0Type::UInt64
    } else if matches!(left, C0Type::Int64) || matches!(right, C0Type::Int64) {
        C0Type::Int64
    } else if matches!(left, C0Type::UInt32) || matches!(right, C0Type::UInt32) {
        C0Type::UInt32
    } else {
        C0Type::Int32
    }
}

fn type_is_data_pointer(c_type: C0Type) -> bool {
    matches!(
        c_type,
        C0Type::Int32Pointer
            | C0Type::Int16Pointer
            | C0Type::UInt8Pointer
            | C0Type::UInt16Pointer
            | C0Type::UInt32Pointer
            | C0Type::Int64Pointer
            | C0Type::UInt64Pointer
            | C0Type::Int16PointerPointer
            | C0Type::UInt16PointerPointer
            | C0Type::Int32PointerPointer
            | C0Type::UInt8PointerPointer
            | C0Type::UInt32PointerPointer
            | C0Type::Int64PointerPointer
            | C0Type::UInt64PointerPointer
            | C0Type::Int32Array(_)
            | C0Type::UInt8Array(_)
            | C0Type::Int16Array(_)
            | C0Type::UInt16Array(_)
            | C0Type::UInt32Array(_)
            | C0Type::Int64Array(_)
            | C0Type::UInt64Array(_)
    )
}

fn pointer_element_type(c_type: C0Type) -> Option<C0Type> {
    c_type.pointee_type()
}

fn validate_contract_segment_expression_types(
    segment: &ContractSegment,
    variables: &BTreeMap<String, C0Type>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    context: &str,
) -> Result<(), ClickError> {
    let _ = infer_contract_expression_type(
        &ContractExpression::CFragment(segment.base.clone()),
        variables,
        click_functions,
        context,
    )?;
    let _ = infer_contract_expression_type(
        &ContractExpression::CFragment(segment.start.clone()),
        variables,
        click_functions,
        context,
    )?;
    let _ = infer_contract_expression_type(
        &ContractExpression::CFragment(segment.end.clone()),
        variables,
        click_functions,
        context,
    )?;
    Ok(())
}

pub(super) fn validate_resource_clause(
    resource: &ResourceClause,
    resources: &BTreeMap<String, usize>,
    recursive_resources: &BTreeSet<String>,
    click_functions: &BTreeMap<String, usize>,
    click_function_types: &BTreeMap<String, ClickFunctionType>,
    variables: &BTreeMap<String, C0Type>,
    context: &str,
) -> Result<(), ClickError> {
    match resource {
        ResourceClause::ViewMemory(_) | ResourceClause::OwnMemory(_) => Ok(()),
        ResourceClause::MemoryAggregate { .. } => Ok(()),
        ResourceClause::Quantified { quantity, resource } => {
            validate_contract_expression_calls(quantity, click_functions, context)?;
            let actual =
                infer_contract_expression_type(quantity, variables, click_function_types, context)?;
            if actual != Some(C0Type::Int32) {
                return Err(ClickError::new(format!(
                    "declared resource quantity must have type int32 in {context}"
                )));
            }
            if !matches!(
                resource.as_ref(),
                ResourceClause::Declared {
                    access: ResourceAccessMode::Own,
                    name,
                    ..
                } if name != CResourceFact::ALLOCATION_RESOURCE_NAME
            ) {
                return Err(ClickError::new(format!(
                    "symbolic quantities require an owned user-declared resource in {context}"
                )));
            }
            if let ResourceClause::Declared { name, .. } = resource.as_ref()
                && recursive_resources.contains(name)
            {
                return Err(ClickError::new(format!(
                    "symbolic quantities for recursive composite resource `{name}` are not supported in {context}"
                )));
            }
            validate_resource_clause(
                resource,
                resources,
                recursive_resources,
                click_functions,
                click_function_types,
                variables,
                context,
            )
        }
        ResourceClause::Declared {
            name,
            arguments,
            parameter_types,
            ..
        } => {
            let Some(arity) = resources.get(name) else {
                return Err(ClickError::new(format!(
                    "unknown resource `{name}` in {context}"
                )));
            };
            if *arity != arguments.len() {
                return Err(ClickError::new(format!(
                    "resource `{name}` expects {arity} argument(s), got {} in {context}",
                    arguments.len()
                )));
            }
            if parameter_types.len() != arguments.len() {
                return Err(ClickError::new(format!(
                    "resource `{name}` has malformed argument type metadata in {context}"
                )));
            }
            for (index, argument) in arguments.iter().enumerate() {
                validate_contract_expression_calls(argument, click_functions, context)?;
                if let Some(actual) = infer_contract_expression_type(
                    argument,
                    variables,
                    click_function_types,
                    context,
                )? {
                    let expected = parameter_types[index];
                    if !resource_types_compatible(name, index, actual, expected) {
                        return Err(ClickError::new(format!(
                            "resource `{name}` argument {index} expects {}, got {} in {context}",
                            describe_c0_type(expected),
                            describe_c0_type(actual)
                        )));
                    }
                }
            }
            Ok(())
        }
    }
}

pub(super) fn validate_predicate_calls_in_proposition(
    proposition: &ClickProposition,
    predicates: &BTreeMap<String, usize>,
    click_functions: &BTreeMap<String, usize>,
    context: &str,
) -> Result<(), ClickError> {
    match proposition {
        ClickProposition::Comparison { left, right, .. } => {
            validate_contract_expression_calls(left, click_functions, context)?;
            validate_contract_expression_calls(right, click_functions, context)
        }
        ClickProposition::FloatClassification { expression, .. } => {
            validate_contract_expression_calls(expression, click_functions, context)
        }
        ClickProposition::Separate { left, right } => {
            validate_resource_subject_calls(left, click_functions, context)?;
            validate_resource_subject_calls(right, click_functions, context)
        }
        ClickProposition::Contains { parent, child } => {
            validate_resource_subject_calls(parent, click_functions, context)?;
            validate_resource_subject_calls(child, click_functions, context)
        }
        ClickProposition::Loadable { segment } => {
            validate_contract_segment_calls(segment, click_functions, context)
        }
        ClickProposition::Defined { expression } => {
            validate_contract_expression_calls(expression, click_functions, context)
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            validate_predicate_calls_in_proposition(left, predicates, click_functions, context)?;
            validate_predicate_calls_in_proposition(right, predicates, click_functions, context)
        }
        ClickProposition::Not(body)
        | ClickProposition::At {
            proposition: body, ..
        }
        | ClickProposition::ForAll { body, .. }
        | ClickProposition::Exists { body, .. } => {
            validate_predicate_calls_in_proposition(body, predicates, click_functions, context)
        }
        ClickProposition::RangeAll {
            start, end, body, ..
        }
        | ClickProposition::RangeAny {
            start, end, body, ..
        } => {
            validate_contract_expression_calls(start, click_functions, context)?;
            validate_contract_expression_calls(end, click_functions, context)?;
            validate_predicate_calls_in_proposition(body, predicates, click_functions, context)
        }
        ClickProposition::PredicateCall { name, arguments } => {
            let Some(arity) = predicates.get(name) else {
                return Err(ClickError::new(format!(
                    "unknown predicate `{name}` in {context}"
                )));
            };
            if *arity != arguments.len() {
                return Err(ClickError::new(format!(
                    "predicate `{name}` expects {arity} argument(s), got {} in {context}",
                    arguments.len()
                )));
            }
            for argument in arguments {
                validate_contract_expression_calls(argument, click_functions, context)?;
            }
            Ok(())
        }
    }
}

pub(super) fn validate_click_function_expression(
    expression: &ContractExpression,
    click_functions: &BTreeMap<String, usize>,
    context: &str,
) -> Result<(), ClickError> {
    if contains_old_expression(expression) {
        return Err(ClickError::new(format!(
            "`old(...)` is not available inside {context}"
        )));
    }
    if contains_at_expression(expression) {
        return Err(ClickError::new(format!(
            "`at(...)` is not available inside {context}"
        )));
    }
    validate_contract_expression_calls(expression, click_functions, context)
}

fn validate_contract_segment_calls(
    segment: &ContractSegment,
    click_functions: &BTreeMap<String, usize>,
    context: &str,
) -> Result<(), ClickError> {
    validate_contract_expression_calls(
        &ContractExpression::CFragment(segment.base.clone()),
        click_functions,
        context,
    )?;
    validate_contract_expression_calls(
        &ContractExpression::CFragment(segment.start.clone()),
        click_functions,
        context,
    )?;
    validate_contract_expression_calls(
        &ContractExpression::CFragment(segment.end.clone()),
        click_functions,
        context,
    )
}

fn validate_contract_expression_calls(
    expression: &ContractExpression,
    click_functions: &BTreeMap<String, usize>,
    context: &str,
) -> Result<(), ClickError> {
    match expression {
        ContractExpression::CFragment(_) | ContractExpression::CBinding(_) => Ok(()),
        ContractExpression::ResourceCount(resource) => match resource.as_ref() {
            ResourceClause::Declared { arguments, .. } => {
                for argument in arguments {
                    if !matches!(argument, ContractExpression::ResourceWildcard) {
                        validate_contract_expression_calls(argument, click_functions, context)?;
                    }
                }
                Ok(())
            }
            _ => Err(ClickError::new("`count(...)` expects a declared resource")),
        },
        ContractExpression::ResourceWildcard => Err(ClickError::new(
            "`_` is only valid inside a `count(...)` resource pattern",
        )),
        ContractExpression::Field { base, .. } => {
            validate_contract_expression_calls(base, click_functions, context)
        }
        ContractExpression::Old(body) => {
            validate_contract_expression_calls(body, click_functions, context)
        }
        ContractExpression::At { expression, .. } => {
            validate_contract_expression_calls(expression, click_functions, context)
        }
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
        | ContractExpression::Index(left, right) => {
            validate_contract_expression_calls(left, click_functions, context)?;
            validate_contract_expression_calls(right, click_functions, context)
        }
        ContractExpression::BitwiseNot(expression) => {
            validate_contract_expression_calls(expression, click_functions, context)
        }
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            validate_if_condition_proposition(condition, click_functions, context)?;
            validate_contract_expression_calls(then_branch, click_functions, context)?;
            validate_contract_expression_calls(else_branch, click_functions, context)
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            validate_contract_expression_calls(start, click_functions, context)?;
            validate_contract_expression_calls(end, click_functions, context)?;
            validate_contract_expression_calls(initial, click_functions, context)?;
            validate_contract_expression_calls(body, click_functions, context)
        }
        ContractExpression::Let { value, body, .. } => {
            validate_contract_expression_calls(value, click_functions, context)?;
            validate_contract_expression_calls(body, click_functions, context)
        }
        ContractExpression::Call { name, arguments } => {
            let Some(arity) = click_functions.get(name) else {
                return Err(ClickError::new(format!(
                    "unknown function `{name}` in {context}"
                )));
            };
            if *arity != arguments.len() {
                return Err(ClickError::new(format!(
                    "function `{name}` expects {arity} argument(s), got {} in {context}",
                    arguments.len()
                )));
            }
            for argument in arguments {
                validate_contract_expression_calls(argument, click_functions, context)?;
            }
            Ok(())
        }
    }
}

fn validate_resource_subject_calls(
    resource: &ResourceSubject,
    click_functions: &BTreeMap<String, usize>,
    context: &str,
) -> Result<(), ClickError> {
    match resource {
        ResourceSubject::Memory(segment) => {
            validate_contract_segment_calls(segment, click_functions, context)
        }
        ResourceSubject::Declared { arguments, .. } => {
            for argument in arguments {
                validate_contract_expression_calls(argument, click_functions, context)?;
            }
            Ok(())
        }
    }
}

fn validate_if_condition_proposition(
    proposition: &ClickProposition,
    click_functions: &BTreeMap<String, usize>,
    context: &str,
) -> Result<(), ClickError> {
    match proposition {
        ClickProposition::Comparison { left, right, .. } => {
            validate_contract_expression_calls(left, click_functions, context)?;
            validate_contract_expression_calls(right, click_functions, context)
        }
        ClickProposition::FloatClassification { expression, .. } => {
            validate_contract_expression_calls(expression, click_functions, context)
        }
        ClickProposition::Separate { left, right } => {
            validate_resource_subject_calls(left, click_functions, context)?;
            validate_resource_subject_calls(right, click_functions, context)
        }
        ClickProposition::Contains { parent, child } => {
            validate_resource_subject_calls(parent, click_functions, context)?;
            validate_resource_subject_calls(child, click_functions, context)
        }
        ClickProposition::Loadable { segment } => {
            validate_contract_segment_calls(segment, click_functions, context)
        }
        ClickProposition::Defined { expression } => {
            validate_contract_expression_calls(expression, click_functions, context)
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            validate_if_condition_proposition(left, click_functions, context)?;
            validate_if_condition_proposition(right, click_functions, context)
        }
        ClickProposition::Not(body)
        | ClickProposition::At {
            proposition: body, ..
        }
        | ClickProposition::ForAll { body, .. }
        | ClickProposition::Exists { body, .. } => {
            validate_if_condition_proposition(body, click_functions, context)
        }
        ClickProposition::RangeAll {
            start, end, body, ..
        }
        | ClickProposition::RangeAny {
            start, end, body, ..
        } => {
            validate_contract_expression_calls(start, click_functions, context)?;
            validate_contract_expression_calls(end, click_functions, context)?;
            validate_if_condition_proposition(body, click_functions, context)
        }
        ClickProposition::PredicateCall { name, .. } => Err(ClickError::new(format!(
            "predicate call `{name}` is not supported in `if` expression condition in {context}"
        ))),
    }
}
