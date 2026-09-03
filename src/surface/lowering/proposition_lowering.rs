use super::*;

pub(in crate::surface) struct KernelPropositionLowerer {
    values: BTreeMap<String, CValue>,
    array_refs: ClickArrayRefs,
    memory: CMemory,
    predicate_environment: PredicateEnvironment,
    click_function_environment: ClickFunctionEnvironment,
    resource_state: Option<CState>,
    assumptions: PureFactContext,
    active_functions: BTreeSet<String>,
    next_variable: u64,
}

impl KernelPropositionLowerer {
    pub(in crate::surface) fn new(
        values: BTreeMap<String, CValue>,
        array_refs: ClickArrayRefs,
        memory: CMemory,
        predicate_environment: &PredicateEnvironment,
        click_function_environment: &ClickFunctionEnvironment,
    ) -> Self {
        Self {
            values,
            array_refs,
            memory,
            predicate_environment: predicate_environment.clone(),
            click_function_environment: click_function_environment.clone(),
            resource_state: None,
            assumptions: PureFactContext::new(),
            active_functions: BTreeSet::new(),
            next_variable: 2_000_000,
        }
    }

    pub(in crate::surface) fn with_resource_state(mut self, state: CState) -> Self {
        self.resource_state = Some(state);
        self
    }

    pub(in crate::surface) fn with_assumptions(mut self, assumptions: PureFactContext) -> Self {
        self.assumptions = assumptions;
        self
    }

    pub(in crate::surface) fn with_active_functions(
        mut self,
        names: impl IntoIterator<Item = String>,
    ) -> Self {
        self.active_functions.extend(names);
        self
    }

    pub(in crate::surface) fn lower_requirement_proposition(
        &mut self,
        proposition: &ClickProposition,
    ) -> Result<Proposition, ClickError> {
        match proposition {
            ClickProposition::Comparison {
                left,
                operator,
                right,
            } => {
                let left = self.lower_requirement_value(left)?;
                let right = self.lower_requirement_value(right)?;
                comparison_proposition(left, *operator, right)
            }
            ClickProposition::Separate { left, right } => {
                let left = self.lower_requirement_resource_subject(left)?;
                let right = self.lower_requirement_resource_subject(right)?;
                Ok(Proposition::CResourceSeparate { left, right })
            }
            ClickProposition::Contains { parent, child } => {
                let parent = self.lower_requirement_resource_subject(parent)?;
                let child = self.lower_requirement_resource_subject(child)?;
                Ok(Proposition::CResourceContains { parent, child })
            }
            ClickProposition::Loadable { segment } => {
                let segment = self.lower_requirement_segment(segment)?;
                loadable_segment_prop(&self.memory, segment)
            }
            ClickProposition::Defined { expression } => {
                let expression = contract_expression_to_c_fragment(expression).ok_or_else(|| {
                    ClickError::new(
                        "`defined(...)` currently requires an expression without `old`, `at`, folds, lets, or Click function calls",
                    )
                })?;
                let state = self.values.iter().fold(
                    self.resource_state
                        .clone()
                        .unwrap_or_else(|| CState::new().with_memory(self.memory.clone())),
                    |state, (name, value)| state.with_local(name.clone(), value.clone()),
                );
                c_expression_definedness_proposition(&state, &expression).map_err(|limit| {
                    ClickError::new(format!(
                        "`defined(...)` elaboration hit execution limit {limit:?}"
                    ))
                })
            }
            ClickProposition::At { .. } => Err(ClickError::new(
                "`at(...)` propositions are not available in function requirements",
            )),
            ClickProposition::And(left, right) => {
                let left = self.lower_requirement_proposition(left)?;
                let outer_assumptions = self.assumptions.clone();
                self.assumptions = self.assumptions.clone().assume_proposition(left.clone());
                let right = self.lower_requirement_proposition(right);
                self.assumptions = outer_assumptions;
                Ok(Proposition::And(Box::new(left), Box::new(right?)))
            }
            ClickProposition::Or(left, right) => Ok(Proposition::Or(
                Box::new(self.lower_requirement_proposition(left)?),
                Box::new(self.lower_requirement_proposition(right)?),
            )),
            ClickProposition::Not(body) => Ok(Proposition::Not(Box::new(
                self.lower_requirement_proposition(body)?,
            ))),
            ClickProposition::Implies(left, right) => {
                let left = self.lower_requirement_proposition(left)?;
                let outer_assumptions = self.assumptions.clone();
                self.assumptions = self.assumptions.clone().assume_proposition(left.clone());
                let right = self.lower_requirement_proposition(right);
                self.assumptions = outer_assumptions;
                Ok(Proposition::Implies(Box::new(left), Box::new(right?)))
            }
            ClickProposition::ForAll { c_type, name, body } => {
                if *c_type != C0Type::Int32 {
                    return Err(ClickError::new("only `forall (...: int32)` is supported"));
                }
                let variable = Variable(self.next_variable);
                self.next_variable += 1;
                let previous = self.values.insert(
                    name.clone(),
                    CValue::Int32(Bitvector32Term::Variable(variable)),
                );
                let body = self.lower_requirement_proposition(body)?;
                match previous {
                    Some(value) => {
                        self.values.insert(name.clone(), value);
                    }
                    None => {
                        self.values.remove(name);
                    }
                }
                Ok(Proposition::ForAll {
                    var: variable,
                    sort: Sort::CInt32,
                    body: Box::new(body),
                })
            }
            ClickProposition::Exists { c_type, name, body } => {
                if *c_type != C0Type::Int32 {
                    return Err(ClickError::new("only `exists (...: int32)` is supported"));
                }
                let variable = Variable(self.next_variable);
                self.next_variable += 1;
                let previous = self.values.insert(
                    name.clone(),
                    CValue::Int32(Bitvector32Term::Variable(variable)),
                );
                let body = self.lower_requirement_proposition(body)?;
                match previous {
                    Some(value) => {
                        self.values.insert(name.clone(), value);
                    }
                    None => {
                        self.values.remove(name);
                    }
                }
                Ok(Proposition::Exists {
                    name: name.clone(),
                    var: variable,
                    sort: Sort::CInt32,
                    body: Box::new(body),
                })
            }
            ClickProposition::RangeAll {
                start,
                end,
                item,
                body,
            } => {
                let start = int32_term_value(
                    self.lower_requirement_value(start)?,
                    "range `all` start bound",
                )
                .map_err(ClickError::new)?;
                let end =
                    int32_term_value(self.lower_requirement_value(end)?, "range `all` end bound")
                        .map_err(ClickError::new)?;
                let variable = Variable(self.next_variable);
                self.next_variable += 1;
                let item_bits = Bitvector32Term::Variable(variable);
                let item_value = CValue::Int32(item_bits.clone());
                let outer_values = self.values.clone();
                self.values.insert(item.clone(), item_value.clone());
                let outer_assumptions = self.assumptions.clone();
                self.assumptions =
                    self.assumptions
                        .clone()
                        .assume_proposition(range_membership_proposition(
                            start.clone(),
                            item_bits.clone(),
                            end.clone(),
                        ));
                let body = match self.lower_requirement_proposition(body) {
                    Ok(body) => body,
                    Err(error) => {
                        self.assumptions = outer_assumptions;
                        self.values = outer_values;
                        return Err(error);
                    }
                };
                self.assumptions = outer_assumptions;
                self.values = outer_values;
                Ok(bounded_forall_int32(variable, start, item_bits, end, body))
            }
            ClickProposition::RangeAny {
                start,
                end,
                item,
                body,
            } => {
                let start = int32_term_value(
                    self.lower_requirement_value(start)?,
                    "range `any` start bound",
                )
                .map_err(ClickError::new)?;
                let end =
                    int32_term_value(self.lower_requirement_value(end)?, "range `any` end bound")
                        .map_err(ClickError::new)?;
                let outer_values = self.values.clone();
                let outer_assumptions = self.assumptions.clone();
                let range_start = start.clone();
                let range_end = end.clone();
                match (
                    concrete_bound_from_term(&start, "any", "start"),
                    concrete_bound_from_term(&end, "any", "end"),
                ) {
                    (Ok(start), Ok(end)) => {
                        let mut proposition = false_proposition();
                        for index in concrete_fold_range(start, end).map_err(ClickError::new)? {
                            self.values = outer_values.clone();
                            self.values.insert(
                                item.clone(),
                                CValue::Int32(Bitvector32Term::Constant(index as u32)),
                            );
                            self.assumptions = outer_assumptions.clone().assume_proposition(
                                range_membership_proposition(
                                    range_start.clone(),
                                    Bitvector32Term::Constant(index as u32),
                                    range_end.clone(),
                                ),
                            );
                            let body = match self.lower_requirement_proposition(body) {
                                Ok(body) => body,
                                Err(error) => {
                                    self.assumptions = outer_assumptions;
                                    self.values = outer_values;
                                    return Err(error);
                                }
                            };
                            self.assumptions = outer_assumptions.clone();
                            proposition = disjunction(proposition, body);
                        }
                        self.assumptions = outer_assumptions;
                        self.values = outer_values;
                        Ok(proposition)
                    }
                    _ => {
                        let variable = Variable(self.next_variable);
                        self.next_variable += 1;
                        let item_bits = Bitvector32Term::Variable(variable);
                        let item_value = CValue::Int32(item_bits.clone());
                        self.values.insert(item.clone(), item_value.clone());
                        self.assumptions = self.assumptions.clone().assume_proposition(
                            range_membership_proposition(
                                start.clone(),
                                item_bits.clone(),
                                end.clone(),
                            ),
                        );
                        let body = match self.lower_requirement_proposition(body) {
                            Ok(body) => body,
                            Err(error) => {
                                self.assumptions = outer_assumptions;
                                self.values = outer_values;
                                return Err(error);
                            }
                        };
                        self.assumptions = outer_assumptions;
                        self.values = outer_values;
                        Ok(bounded_exists_int32(
                            item.clone(),
                            variable,
                            start,
                            item_bits,
                            end,
                            body,
                        ))
                    }
                }
            }
            ClickProposition::PredicateCall { name, arguments } => {
                let definition = self
                    .predicate_environment
                    .get(name)
                    .ok_or_else(|| ClickError::new(format!("unknown predicate `{name}`")))?;
                let state = self
                    .resource_state
                    .clone()
                    .unwrap_or_else(|| CState::new().with_memory(self.memory.clone()));
                let recorded_snapshots = RecordedSnapshots::new();
                let lowered_arguments = lower_predicate_call_arguments_with_environment(
                    definition,
                    arguments,
                    &self.values,
                    &self.array_refs,
                    &state,
                    &state,
                    None,
                    &self.assumptions,
                    &self.predicate_environment,
                    &self.click_function_environment,
                    &recorded_snapshots,
                    &mut self.active_functions,
                )
                .map_err(ClickError::new)?;
                Ok(Proposition::Predicate {
                    name: name.clone(),
                    arguments: lowered_arguments,
                })
            }
        }
    }

    fn lower_requirement_segment(
        &mut self,
        segment: &ContractSegment,
    ) -> Result<EvaluatedContractSegment, ClickError> {
        if segment.state != ContractSegmentState::Current {
            return Err(ClickError::new(
                "`old(...)` is not available in memory resource subjects",
            ));
        }
        let base = self.lower_requirement_c_expression(&segment.base)?;
        let CValue::Pointer(base) = base else {
            return Err(ClickError::new(
                "segment base did not evaluate to a pointer",
            ));
        };
        let start = self.lower_requirement_c_expression(&segment.start)?;
        let CValue::Int32(start) = start else {
            return Err(ClickError::new("segment start did not evaluate to int32"));
        };
        let end = self.lower_requirement_c_expression(&segment.end)?;
        let CValue::Int32(end) = end else {
            return Err(ClickError::new("segment end did not evaluate to int32"));
        };

        Ok(EvaluatedContractSegment {
            source: segment.clone(),
            base,
            start,
            end,
            element_width: contract_segment_element_width_from_array_refs(
                &self.array_refs,
                segment,
            )
            .unwrap_or(4),
        })
    }

    fn lower_requirement_resource_subject(
        &mut self,
        resource: &ResourceSubject,
    ) -> Result<CResource, ClickError> {
        match resource {
            ResourceSubject::Memory(segment) => {
                let range = self.lower_requirement_segment(segment)?;
                Ok(CResource::Memory(CMemoryRange::new_with_element_width(
                    range.base,
                    range.start,
                    range.end,
                    range.element_width,
                )))
            }
            ResourceSubject::Declared {
                kind,
                name,
                arguments,
                parameter_types,
            } => {
                if arguments.len() != parameter_types.len() {
                    return Err(ClickError::new(format!(
                        "resource `{name}` has malformed argument type metadata"
                    )));
                }
                let mut values = Vec::new();
                for (index, (argument, parameter_type)) in
                    arguments.iter().zip(parameter_types).enumerate()
                {
                    let value = self.lower_requirement_value(argument)?;
                    if !c_value_matches_click_type(&value, *parameter_type) {
                        return Err(ClickError::new(format!(
                            "resource `{name}` argument {index} evaluated to {value:?}, which does not match {:?}",
                            parameter_type
                        )));
                    }
                    values.push(value);
                }
                Ok(match kind {
                    ResourceKind::Composite => CResource::Composite {
                        name: name.clone(),
                        arguments: values,
                    },
                    ResourceKind::Token => CResource::Token {
                        name: name.clone(),
                        arguments: values,
                    },
                })
            }
        }
    }

    fn lower_requirement_value(
        &mut self,
        expression: &ContractExpression,
    ) -> Result<CValue, ClickError> {
        match expression {
            ContractExpression::CFragment(expression)
            | ContractExpression::Field {
                lowered: expression,
                ..
            } => self.lower_requirement_c_expression(expression),
            ContractExpression::CBinding(name) => {
                self.lower_requirement_c_expression(&CExpression::Variable(name.clone()))
            }
            ContractExpression::ResourceCount(resource) => {
                let ResourceClause::Declared {
                    name, arguments, ..
                } = resource.as_ref()
                else {
                    return Err(ClickError::new("`count(...)` expects a declared resource"));
                };
                let values = arguments
                    .iter()
                    .map(|argument| match argument {
                        ContractExpression::ResourceWildcard => Ok(None),
                        argument => self.lower_requirement_value(argument).map(Some),
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let count = self
                    .resource_state
                    .as_ref()
                    .map(|state| state.counted_population_sum(name, &values, &self.assumptions))
                    .unwrap_or(Bitvector32Term::Constant(0));
                Ok(CValue::Int32(count))
            }
            ContractExpression::ResourceWildcard => Err(ClickError::new(
                "`_` is only valid inside a `count(...)` resource pattern",
            )),
            ContractExpression::Old(_) => Err(ClickError::new(
                "`old(...)` is not available in `requires` clauses",
            )),
            ContractExpression::At { .. } => Err(ClickError::new(
                "`at(...)` is not available in `requires` clauses",
            )),
            ContractExpression::Add(left, right) => {
                let left = self.lower_requirement_value(left)?;
                let right = self.lower_requirement_value(right)?;
                lower_contract_add(left, right)
            }
            ContractExpression::Subtract(left, right) => {
                let left = self.lower_requirement_value(left)?;
                let right = self.lower_requirement_value(right)?;
                lower_contract_subtract(left, right)
            }
            ContractExpression::Multiply(left, right) => {
                let left = self.lower_requirement_value(left)?;
                let right = self.lower_requirement_value(right)?;
                lower_contract_multiply(left, right)
            }
            ContractExpression::Divide(left, right) => {
                let left = self.lower_requirement_value(left)?;
                let right = self.lower_requirement_value(right)?;
                lower_contract_divide(left, right)
            }
            ContractExpression::Remainder(left, right) => {
                let left = self.lower_requirement_value(left)?;
                let right = self.lower_requirement_value(right)?;
                lower_contract_remainder(left, right)
            }
            ContractExpression::ShiftLeft(left, right) => {
                let left = self.lower_requirement_value(left)?;
                let right = self.lower_requirement_value(right)?;
                lower_contract_shift_left(left, right)
            }
            ContractExpression::ShiftRight(left, right) => {
                let left = self.lower_requirement_value(left)?;
                let right = self.lower_requirement_value(right)?;
                lower_contract_shift_right(left, right)
            }
            ContractExpression::BitwiseAnd(left, right) => {
                let left = self.lower_requirement_value(left)?;
                let right = self.lower_requirement_value(right)?;
                lower_contract_bitwise_binary(left, right, "&", bitvector32_and)
            }
            ContractExpression::BitwiseOr(left, right) => {
                let left = self.lower_requirement_value(left)?;
                let right = self.lower_requirement_value(right)?;
                lower_contract_bitwise_binary(left, right, "|", bitvector32_or)
            }
            ContractExpression::BitwiseXor(left, right) => {
                let left = self.lower_requirement_value(left)?;
                let right = self.lower_requirement_value(right)?;
                lower_contract_bitwise_binary(left, right, "^", bitvector32_xor)
            }
            ContractExpression::BitwiseNot(expression) => {
                let value = self.lower_requirement_value(expression)?;
                lower_contract_bitwise_not(value)
            }
            ContractExpression::Index(base, index) => {
                let state = self
                    .resource_state
                    .clone()
                    .unwrap_or_else(|| CState::new().with_memory(self.memory.clone()));
                let recorded_snapshots = RecordedSnapshots::new();
                let array_ref = evaluate_contract_array_ref_with_environment(
                    &self.values,
                    &self.array_refs,
                    &state,
                    &state,
                    None,
                    &self.assumptions,
                    base,
                    &self.predicate_environment,
                    &self.click_function_environment,
                    &recorded_snapshots,
                    &mut self.active_functions,
                )
                .map_err(ClickError::new)?;
                let index = self.lower_requirement_value(index)?;
                let CValue::Int32(index) = index else {
                    return Err(ClickError::new(format!(
                        "array index did not evaluate to int32: `{index:?}`"
                    )));
                };
                let element_type = array_ref.element_type;
                let pointer =
                    offset_pointer_by_elements(array_ref.pointer, index, element_type.byte_width());
                evaluate_contract_memory_load_with_resources(
                    &array_ref.memory,
                    self.resource_state.as_ref().map(CState::resources),
                    pointer,
                    element_type,
                    &self.assumptions,
                )
                .map_err(ClickError::new)
            }
            ContractExpression::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let condition = self.lower_requirement_proposition(condition)?;
                if self.assumptions.proves(&condition) {
                    return self.lower_requirement_value(then_branch);
                }
                if assumptions_prove_proposition_false(&self.assumptions, &condition) {
                    return self.lower_requirement_value(else_branch);
                }

                let then_value = self.lower_requirement_value(then_branch)?;
                let else_value = self.lower_requirement_value(else_branch)?;
                conditional_contract_value(&condition, then_value, else_value)
                    .map_err(ClickError::new)
            }
            ContractExpression::RangeFold {
                start,
                end,
                initial,
                accumulator,
                item,
                body,
            } => {
                let start = int32_term_value(self.lower_requirement_value(start)?, "fold start")
                    .map_err(ClickError::new)?;
                let end = int32_term_value(self.lower_requirement_value(end)?, "fold end")
                    .map_err(ClickError::new)?;
                let mut value = self.lower_requirement_value(initial)?;
                let outer_values = self.values.clone();
                match (
                    concrete_bound_from_term(&start, "fold", "start"),
                    concrete_bound_from_term(&end, "fold", "end"),
                ) {
                    (Ok(start), Ok(end)) => {
                        for index in concrete_fold_range(start, end).map_err(ClickError::new)? {
                            self.values = outer_values.clone();
                            self.values.insert(accumulator.clone(), value);
                            self.values.insert(
                                item.clone(),
                                CValue::Int32(Bitvector32Term::Constant(index as u32)),
                            );
                            match self.lower_requirement_value(body) {
                                Ok(next) => value = next,
                                Err(error) => {
                                    self.values = outer_values;
                                    return Err(error);
                                }
                            }
                        }
                        self.values = outer_values;
                        Ok(value)
                    }
                    _ => {
                        self.values = outer_values.clone();
                        self.values.insert(accumulator.clone(), value.clone());
                        self.values.insert(
                            item.clone(),
                            CValue::Int32(Bitvector32Term::Variable(fold_bound_variable(item, 1))),
                        );
                        self.values.insert(
                            accumulator.clone(),
                            CValue::Int32(Bitvector32Term::Variable(fold_bound_variable(
                                accumulator,
                                0,
                            ))),
                        );
                        let body_value = match self.lower_requirement_value(body) {
                            Ok(body_value) => body_value,
                            Err(error) => {
                                self.values = outer_values;
                                return Err(error);
                            }
                        };
                        self.values = outer_values;
                        symbolic_range_fold_value(start, end, value, accumulator, item, body_value)
                            .map_err(ClickError::new)
                    }
                }
            }
            ContractExpression::Let {
                name,
                c_type,
                value,
                body,
            } => {
                let value = self.lower_requirement_value(value)?;
                let value =
                    checked_contract_let_value(value, *c_type, name).map_err(ClickError::new)?;
                let outer_values = self.values.clone();
                self.values.insert(name.clone(), value);
                let body_value = self.lower_requirement_value(body);
                self.values = outer_values;
                body_value
            }
            ContractExpression::Call { name, arguments } => {
                let state = CState::new().with_memory(self.memory.clone());
                let recorded_snapshots = RecordedSnapshots::new();
                evaluate_click_function_call(
                    &self.click_function_environment.clone(),
                    name,
                    arguments,
                    &self.values,
                    &self.array_refs,
                    &state,
                    &state,
                    None,
                    &self.assumptions,
                    &self.predicate_environment.clone(),
                    &recorded_snapshots,
                    &mut self.active_functions,
                )
                .map_err(ClickError::new)
            }
        }
    }

    pub(in crate::surface) fn lower_requirement_c_expression(
        &self,
        expression: &CExpression,
    ) -> Result<CValue, ClickError> {
        match expression {
            CExpression::Value(value) => Ok(value.clone()),
            CExpression::Variable(name) => {
                self.values.get(name).cloned().ok_or_else(|| {
                    ClickError::new(format!("unknown requirement variable `{name}`"))
                })
            }
            CExpression::Add(left, right) => lower_contract_add(
                self.lower_requirement_c_expression(left)?,
                self.lower_requirement_c_expression(right)?,
            ),
            CExpression::Subtract(left, right) => lower_contract_subtract(
                self.lower_requirement_c_expression(left)?,
                self.lower_requirement_c_expression(right)?,
            ),
            CExpression::Multiply(left, right) => lower_contract_multiply(
                self.lower_requirement_c_expression(left)?,
                self.lower_requirement_c_expression(right)?,
            ),
            CExpression::Divide(left, right) => lower_contract_divide(
                self.lower_requirement_c_expression(left)?,
                self.lower_requirement_c_expression(right)?,
            ),
            CExpression::Remainder(left, right) => lower_contract_remainder(
                self.lower_requirement_c_expression(left)?,
                self.lower_requirement_c_expression(right)?,
            ),
            CExpression::ShiftLeft(left, right) => lower_contract_shift_left(
                self.lower_requirement_c_expression(left)?,
                self.lower_requirement_c_expression(right)?,
            ),
            CExpression::ShiftRight(left, right) => lower_contract_shift_right(
                self.lower_requirement_c_expression(left)?,
                self.lower_requirement_c_expression(right)?,
            ),
            CExpression::BitwiseAnd(left, right) => lower_contract_bitwise_binary(
                self.lower_requirement_c_expression(left)?,
                self.lower_requirement_c_expression(right)?,
                "&",
                bitvector32_and,
            ),
            CExpression::BitwiseOr(left, right) => lower_contract_bitwise_binary(
                self.lower_requirement_c_expression(left)?,
                self.lower_requirement_c_expression(right)?,
                "|",
                bitvector32_or,
            ),
            CExpression::BitwiseXor(left, right) => lower_contract_bitwise_binary(
                self.lower_requirement_c_expression(left)?,
                self.lower_requirement_c_expression(right)?,
                "^",
                bitvector32_xor,
            ),
            CExpression::BitwiseNot(expression) => {
                lower_contract_bitwise_not(self.lower_requirement_c_expression(expression)?)
            }
            CExpression::Load(pointer) => {
                let pointer = self.lower_requirement_c_expression(pointer)?;
                let CValue::Pointer(pointer) = pointer else {
                    return Err(ClickError::new("field load base is not a pointer"));
                };
                evaluate_contract_memory_load_from_memory(
                    &self.memory,
                    pointer,
                    CType::Int32,
                    &self.assumptions,
                )
                .map_err(ClickError::new)
            }
            CExpression::TypedLoad {
                pointer,
                value_type: CType::Int32Array(_) | CType::UInt8Array(_),
            } => self.lower_requirement_c_expression(pointer),
            CExpression::TypedLoad {
                pointer,
                value_type,
            } => {
                let pointer = self.lower_requirement_c_expression(pointer)?;
                let CValue::Pointer(pointer) = pointer else {
                    return Err(ClickError::new("field load base is not a pointer"));
                };
                evaluate_contract_memory_load_from_memory(
                    &self.memory,
                    pointer,
                    *value_type,
                    &self.assumptions,
                )
                .map_err(ClickError::new)
            }
            CExpression::PointerOffsetBytes { pointer, bytes } => {
                let pointer = self.lower_requirement_c_expression(pointer)?;
                let CValue::Pointer(pointer) = pointer else {
                    return Err(ClickError::new(
                        "byte-offset expression base is not a pointer",
                    ));
                };
                Ok(CValue::Pointer(pointer.offset_by_bytes(*bytes)))
            }
            _ => Err(ClickError::new(format!(
                "unsupported expression in `requires` proposition: `{expression:?}`"
            ))),
        }
    }
}

pub(in crate::surface) fn comparison_proposition(
    left: CValue,
    operator: ComparisonOperator,
    right: CValue,
) -> Result<Proposition, ClickError> {
    let pointer_and_null = match (&left, &right) {
        (CValue::Pointer(pointer), CValue::Int32(Bitvector32Term::Constant(0))) => {
            Some((pointer.clone(), Pointer::null()))
        }
        (CValue::Int32(Bitvector32Term::Constant(0)), CValue::Pointer(pointer)) => {
            Some((Pointer::null(), pointer.clone()))
        }
        _ => None,
    };
    if let Some((left, right)) = pointer_and_null {
        let value = match operator {
            ComparisonOperator::Equal => true,
            ComparisonOperator::NotEqual => false,
            _ => {
                return Err(ClickError::new(
                    "pointer propositions support only `==` and `!=`",
                ));
            }
        };
        return Ok(Proposition::ConditionIs(
            ConditionTerm::pointer_equal(left, right),
            value,
        ));
    }
    if let (CValue::Pointer(left), CValue::Pointer(right)) = (&left, &right) {
        let value = match operator {
            ComparisonOperator::Equal => true,
            ComparisonOperator::NotEqual => false,
            _ => {
                return Err(ClickError::new(
                    "pointer propositions support only `==` and `!=`",
                ));
            }
        };
        return Ok(Proposition::ConditionIs(
            ConditionTerm::pointer_equal(left.clone(), right.clone()),
            value,
        ));
    }
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        let Some((condition, value)) = comparison_condition(left_term, operator, right_term) else {
            return Err(ClickError::new("unsupported proposition comparison"));
        };
        Ok(Proposition::ConditionIs(condition, value))
    } else {
        Err(ClickError::new(format!(
            "cannot compare `{left:?}` and `{right:?}` in proposition"
        )))
    }
}

pub(in crate::surface) fn proposition_as_single_condition(
    proposition: &Proposition,
) -> Option<(ConditionTerm, bool)> {
    match proposition {
        Proposition::ConditionIs(condition, value) => Some((condition.clone(), *value)),
        Proposition::Not(body) => {
            let Proposition::ConditionIs(condition, value) = body.as_ref() else {
                return None;
            };
            Some((condition.clone(), !*value))
        }
        _ => None,
    }
}

pub(in crate::surface) fn assumptions_prove_proposition_false(
    assumptions: &PureFactContext,
    proposition: &Proposition,
) -> bool {
    match proposition {
        Proposition::ConditionIs(condition, value) => {
            assumptions.proves(&Proposition::ConditionIs(condition.clone(), !*value))
        }
        _ => assumptions.proves(&Proposition::Not(Box::new(proposition.clone()))),
    }
}

pub(in crate::surface) fn conditional_contract_value(
    proposition: &Proposition,
    then_value: CValue,
    else_value: CValue,
) -> Result<CValue, String> {
    if then_value == else_value {
        return Ok(then_value);
    }

    let Some((condition, expected)) = proposition_as_single_condition(proposition) else {
        return Err(
            "symbolic `if` expressions currently require a single comparison condition".to_string(),
        );
    };

    let (CValue::Int32(then_term), CValue::Int32(else_term)) = (then_value, else_value) else {
        return Err(
            "symbolic `if` expressions currently support only int32 branch values".to_string(),
        );
    };

    let (then_term, else_term) = if expected {
        (then_term, else_term)
    } else {
        (else_term, then_term)
    };
    Ok(CValue::Int32(Bitvector32Term::if_then_else(
        condition, then_term, else_term,
    )))
}

pub(in crate::surface) fn true_proposition() -> Proposition {
    Proposition::ConditionIs(ConditionTerm::Constant(true), true)
}

pub(in crate::surface) fn false_proposition() -> Proposition {
    Proposition::ConditionIs(ConditionTerm::Constant(false), true)
}

pub(in crate::surface) fn conjunction(left: Proposition, right: Proposition) -> Proposition {
    match (&left, &right) {
        (Proposition::ConditionIs(ConditionTerm::Constant(true), true), _) => right,
        (_, Proposition::ConditionIs(ConditionTerm::Constant(true), true)) => left,
        (Proposition::ConditionIs(ConditionTerm::Constant(false), true), _)
        | (_, Proposition::ConditionIs(ConditionTerm::Constant(false), true)) => {
            false_proposition()
        }
        _ => Proposition::And(Box::new(left), Box::new(right)),
    }
}

pub(in crate::surface) fn disjunction(left: Proposition, right: Proposition) -> Proposition {
    match (&left, &right) {
        (Proposition::ConditionIs(ConditionTerm::Constant(false), true), _) => right,
        (_, Proposition::ConditionIs(ConditionTerm::Constant(false), true)) => left,
        (Proposition::ConditionIs(ConditionTerm::Constant(true), true), _)
        | (_, Proposition::ConditionIs(ConditionTerm::Constant(true), true)) => true_proposition(),
        _ => Proposition::Or(Box::new(left), Box::new(right)),
    }
}

pub(in crate::surface) fn range_membership_proposition(
    start: Bitvector32Term,
    item: Bitvector32Term,
    end: Bitvector32Term,
) -> Proposition {
    conjunction(
        Proposition::ConditionIs(signed_less_equal(start, item.clone()), true),
        Proposition::ConditionIs(signed_less_than(item, end), true),
    )
}

pub(in crate::surface) fn bounded_forall_int32(
    variable: Variable,
    start: Bitvector32Term,
    item: Bitvector32Term,
    end: Bitvector32Term,
    body: Proposition,
) -> Proposition {
    Proposition::ForAll {
        var: variable,
        sort: Sort::CInt32,
        body: Box::new(Proposition::Implies(
            Box::new(range_membership_proposition(start, item, end)),
            Box::new(body),
        )),
    }
}

pub(in crate::surface) fn bounded_exists_int32(
    name: String,
    variable: Variable,
    start: Bitvector32Term,
    item: Bitvector32Term,
    end: Bitvector32Term,
    body: Proposition,
) -> Proposition {
    Proposition::Exists {
        name,
        var: variable,
        sort: Sort::CInt32,
        body: Box::new(conjunction(
            range_membership_proposition(start, item, end),
            body,
        )),
    }
}

pub(in crate::surface) fn spec_range_membership_proposition(
    start: SpecExpression,
    item: SpecExpression,
    end: SpecExpression,
) -> SpecProposition {
    SpecProposition::And(
        Box::new(SpecProposition::Comparison {
            left: start,
            operator: CComparisonOperator::LessEqual,
            right: item.clone(),
        }),
        Box::new(SpecProposition::Comparison {
            left: item,
            operator: CComparisonOperator::LessThan,
            right: end,
        }),
    )
}

pub(in crate::surface) fn int32_term_value(
    value: CValue,
    label: &str,
) -> Result<Bitvector32Term, String> {
    let CValue::Int32(bits) = value else {
        return Err(format!("`{label}` is not int32"));
    };
    Ok(simp_bitvector(&bits))
}

pub(in crate::surface) fn promoted_int32_term(value: &CValue) -> Option<Bitvector32Term> {
    match value {
        CValue::Int32(bits) | CValue::UInt8(bits) => Some(simp_bitvector(bits)),
        CValue::Void | CValue::Pointer(_) => None,
    }
}

pub(in crate::surface) fn concrete_fold_range(
    start: i32,
    end: i32,
) -> Result<std::ops::Range<i32>, String> {
    let length = i64::from(end) - i64::from(start);
    if length <= 0 {
        return Ok(start..start);
    }
    if length > MAX_CONCRETE_RANGE_FOLD_STEPS {
        return Err(format!(
            "`fold` range has {length} iterations; the current concrete unroll limit is {MAX_CONCRETE_RANGE_FOLD_STEPS}"
        ));
    }
    Ok(start..end)
}

pub(in crate::surface) fn concrete_bound_from_term(
    term: &Bitvector32Term,
    construct: &str,
    label: &str,
) -> Result<i32, String> {
    let term = simp_bitvector(term);
    let Bitvector32Term::Constant(value) = term else {
        return Err(format!(
            "symbolic `{construct}` {label} bounds are not supported yet"
        ));
    };
    Ok(value as i32)
}

pub(in crate::surface) fn fold_bound_variable(name: &str, salt: u64) -> Variable {
    let mut hash = 0xcbf2_9ce4_8422_2325_u64 ^ salt;
    for byte in name.bytes() {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x1000_0000_01b3);
    }
    Variable(3_000_000 + (hash % 1_000_000_000))
}

pub(in crate::surface) fn symbolic_range_fold_value(
    start: Bitvector32Term,
    end: Bitvector32Term,
    initial: CValue,
    accumulator: &str,
    item: &str,
    body_value: CValue,
) -> Result<CValue, String> {
    let initial = int32_term_value(initial, "fold initial value")?;
    let body = int32_term_value(body_value, "fold body value")?;
    Ok(CValue::Int32(Bitvector32Term::range_fold(
        start,
        end,
        initial,
        fold_bound_variable(accumulator, 0),
        fold_bound_variable(item, 1),
        body,
    )))
}

pub(in crate::surface) fn lower_contract_add(
    left: CValue,
    right: CValue,
) -> Result<CValue, ClickError> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        return Ok(CValue::Int32(bitvector32_add(left_term, right_term)));
    }

    match (left, right) {
        (CValue::Pointer(pointer), offset) => promoted_int32_term(&offset)
            .map(|index| CValue::Pointer(offset_pointer_by_int32_elements(pointer, index)))
            .ok_or_else(|| {
                ClickError::new(format!(
                    "cannot add pointer and `{offset:?}` in proposition"
                ))
            }),
        (offset, CValue::Pointer(pointer)) => promoted_int32_term(&offset)
            .map(|index| CValue::Pointer(offset_pointer_by_int32_elements(pointer, index)))
            .ok_or_else(|| {
                ClickError::new(format!(
                    "cannot add `{offset:?}` and pointer in proposition"
                ))
            }),
        (left, right) => Err(ClickError::new(format!(
            "cannot add `{left:?}` and `{right:?}` in proposition"
        ))),
    }
}

pub(in crate::surface) fn lower_contract_subtract(
    left: CValue,
    right: CValue,
) -> Result<CValue, ClickError> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        return Ok(CValue::Int32(bitvector32_subtract(left_term, right_term)));
    }

    match (left, right) {
        (CValue::Pointer(pointer), offset) => {
            let Some(index) = promoted_int32_term(&offset) else {
                return Err(ClickError::new(format!(
                    "cannot subtract `{offset:?}` from pointer in proposition"
                )));
            };
            Ok(CValue::Pointer(offset_pointer_by_int32_elements(
                pointer,
                bitvector32_subtract(Bitvector32Term::Constant(0), index),
            )))
        }
        (left, right) => Err(ClickError::new(format!(
            "cannot subtract `{right:?}` from `{left:?}` in proposition"
        ))),
    }
}

pub(in crate::surface) fn lower_contract_multiply(
    left: CValue,
    right: CValue,
) -> Result<CValue, ClickError> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        Ok(CValue::Int32(bitvector32_multiply(left_term, right_term)))
    } else {
        Err(ClickError::new(format!(
            "cannot multiply `{left:?}` and `{right:?}` in proposition"
        )))
    }
}

pub(in crate::surface) fn lower_contract_divide(
    left: CValue,
    right: CValue,
) -> Result<CValue, ClickError> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        bitvector32_divide(left_term, right_term)
            .map(CValue::Int32)
            .map_err(ClickError::new)
    } else {
        Err(ClickError::new(format!(
            "cannot divide `{left:?}` by `{right:?}` in proposition"
        )))
    }
}

pub(in crate::surface) fn lower_contract_remainder(
    left: CValue,
    right: CValue,
) -> Result<CValue, ClickError> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        bitvector32_remainder(left_term, right_term)
            .map(CValue::Int32)
            .map_err(ClickError::new)
    } else {
        Err(ClickError::new(format!(
            "cannot compute `{left:?}` % `{right:?}` in proposition"
        )))
    }
}

pub(in crate::surface) fn lower_contract_shift_left(
    left: CValue,
    right: CValue,
) -> Result<CValue, ClickError> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        bitvector32_shift_left(left_term, right_term)
            .map(CValue::Int32)
            .map_err(ClickError::new)
    } else {
        Err(ClickError::new(format!(
            "cannot apply `<<` to `{left:?}` and `{right:?}` in proposition"
        )))
    }
}

pub(in crate::surface) fn lower_contract_shift_right(
    left: CValue,
    right: CValue,
) -> Result<CValue, ClickError> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        bitvector32_shift_right(left_term, right_term)
            .map(CValue::Int32)
            .map_err(ClickError::new)
    } else {
        Err(ClickError::new(format!(
            "cannot apply `>>` to `{left:?}` and `{right:?}` in proposition"
        )))
    }
}

pub(in crate::surface) fn lower_contract_bitwise_binary(
    left: CValue,
    right: CValue,
    operator: &str,
    apply: fn(Bitvector32Term, Bitvector32Term) -> Bitvector32Term,
) -> Result<CValue, ClickError> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        Ok(CValue::Int32(apply(left_term, right_term)))
    } else {
        Err(ClickError::new(format!(
            "cannot apply `{operator}` to `{left:?}` and `{right:?}` in proposition"
        )))
    }
}

pub(in crate::surface) fn lower_contract_bitwise_not(value: CValue) -> Result<CValue, ClickError> {
    if let Some(term) = promoted_int32_term(&value) {
        Ok(CValue::Int32(bitvector32_not(term)))
    } else {
        Err(ClickError::new(format!(
            "cannot apply `~` to `{value:?}` in proposition"
        )))
    }
}

pub(in crate::surface) fn bitvector32_add(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Bitvector32Term {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            Bitvector32Term::Constant(left.wrapping_add(*right))
        }
        (Bitvector32Term::Constant(constant), Bitvector32Term::Subtract(base, subtrahend))
            if subtrahend.as_ref() == &Bitvector32Term::Constant(*constant) =>
        {
            base.as_ref().clone()
        }
        (Bitvector32Term::Subtract(base, subtrahend), Bitvector32Term::Constant(constant))
            if subtrahend.as_ref() == &Bitvector32Term::Constant(*constant) =>
        {
            base.as_ref().clone()
        }
        (Bitvector32Term::Subtract(zero, subtrahend), Bitvector32Term::Add(base, addend))
            if zero.as_ref() == &Bitvector32Term::Constant(0) && subtrahend == base =>
        {
            addend.as_ref().clone()
        }
        (Bitvector32Term::Subtract(zero, subtrahend), Bitvector32Term::Add(addend, base))
            if zero.as_ref() == &Bitvector32Term::Constant(0) && subtrahend == base =>
        {
            addend.as_ref().clone()
        }
        (Bitvector32Term::Add(base, addend), Bitvector32Term::Subtract(zero, subtrahend))
            if zero.as_ref() == &Bitvector32Term::Constant(0) && base == subtrahend =>
        {
            addend.as_ref().clone()
        }
        (Bitvector32Term::Add(addend, base), Bitvector32Term::Subtract(zero, subtrahend))
            if zero.as_ref() == &Bitvector32Term::Constant(0) && base == subtrahend =>
        {
            addend.as_ref().clone()
        }
        (_, Bitvector32Term::Constant(0)) => left,
        (Bitvector32Term::Constant(0), _) => right,
        _ => Bitvector32Term::Add(Box::new(left), Box::new(right)),
    }
}

pub(in crate::surface) fn bitvector32_subtract(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Bitvector32Term {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            Bitvector32Term::Constant(left.wrapping_sub(*right))
        }
        (_, Bitvector32Term::Constant(0)) => left,
        _ if left == right => Bitvector32Term::Constant(0),
        (
            Bitvector32Term::Add(left_base, left_addend),
            Bitvector32Term::Add(right_base, right_addend),
        ) if left_base == right_base => {
            bitvector32_subtract(left_addend.as_ref().clone(), right_addend.as_ref().clone())
        }
        (
            Bitvector32Term::Add(left_base, left_addend),
            Bitvector32Term::Add(right_base, right_addend),
        ) if left_base == right_addend => {
            bitvector32_subtract(left_addend.as_ref().clone(), right_base.as_ref().clone())
        }
        (
            Bitvector32Term::Add(left_base, left_addend),
            Bitvector32Term::Add(right_base, right_addend),
        ) if left_addend == right_base => {
            bitvector32_subtract(left_base.as_ref().clone(), right_addend.as_ref().clone())
        }
        (
            Bitvector32Term::Add(left_base, left_addend),
            Bitvector32Term::Add(right_base, right_addend),
        ) if left_addend == right_addend => {
            bitvector32_subtract(left_base.as_ref().clone(), right_base.as_ref().clone())
        }
        (Bitvector32Term::Add(left_base, left_addend), _) if left_base.as_ref() == &right => {
            left_addend.as_ref().clone()
        }
        (Bitvector32Term::Add(left_base, left_addend), _) if left_addend.as_ref() == &right => {
            left_base.as_ref().clone()
        }
        (_, Bitvector32Term::Add(right_base, right_addend)) if &left == right_base.as_ref() => {
            bitvector32_subtract(Bitvector32Term::Constant(0), right_addend.as_ref().clone())
        }
        (_, Bitvector32Term::Add(right_base, right_addend)) if &left == right_addend.as_ref() => {
            bitvector32_subtract(Bitvector32Term::Constant(0), right_base.as_ref().clone())
        }
        _ => Bitvector32Term::Subtract(Box::new(left), Box::new(right)),
    }
}

pub(in crate::surface) fn bitvector32_multiply(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Bitvector32Term {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            Bitvector32Term::Constant(left.wrapping_mul(*right))
        }
        (_, Bitvector32Term::Constant(1)) => left,
        (Bitvector32Term::Constant(1), _) => right,
        (_, Bitvector32Term::Constant(0)) | (Bitvector32Term::Constant(0), _) => {
            Bitvector32Term::Constant(0)
        }
        _ => Bitvector32Term::Multiply(Box::new(left), Box::new(right)),
    }
}

pub(in crate::surface) fn bitvector32_divide(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Result<Bitvector32Term, String> {
    match (&left, &right) {
        (_, Bitvector32Term::Constant(0)) => Err("division by zero in proposition".to_string()),
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right))
            if *left == i32::MIN as u32 && *right == (-1i32) as u32 =>
        {
            Err("signed division overflow in proposition".to_string())
        }
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => Ok(
            Bitvector32Term::Constant(((*left as i32) / (*right as i32)) as u32),
        ),
        (_, Bitvector32Term::Constant(1)) => Ok(left),
        _ => Ok(Bitvector32Term::Divide(Box::new(left), Box::new(right))),
    }
}

pub(in crate::surface) fn bitvector32_remainder(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Result<Bitvector32Term, String> {
    match (&left, &right) {
        (_, Bitvector32Term::Constant(0)) => Err("division by zero in proposition".to_string()),
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right))
            if *left == i32::MIN as u32 && *right == (-1i32) as u32 =>
        {
            Err("signed division overflow in proposition".to_string())
        }
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => Ok(
            Bitvector32Term::Constant(((*left as i32) % (*right as i32)) as u32),
        ),
        (_, Bitvector32Term::Constant(1)) => Ok(Bitvector32Term::Constant(0)),
        _ => Ok(Bitvector32Term::Remainder(Box::new(left), Box::new(right))),
    }
}

pub(in crate::surface) fn bitvector32_shift_count(right: u32) -> Option<u32> {
    let right = right as i32;
    (0..32).contains(&right).then_some(right as u32)
}

pub(in crate::surface) fn bitvector32_shift_left(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Result<Bitvector32Term, String> {
    match (&left, &right) {
        (_, Bitvector32Term::Constant(right)) if bitvector32_shift_count(*right).is_none() => {
            Err("invalid shift count in proposition".to_string())
        }
        (Bitvector32Term::Constant(left), _) if (*left as i32) < 0 => {
            Err("left shift of negative value in proposition".to_string())
        }
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            let count =
                bitvector32_shift_count(*right).expect("constant shift count was checked above");
            let shifted = ((*left as i32) as i64) << count;
            if shifted > i64::from(i32::MAX) {
                Err("signed left shift overflow in proposition".to_string())
            } else {
                Ok(Bitvector32Term::Constant((shifted as i32) as u32))
            }
        }
        _ => Ok(Bitvector32Term::ShiftLeft(Box::new(left), Box::new(right))),
    }
}

pub(in crate::surface) fn bitvector32_shift_right(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Result<Bitvector32Term, String> {
    match (&left, &right) {
        (_, Bitvector32Term::Constant(right)) if bitvector32_shift_count(*right).is_none() => {
            Err("invalid shift count in proposition".to_string())
        }
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            let count =
                bitvector32_shift_count(*right).expect("constant shift count was checked above");
            Ok(Bitvector32Term::Constant(((*left as i32) >> count) as u32))
        }
        (_, Bitvector32Term::Constant(0)) => Ok(left),
        _ => Ok(Bitvector32Term::ArithmeticShiftRight(
            Box::new(left),
            Box::new(right),
        )),
    }
}

pub(in crate::surface) fn bitvector32_and(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Bitvector32Term {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            Bitvector32Term::Constant(*left & *right)
        }
        (_, Bitvector32Term::Constant(u32::MAX)) => left,
        (Bitvector32Term::Constant(u32::MAX), _) => right,
        (_, Bitvector32Term::Constant(0)) | (Bitvector32Term::Constant(0), _) => {
            Bitvector32Term::Constant(0)
        }
        _ if left == right => left,
        _ => Bitvector32Term::BitwiseAnd(Box::new(left), Box::new(right)),
    }
}

pub(in crate::surface) fn bitvector32_or(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Bitvector32Term {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            Bitvector32Term::Constant(*left | *right)
        }
        (_, Bitvector32Term::Constant(0)) => left,
        (Bitvector32Term::Constant(0), _) => right,
        (_, Bitvector32Term::Constant(u32::MAX)) | (Bitvector32Term::Constant(u32::MAX), _) => {
            Bitvector32Term::Constant(u32::MAX)
        }
        _ if left == right => left,
        _ => Bitvector32Term::BitwiseOr(Box::new(left), Box::new(right)),
    }
}

pub(in crate::surface) fn bitvector32_xor(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Bitvector32Term {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            Bitvector32Term::Constant(*left ^ *right)
        }
        (_, Bitvector32Term::Constant(0)) => left,
        (Bitvector32Term::Constant(0), _) => right,
        _ if left == right => Bitvector32Term::Constant(0),
        _ => Bitvector32Term::BitwiseXor(Box::new(left), Box::new(right)),
    }
}

pub(in crate::surface) fn bitvector32_not(value: Bitvector32Term) -> Bitvector32Term {
    match value {
        Bitvector32Term::Constant(value) => Bitvector32Term::Constant(!value),
        Bitvector32Term::BitwiseNot(inner) => *inner,
        value => Bitvector32Term::BitwiseNot(Box::new(value)),
    }
}

pub(in crate::surface) fn signed_less_than(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> ConditionTerm {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            ConditionTerm::Constant((*left as i32) < (*right as i32))
        }
        _ => ConditionTerm::Bitvector32SignedLessThan(Box::new(left), Box::new(right)),
    }
}

pub(in crate::surface) fn signed_less_equal(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> ConditionTerm {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            ConditionTerm::Constant((*left as i32) <= (*right as i32))
        }
        _ => ConditionTerm::Bitvector32SignedLessEqual(Box::new(left), Box::new(right)),
    }
}

pub(in crate::surface) fn signed_greater_than(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> ConditionTerm {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            ConditionTerm::Constant((*left as i32) > (*right as i32))
        }
        _ => ConditionTerm::Bitvector32SignedGreaterThan(Box::new(left), Box::new(right)),
    }
}

pub(in crate::surface) fn signed_greater_equal(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> ConditionTerm {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            ConditionTerm::Constant((*left as i32) >= (*right as i32))
        }
        _ => ConditionTerm::Bitvector32SignedGreaterEqual(Box::new(left), Box::new(right)),
    }
}

pub(in crate::surface) fn bitvector32_equal(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> ConditionTerm {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            ConditionTerm::Constant(left == right)
        }
        _ => ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
    }
}
