use super::*;

type FunctionContractSummary = (
    Vec<SpecProposition>,
    Vec<SpecProposition>,
    Vec<CMemorySegment>,
    Vec<CFunctionContractClaim>,
    bool,
);

pub(super) fn lower_composite_resource_facts(
    definition: &ResourceDefinition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Vec<SpecProposition>, ClickError> {
    let body = definition
        .composite_body()
        .expect("only composite definitions have logical facts");
    let entry_state = CState::new();
    let mut lowerer = AnnotationLowerer {
        structural_clauses: &[],
        function_effects: &[],
        predicate_environment,
        click_function_environment,
        entry_state: &entry_state,
        entry_values: BTreeMap::new(),
        parameter_array_element_types: definition
            .parameters()
            .iter()
            .filter_map(|parameter| {
                Some((
                    parameter.name().to_string(),
                    click_array_element_type(parameter.c_type())?,
                ))
            })
            .collect(),
        quantified_values: BTreeMap::new(),
        loop_index: 0,
        statement_index: 0,
        next_quantifier_variable: 3_200_000,
    };
    let all_predicates = predicate_environment
        .definitions
        .keys()
        .cloned()
        .collect::<Vec<_>>();
    body.facts()
        .iter()
        .map(|fact| {
            let fact = unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                &all_predicates,
                fact,
                &mut BTreeSet::new(),
            )
            .map_err(ClickError::new)?;
            lowerer
                .click_proposition_to_spec_proposition(&fact, &SpecElaborationContext::default())
                .map_err(ClickError::new)
        })
        .collect()
}

pub(super) fn annotated_function(
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    entry_state: &CState,
    arguments: &[CExpression],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
    inherit_function_effects_into_loops: bool,
) -> Result<CFunction, ClickError> {
    let mut lowerer = AnnotationLowerer {
        structural_clauses: function_block.structural_clauses(),
        function_effects: if inherit_function_effects_into_loops {
            function_block.effects()
        } else {
            &[]
        },
        predicate_environment,
        click_function_environment,
        entry_state,
        entry_values: parameter_values(parsed_function.parameters(), arguments)?,
        parameter_array_element_types: parsed_function
            .parameters()
            .iter()
            .filter_map(|parameter| {
                Some((
                    parameter.name().to_string(),
                    click_array_element_type(parameter.c_type())?,
                ))
            })
            .collect(),
        quantified_values: BTreeMap::new(),
        loop_index: 0,
        statement_index: 0,
        next_quantifier_variable: 3_000_000,
    };
    let body = lowerer.lower_statement(parsed_function.body())?;
    let (resource_requires, resource_ensures) =
        function_resource_summary(function_block, resource_environment)?;
    let (
        contract_requires,
        contract_ensures,
        contract_mutable,
        contract_claims,
        opaque_contract_supported,
    ) = function_contract_summary(
        function_block,
        parsed_function,
        predicate_environment,
        click_function_environment,
        resource_environment,
    )?;
    let source_body = parsed_function.to_kernel_function().body().clone();
    Ok(c_function(
        parsed_function.return_type().to_kernel_type(),
        parsed_function.name().to_string(),
        parsed_function
            .parameters()
            .iter()
            .map(syntax::C0Parameter::to_kernel_parameter)
            .collect(),
        body,
    )
    .with_source_body(source_body)
    .with_resource_summary(resource_requires, resource_ensures)
    .with_composite_resource_definitions(composite_resource_definitions(
        resource_environment,
        predicate_environment,
        click_function_environment,
    )?)
    .with_contract(
        contract_requires,
        contract_ensures,
        contract_mutable,
        contract_claims,
        opaque_contract_supported,
    ))
}

pub(super) fn function_contract_summary(
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
) -> Result<FunctionContractSummary, ClickError> {
    let entry_state = CState::new();
    let mut lowerer = AnnotationLowerer {
        structural_clauses: function_block.structural_clauses(),
        function_effects: &[],
        predicate_environment,
        click_function_environment,
        entry_state: &entry_state,
        entry_values: BTreeMap::new(),
        parameter_array_element_types: parsed_function
            .parameters()
            .iter()
            .filter_map(|parameter| {
                Some((
                    parameter.name().to_string(),
                    click_array_element_type(parameter.c_type())?,
                ))
            })
            .collect(),
        quantified_values: BTreeMap::new(),
        loop_index: 0,
        statement_index: 0,
        next_quantifier_variable: 3_100_000,
    };
    let context = SpecElaborationContext::for_function_contract();
    let all_predicates = predicate_environment
        .definitions
        .keys()
        .cloned()
        .collect::<Vec<_>>();
    let unfold_contract_predicates = |proposition: &ClickProposition| {
        unfold_click_predicates_in_proposition_with_active(
            predicate_environment,
            &all_predicates,
            proposition,
            &mut BTreeSet::new(),
        )
    };
    let mut opaque_contract_supported = true;
    let mut requires = Vec::new();
    for requirement in function_block.requires() {
        let proposition = match requirement.inner() {
            Requirement::Proposition(proposition) => proposition.clone(),
            Requirement::LoadableSegment { segment } => ClickProposition::Loadable {
                segment: segment.clone(),
            },
            Requirement::LoadableBytes {
                name,
                bytes: RangeBytes::Constant(bytes),
            } => {
                let element_width = parsed_function
                    .parameters()
                    .iter()
                    .find(|parameter| parameter.name() == name)
                    .and_then(|parameter| click_array_element_type(parameter.c_type()))
                    .map(CType::byte_width);
                let Some(element_width) = element_width else {
                    opaque_contract_supported = false;
                    continue;
                };
                if bytes % element_width != 0 {
                    opaque_contract_supported = false;
                    continue;
                }
                requires.push(SpecProposition::MemoryLoadable {
                    memory: SpecMemory::Current,
                    base: SpecExpression::CExpression(CExpression::Variable(name.clone())),
                    start: SpecExpression::Value(int32(0)),
                    end: SpecExpression::Value(int32(bytes / element_width)),
                    element_width,
                });
                continue;
            }
            Requirement::LoadableBytes { .. } => {
                opaque_contract_supported = false;
                continue;
            }
            Requirement::Resource(_) | Requirement::Labeled { .. } => continue,
        };
        let Ok(proposition) = unfold_contract_predicates(&proposition) else {
            opaque_contract_supported = false;
            continue;
        };
        if !proposition_supported_in_opaque_contract(&proposition) {
            opaque_contract_supported = false;
            continue;
        }
        match lowerer.click_proposition_to_spec_proposition(&proposition, &context) {
            Ok(proposition) => requires.push(proposition),
            Err(_) => opaque_contract_supported = false,
        }
    }
    let mut ensures = Vec::new();
    for proposition in function_block
        .ensures()
        .iter()
        .filter_map(|clause| match clause.ensure() {
            Ensure::Proposition(proposition) => Some(proposition),
            Ensure::Resource(_) => None,
        })
    {
        let Ok(proposition) = unfold_contract_predicates(proposition) else {
            opaque_contract_supported = false;
            continue;
        };
        if !proposition_supported_in_opaque_contract(&proposition) {
            opaque_contract_supported = false;
            continue;
        }
        match lowerer.click_proposition_to_spec_proposition(&proposition, &context) {
            Ok(proposition) => ensures.push(proposition),
            Err(_) => opaque_contract_supported = false,
        }
    }

    let mut mutable = Vec::new();
    if function_block.effects().is_empty() {
        for requirement in function_block.requires() {
            if let Requirement::Resource(resource) = requirement.inner() {
                collect_owned_resource_memory_segments(
                    resource,
                    resource_environment,
                    &mut mutable,
                )?;
            }
        }
    }
    for effect in function_block.effects() {
        match effect.effect() {
            Effect::Immutable => {}
            Effect::Mutable(segments) => {
                mutable.extend(segments.iter().map(|segment| {
                    CMemorySegment::new(
                        segment.base.clone(),
                        segment.start.clone(),
                        segment.end.clone(),
                    )
                }));
            }
        }
    }
    let claims = if function_block.effects().is_empty() && function_block.ensures().is_empty() {
        vec![CFunctionContractClaim::body_safety()]
    } else {
        let mut proposition_index = 0;
        let mut resource_index = 0;
        let mut claims = function_block
            .effects()
            .iter()
            .enumerate()
            .map(|(index, _)| CFunctionContractClaim::effect(index))
            .collect::<Vec<_>>();
        for (source_index, ensure) in function_block.ensures().iter().enumerate() {
            claims.push(match ensure.ensure() {
                Ensure::Proposition(_) => {
                    let claim =
                        CFunctionContractClaim::ensure_proposition(source_index, proposition_index);
                    proposition_index += 1;
                    claim
                }
                Ensure::Resource(_) => {
                    let claim =
                        CFunctionContractClaim::ensure_resource(source_index, resource_index);
                    resource_index += 1;
                    claim
                }
            });
        }
        claims
    };
    Ok((
        requires,
        ensures,
        mutable,
        claims,
        opaque_contract_supported,
    ))
}

fn proposition_supported_in_opaque_contract(proposition: &ClickProposition) -> bool {
    match proposition {
        ClickProposition::Separate { .. }
        | ClickProposition::Contains { .. }
        | ClickProposition::Loadable { .. }
        | ClickProposition::Defined { .. } => true,
        ClickProposition::At { .. } => false,
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            proposition_supported_in_opaque_contract(left)
                && proposition_supported_in_opaque_contract(right)
        }
        ClickProposition::Not(body)
        | ClickProposition::ForAll { body, .. }
        | ClickProposition::Exists { body, .. }
        | ClickProposition::RangeAll { body, .. }
        | ClickProposition::RangeAny { body, .. } => proposition_supported_in_opaque_contract(body),
        ClickProposition::Comparison { .. } | ClickProposition::PredicateCall { .. } => true,
    }
}

fn collect_owned_resource_memory_segments(
    resource: &ResourceClause,
    resource_environment: &ResourceEnvironment,
    output: &mut Vec<CMemorySegment>,
) -> Result<(), ClickError> {
    match resource {
        ResourceClause::Read(_) => Ok(()),
        ResourceClause::Write(segment) => {
            output.push(CMemorySegment::new(
                segment.base.clone(),
                segment.start.clone(),
                segment.end.clone(),
            ));
            Ok(())
        }
        ResourceClause::Declared {
            access: ResourceAccessMode::View,
            ..
        } => Ok(()),
        ResourceClause::Declared {
            access: ResourceAccessMode::Own,
            kind: ResourceKind::Token,
            ..
        } => Ok(()),
        ResourceClause::Declared {
            access: ResourceAccessMode::Own,
            kind: ResourceKind::Composite,
            name,
            arguments,
            ..
        } => {
            let definition = resource_environment
                .get(name)
                .ok_or_else(|| ClickError::new(format!("unknown composite resource `{name}`")))?;
            let Some(body) = definition.composite_body() else {
                return Ok(());
            };
            let substitutions = resource_argument_contract_substitutions(definition, arguments)?;
            for contained in body.contains() {
                let contained = substitute_resource_clause_for_summary(contained, &substitutions)
                    .map_err(ClickError::new)?;
                collect_owned_resource_memory_segments(&contained, resource_environment, output)?;
            }
            Ok(())
        }
    }
}

struct AnnotationLowerer<'a> {
    structural_clauses: &'a [StructuralClause],
    function_effects: &'a [EffectClause],
    predicate_environment: &'a PredicateEnvironment,
    click_function_environment: &'a ClickFunctionEnvironment,
    entry_state: &'a CState,
    entry_values: BTreeMap<String, CValue>,
    parameter_array_element_types: BTreeMap<String, CType>,
    quantified_values: BTreeMap<String, CValue>,
    loop_index: usize,
    statement_index: usize,
    next_quantifier_variable: u64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct LabeledCheck {
    condition: CExpression,
    label: String,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ResolvedProgramPoint {
    FunctionEntry,
    LoopEntry(usize),
}

impl AnnotationLowerer<'_> {
    fn lower_statement(
        &mut self,
        statement: &syntax::C0Statement,
    ) -> Result<CStatement, ClickError> {
        Ok(match statement {
            syntax::C0Statement::Seq(first, second) => {
                c_seq(self.lower_statement(first)?, self.lower_statement(second)?)
            }
            syntax::C0Statement::While { condition, body } => {
                let statement_index = self.next_statement_index();
                let loop_index = self.next_loop_index();
                let lowered_body = self.lower_statement(body)?;
                let loop_asserts = self.loop_assert_checks(loop_index);
                let invariant_checks = self.loop_invariant_checks(loop_index)?;
                let effect_checks = self.loop_effect_checks(loop_index, body)?;
                let lowered_loop = c_while_with_invariant_and_effect_checks(
                    condition.to_kernel_expression(),
                    Vec::new(),
                    invariant_checks,
                    effect_checks,
                    lowered_body,
                );
                let lowered_loop = prepend_labeled_asserts(lowered_loop, &loop_asserts);
                self.prepend_statement_asserts(statement_index, lowered_loop)
            }
            syntax::C0Statement::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let statement_index = self.next_statement_index();
                let lowered = c_if(
                    condition.to_kernel_expression(),
                    self.lower_statement(then_branch)?,
                    self.lower_statement(else_branch)?,
                );
                self.prepend_statement_asserts(statement_index, lowered)
            }
            statement => {
                let statement_index = self.next_statement_index();
                let lowered = statement.to_kernel_statement();
                self.prepend_statement_asserts(statement_index, lowered)
            }
        })
    }

    fn next_statement_index(&mut self) -> usize {
        let index = self.statement_index;
        self.statement_index += 1;
        index
    }

    fn next_loop_index(&mut self) -> usize {
        let index = self.loop_index;
        self.loop_index += 1;
        index
    }

    fn prepend_statement_asserts(
        &self,
        statement_index: usize,
        statement: CStatement,
    ) -> CStatement {
        let checks = self
            .structural_clauses
            .iter()
            .filter(|clause| clause.region() == &CodeRegion::Statement(statement_index))
            .flat_map(StructuralClause::items)
            .filter(|item| item.kind() == StructuralItemKind::Assert)
            .enumerate()
            .map(|(item_index, item)| LabeledCheck {
                condition: click_proposition_to_c_expression(
                    item.proposition()
                        .expect("assert structural item should contain a proposition"),
                )
                .expect("structural propositions should be validated before lowering"),
                label: format!(
                    "statement {statement_index} {} {item_index}",
                    structural_item_kind_label(item.kind())
                ),
            })
            .collect::<Vec<_>>();
        prepend_labeled_asserts(statement, &checks)
    }

    fn loop_invariant_checks(
        &mut self,
        loop_index: usize,
    ) -> Result<Vec<CLoopInvariantCheck>, ClickError> {
        let unfolded_predicates = self
            .structural_clauses
            .iter()
            .filter(|clause| clause.region() == &CodeRegion::Loop(loop_index))
            .flat_map(|clause| {
                clause
                    .initialize_proof()
                    .into_iter()
                    .chain(clause.preserve_proof())
            })
            .flat_map(Proof::unfold_tactic_names)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        self.structural_clauses
            .iter()
            .filter(|clause| clause.region() == &CodeRegion::Loop(loop_index))
            .flat_map(StructuralClause::items)
            .filter(|item| item.kind() == StructuralItemKind::Invariant)
            .enumerate()
            .map(|(item_index, item)| {
                let proposition = unfold_structural_invariant_proposition(
                    self.predicate_environment,
                    item.proposition()
                        .expect("invariant structural item should contain a proposition"),
                    &unfolded_predicates,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "loop {loop_index} invariant {item_index}: {message}"
                    ))
                })?;
                Ok(CLoopInvariantCheck::new(
                    self.click_proposition_to_spec_proposition(
                        &proposition,
                        &SpecElaborationContext::for_loop_invariant(loop_index),
                    )
                    .map_err(|message| {
                        ClickError::new(format!(
                            "loop {loop_index} invariant {item_index}: {message}"
                        ))
                    })?,
                    Some(format!("loop {loop_index} invariant {item_index} entry")),
                    Some(format!(
                        "loop {loop_index} invariant {item_index} preservation"
                    )),
                ))
            })
            .collect()
    }

    fn click_proposition_to_spec_proposition(
        &mut self,
        proposition: &ClickProposition,
        environment: &SpecElaborationContext,
    ) -> Result<SpecProposition, String> {
        match proposition {
            ClickProposition::Comparison {
                left,
                operator,
                right,
            } => Ok(SpecProposition::Comparison {
                left: self.lower_contract_expression_to_spec(left, environment)?,
                operator: c_comparison_operator(*operator),
                right: self.lower_contract_expression_to_spec(right, environment)?,
            }),
            ClickProposition::Separate { left, right } => Ok(SpecProposition::ResourceSeparate {
                left: self.lower_resource_subject_to_spec(left, environment)?,
                right: self.lower_resource_subject_to_spec(right, environment)?,
            }),
            ClickProposition::Contains { parent, child } => Ok(SpecProposition::ResourceContains {
                parent: self.lower_resource_subject_to_spec(parent, environment)?,
                child: self.lower_resource_subject_to_spec(child, environment)?,
            }),
            ClickProposition::Loadable { segment } => {
                let segment_environment = self.spec_segment_environment(segment, environment)?;
                Ok(SpecProposition::MemoryLoadable {
                    memory: segment_environment.current_memory.clone(),
                    base: self
                        .lower_contract_segment_base_to_spec(&segment.base, &segment_environment)?,
                    start: self.lower_c_fragment_to_spec(&segment.start, &segment_environment)?,
                    end: self.lower_c_fragment_to_spec(&segment.end, &segment_environment)?,
                    element_width: self.contract_segment_element_width(segment),
                })
            }
            ClickProposition::Defined { expression } => Ok(SpecProposition::Defined(
                self.lower_contract_expression_to_spec(expression, environment)?,
            )),
            ClickProposition::At { .. } => {
                Err("`at(...)` propositions are proof-script snapshots".to_string())
            }
            ClickProposition::And(left, right) => Ok(SpecProposition::And(
                Box::new(self.click_proposition_to_spec_proposition(left, environment)?),
                Box::new(self.click_proposition_to_spec_proposition(right, environment)?),
            )),
            ClickProposition::Or(left, right) => Ok(SpecProposition::Or(
                Box::new(self.click_proposition_to_spec_proposition(left, environment)?),
                Box::new(self.click_proposition_to_spec_proposition(right, environment)?),
            )),
            ClickProposition::Not(body) => Ok(SpecProposition::Not(Box::new(
                self.click_proposition_to_spec_proposition(body, environment)?,
            ))),
            ClickProposition::Implies(left, right) => Ok(SpecProposition::Implies(
                Box::new(self.click_proposition_to_spec_proposition(left, environment)?),
                Box::new(self.click_proposition_to_spec_proposition(right, environment)?),
            )),
            ClickProposition::ForAll { c_type, name, body } => {
                if *c_type != C0Type::Int32 {
                    return Err("only `forall (int32 ...)` is supported".to_string());
                }
                let variable = Variable(self.next_quantifier_variable);
                self.next_quantifier_variable += 1;
                let mut body_environment = environment.clone();
                body_environment.values.insert(
                    name.clone(),
                    SpecExpression::Value(CValue::Int32(Bitvector32Term::Variable(variable))),
                );
                let previous = self.quantified_values.insert(
                    name.clone(),
                    CValue::Int32(Bitvector32Term::Variable(variable)),
                );
                let body = self.click_proposition_to_spec_proposition(body, &body_environment)?;
                match previous {
                    Some(value) => {
                        self.quantified_values.insert(name.clone(), value);
                    }
                    None => {
                        self.quantified_values.remove(name);
                    }
                }
                Ok(SpecProposition::ForAllInt32 {
                    name: name.clone(),
                    variable,
                    body: Box::new(body),
                })
            }
            ClickProposition::Exists { c_type, name, body } => {
                if *c_type != C0Type::Int32 {
                    return Err("only `exists (int32 ...)` is supported".to_string());
                }
                let variable = Variable(self.next_quantifier_variable);
                self.next_quantifier_variable += 1;
                let mut body_environment = environment.clone();
                body_environment.values.insert(
                    name.clone(),
                    SpecExpression::Value(CValue::Int32(Bitvector32Term::Variable(variable))),
                );
                let previous = self.quantified_values.insert(
                    name.clone(),
                    CValue::Int32(Bitvector32Term::Variable(variable)),
                );
                let body = self.click_proposition_to_spec_proposition(body, &body_environment)?;
                match previous {
                    Some(value) => {
                        self.quantified_values.insert(name.clone(), value);
                    }
                    None => {
                        self.quantified_values.remove(name);
                    }
                }
                Ok(SpecProposition::ExistsInt32 {
                    name: name.clone(),
                    variable,
                    body: Box::new(body),
                })
            }
            ClickProposition::RangeAll {
                start,
                end,
                item,
                body,
            } => {
                let start = self.lower_contract_expression_to_spec(start, environment)?;
                let end = self.lower_contract_expression_to_spec(end, environment)?;
                let variable = Variable(self.next_quantifier_variable);
                self.next_quantifier_variable += 1;
                let item_value =
                    SpecExpression::Value(CValue::Int32(Bitvector32Term::Variable(variable)));
                let mut body_environment = environment.clone();
                body_environment
                    .values
                    .insert(item.clone(), item_value.clone());
                let previous = self.quantified_values.insert(
                    item.clone(),
                    CValue::Int32(Bitvector32Term::Variable(variable)),
                );
                let body = self.click_proposition_to_spec_proposition(body, &body_environment)?;
                match previous {
                    Some(value) => {
                        self.quantified_values.insert(item.clone(), value);
                    }
                    None => {
                        self.quantified_values.remove(item);
                    }
                }
                let range = spec_range_membership_proposition(start, item_value, end);
                Ok(SpecProposition::ForAllInt32 {
                    name: item.clone(),
                    variable,
                    body: Box::new(SpecProposition::Implies(Box::new(range), Box::new(body))),
                })
            }
            ClickProposition::RangeAny {
                start,
                end,
                item,
                body,
            } => {
                let start = self.lower_contract_expression_to_spec(start, environment)?;
                let end = self.lower_contract_expression_to_spec(end, environment)?;
                let variable = Variable(self.next_quantifier_variable);
                self.next_quantifier_variable += 1;
                let item_value =
                    SpecExpression::Value(CValue::Int32(Bitvector32Term::Variable(variable)));
                let mut body_environment = environment.clone();
                body_environment
                    .values
                    .insert(item.clone(), item_value.clone());
                let previous = self.quantified_values.insert(
                    item.clone(),
                    CValue::Int32(Bitvector32Term::Variable(variable)),
                );
                let body = self.click_proposition_to_spec_proposition(body, &body_environment)?;
                match previous {
                    Some(value) => {
                        self.quantified_values.insert(item.clone(), value);
                    }
                    None => {
                        self.quantified_values.remove(item);
                    }
                }
                let range = spec_range_membership_proposition(start, item_value, end);
                Ok(SpecProposition::ExistsInt32 {
                    name: item.clone(),
                    variable,
                    body: Box::new(SpecProposition::And(Box::new(range), Box::new(body))),
                })
            }
            ClickProposition::PredicateCall { name, arguments } => {
                let definition = self
                    .predicate_environment
                    .get(name)
                    .ok_or_else(|| format!("unknown predicate `{name}`"))?;
                let mut lowered_arguments = Vec::new();
                for (parameter, argument) in definition.parameters().iter().zip(arguments) {
                    if parameter_is_click_array_ref(parameter) {
                        let expected_element_type = click_array_element_type(parameter.c_type())
                            .ok_or_else(|| {
                                format!(
                                    "predicate `{}` parameter `{}` is not an array-ref parameter",
                                    definition.name(),
                                    parameter.name()
                                )
                            })?;
                        let array_ref = self.lower_array_ref_to_spec(argument, environment)?;
                        if array_ref.element_type != expected_element_type {
                            return Err(format!(
                                "predicate `{}` parameter `{}` expects {:?} array elements, got {:?}",
                                definition.name(),
                                parameter.name(),
                                expected_element_type,
                                array_ref.element_type
                            ));
                        }
                        lowered_arguments.push(SpecPredicateArgument::ArrayRef {
                            memory: array_ref.memory,
                            pointer: array_ref.pointer,
                        });
                    } else {
                        lowered_arguments.push(SpecPredicateArgument::Value(
                            self.lower_contract_expression_to_spec(argument, environment)?,
                        ));
                    }
                }
                Ok(SpecProposition::Predicate {
                    name: name.clone(),
                    arguments: lowered_arguments,
                })
            }
        }
    }

    fn lower_contract_expression_to_spec(
        &mut self,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> Result<SpecExpression, String> {
        match expression {
            ContractExpression::CFragment(expression)
            | ContractExpression::Field {
                lowered: expression,
                ..
            } => self.lower_c_fragment_to_spec(expression, environment),
            ContractExpression::CBinding(name) => {
                self.lower_c_fragment_to_spec(&CExpression::Variable(name.clone()), environment)
            }
            ContractExpression::Old(expression) => {
                let old_environment =
                    environment.old_state(&self.entry_values, self.entry_state.memory())?;
                self.lower_contract_expression_to_spec(expression, &old_environment)
            }
            ContractExpression::At {
                selector,
                expression,
            } => self.lower_at_expression_to_spec(selector, expression, environment),
            ContractExpression::Add(left, right) => Ok(SpecExpression::Add(
                Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                Box::new(self.lower_contract_expression_to_spec(right, environment)?),
            )),
            ContractExpression::Subtract(left, right) => Ok(SpecExpression::Subtract(
                Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                Box::new(self.lower_contract_expression_to_spec(right, environment)?),
            )),
            ContractExpression::Multiply(left, right) => Ok(SpecExpression::Multiply(
                Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                Box::new(self.lower_contract_expression_to_spec(right, environment)?),
            )),
            ContractExpression::Divide(left, right) => Ok(SpecExpression::Divide(
                Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                Box::new(self.lower_contract_expression_to_spec(right, environment)?),
            )),
            ContractExpression::Remainder(left, right) => Ok(SpecExpression::Remainder(
                Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                Box::new(self.lower_contract_expression_to_spec(right, environment)?),
            )),
            ContractExpression::ShiftLeft(left, right) => Ok(SpecExpression::ShiftLeft(
                Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                Box::new(self.lower_contract_expression_to_spec(right, environment)?),
            )),
            ContractExpression::ShiftRight(left, right) => Ok(SpecExpression::ShiftRight(
                Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                Box::new(self.lower_contract_expression_to_spec(right, environment)?),
            )),
            ContractExpression::BitwiseAnd(left, right) => Ok(SpecExpression::BitwiseAnd(
                Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                Box::new(self.lower_contract_expression_to_spec(right, environment)?),
            )),
            ContractExpression::BitwiseOr(left, right) => Ok(SpecExpression::BitwiseOr(
                Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                Box::new(self.lower_contract_expression_to_spec(right, environment)?),
            )),
            ContractExpression::BitwiseXor(left, right) => Ok(SpecExpression::BitwiseXor(
                Box::new(self.lower_contract_expression_to_spec(left, environment)?),
                Box::new(self.lower_contract_expression_to_spec(right, environment)?),
            )),
            ContractExpression::BitwiseNot(expression) => Ok(SpecExpression::BitwiseNot(Box::new(
                self.lower_contract_expression_to_spec(expression, environment)?,
            ))),
            ContractExpression::Index(base, index) => {
                let array_ref = self.lower_array_ref_to_spec(base, environment)?;
                let index = self.lower_contract_expression_to_spec(index, environment)?;
                Ok(SpecExpression::MemoryLoad {
                    memory: array_ref.memory,
                    pointer: Box::new(SpecExpression::PointerOffset {
                        pointer: Box::new(array_ref.pointer),
                        elements: Box::new(index),
                        byte_width: array_ref.element_type.byte_width(),
                    }),
                    value_type: array_ref.element_type,
                })
            }
            ContractExpression::If {
                condition,
                then_branch,
                else_branch,
            } => Ok(SpecExpression::If {
                condition: Box::new(
                    self.click_proposition_to_spec_proposition(condition, environment)?,
                ),
                then_branch: Box::new(
                    self.lower_contract_expression_to_spec(then_branch, environment)?,
                ),
                else_branch: Box::new(
                    self.lower_contract_expression_to_spec(else_branch, environment)?,
                ),
            }),
            ContractExpression::RangeFold {
                start,
                end,
                initial,
                accumulator,
                item,
                body,
            } => {
                let mut body_environment = environment.clone();
                body_environment.values.insert(
                    accumulator.clone(),
                    SpecExpression::CExpression(CExpression::Variable(accumulator.clone())),
                );
                body_environment.values.insert(
                    item.clone(),
                    SpecExpression::CExpression(CExpression::Variable(item.clone())),
                );
                Ok(SpecExpression::RangeFold {
                    start: Box::new(self.lower_contract_expression_to_spec(start, environment)?),
                    end: Box::new(self.lower_contract_expression_to_spec(end, environment)?),
                    initial: Box::new(
                        self.lower_contract_expression_to_spec(initial, environment)?,
                    ),
                    accumulator: accumulator.clone(),
                    item: item.clone(),
                    body: Box::new(
                        self.lower_contract_expression_to_spec(body, &body_environment)?,
                    ),
                })
            }
            ContractExpression::Let {
                name, value, body, ..
            } => {
                let value = self.lower_contract_expression_to_spec(value, environment)?;
                let mut body_environment = environment.clone();
                body_environment.values.insert(
                    name.clone(),
                    SpecExpression::CExpression(CExpression::Variable(name.clone())),
                );
                Ok(SpecExpression::Let {
                    name: name.clone(),
                    value: Box::new(value),
                    body: Box::new(
                        self.lower_contract_expression_to_spec(body, &body_environment)?,
                    ),
                })
            }
            ContractExpression::Call { name, arguments } => {
                self.lower_click_function_call_to_spec(name, arguments, environment)
            }
        }
    }

    fn spec_segment_environment(
        &self,
        segment: &ContractSegment,
        environment: &SpecElaborationContext,
    ) -> Result<SpecElaborationContext, String> {
        match segment.state {
            ContractSegmentState::Current => Ok(environment.clone()),
            ContractSegmentState::Old => {
                environment.old_state(&self.entry_values, self.entry_state.memory())
            }
        }
    }

    fn contract_segment_element_width(&self, segment: &ContractSegment) -> u32 {
        self.c_expression_array_element_type(
            &segment.base,
            &SpecElaborationContext::for_function_contract(),
        )
        .unwrap_or(CType::Int32)
        .byte_width()
    }

    fn lower_contract_segment_base_to_spec(
        &self,
        expression: &CExpression,
        environment: &SpecElaborationContext,
    ) -> Result<SpecExpression, String> {
        if let CExpression::Add(left, right) = expression {
            if let Some(element_type) = self.c_expression_array_element_type(left, environment) {
                return Ok(SpecExpression::PointerOffset {
                    pointer: Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                    elements: Box::new(self.lower_c_fragment_to_spec(right, environment)?),
                    byte_width: element_type.byte_width(),
                });
            }
            if let Some(element_type) = self.c_expression_array_element_type(right, environment) {
                return Ok(SpecExpression::PointerOffset {
                    pointer: Box::new(self.lower_c_fragment_to_spec(right, environment)?),
                    elements: Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                    byte_width: element_type.byte_width(),
                });
            }
        }
        self.lower_c_fragment_to_spec(expression, environment)
    }

    fn lower_resource_subject_to_spec(
        &mut self,
        resource: &ResourceSubject,
        environment: &SpecElaborationContext,
    ) -> Result<SpecResource, String> {
        match resource {
            ResourceSubject::Memory(segment) => {
                let environment = self.spec_segment_environment(segment, environment)?;
                Ok(SpecResource::Memory {
                    base: self.lower_contract_segment_base_to_spec(&segment.base, &environment)?,
                    start: self.lower_c_fragment_to_spec(&segment.start, &environment)?,
                    end: self.lower_c_fragment_to_spec(&segment.end, &environment)?,
                })
            }
            ResourceSubject::Declared {
                kind,
                name,
                arguments,
                ..
            } => {
                let arguments = arguments
                    .iter()
                    .map(|argument| self.lower_contract_expression_to_spec(argument, environment))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(match kind {
                    ResourceKind::Composite => SpecResource::Composite {
                        name: name.clone(),
                        arguments,
                    },
                    ResourceKind::Token => SpecResource::Token {
                        name: name.clone(),
                        arguments,
                    },
                })
            }
        }
    }

    fn lower_at_expression_to_spec(
        &mut self,
        selector: &VisitSelector,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> Result<SpecExpression, String> {
        match self.resolve_visit_selector(selector)? {
            ResolvedProgramPoint::FunctionEntry => {
                let old_environment =
                    environment.old_state(&self.entry_values, self.entry_state.memory())?;
                self.lower_contract_expression_to_spec(expression, &old_environment)
            }
            ResolvedProgramPoint::LoopEntry(loop_index) => {
                if environment.current_loop_entry != Some(loop_index) {
                    return Err(format!(
                        "`at(loop({loop_index}).entry, ...)` is currently supported only inside that loop's invariant"
                    ));
                }
                Ok(SpecExpression::LoopEntrySnapshot(Box::new(
                    self.lower_contract_expression_to_spec(expression, environment)?,
                )))
            }
        }
    }

    fn resolve_visit_selector(
        &self,
        selector: &VisitSelector,
    ) -> Result<ResolvedProgramPoint, String> {
        match selector {
            VisitSelector::ProgramPoint(program_point) => {
                self.resolve_program_point_ref(program_point)
            }
        }
    }

    fn resolve_program_point_ref(
        &self,
        program_point: &ProgramPointRef,
    ) -> Result<ResolvedProgramPoint, String> {
        let region = self.resolve_code_region_ref(&program_point.region)?;
        match (region, program_point.kind) {
            (CodeRegion::Function, ProgramPointKind::Entry) => {
                Ok(ResolvedProgramPoint::FunctionEntry)
            }
            (CodeRegion::Loop(index), ProgramPointKind::Entry) => {
                Ok(ResolvedProgramPoint::LoopEntry(index))
            }
            (CodeRegion::Function, ProgramPointKind::Exit) => {
                Err("`at(function.exit, ...)` is not supported yet".to_string())
            }
            (CodeRegion::Loop(index), ProgramPointKind::Exit) => Err(format!(
                "`at(loop({index}).exit, ...)` requires a recorded snapshot in an execution proof"
            )),
            (CodeRegion::Statement(index), kind) => Err(format!(
                "`at(statement({index}).{}, ...)` is not supported in this context yet",
                match kind {
                    ProgramPointKind::Entry => "entry",
                    ProgramPointKind::Exit => "exit",
                }
            )),
        }
    }

    fn resolve_code_region_ref(&self, region_ref: &CodeRegionRef) -> Result<CodeRegion, String> {
        match region_ref {
            CodeRegionRef::Function => Ok(CodeRegion::Function),
            CodeRegionRef::Loop(index) => Ok(CodeRegion::Loop(*index)),
            CodeRegionRef::Statement(index) => Ok(CodeRegion::Statement(*index)),
            CodeRegionRef::Label(label) => self
                .structural_clauses
                .iter()
                .find(|clause| clause.label() == Some(label.as_str()))
                .map(|clause| *clause.region())
                .ok_or_else(|| format!("unknown code region label `{label}`")),
        }
    }

    fn lower_c_fragment_to_spec(
        &self,
        expression: &CExpression,
        environment: &SpecElaborationContext,
    ) -> Result<SpecExpression, String> {
        match expression {
            CExpression::Value(value) => Ok(SpecExpression::Value(value.clone())),
            CExpression::Variable(name) => match environment.values.get(name) {
                Some(value) => Ok(value.clone()),
                None if matches!(environment.current_memory, SpecMemory::Fixed(_)) => {
                    if name == "result" {
                        Err("`result` is not available inside `old(...)`".to_string())
                    } else {
                        Err(format!("unknown old-state variable `{name}`"))
                    }
                }
                None => Ok(SpecExpression::CExpression(CExpression::Variable(
                    name.clone(),
                ))),
            },
            CExpression::PointerOffsetBytes { pointer, bytes } => {
                Ok(SpecExpression::PointerOffset {
                    pointer: Box::new(self.lower_c_fragment_to_spec(pointer, environment)?),
                    elements: Box::new(SpecExpression::Value(int32(*bytes))),
                    byte_width: 1,
                })
            }
            CExpression::Add(left, right) => Ok(SpecExpression::Add(
                Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                Box::new(self.lower_c_fragment_to_spec(right, environment)?),
            )),
            CExpression::Subtract(left, right) => Ok(SpecExpression::Subtract(
                Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                Box::new(self.lower_c_fragment_to_spec(right, environment)?),
            )),
            CExpression::Multiply(left, right) => Ok(SpecExpression::Multiply(
                Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                Box::new(self.lower_c_fragment_to_spec(right, environment)?),
            )),
            CExpression::Divide(left, right) => Ok(SpecExpression::Divide(
                Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                Box::new(self.lower_c_fragment_to_spec(right, environment)?),
            )),
            CExpression::Remainder(left, right) => Ok(SpecExpression::Remainder(
                Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                Box::new(self.lower_c_fragment_to_spec(right, environment)?),
            )),
            CExpression::ShiftLeft(left, right) => Ok(SpecExpression::ShiftLeft(
                Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                Box::new(self.lower_c_fragment_to_spec(right, environment)?),
            )),
            CExpression::ShiftRight(left, right) => Ok(SpecExpression::ShiftRight(
                Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                Box::new(self.lower_c_fragment_to_spec(right, environment)?),
            )),
            CExpression::BitwiseAnd(left, right) => Ok(SpecExpression::BitwiseAnd(
                Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                Box::new(self.lower_c_fragment_to_spec(right, environment)?),
            )),
            CExpression::BitwiseOr(left, right) => Ok(SpecExpression::BitwiseOr(
                Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                Box::new(self.lower_c_fragment_to_spec(right, environment)?),
            )),
            CExpression::BitwiseXor(left, right) => Ok(SpecExpression::BitwiseXor(
                Box::new(self.lower_c_fragment_to_spec(left, environment)?),
                Box::new(self.lower_c_fragment_to_spec(right, environment)?),
            )),
            CExpression::BitwiseNot(expression) => Ok(SpecExpression::BitwiseNot(Box::new(
                self.lower_c_fragment_to_spec(expression, environment)?,
            ))),
            CExpression::Index(base, index) => {
                let element_type = self
                    .c_expression_array_element_type(base, environment)
                    .unwrap_or(CType::Int32);
                let pointer = SpecExpression::PointerOffset {
                    pointer: Box::new(self.lower_c_fragment_to_spec(base, environment)?),
                    elements: Box::new(self.lower_c_fragment_to_spec(index, environment)?),
                    byte_width: element_type.byte_width(),
                };
                Ok(SpecExpression::MemoryLoad {
                    memory: environment.current_memory.clone(),
                    pointer: Box::new(pointer),
                    value_type: element_type,
                })
            }
            CExpression::TypedLoad {
                pointer,
                value_type,
            } => Ok(SpecExpression::MemoryLoad {
                memory: environment.current_memory.clone(),
                pointer: Box::new(self.lower_c_fragment_to_spec(pointer, environment)?),
                value_type: *value_type,
            }),
            CExpression::Load(pointer) => Ok(SpecExpression::MemoryLoad {
                memory: environment.current_memory.clone(),
                pointer: Box::new(self.lower_c_fragment_to_spec(pointer, environment)?),
                value_type: CType::Int32,
            }),
            expression => Ok(SpecExpression::CExpression(expression.clone())),
        }
    }

    fn lower_click_function_call_to_spec(
        &mut self,
        name: &str,
        arguments: &[ContractExpression],
        environment: &SpecElaborationContext,
    ) -> Result<SpecExpression, String> {
        let definition = self
            .click_function_environment
            .get(name)
            .ok_or_else(|| format!("unknown function `{name}`"))?;
        if arguments.len() != definition.parameters().len() {
            return Err(format!(
                "function `{}` expects {} argument(s), got {}",
                definition.name(),
                definition.parameters().len(),
                arguments.len()
            ));
        }

        let mut function_environment =
            SpecElaborationContext::with_current_memory(environment.current_memory.clone());
        for (parameter, argument) in definition.parameters().iter().zip(arguments) {
            if parameter_is_click_array_ref(parameter) {
                let expected_element_type = click_array_element_type(parameter.c_type())
                    .ok_or_else(|| {
                        format!(
                            "function `{}` parameter `{}` is not an array-ref parameter",
                            definition.name(),
                            parameter.name()
                        )
                    })?;
                let array_ref = self.lower_array_ref_to_spec(argument, environment)?;
                if array_ref.element_type != expected_element_type {
                    return Err(format!(
                        "function `{}` parameter `{}` expects {:?} array elements, got {:?}",
                        definition.name(),
                        parameter.name(),
                        expected_element_type,
                        array_ref.element_type
                    ));
                }
                function_environment
                    .array_refs
                    .insert(parameter.name().to_string(), array_ref);
            } else {
                function_environment.values.insert(
                    parameter.name().to_string(),
                    self.lower_contract_expression_to_spec(argument, environment)?,
                );
            }
        }

        self.lower_contract_expression_to_spec(definition.body(), &function_environment)
    }

    fn lower_array_ref_to_spec(
        &mut self,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> Result<SpecArrayRef, String> {
        match expression {
            ContractExpression::Old(expression) => {
                let old_environment =
                    environment.old_state(&self.entry_values, self.entry_state.memory())?;
                self.lower_array_ref_to_spec(expression, &old_environment)
            }
            ContractExpression::At {
                selector,
                expression,
            } => self.lower_at_array_ref_to_spec(selector, expression, environment),
            ContractExpression::CFragment(CExpression::Variable(name)) => {
                if let Some(array_ref) = environment.array_refs.get(name) {
                    return Ok(array_ref.clone());
                }
                Ok(SpecArrayRef {
                    memory: environment.current_memory.clone(),
                    pointer: self.lower_c_fragment_to_spec(
                        &CExpression::Variable(name.clone()),
                        environment,
                    )?,
                    element_type: self.array_ref_element_type_for_name(name),
                })
            }
            ContractExpression::Add(left, right) => {
                if let Ok(array_ref) = self.lower_array_ref_to_spec(left, environment) {
                    let offset = self.lower_contract_expression_to_spec(right, environment)?;
                    let element_type = array_ref.element_type;
                    return Ok(SpecArrayRef {
                        memory: array_ref.memory,
                        pointer: SpecExpression::PointerOffset {
                            pointer: Box::new(array_ref.pointer),
                            elements: Box::new(offset),
                            byte_width: element_type.byte_width(),
                        },
                        element_type,
                    });
                }
                if let Ok(array_ref) = self.lower_array_ref_to_spec(right, environment) {
                    let offset = self.lower_contract_expression_to_spec(left, environment)?;
                    let element_type = array_ref.element_type;
                    return Ok(SpecArrayRef {
                        memory: array_ref.memory,
                        pointer: SpecExpression::PointerOffset {
                            pointer: Box::new(array_ref.pointer),
                            elements: Box::new(offset),
                            byte_width: element_type.byte_width(),
                        },
                        element_type,
                    });
                }
                Ok(SpecArrayRef {
                    memory: environment.current_memory.clone(),
                    pointer: self.lower_contract_expression_to_spec(expression, environment)?,
                    element_type: self.contract_array_element_type(expression, environment),
                })
            }
            ContractExpression::Subtract(left, right) => {
                if let Ok(array_ref) = self.lower_array_ref_to_spec(left, environment) {
                    let offset = self.lower_contract_expression_to_spec(right, environment)?;
                    let negative_offset = SpecExpression::Subtract(
                        Box::new(SpecExpression::Value(CValue::Int32(
                            Bitvector32Term::Constant(0),
                        ))),
                        Box::new(offset),
                    );
                    let element_type = array_ref.element_type;
                    return Ok(SpecArrayRef {
                        memory: array_ref.memory,
                        pointer: SpecExpression::PointerOffset {
                            pointer: Box::new(array_ref.pointer),
                            elements: Box::new(negative_offset),
                            byte_width: element_type.byte_width(),
                        },
                        element_type,
                    });
                }
                Ok(SpecArrayRef {
                    memory: environment.current_memory.clone(),
                    pointer: self.lower_contract_expression_to_spec(expression, environment)?,
                    element_type: self.contract_array_element_type(expression, environment),
                })
            }
            _ => Ok(SpecArrayRef {
                memory: environment.current_memory.clone(),
                pointer: self.lower_contract_expression_to_spec(expression, environment)?,
                element_type: self.contract_array_element_type(expression, environment),
            }),
        }
    }

    fn lower_at_array_ref_to_spec(
        &mut self,
        selector: &VisitSelector,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> Result<SpecArrayRef, String> {
        match self.resolve_visit_selector(selector)? {
            ResolvedProgramPoint::FunctionEntry => {
                let old_environment =
                    environment.old_state(&self.entry_values, self.entry_state.memory())?;
                self.lower_array_ref_to_spec(expression, &old_environment)
            }
            ResolvedProgramPoint::LoopEntry(loop_index) => {
                if environment.current_loop_entry != Some(loop_index) {
                    return Err(format!(
                        "`at(loop({loop_index}).entry, ...)` is currently supported only inside that loop's invariant"
                    ));
                }
                let SpecArrayRef {
                    memory,
                    pointer,
                    element_type,
                } = self.lower_array_ref_to_spec(expression, environment)?;
                let memory = match memory {
                    SpecMemory::Current => SpecMemory::LoopEntry,
                    memory => memory,
                };
                Ok(SpecArrayRef {
                    memory,
                    pointer: SpecExpression::LoopEntrySnapshot(Box::new(pointer)),
                    element_type,
                })
            }
        }
    }

    fn array_ref_element_type_for_name(&self, name: &str) -> CType {
        self.parameter_array_element_types
            .get(name)
            .copied()
            .unwrap_or(CType::Int32)
    }

    fn contract_array_element_type(
        &self,
        expression: &ContractExpression,
        environment: &SpecElaborationContext,
    ) -> CType {
        match expression {
            ContractExpression::CFragment(CExpression::Variable(name)) => environment
                .array_refs
                .get(name)
                .map(|array_ref| array_ref.element_type)
                .unwrap_or_else(|| self.array_ref_element_type_for_name(name)),
            ContractExpression::At { expression, .. } => {
                self.contract_array_element_type(expression, environment)
            }
            ContractExpression::Old(expression) => {
                self.contract_array_element_type(expression, environment)
            }
            ContractExpression::Add(left, right) => {
                let left_type = self.contract_array_element_type(left, environment);
                if left_type != CType::Int32 {
                    return left_type;
                }
                self.contract_array_element_type(right, environment)
            }
            ContractExpression::Subtract(left, _) => {
                self.contract_array_element_type(left, environment)
            }
            _ => CType::Int32,
        }
    }

    fn c_expression_array_element_type(
        &self,
        expression: &CExpression,
        environment: &SpecElaborationContext,
    ) -> Option<CType> {
        match expression {
            CExpression::Variable(name) => environment
                .array_refs
                .get(name)
                .map(|array_ref| array_ref.element_type)
                .or_else(|| self.parameter_array_element_types.get(name).copied()),
            CExpression::TypedLoad { value_type, .. } => value_type.pointee_type(),
            CExpression::PointerOffsetBytes { pointer, .. } => {
                self.c_expression_array_element_type(pointer, environment)
            }
            CExpression::Add(left, right) => self
                .c_expression_array_element_type(left, environment)
                .or_else(|| self.c_expression_array_element_type(right, environment)),
            CExpression::Subtract(left, _) => {
                self.c_expression_array_element_type(left, environment)
            }
            _ => None,
        }
    }

    fn lower_current_invariant_c_expression(
        &self,
        expression: &CExpression,
    ) -> Result<CExpression, String> {
        match expression {
            CExpression::Value(value) => Ok(CExpression::Value(value.clone())),
            CExpression::Variable(name) => Ok(self
                .quantified_values
                .get(name)
                .cloned()
                .map(CExpression::Value)
                .unwrap_or_else(|| CExpression::Variable(name.clone()))),
            CExpression::AddressOf(expression) => Ok(CExpression::AddressOf(Box::new(
                self.lower_current_invariant_c_expression(expression)?,
            ))),
            CExpression::PointerOffsetBytes { pointer, bytes } => {
                Ok(CExpression::PointerOffsetBytes {
                    pointer: Box::new(self.lower_current_invariant_c_expression(pointer)?),
                    bytes: *bytes,
                })
            }
            CExpression::Add(left, right) => Ok(CExpression::Add(
                Box::new(self.lower_current_invariant_c_expression(left)?),
                Box::new(self.lower_current_invariant_c_expression(right)?),
            )),
            CExpression::Subtract(left, right) => Ok(CExpression::Subtract(
                Box::new(self.lower_current_invariant_c_expression(left)?),
                Box::new(self.lower_current_invariant_c_expression(right)?),
            )),
            CExpression::Multiply(left, right) => Ok(CExpression::Multiply(
                Box::new(self.lower_current_invariant_c_expression(left)?),
                Box::new(self.lower_current_invariant_c_expression(right)?),
            )),
            CExpression::Divide(left, right) => Ok(CExpression::Divide(
                Box::new(self.lower_current_invariant_c_expression(left)?),
                Box::new(self.lower_current_invariant_c_expression(right)?),
            )),
            CExpression::Remainder(left, right) => Ok(CExpression::Remainder(
                Box::new(self.lower_current_invariant_c_expression(left)?),
                Box::new(self.lower_current_invariant_c_expression(right)?),
            )),
            CExpression::ShiftLeft(left, right) => Ok(CExpression::ShiftLeft(
                Box::new(self.lower_current_invariant_c_expression(left)?),
                Box::new(self.lower_current_invariant_c_expression(right)?),
            )),
            CExpression::ShiftRight(left, right) => Ok(CExpression::ShiftRight(
                Box::new(self.lower_current_invariant_c_expression(left)?),
                Box::new(self.lower_current_invariant_c_expression(right)?),
            )),
            CExpression::BitwiseAnd(left, right) => Ok(CExpression::BitwiseAnd(
                Box::new(self.lower_current_invariant_c_expression(left)?),
                Box::new(self.lower_current_invariant_c_expression(right)?),
            )),
            CExpression::BitwiseOr(left, right) => Ok(CExpression::BitwiseOr(
                Box::new(self.lower_current_invariant_c_expression(left)?),
                Box::new(self.lower_current_invariant_c_expression(right)?),
            )),
            CExpression::BitwiseXor(left, right) => Ok(CExpression::BitwiseXor(
                Box::new(self.lower_current_invariant_c_expression(left)?),
                Box::new(self.lower_current_invariant_c_expression(right)?),
            )),
            CExpression::BitwiseNot(expression) => Ok(CExpression::BitwiseNot(Box::new(
                self.lower_current_invariant_c_expression(expression)?,
            ))),
            CExpression::Load(pointer) => Ok(CExpression::Load(Box::new(
                self.lower_current_invariant_c_expression(pointer)?,
            ))),
            CExpression::TypedLoad {
                pointer,
                value_type,
            } => Ok(CExpression::TypedLoad {
                pointer: Box::new(self.lower_current_invariant_c_expression(pointer)?),
                value_type: *value_type,
            }),
            CExpression::Index(base, index) => Ok(CExpression::Index(
                Box::new(self.lower_current_invariant_c_expression(base)?),
                Box::new(self.lower_current_invariant_c_expression(index)?),
            )),
            expression => Err(format!(
                "unsupported expression in loop invariant: `{expression:?}`"
            )),
        }
    }

    fn loop_assert_checks(&self, loop_index: usize) -> Vec<LabeledCheck> {
        self.structural_clauses
            .iter()
            .filter(|clause| clause.region() == &CodeRegion::Loop(loop_index))
            .flat_map(StructuralClause::items)
            .filter(|item| item.kind() == StructuralItemKind::Assert)
            .enumerate()
            .map(|(item_index, item)| LabeledCheck {
                condition: click_proposition_to_c_expression(
                    item.proposition()
                        .expect("assert structural item should contain a proposition"),
                )
                .expect("structural propositions should be validated before lowering"),
                label: format!("loop {loop_index} assert {item_index}"),
            })
            .collect()
    }

    fn loop_effect_checks(
        &self,
        loop_index: usize,
        body: &syntax::C0Statement,
    ) -> Result<Vec<CLoopEffectCheck>, ClickError> {
        let modified_locals = c0_loop_modified_locals(body);
        let mut checks = self
            .structural_clauses
            .iter()
            .filter(|clause| clause.region() == &CodeRegion::Loop(loop_index))
            .flat_map(StructuralClause::items)
            .filter(|item| item.is_effect_kind())
            .enumerate()
            .map(|(item_index, item)| {
                let effect = item
                    .effect()
                    .expect("effect structural item should contain an effect");
                let span = match item.kind() {
                    StructuralItemKind::Effect => CLoopEffectSpan::Whole,
                    StructuralItemKind::StepEffect => CLoopEffectSpan::Step,
                    _ => unreachable!("loop effect filter should only include effect items"),
                };
                let lowered = self
                    .lower_loop_effect(effect, span, &modified_locals)
                    .map_err(|message| {
                        ClickError::new(format!("loop {loop_index} effect {item_index}: {message}"))
                    })?;
                let context = match effect {
                    Effect::Immutable => match span {
                        CLoopEffectSpan::Whole => {
                            format!("loop {loop_index} immutable {item_index}")
                        }
                        CLoopEffectSpan::Step => {
                            format!("loop {loop_index} step immutable {item_index}")
                        }
                    },
                    Effect::Mutable(_) => match span {
                        CLoopEffectSpan::Whole => {
                            format!("loop {loop_index} mutable {item_index}")
                        }
                        CLoopEffectSpan::Step => {
                            format!("loop {loop_index} step mutable {item_index}")
                        }
                    },
                };
                Ok(CLoopEffectCheck::new_with_span(
                    lowered,
                    span,
                    Some(context),
                ))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let function_mutable = self
            .function_effects
            .iter()
            .flat_map(|clause| match clause.effect() {
                Effect::Mutable(segments) => segments.clone(),
                Effect::Immutable => Vec::new(),
            })
            .collect::<Vec<_>>();
        let implicit_effect = if !function_mutable.is_empty() {
            Some(Effect::Mutable(function_mutable))
        } else if self
            .function_effects
            .iter()
            .any(|clause| matches!(clause.effect(), Effect::Immutable))
        {
            Some(Effect::Immutable)
        } else {
            None
        };
        if let Some(effect) = implicit_effect {
            let lowered = self
                .lower_loop_effect(&effect, CLoopEffectSpan::Whole, &modified_locals)
                .map_err(|message| {
                    ClickError::new(format!(
                        "loop {loop_index} inherited function effect: {message}"
                    ))
                })?;
            checks.push(CLoopEffectCheck::new_with_span(
                lowered,
                CLoopEffectSpan::Whole,
                Some(format!("loop {loop_index} inherited function effect")),
            ));
        }
        Ok(checks)
    }

    fn lower_loop_effect(
        &self,
        effect: &Effect,
        span: CLoopEffectSpan,
        modified_locals: &BTreeSet<String>,
    ) -> Result<CLoopEffect, String> {
        match effect {
            Effect::Immutable => Ok(CLoopEffect::Immutable),
            Effect::Mutable(segments) => segments
                .iter()
                .map(|segment| {
                    if segment.state != ContractSegmentState::Current {
                        return Err(
                            "`mutable` inside `loop` expects current-state segments; `old(...)` is not supported here"
                                .to_string(),
                        );
                    }
                    if span == CLoopEffectSpan::Whole {
                        let names = contract_segment_referenced_names(segment);
                        if let Some(name) = names.iter().find(|name| modified_locals.contains(*name))
                        {
                            return Err(format!(
                                "whole-loop `mutable` segment references loop-modified local `{name}`; use `step {{ ... }}` for iteration-relative effects or state a stable whole-loop range"
                            ));
                        }
                    }
                    Ok(CMemorySegment::new(
                        self.lower_current_invariant_c_expression(&segment.base)?,
                        self.lower_current_invariant_c_expression(&segment.start)?,
                        self.lower_current_invariant_c_expression(&segment.end)?,
                    ))
                })
                .collect::<Result<Vec<_>, _>>()
                .map(CLoopEffect::Mutable),
        }
    }
}

pub(super) fn unfold_structural_invariant_proposition(
    predicate_environment: &PredicateEnvironment,
    proposition: &ClickProposition,
    unfolded_predicates: &[String],
) -> Result<ClickProposition, String> {
    if unfolded_predicates.is_empty() {
        return Ok(proposition.clone());
    }

    for name in unfolded_predicates {
        if predicate_environment.get(name).is_none() {
            return Err(format!("unknown predicate `{name}`"));
        }
    }

    let mut active = BTreeSet::new();
    unfold_click_predicates_in_proposition_with_active(
        predicate_environment,
        unfolded_predicates,
        proposition,
        &mut active,
    )
}

pub(super) fn unfold_click_predicates_in_proposition_with_active(
    predicate_environment: &PredicateEnvironment,
    unfolded_predicates: &[String],
    proposition: &ClickProposition,
    active: &mut BTreeSet<String>,
) -> Result<ClickProposition, String> {
    match proposition {
        ClickProposition::PredicateCall { name, arguments }
            if unfolded_predicates
                .iter()
                .any(|predicate| predicate == name) =>
        {
            if !active.insert(name.clone()) {
                return Err(format!("recursive unfold of predicate `{name}`"));
            }
            let definition = predicate_environment
                .get(name)
                .ok_or_else(|| format!("unknown predicate `{name}`"))?;
            let unfolded = instantiate_click_predicate_definition(definition, arguments)?;
            let unfolded = unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                &unfolded,
                active,
            )?;
            active.remove(name);
            Ok(unfolded)
        }
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => Ok(ClickProposition::Comparison {
            left: left.clone(),
            operator: *operator,
            right: right.clone(),
        }),
        ClickProposition::Separate { left, right } => Ok(ClickProposition::Separate {
            left: left.clone(),
            right: right.clone(),
        }),
        ClickProposition::Contains { parent, child } => Ok(ClickProposition::Contains {
            parent: parent.clone(),
            child: child.clone(),
        }),
        ClickProposition::Loadable { segment } => Ok(ClickProposition::Loadable {
            segment: segment.clone(),
        }),
        ClickProposition::Defined { expression } => Ok(ClickProposition::Defined {
            expression: expression.clone(),
        }),
        ClickProposition::At {
            selector,
            proposition,
        } => Ok(ClickProposition::At {
            selector: selector.clone(),
            proposition: Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                proposition,
                active,
            )?),
        }),
        ClickProposition::And(left, right) => Ok(ClickProposition::And(
            Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                left,
                active,
            )?),
            Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                right,
                active,
            )?),
        )),
        ClickProposition::Or(left, right) => Ok(ClickProposition::Or(
            Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                left,
                active,
            )?),
            Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                right,
                active,
            )?),
        )),
        ClickProposition::Not(body) => Ok(ClickProposition::Not(Box::new(
            unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                body,
                active,
            )?,
        ))),
        ClickProposition::Implies(left, right) => Ok(ClickProposition::Implies(
            Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                left,
                active,
            )?),
            Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                right,
                active,
            )?),
        )),
        ClickProposition::ForAll { c_type, name, body } => Ok(ClickProposition::ForAll {
            c_type: *c_type,
            name: name.clone(),
            body: Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                body,
                active,
            )?),
        }),
        ClickProposition::Exists { c_type, name, body } => Ok(ClickProposition::Exists {
            c_type: *c_type,
            name: name.clone(),
            body: Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                body,
                active,
            )?),
        }),
        ClickProposition::RangeAll {
            start,
            end,
            item,
            body,
        } => Ok(ClickProposition::RangeAll {
            start: start.clone(),
            end: end.clone(),
            item: item.clone(),
            body: Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                body,
                active,
            )?),
        }),
        ClickProposition::RangeAny {
            start,
            end,
            item,
            body,
        } => Ok(ClickProposition::RangeAny {
            start: start.clone(),
            end: end.clone(),
            item: item.clone(),
            body: Box::new(unfold_click_predicates_in_proposition_with_active(
                predicate_environment,
                unfolded_predicates,
                body,
                active,
            )?),
        }),
        ClickProposition::PredicateCall { name, arguments } => {
            Ok(ClickProposition::PredicateCall {
                name: name.clone(),
                arguments: arguments.clone(),
            })
        }
    }
}

pub(super) fn instantiate_click_predicate_definition(
    definition: &PredicateDefinition,
    arguments: &[ContractExpression],
) -> Result<ClickProposition, String> {
    if arguments.len() != definition.parameters().len() {
        return Err(format!(
            "predicate `{}` expects {} argument(s), got {}",
            definition.name(),
            definition.parameters().len(),
            arguments.len()
        ));
    }

    let substitutions = definition
        .parameters()
        .iter()
        .zip(arguments)
        .map(|(parameter, argument)| (parameter.name().to_string(), argument.clone()))
        .collect::<BTreeMap<_, _>>();
    substitute_click_proposition(definition.body(), &substitutions)
}

pub(super) fn substitute_click_proposition(
    proposition: &ClickProposition,
    substitutions: &BTreeMap<String, ContractExpression>,
) -> Result<ClickProposition, String> {
    match proposition {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => Ok(ClickProposition::Comparison {
            left: substitute_contract_expression(left, substitutions)?,
            operator: *operator,
            right: substitute_contract_expression(right, substitutions)?,
        }),
        ClickProposition::Separate { left, right } => Ok(ClickProposition::Separate {
            left: substitute_resource_subject(left, substitutions)?,
            right: substitute_resource_subject(right, substitutions)?,
        }),
        ClickProposition::Contains { parent, child } => Ok(ClickProposition::Contains {
            parent: substitute_resource_subject(parent, substitutions)?,
            child: substitute_resource_subject(child, substitutions)?,
        }),
        ClickProposition::Loadable { segment } => Ok(ClickProposition::Loadable {
            segment: substitute_contract_segment(segment, substitutions)?,
        }),
        ClickProposition::Defined { expression } => Ok(ClickProposition::Defined {
            expression: substitute_contract_expression(expression, substitutions)?,
        }),
        ClickProposition::At {
            selector,
            proposition,
        } => Ok(ClickProposition::At {
            selector: selector.clone(),
            proposition: Box::new(substitute_click_proposition(proposition, substitutions)?),
        }),
        ClickProposition::And(left, right) => Ok(ClickProposition::And(
            Box::new(substitute_click_proposition(left, substitutions)?),
            Box::new(substitute_click_proposition(right, substitutions)?),
        )),
        ClickProposition::Or(left, right) => Ok(ClickProposition::Or(
            Box::new(substitute_click_proposition(left, substitutions)?),
            Box::new(substitute_click_proposition(right, substitutions)?),
        )),
        ClickProposition::Not(body) => Ok(ClickProposition::Not(Box::new(
            substitute_click_proposition(body, substitutions)?,
        ))),
        ClickProposition::Implies(left, right) => Ok(ClickProposition::Implies(
            Box::new(substitute_click_proposition(left, substitutions)?),
            Box::new(substitute_click_proposition(right, substitutions)?),
        )),
        ClickProposition::ForAll { c_type, name, body } => {
            let mut scoped = substitutions.clone();
            scoped.remove(name);
            Ok(ClickProposition::ForAll {
                c_type: *c_type,
                name: name.clone(),
                body: Box::new(substitute_click_proposition(body, &scoped)?),
            })
        }
        ClickProposition::Exists { c_type, name, body } => {
            let mut scoped = substitutions.clone();
            scoped.remove(name);
            Ok(ClickProposition::Exists {
                c_type: *c_type,
                name: name.clone(),
                body: Box::new(substitute_click_proposition(body, &scoped)?),
            })
        }
        ClickProposition::RangeAll {
            start,
            end,
            item,
            body,
        } => {
            let mut scoped = substitutions.clone();
            scoped.remove(item);
            Ok(ClickProposition::RangeAll {
                start: substitute_contract_expression(start, substitutions)?,
                end: substitute_contract_expression(end, substitutions)?,
                item: item.clone(),
                body: Box::new(substitute_click_proposition(body, &scoped)?),
            })
        }
        ClickProposition::RangeAny {
            start,
            end,
            item,
            body,
        } => {
            let mut scoped = substitutions.clone();
            scoped.remove(item);
            Ok(ClickProposition::RangeAny {
                start: substitute_contract_expression(start, substitutions)?,
                end: substitute_contract_expression(end, substitutions)?,
                item: item.clone(),
                body: Box::new(substitute_click_proposition(body, &scoped)?),
            })
        }
        ClickProposition::PredicateCall { name, arguments } => {
            Ok(ClickProposition::PredicateCall {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| substitute_contract_expression(argument, substitutions))
                    .collect::<Result<Vec<_>, _>>()?,
            })
        }
    }
}

fn substitute_contract_segment(
    segment: &ContractSegment,
    substitutions: &BTreeMap<String, ContractExpression>,
) -> Result<ContractSegment, String> {
    let surface = match &segment.surface {
        ContractSegmentSurface::Range { base, start, end } => ContractSegmentSurface::Range {
            base: substitute_contract_expression(base, substitutions)?,
            start: substitute_contract_expression(start, substitutions)?,
            end: substitute_contract_expression(end, substitutions)?,
        },
        surface => surface.clone(),
    };
    Ok(ContractSegment {
        state: segment.state,
        base: substitute_c_fragment(&segment.base, substitutions)?,
        start: substitute_c_fragment(&segment.start, substitutions)?,
        end: substitute_c_fragment(&segment.end, substitutions)?,
        surface,
    })
}

fn substitute_resource_subject(
    resource: &ResourceSubject,
    substitutions: &BTreeMap<String, ContractExpression>,
) -> Result<ResourceSubject, String> {
    match resource {
        ResourceSubject::Memory(segment) => Ok(ResourceSubject::Memory(
            substitute_contract_segment(segment, substitutions)?,
        )),
        ResourceSubject::Declared {
            kind,
            name,
            arguments,
            parameter_types,
        } => Ok(ResourceSubject::Declared {
            kind: *kind,
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_contract_expression(argument, substitutions))
                .collect::<Result<Vec<_>, _>>()?,
            parameter_types: parameter_types.clone(),
        }),
    }
}

pub(super) fn apply_contract_lets_to_requirement(
    requirement: Requirement,
    bindings: &[ContractLetBinding],
) -> Result<Requirement, String> {
    match requirement {
        Requirement::Labeled { label, requirement } => Ok(Requirement::Labeled {
            label,
            requirement: Box::new(apply_contract_lets_to_requirement(*requirement, bindings)?),
        }),
        Requirement::LoadableBytes { name, bytes } => Ok(Requirement::LoadableBytes {
            name,
            bytes: apply_contract_lets_to_range_bytes(bytes, bindings)?,
        }),
        Requirement::LoadableSegment { segment } => Ok(Requirement::LoadableSegment {
            segment: apply_contract_lets_to_segment(segment, bindings)?,
        }),
        Requirement::Resource(resource) => Ok(Requirement::Resource(
            apply_contract_lets_to_resource_clause(resource, bindings)?,
        )),
        Requirement::Proposition(proposition) => Ok(Requirement::Proposition(
            apply_contract_lets_to_proposition(proposition, bindings)?,
        )),
    }
}

pub(super) fn apply_contract_lets_to_ensure_clause(
    clause: EnsureClause,
    bindings: &[ContractLetBinding],
) -> Result<EnsureClause, String> {
    let EnsureClause {
        name,
        ensure,
        proof,
    } = clause;
    let ensure = match ensure {
        Ensure::Proposition(proposition) => {
            Ensure::Proposition(apply_contract_lets_to_proposition(proposition, bindings)?)
        }
        Ensure::Resource(resource) => {
            Ensure::Resource(apply_contract_lets_to_resource_clause(resource, bindings)?)
        }
    };
    Ok(EnsureClause {
        name,
        ensure,
        proof,
    })
}

pub(super) fn apply_contract_lets_to_resource_clause(
    resource: ResourceClause,
    bindings: &[ContractLetBinding],
) -> Result<ResourceClause, String> {
    match resource {
        ResourceClause::Read(segment) => Ok(ResourceClause::Read(apply_contract_lets_to_segment(
            segment, bindings,
        )?)),
        ResourceClause::Write(segment) => Ok(ResourceClause::Write(
            apply_contract_lets_to_segment(segment, bindings)?,
        )),
        ResourceClause::Declared {
            access,
            kind,
            name,
            arguments,
            parameter_types,
        } => Ok(ResourceClause::Declared {
            access,
            kind,
            name,
            arguments: arguments
                .into_iter()
                .map(|argument| apply_contract_lets_to_expression(argument, bindings))
                .collect::<Result<Vec<_>, _>>()?,
            parameter_types,
        }),
    }
}

fn apply_contract_lets_to_resource_subject(
    resource: ResourceSubject,
    bindings: &[ContractLetBinding],
) -> Result<ResourceSubject, String> {
    match resource {
        ResourceSubject::Memory(segment) => Ok(ResourceSubject::Memory(
            apply_contract_lets_to_segment(segment, bindings)?,
        )),
        ResourceSubject::Declared {
            kind,
            name,
            arguments,
            parameter_types,
        } => Ok(ResourceSubject::Declared {
            kind,
            name,
            arguments: arguments
                .into_iter()
                .map(|argument| apply_contract_lets_to_expression(argument, bindings))
                .collect::<Result<Vec<_>, _>>()?,
            parameter_types,
        }),
    }
}

pub(super) fn apply_contract_lets_to_effect_clause(
    clause: EffectClause,
    bindings: &[ContractLetBinding],
) -> Result<EffectClause, String> {
    let EffectClause { effect, proof } = clause;
    Ok(EffectClause {
        effect: apply_contract_lets_to_effect(effect, bindings)?,
        proof,
    })
}

pub(super) fn apply_contract_lets_to_structural_clause(
    clause: StructuralClause,
    bindings: &[ContractLetBinding],
) -> Result<StructuralClause, String> {
    let StructuralClause {
        region,
        label,
        items,
        initialize_proof,
        preserve_proof,
    } = clause;
    let items = items
        .into_iter()
        .map(|item| apply_contract_lets_to_structural_item(item, bindings))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(StructuralClause {
        region,
        label,
        items,
        initialize_proof,
        preserve_proof,
    })
}

pub(super) fn apply_contract_lets_to_structural_item(
    item: StructuralItem,
    bindings: &[ContractLetBinding],
) -> Result<StructuralItem, String> {
    let StructuralItem { kind, claim, proof } = item;
    let claim = match claim {
        StructuralItemClaim::Proposition(proposition) => StructuralItemClaim::Proposition(
            apply_contract_lets_to_proposition(proposition, bindings)?,
        ),
        StructuralItemClaim::Effect(effect) => {
            StructuralItemClaim::Effect(apply_contract_lets_to_effect(effect, bindings)?)
        }
    };
    Ok(StructuralItem { kind, claim, proof })
}

pub(super) fn apply_contract_lets_to_effect(
    effect: Effect,
    bindings: &[ContractLetBinding],
) -> Result<Effect, String> {
    match effect {
        Effect::Immutable => Ok(Effect::Immutable),
        Effect::Mutable(segments) => Ok(Effect::Mutable(
            segments
                .into_iter()
                .map(|segment| apply_contract_lets_to_segment(segment, bindings))
                .collect::<Result<Vec<_>, _>>()?,
        )),
    }
}

pub(super) fn apply_contract_lets_to_segment(
    segment: ContractSegment,
    bindings: &[ContractLetBinding],
) -> Result<ContractSegment, String> {
    let substitutions = contract_let_substitutions(bindings);
    let surface = match segment.surface {
        ContractSegmentSurface::Range { base, start, end } => ContractSegmentSurface::Range {
            base: substitute_contract_expression(&base, &substitutions)?,
            start: substitute_contract_expression(&start, &substitutions)?,
            end: substitute_contract_expression(&end, &substitutions)?,
        },
        surface => surface,
    };
    let segment = ContractSegment {
        state: segment.state,
        base: substitute_c_fragment(&segment.base, &substitutions)?,
        start: substitute_c_fragment(&segment.start, &substitutions)?,
        end: substitute_c_fragment(&segment.end, &substitutions)?,
        surface,
    };
    reject_contract_where_let_references(
        &contract_segment_referenced_names(&segment),
        bindings,
        "memory segment expressions",
    )?;
    Ok(segment)
}

pub(super) fn apply_contract_lets_to_range_bytes(
    bytes: RangeBytes,
    bindings: &[ContractLetBinding],
) -> Result<RangeBytes, String> {
    reject_contract_where_let_references(
        &range_bytes_referenced_names(&bytes),
        bindings,
        "loadable byte expressions",
    )?;
    let bytes = match bytes {
        RangeBytes::Constant(_) => Ok(bytes),
        RangeBytes::Parameter(name) => {
            let substitutions = contract_let_substitutions(bindings);
            let Some(value) = substitutions.get(&name) else {
                return Ok(RangeBytes::Parameter(name));
            };
            let c_fragment = contract_expression_as_c_fragment(value).ok_or_else(|| {
                format!(
                    "contract `let` `{name}` cannot be used in a loadable byte expression because it is not a C fragment"
                )
            })?;
            range_bytes_from_c_expression(&c_fragment).ok_or_else(|| {
                format!("contract `let` `{name}` cannot be used in a loadable byte expression")
            })
        }
        RangeBytes::Add(left, right) => Ok(RangeBytes::Add(
            Box::new(apply_contract_lets_to_range_bytes(*left, bindings)?),
            Box::new(apply_contract_lets_to_range_bytes(*right, bindings)?),
        )),
        RangeBytes::Subtract(left, right) => Ok(RangeBytes::Subtract(
            Box::new(apply_contract_lets_to_range_bytes(*left, bindings)?),
            Box::new(apply_contract_lets_to_range_bytes(*right, bindings)?),
        )),
        RangeBytes::Multiply(left, right) => Ok(RangeBytes::Multiply(
            Box::new(apply_contract_lets_to_range_bytes(*left, bindings)?),
            Box::new(apply_contract_lets_to_range_bytes(*right, bindings)?),
        )),
    }?;
    reject_contract_where_let_references(
        &range_bytes_referenced_names(&bytes),
        bindings,
        "loadable byte expressions",
    )?;
    Ok(bytes)
}

pub(super) fn reject_contract_where_let_references(
    referenced_names: &BTreeSet<String>,
    bindings: &[ContractLetBinding],
    context: &str,
) -> Result<(), String> {
    if let Some(binding) = bindings.iter().find(|binding| {
        binding.where_condition().is_some() && referenced_names.contains(&binding.name)
    }) {
        return Err(format!(
            "`let ... where` `{}` cannot be used in {context} yet",
            binding.name
        ));
    }
    Ok(())
}

pub(super) fn range_bytes_referenced_names(bytes: &RangeBytes) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    collect_range_bytes_referenced_names(bytes, &mut names);
    names
}

pub(super) fn collect_range_bytes_referenced_names(
    bytes: &RangeBytes,
    names: &mut BTreeSet<String>,
) {
    match bytes {
        RangeBytes::Constant(_) => {}
        RangeBytes::Parameter(name) => {
            names.insert(name.clone());
        }
        RangeBytes::Add(left, right)
        | RangeBytes::Subtract(left, right)
        | RangeBytes::Multiply(left, right) => {
            collect_range_bytes_referenced_names(left, names);
            collect_range_bytes_referenced_names(right, names);
        }
    }
}

pub(super) fn range_bytes_from_c_expression(expression: &CExpression) -> Option<RangeBytes> {
    match expression {
        CExpression::Value(CValue::Int32(Bitvector32Term::Constant(value))) => {
            Some(RangeBytes::Constant(*value))
        }
        CExpression::Variable(name) => Some(RangeBytes::Parameter(name.clone())),
        CExpression::Add(left, right) => Some(RangeBytes::Add(
            Box::new(range_bytes_from_c_expression(left)?),
            Box::new(range_bytes_from_c_expression(right)?),
        )),
        CExpression::Subtract(left, right) => Some(RangeBytes::Subtract(
            Box::new(range_bytes_from_c_expression(left)?),
            Box::new(range_bytes_from_c_expression(right)?),
        )),
        CExpression::Multiply(left, right) => Some(RangeBytes::Multiply(
            Box::new(range_bytes_from_c_expression(left)?),
            Box::new(range_bytes_from_c_expression(right)?),
        )),
        _ => None,
    }
}

pub(super) fn apply_contract_lets_to_proposition(
    proposition: ClickProposition,
    bindings: &[ContractLetBinding],
) -> Result<ClickProposition, String> {
    let proposition = apply_contract_let_expressions_to_proposition(proposition, bindings)?;
    wrap_contract_where_lets_proposition(proposition, bindings)
}

pub(super) fn apply_contract_let_expressions_to_proposition(
    proposition: ClickProposition,
    bindings: &[ContractLetBinding],
) -> Result<ClickProposition, String> {
    match proposition {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => Ok(ClickProposition::Comparison {
            left: apply_contract_lets_to_expression(left, bindings)?,
            operator,
            right: apply_contract_lets_to_expression(right, bindings)?,
        }),
        ClickProposition::Separate { left, right } => Ok(ClickProposition::Separate {
            left: apply_contract_lets_to_resource_subject(left, bindings)?,
            right: apply_contract_lets_to_resource_subject(right, bindings)?,
        }),
        ClickProposition::Contains { parent, child } => Ok(ClickProposition::Contains {
            parent: apply_contract_lets_to_resource_subject(parent, bindings)?,
            child: apply_contract_lets_to_resource_subject(child, bindings)?,
        }),
        ClickProposition::Loadable { segment } => Ok(ClickProposition::Loadable {
            segment: apply_contract_lets_to_segment(segment, bindings)?,
        }),
        ClickProposition::Defined { expression } => Ok(ClickProposition::Defined {
            expression: apply_contract_lets_to_expression(expression, bindings)?,
        }),
        ClickProposition::At {
            selector,
            proposition,
        } => Ok(ClickProposition::At {
            selector,
            proposition: Box::new(apply_contract_let_expressions_to_proposition(
                *proposition,
                bindings,
            )?),
        }),
        ClickProposition::And(left, right) => Ok(ClickProposition::And(
            Box::new(apply_contract_let_expressions_to_proposition(
                *left, bindings,
            )?),
            Box::new(apply_contract_let_expressions_to_proposition(
                *right, bindings,
            )?),
        )),
        ClickProposition::Or(left, right) => Ok(ClickProposition::Or(
            Box::new(apply_contract_let_expressions_to_proposition(
                *left, bindings,
            )?),
            Box::new(apply_contract_let_expressions_to_proposition(
                *right, bindings,
            )?),
        )),
        ClickProposition::Not(body) => Ok(ClickProposition::Not(Box::new(
            apply_contract_let_expressions_to_proposition(*body, bindings)?,
        ))),
        ClickProposition::Implies(left, right) => Ok(ClickProposition::Implies(
            Box::new(apply_contract_let_expressions_to_proposition(
                *left, bindings,
            )?),
            Box::new(apply_contract_let_expressions_to_proposition(
                *right, bindings,
            )?),
        )),
        ClickProposition::ForAll { c_type, name, body } => {
            let scoped = contract_lets_without_name(bindings, &name);
            Ok(ClickProposition::ForAll {
                c_type,
                name,
                body: Box::new(apply_contract_let_expressions_to_proposition(
                    *body, &scoped,
                )?),
            })
        }
        ClickProposition::Exists { c_type, name, body } => {
            let scoped = contract_lets_without_name(bindings, &name);
            Ok(ClickProposition::Exists {
                c_type,
                name,
                body: Box::new(apply_contract_let_expressions_to_proposition(
                    *body, &scoped,
                )?),
            })
        }
        ClickProposition::RangeAll {
            start,
            end,
            item,
            body,
        } => {
            let scoped = contract_lets_without_name(bindings, &item);
            Ok(ClickProposition::RangeAll {
                start: apply_contract_lets_to_expression(start, bindings)?,
                end: apply_contract_lets_to_expression(end, bindings)?,
                item,
                body: Box::new(apply_contract_let_expressions_to_proposition(
                    *body, &scoped,
                )?),
            })
        }
        ClickProposition::RangeAny {
            start,
            end,
            item,
            body,
        } => {
            let scoped = contract_lets_without_name(bindings, &item);
            Ok(ClickProposition::RangeAny {
                start: apply_contract_lets_to_expression(start, bindings)?,
                end: apply_contract_lets_to_expression(end, bindings)?,
                item,
                body: Box::new(apply_contract_let_expressions_to_proposition(
                    *body, &scoped,
                )?),
            })
        }
        ClickProposition::PredicateCall { name, arguments } => {
            Ok(ClickProposition::PredicateCall {
                name,
                arguments: arguments
                    .into_iter()
                    .map(|argument| apply_contract_lets_to_expression(argument, bindings))
                    .collect::<Result<Vec<_>, _>>()?,
            })
        }
    }
}

pub(super) fn wrap_contract_where_lets_proposition(
    mut proposition: ClickProposition,
    bindings: &[ContractLetBinding],
) -> Result<ClickProposition, String> {
    for (index, binding) in bindings.iter().enumerate().rev() {
        let Some(condition) = binding.where_condition() else {
            continue;
        };
        let condition =
            apply_contract_let_expressions_to_proposition(condition.clone(), &bindings[..index])?;
        let Some(c_type) = binding.c_type else {
            return Err(format!(
                "`let ... where` `{}` requires an explicit type annotation",
                binding.name
            ));
        };
        proposition = ClickProposition::Exists {
            c_type,
            name: binding.name.clone(),
            body: Box::new(ClickProposition::And(
                Box::new(condition),
                Box::new(proposition),
            )),
        };
    }
    Ok(proposition)
}

pub(super) fn apply_contract_lets_to_expression(
    expression: ContractExpression,
    bindings: &[ContractLetBinding],
) -> Result<ContractExpression, String> {
    let referenced_names = contract_expression_referenced_names(&expression);
    let referenced_bindings = bindings
        .iter()
        .filter(|binding| binding.value().is_some() && referenced_names.contains(&binding.name))
        .cloned()
        .collect::<Vec<_>>();
    let substitutions = contract_let_substitutions(bindings);
    let expression = substitute_contract_expression(&expression, &substitutions)?;
    Ok(wrap_contract_lets_expression(
        expression,
        &referenced_bindings,
    ))
}

pub(super) fn wrap_contract_lets_expression(
    mut expression: ContractExpression,
    bindings: &[ContractLetBinding],
) -> ContractExpression {
    for binding in bindings.iter().rev() {
        let Some(value) = binding.value() else {
            continue;
        };
        expression = ContractExpression::Let {
            name: binding.name.clone(),
            c_type: binding.c_type,
            value: Box::new(value.clone()),
            body: Box::new(expression),
        };
    }
    expression
}

pub(super) fn contract_lets_without_name(
    bindings: &[ContractLetBinding],
    name: &str,
) -> Vec<ContractLetBinding> {
    bindings
        .iter()
        .filter(|binding| binding.name != name)
        .cloned()
        .collect()
}

pub(super) fn contract_expression_referenced_names(
    expression: &ContractExpression,
) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    collect_contract_expression_referenced_names(expression, &mut names);
    names
}

pub(super) fn collect_contract_expression_referenced_names(
    expression: &ContractExpression,
    names: &mut BTreeSet<String>,
) {
    match expression {
        ContractExpression::CFragment(expression) => {
            collect_c_expression_referenced_names(expression, names);
        }
        ContractExpression::Field { base, .. } => {
            collect_contract_expression_referenced_names(base, names);
        }
        ContractExpression::CBinding(name) => {
            names.insert(name.clone());
        }
        ContractExpression::Old(expression) | ContractExpression::BitwiseNot(expression) => {
            collect_contract_expression_referenced_names(expression, names);
        }
        ContractExpression::At { expression, .. } => {
            collect_contract_expression_referenced_names(expression, names);
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
            collect_contract_expression_referenced_names(left, names);
            collect_contract_expression_referenced_names(right, names);
        }
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_click_proposition_referenced_names(condition, names);
            collect_contract_expression_referenced_names(then_branch, names);
            collect_contract_expression_referenced_names(else_branch, names);
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            collect_contract_expression_referenced_names(start, names);
            collect_contract_expression_referenced_names(end, names);
            collect_contract_expression_referenced_names(initial, names);
            let mut body_names = BTreeSet::new();
            collect_contract_expression_referenced_names(body, &mut body_names);
            body_names.remove(accumulator);
            body_names.remove(item);
            names.extend(body_names);
        }
        ContractExpression::Let {
            name, value, body, ..
        } => {
            collect_contract_expression_referenced_names(value, names);
            let mut body_names = BTreeSet::new();
            collect_contract_expression_referenced_names(body, &mut body_names);
            body_names.remove(name);
            names.extend(body_names);
        }
        ContractExpression::Call { arguments, .. } => {
            for argument in arguments {
                collect_contract_expression_referenced_names(argument, names);
            }
        }
    }
}

pub(super) fn collect_click_proposition_referenced_names(
    proposition: &ClickProposition,
    names: &mut BTreeSet<String>,
) {
    match proposition {
        ClickProposition::Comparison { left, right, .. } => {
            collect_contract_expression_referenced_names(left, names);
            collect_contract_expression_referenced_names(right, names);
        }
        ClickProposition::Separate { left, right } => {
            collect_resource_subject_referenced_names(left, names);
            collect_resource_subject_referenced_names(right, names);
        }
        ClickProposition::Contains { parent, child } => {
            collect_resource_subject_referenced_names(parent, names);
            collect_resource_subject_referenced_names(child, names);
        }
        ClickProposition::Loadable { segment } => {
            names.extend(contract_segment_referenced_names(segment));
        }
        ClickProposition::Defined { expression } => {
            collect_contract_expression_referenced_names(expression, names);
        }
        ClickProposition::At { proposition, .. } => {
            collect_click_proposition_referenced_names(proposition, names);
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            collect_click_proposition_referenced_names(left, names);
            collect_click_proposition_referenced_names(right, names);
        }
        ClickProposition::Not(body) => collect_click_proposition_referenced_names(body, names),
        ClickProposition::ForAll { name, body, .. }
        | ClickProposition::Exists { name, body, .. } => {
            let mut body_names = BTreeSet::new();
            collect_click_proposition_referenced_names(body, &mut body_names);
            body_names.remove(name);
            names.extend(body_names);
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
            collect_contract_expression_referenced_names(start, names);
            collect_contract_expression_referenced_names(end, names);
            let mut body_names = BTreeSet::new();
            collect_click_proposition_referenced_names(body, &mut body_names);
            body_names.remove(item);
            names.extend(body_names);
        }
        ClickProposition::PredicateCall { arguments, .. } => {
            for argument in arguments {
                collect_contract_expression_referenced_names(argument, names);
            }
        }
    }
}

pub(super) fn contract_let_substitutions(
    bindings: &[ContractLetBinding],
) -> BTreeMap<String, ContractExpression> {
    bindings
        .iter()
        .filter_map(|binding| {
            binding
                .value()
                .map(|value| (binding.name.clone(), value.clone()))
        })
        .collect()
}

pub(super) fn substitute_contract_expression(
    expression: &ContractExpression,
    substitutions: &BTreeMap<String, ContractExpression>,
) -> Result<ContractExpression, String> {
    match expression {
        ContractExpression::CBinding(_) => Ok(expression.clone()),
        ContractExpression::CFragment(CExpression::Variable(name)) => Ok(substitutions
            .get(name)
            .cloned()
            .unwrap_or_else(|| expression.clone())),
        ContractExpression::CFragment(expression) => {
            substitute_c_fragment_as_contract(expression, substitutions)
        }
        ContractExpression::Field {
            base,
            field,
            lowered,
        } => Ok(ContractExpression::Field {
            base: Box::new(substitute_contract_expression(base, substitutions)?),
            field: field.clone(),
            lowered: substitute_c_fragment(lowered, substitutions)?,
        }),
        ContractExpression::Old(expression) => Ok(ContractExpression::Old(Box::new(
            substitute_contract_expression(expression, substitutions)?,
        ))),
        ContractExpression::At {
            selector,
            expression,
        } => Ok(ContractExpression::At {
            selector: selector.clone(),
            expression: Box::new(substitute_contract_expression(expression, substitutions)?),
        }),
        ContractExpression::Add(left, right) => Ok(ContractExpression::Add(
            Box::new(substitute_contract_expression(left, substitutions)?),
            Box::new(substitute_contract_expression(right, substitutions)?),
        )),
        ContractExpression::Subtract(left, right) => Ok(ContractExpression::Subtract(
            Box::new(substitute_contract_expression(left, substitutions)?),
            Box::new(substitute_contract_expression(right, substitutions)?),
        )),
        ContractExpression::Multiply(left, right) => Ok(ContractExpression::Multiply(
            Box::new(substitute_contract_expression(left, substitutions)?),
            Box::new(substitute_contract_expression(right, substitutions)?),
        )),
        ContractExpression::Divide(left, right) => Ok(ContractExpression::Divide(
            Box::new(substitute_contract_expression(left, substitutions)?),
            Box::new(substitute_contract_expression(right, substitutions)?),
        )),
        ContractExpression::Remainder(left, right) => Ok(ContractExpression::Remainder(
            Box::new(substitute_contract_expression(left, substitutions)?),
            Box::new(substitute_contract_expression(right, substitutions)?),
        )),
        ContractExpression::ShiftLeft(left, right) => Ok(ContractExpression::ShiftLeft(
            Box::new(substitute_contract_expression(left, substitutions)?),
            Box::new(substitute_contract_expression(right, substitutions)?),
        )),
        ContractExpression::ShiftRight(left, right) => Ok(ContractExpression::ShiftRight(
            Box::new(substitute_contract_expression(left, substitutions)?),
            Box::new(substitute_contract_expression(right, substitutions)?),
        )),
        ContractExpression::BitwiseAnd(left, right) => Ok(ContractExpression::BitwiseAnd(
            Box::new(substitute_contract_expression(left, substitutions)?),
            Box::new(substitute_contract_expression(right, substitutions)?),
        )),
        ContractExpression::BitwiseOr(left, right) => Ok(ContractExpression::BitwiseOr(
            Box::new(substitute_contract_expression(left, substitutions)?),
            Box::new(substitute_contract_expression(right, substitutions)?),
        )),
        ContractExpression::BitwiseXor(left, right) => Ok(ContractExpression::BitwiseXor(
            Box::new(substitute_contract_expression(left, substitutions)?),
            Box::new(substitute_contract_expression(right, substitutions)?),
        )),
        ContractExpression::BitwiseNot(expression) => Ok(ContractExpression::BitwiseNot(Box::new(
            substitute_contract_expression(expression, substitutions)?,
        ))),
        ContractExpression::Index(base, index) => Ok(ContractExpression::Index(
            Box::new(substitute_contract_expression(base, substitutions)?),
            Box::new(substitute_contract_expression(index, substitutions)?),
        )),
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => Ok(ContractExpression::If {
            condition: Box::new(substitute_click_proposition(condition, substitutions)?),
            then_branch: Box::new(substitute_contract_expression(then_branch, substitutions)?),
            else_branch: Box::new(substitute_contract_expression(else_branch, substitutions)?),
        }),
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            let mut scoped = substitutions.clone();
            scoped.remove(accumulator);
            scoped.remove(item);
            Ok(ContractExpression::RangeFold {
                start: Box::new(substitute_contract_expression(start, substitutions)?),
                end: Box::new(substitute_contract_expression(end, substitutions)?),
                initial: Box::new(substitute_contract_expression(initial, substitutions)?),
                accumulator: accumulator.clone(),
                item: item.clone(),
                body: Box::new(substitute_contract_expression(body, &scoped)?),
            })
        }
        ContractExpression::Let {
            name,
            c_type,
            value,
            body,
        } => {
            let mut scoped = substitutions.clone();
            scoped.remove(name);
            Ok(ContractExpression::Let {
                name: name.clone(),
                c_type: *c_type,
                value: Box::new(substitute_contract_expression(value, substitutions)?),
                body: Box::new(substitute_contract_expression(body, &scoped)?),
            })
        }
        ContractExpression::Call { name, arguments } => Ok(ContractExpression::Call {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_contract_expression(argument, substitutions))
                .collect::<Result<Vec<_>, _>>()?,
        }),
    }
}

pub(super) fn substitute_c_fragment_as_contract(
    expression: &CExpression,
    substitutions: &BTreeMap<String, ContractExpression>,
) -> Result<ContractExpression, String> {
    match expression {
        CExpression::Value(_) => Ok(ContractExpression::CFragment(expression.clone())),
        CExpression::Variable(name) => Ok(substitutions
            .get(name)
            .cloned()
            .unwrap_or_else(|| ContractExpression::CFragment(expression.clone()))),
        CExpression::Add(left, right) => Ok(ContractExpression::Add(
            Box::new(substitute_c_fragment_as_contract(left, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(right, substitutions)?),
        )),
        CExpression::Subtract(left, right) => Ok(ContractExpression::Subtract(
            Box::new(substitute_c_fragment_as_contract(left, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(right, substitutions)?),
        )),
        CExpression::Multiply(left, right) => Ok(ContractExpression::Multiply(
            Box::new(substitute_c_fragment_as_contract(left, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(right, substitutions)?),
        )),
        CExpression::Divide(left, right) => Ok(ContractExpression::Divide(
            Box::new(substitute_c_fragment_as_contract(left, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(right, substitutions)?),
        )),
        CExpression::Remainder(left, right) => Ok(ContractExpression::Remainder(
            Box::new(substitute_c_fragment_as_contract(left, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(right, substitutions)?),
        )),
        CExpression::ShiftLeft(left, right) => Ok(ContractExpression::ShiftLeft(
            Box::new(substitute_c_fragment_as_contract(left, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(right, substitutions)?),
        )),
        CExpression::ShiftRight(left, right) => Ok(ContractExpression::ShiftRight(
            Box::new(substitute_c_fragment_as_contract(left, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(right, substitutions)?),
        )),
        CExpression::BitwiseAnd(left, right) => Ok(ContractExpression::BitwiseAnd(
            Box::new(substitute_c_fragment_as_contract(left, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(right, substitutions)?),
        )),
        CExpression::BitwiseOr(left, right) => Ok(ContractExpression::BitwiseOr(
            Box::new(substitute_c_fragment_as_contract(left, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(right, substitutions)?),
        )),
        CExpression::BitwiseXor(left, right) => Ok(ContractExpression::BitwiseXor(
            Box::new(substitute_c_fragment_as_contract(left, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(right, substitutions)?),
        )),
        CExpression::BitwiseNot(expression) => Ok(ContractExpression::BitwiseNot(Box::new(
            substitute_c_fragment_as_contract(expression, substitutions)?,
        ))),
        CExpression::Index(base, index) => Ok(ContractExpression::Index(
            Box::new(substitute_c_fragment_as_contract(base, substitutions)?),
            Box::new(substitute_c_fragment_as_contract(index, substitutions)?),
        )),
        _ => Ok(ContractExpression::CFragment(substitute_c_fragment(
            expression,
            substitutions,
        )?)),
    }
}

pub(super) fn substitute_c_fragment(
    expression: &CExpression,
    substitutions: &BTreeMap<String, ContractExpression>,
) -> Result<CExpression, String> {
    match expression {
        CExpression::Value(_) => Ok(expression.clone()),
        CExpression::Variable(name) => {
            let Some(substitution) = substitutions.get(name) else {
                return Ok(expression.clone());
            };
            contract_expression_as_c_fragment(substitution).ok_or_else(|| {
                format!(
                    "cannot substitute non-C-fragment expression for `{name}` inside C fragment `{expression:?}`"
                )
            })
        }
        CExpression::AddressOf(body) => Ok(CExpression::AddressOf(Box::new(
            substitute_c_fragment(body, substitutions)?,
        ))),
        CExpression::PointerOffsetBytes { pointer, bytes } => Ok(CExpression::PointerOffsetBytes {
            pointer: Box::new(substitute_c_fragment(pointer, substitutions)?),
            bytes: *bytes,
        }),
        CExpression::LessThan(left, right) => Ok(CExpression::LessThan(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::LessEqual(left, right) => Ok(CExpression::LessEqual(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::GreaterThan(left, right) => Ok(CExpression::GreaterThan(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::GreaterEqual(left, right) => Ok(CExpression::GreaterEqual(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::Equal(left, right) => Ok(CExpression::Equal(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::NotEqual(left, right) => Ok(CExpression::NotEqual(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::Not(body) => Ok(CExpression::Not(Box::new(substitute_c_fragment(
            body,
            substitutions,
        )?))),
        CExpression::And(left, right) => Ok(CExpression::And(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::Or(left, right) => Ok(CExpression::Or(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::Add(left, right) => Ok(CExpression::Add(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::Subtract(left, right) => Ok(CExpression::Subtract(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::Multiply(left, right) => Ok(CExpression::Multiply(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::Divide(left, right) => Ok(CExpression::Divide(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::Remainder(left, right) => Ok(CExpression::Remainder(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::ShiftLeft(left, right) => Ok(CExpression::ShiftLeft(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::ShiftRight(left, right) => Ok(CExpression::ShiftRight(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::BitwiseAnd(left, right) => Ok(CExpression::BitwiseAnd(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::BitwiseOr(left, right) => Ok(CExpression::BitwiseOr(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::BitwiseXor(left, right) => Ok(CExpression::BitwiseXor(
            Box::new(substitute_c_fragment(left, substitutions)?),
            Box::new(substitute_c_fragment(right, substitutions)?),
        )),
        CExpression::BitwiseNot(expression) => Ok(CExpression::BitwiseNot(Box::new(
            substitute_c_fragment(expression, substitutions)?,
        ))),
        CExpression::Load(body) => Ok(CExpression::Load(Box::new(substitute_c_fragment(
            body,
            substitutions,
        )?))),
        CExpression::TypedLoad {
            pointer,
            value_type,
        } => Ok(CExpression::TypedLoad {
            pointer: Box::new(substitute_c_fragment(pointer, substitutions)?),
            value_type: *value_type,
        }),
        CExpression::Index(base, index) => Ok(CExpression::Index(
            Box::new(substitute_c_fragment(base, substitutions)?),
            Box::new(substitute_c_fragment(index, substitutions)?),
        )),
    }
}

pub(super) fn contract_expression_as_c_fragment(
    expression: &ContractExpression,
) -> Option<CExpression> {
    match expression {
        ContractExpression::CFragment(expression) => Some(expression.clone()),
        ContractExpression::Field { lowered, .. } => Some(lowered.clone()),
        ContractExpression::CBinding(name) => Some(CExpression::Variable(name.clone())),
        ContractExpression::Old(_) => None,
        ContractExpression::At { .. } => None,
        ContractExpression::Add(left, right) => Some(CExpression::Add(
            Box::new(contract_expression_as_c_fragment(left)?),
            Box::new(contract_expression_as_c_fragment(right)?),
        )),
        ContractExpression::Subtract(left, right) => Some(CExpression::Subtract(
            Box::new(contract_expression_as_c_fragment(left)?),
            Box::new(contract_expression_as_c_fragment(right)?),
        )),
        ContractExpression::Multiply(left, right) => Some(CExpression::Multiply(
            Box::new(contract_expression_as_c_fragment(left)?),
            Box::new(contract_expression_as_c_fragment(right)?),
        )),
        ContractExpression::Divide(left, right) => Some(CExpression::Divide(
            Box::new(contract_expression_as_c_fragment(left)?),
            Box::new(contract_expression_as_c_fragment(right)?),
        )),
        ContractExpression::Remainder(left, right) => Some(CExpression::Remainder(
            Box::new(contract_expression_as_c_fragment(left)?),
            Box::new(contract_expression_as_c_fragment(right)?),
        )),
        ContractExpression::ShiftLeft(left, right) => Some(CExpression::ShiftLeft(
            Box::new(contract_expression_as_c_fragment(left)?),
            Box::new(contract_expression_as_c_fragment(right)?),
        )),
        ContractExpression::ShiftRight(left, right) => Some(CExpression::ShiftRight(
            Box::new(contract_expression_as_c_fragment(left)?),
            Box::new(contract_expression_as_c_fragment(right)?),
        )),
        ContractExpression::BitwiseAnd(left, right) => Some(CExpression::BitwiseAnd(
            Box::new(contract_expression_as_c_fragment(left)?),
            Box::new(contract_expression_as_c_fragment(right)?),
        )),
        ContractExpression::BitwiseOr(left, right) => Some(CExpression::BitwiseOr(
            Box::new(contract_expression_as_c_fragment(left)?),
            Box::new(contract_expression_as_c_fragment(right)?),
        )),
        ContractExpression::BitwiseXor(left, right) => Some(CExpression::BitwiseXor(
            Box::new(contract_expression_as_c_fragment(left)?),
            Box::new(contract_expression_as_c_fragment(right)?),
        )),
        ContractExpression::BitwiseNot(expression) => Some(CExpression::BitwiseNot(Box::new(
            contract_expression_as_c_fragment(expression)?,
        ))),
        ContractExpression::Index(base, index) => Some(CExpression::Index(
            Box::new(contract_expression_as_c_fragment(base)?),
            Box::new(contract_expression_as_c_fragment(index)?),
        )),
        ContractExpression::If { .. }
        | ContractExpression::RangeFold { .. }
        | ContractExpression::Let { .. } => None,
        ContractExpression::Call { .. } => None,
    }
}

pub(super) fn structural_item_kind_label(kind: StructuralItemKind) -> &'static str {
    match kind {
        StructuralItemKind::Assert => "assert",
        StructuralItemKind::Invariant => "invariant",
        StructuralItemKind::Effect => "effect",
        StructuralItemKind::StepEffect => "step effect",
    }
}

fn prepend_labeled_asserts(statement: CStatement, checks: &[LabeledCheck]) -> CStatement {
    checks.iter().rev().fold(statement, |statement, check| {
        c_seq(
            c_labeled_assert(check.condition.clone(), check.label.clone()),
            statement,
        )
    })
}

pub(super) fn click_proposition_to_c_expression(
    proposition: &ClickProposition,
) -> Option<CExpression> {
    match proposition {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => {
            let left = contract_expression_to_c_fragment(left)?;
            let right = contract_expression_to_c_fragment(right)?;
            Some(match operator {
                ComparisonOperator::Equal => CExpression::Equal(Box::new(left), Box::new(right)),
                ComparisonOperator::NotEqual => {
                    CExpression::NotEqual(Box::new(left), Box::new(right))
                }
                ComparisonOperator::LessThan => {
                    CExpression::LessThan(Box::new(left), Box::new(right))
                }
                ComparisonOperator::LessEqual => {
                    CExpression::LessEqual(Box::new(left), Box::new(right))
                }
                ComparisonOperator::GreaterThan => {
                    CExpression::GreaterThan(Box::new(left), Box::new(right))
                }
                ComparisonOperator::GreaterEqual => {
                    CExpression::GreaterEqual(Box::new(left), Box::new(right))
                }
            })
        }
        ClickProposition::And(left, right) => Some(CExpression::And(
            Box::new(click_proposition_to_c_expression(left)?),
            Box::new(click_proposition_to_c_expression(right)?),
        )),
        ClickProposition::Or(left, right) => Some(CExpression::Or(
            Box::new(click_proposition_to_c_expression(left)?),
            Box::new(click_proposition_to_c_expression(right)?),
        )),
        ClickProposition::Not(body) => Some(CExpression::Not(Box::new(
            click_proposition_to_c_expression(body)?,
        ))),
        ClickProposition::Implies(left, right) => Some(CExpression::Or(
            Box::new(CExpression::Not(Box::new(
                click_proposition_to_c_expression(left)?,
            ))),
            Box::new(click_proposition_to_c_expression(right)?),
        )),
        ClickProposition::ForAll { .. }
        | ClickProposition::Exists { .. }
        | ClickProposition::RangeAll { .. }
        | ClickProposition::RangeAny { .. }
        | ClickProposition::Separate { .. }
        | ClickProposition::Contains { .. }
        | ClickProposition::Loadable { .. }
        | ClickProposition::Defined { .. }
        | ClickProposition::At { .. }
        | ClickProposition::PredicateCall { .. } => None,
    }
}

pub(super) fn c_comparison_operator(operator: ComparisonOperator) -> CComparisonOperator {
    match operator {
        ComparisonOperator::Equal => CComparisonOperator::Equal,
        ComparisonOperator::NotEqual => CComparisonOperator::NotEqual,
        ComparisonOperator::LessThan => CComparisonOperator::LessThan,
        ComparisonOperator::LessEqual => CComparisonOperator::LessEqual,
        ComparisonOperator::GreaterThan => CComparisonOperator::GreaterThan,
        ComparisonOperator::GreaterEqual => CComparisonOperator::GreaterEqual,
    }
}

pub(super) fn contract_expression_to_c_fragment(
    expression: &ContractExpression,
) -> Option<CExpression> {
    match expression {
        ContractExpression::CFragment(expression) => Some(expression.clone()),
        ContractExpression::Field { lowered, .. } => Some(lowered.clone()),
        ContractExpression::CBinding(name) => Some(CExpression::Variable(name.clone())),
        ContractExpression::Old(_) => None,
        ContractExpression::At { .. } => None,
        ContractExpression::Add(left, right) => Some(CExpression::Add(
            Box::new(contract_expression_to_c_fragment(left)?),
            Box::new(contract_expression_to_c_fragment(right)?),
        )),
        ContractExpression::Subtract(left, right) => Some(CExpression::Subtract(
            Box::new(contract_expression_to_c_fragment(left)?),
            Box::new(contract_expression_to_c_fragment(right)?),
        )),
        ContractExpression::Multiply(left, right) => Some(CExpression::Multiply(
            Box::new(contract_expression_to_c_fragment(left)?),
            Box::new(contract_expression_to_c_fragment(right)?),
        )),
        ContractExpression::Divide(left, right) => Some(CExpression::Divide(
            Box::new(contract_expression_to_c_fragment(left)?),
            Box::new(contract_expression_to_c_fragment(right)?),
        )),
        ContractExpression::Remainder(left, right) => Some(CExpression::Remainder(
            Box::new(contract_expression_to_c_fragment(left)?),
            Box::new(contract_expression_to_c_fragment(right)?),
        )),
        ContractExpression::ShiftLeft(left, right) => Some(CExpression::ShiftLeft(
            Box::new(contract_expression_to_c_fragment(left)?),
            Box::new(contract_expression_to_c_fragment(right)?),
        )),
        ContractExpression::ShiftRight(left, right) => Some(CExpression::ShiftRight(
            Box::new(contract_expression_to_c_fragment(left)?),
            Box::new(contract_expression_to_c_fragment(right)?),
        )),
        ContractExpression::BitwiseAnd(left, right) => Some(CExpression::BitwiseAnd(
            Box::new(contract_expression_to_c_fragment(left)?),
            Box::new(contract_expression_to_c_fragment(right)?),
        )),
        ContractExpression::BitwiseOr(left, right) => Some(CExpression::BitwiseOr(
            Box::new(contract_expression_to_c_fragment(left)?),
            Box::new(contract_expression_to_c_fragment(right)?),
        )),
        ContractExpression::BitwiseXor(left, right) => Some(CExpression::BitwiseXor(
            Box::new(contract_expression_to_c_fragment(left)?),
            Box::new(contract_expression_to_c_fragment(right)?),
        )),
        ContractExpression::BitwiseNot(expression) => Some(CExpression::BitwiseNot(Box::new(
            contract_expression_to_c_fragment(expression)?,
        ))),
        ContractExpression::Index(base, index) => Some(CExpression::Index(
            Box::new(contract_expression_to_c_fragment(base)?),
            Box::new(contract_expression_to_c_fragment(index)?),
        )),
        ContractExpression::If { .. }
        | ContractExpression::RangeFold { .. }
        | ContractExpression::Let { .. } => None,
        ContractExpression::Call { .. } => None,
    }
}

pub(super) fn count_loops(statement: &syntax::C0Statement) -> usize {
    match statement {
        syntax::C0Statement::Seq(first, second) => count_loops(first) + count_loops(second),
        syntax::C0Statement::If {
            then_branch,
            else_branch,
            ..
        } => count_loops(then_branch) + count_loops(else_branch),
        syntax::C0Statement::While { body, .. } => 1 + count_loops(body),
        _ => 0,
    }
}

pub(super) fn count_statements(statement: &syntax::C0Statement) -> usize {
    match statement {
        syntax::C0Statement::Seq(first, second) => {
            count_statements(first) + count_statements(second)
        }
        syntax::C0Statement::If {
            then_branch,
            else_branch,
            ..
        } => 1 + count_statements(then_branch) + count_statements(else_branch),
        syntax::C0Statement::While { body, .. } => 1 + count_statements(body),
        _ => 1,
    }
}

#[derive(Clone, Default)]
pub(super) struct SourceExecutionLayout {
    statements: BTreeMap<usize, SourceStatementRegion>,
    loop_bodies: BTreeMap<usize, usize>,
    loop_statements: BTreeMap<usize, usize>,
}

#[derive(Clone, Copy)]
pub(super) struct SourceStatementRegion {
    pub(super) continuation_node: usize,
    pub(super) kind: SourceStatementKind,
}

#[derive(Clone, Copy)]
pub(super) enum SourceStatementKind {
    Plain,
    If {
        then_statement_index: usize,
        else_statement_index: usize,
    },
    Loop {
        loop_index: usize,
    },
}

impl SourceExecutionLayout {
    pub(super) fn new(statement: &syntax::C0Statement) -> Self {
        fn visit(
            statement: &syntax::C0Statement,
            next_statement_index: &mut usize,
            next_loop_index: &mut usize,
            layout: &mut SourceExecutionLayout,
        ) {
            match statement {
                syntax::C0Statement::Seq(first, second) => {
                    visit(first, next_statement_index, next_loop_index, layout);
                    visit(second, next_statement_index, next_loop_index, layout);
                }
                syntax::C0Statement::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    let statement_index = *next_statement_index;
                    *next_statement_index += 1;
                    let then_statement_index = *next_statement_index;
                    visit(then_branch, next_statement_index, next_loop_index, layout);
                    let else_statement_index = *next_statement_index;
                    visit(else_branch, next_statement_index, next_loop_index, layout);
                    layout.statements.insert(
                        statement_index,
                        SourceStatementRegion {
                            continuation_node: *next_statement_index,
                            kind: SourceStatementKind::If {
                                then_statement_index,
                                else_statement_index,
                            },
                        },
                    );
                }
                syntax::C0Statement::While { body, .. } => {
                    let statement_index = *next_statement_index;
                    let loop_index = *next_loop_index;
                    *next_statement_index += 1;
                    *next_loop_index += 1;
                    layout.loop_bodies.insert(loop_index, *next_statement_index);
                    layout.loop_statements.insert(loop_index, statement_index);
                    visit(body, next_statement_index, next_loop_index, layout);
                    layout.statements.insert(
                        statement_index,
                        SourceStatementRegion {
                            continuation_node: *next_statement_index,
                            kind: SourceStatementKind::Loop { loop_index },
                        },
                    );
                }
                _ => {
                    let statement_index = *next_statement_index;
                    *next_statement_index += 1;
                    layout.statements.insert(
                        statement_index,
                        SourceStatementRegion {
                            continuation_node: *next_statement_index,
                            kind: SourceStatementKind::Plain,
                        },
                    );
                }
            }
        }

        let mut layout = Self::default();
        visit(statement, &mut 0, &mut 0, &mut layout);
        layout
    }

    pub(super) fn statement(&self, index: usize) -> Option<SourceStatementRegion> {
        self.statements.get(&index).copied()
    }

    pub(super) fn statement_count(&self) -> usize {
        self.statements.len()
    }

    pub(super) fn loop_body_entry(&self, loop_index: usize) -> Option<usize> {
        self.loop_bodies.get(&loop_index).copied()
    }

    pub(super) fn loop_statement(&self, loop_index: usize) -> Option<usize> {
        self.loop_statements.get(&loop_index).copied()
    }
}

pub(super) fn c0_loop_modified_locals(statement: &syntax::C0Statement) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    collect_c0_loop_modified_locals(statement, &mut names);
    names
}

pub(super) fn collect_c0_loop_modified_locals(
    statement: &syntax::C0Statement,
    names: &mut BTreeSet<String>,
) {
    match statement {
        syntax::C0Statement::Skip
        | syntax::C0Statement::Declare { .. }
        | syntax::C0Statement::Return(_)
        | syntax::C0Statement::Store { .. } => {}
        syntax::C0Statement::Assign { name, .. } => {
            names.insert(name.clone());
        }
        syntax::C0Statement::CallAssign { target, .. } => {
            names.insert(target.clone());
        }
        syntax::C0Statement::Seq(first, second) => {
            collect_c0_loop_modified_locals(first, names);
            collect_c0_loop_modified_locals(second, names);
        }
        syntax::C0Statement::If {
            then_branch,
            else_branch,
            ..
        } => {
            collect_c0_loop_modified_locals(then_branch, names);
            collect_c0_loop_modified_locals(else_branch, names);
        }
        syntax::C0Statement::While { body, .. } => {
            collect_c0_loop_modified_locals(body, names);
        }
    }
}

pub(super) fn contract_segment_referenced_names(segment: &ContractSegment) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    collect_c_expression_referenced_names(&segment.base, &mut names);
    collect_c_expression_referenced_names(&segment.start, &mut names);
    collect_c_expression_referenced_names(&segment.end, &mut names);
    names
}

fn collect_resource_subject_referenced_names(
    resource: &ResourceSubject,
    names: &mut BTreeSet<String>,
) {
    match resource {
        ResourceSubject::Memory(segment) => {
            names.extend(contract_segment_referenced_names(segment))
        }
        ResourceSubject::Declared { arguments, .. } => {
            for argument in arguments {
                collect_contract_expression_referenced_names(argument, names);
            }
        }
    }
}

pub(super) fn collect_c_expression_referenced_names(
    expression: &CExpression,
    names: &mut BTreeSet<String>,
) {
    match expression {
        CExpression::Value(_) => {}
        CExpression::Variable(name) => {
            names.insert(name.clone());
        }
        CExpression::AddressOf(expression)
        | CExpression::Not(expression)
        | CExpression::Load(expression) => {
            collect_c_expression_referenced_names(expression, names);
        }
        CExpression::PointerOffsetBytes { pointer, .. } => {
            collect_c_expression_referenced_names(pointer, names);
        }
        CExpression::TypedLoad { pointer, .. } => {
            collect_c_expression_referenced_names(pointer, names);
        }
        CExpression::LessThan(left, right)
        | CExpression::LessEqual(left, right)
        | CExpression::GreaterThan(left, right)
        | CExpression::GreaterEqual(left, right)
        | CExpression::Equal(left, right)
        | CExpression::NotEqual(left, right)
        | CExpression::And(left, right)
        | CExpression::Or(left, right)
        | CExpression::Add(left, right)
        | CExpression::Subtract(left, right)
        | CExpression::Multiply(left, right)
        | CExpression::Divide(left, right)
        | CExpression::Remainder(left, right)
        | CExpression::ShiftLeft(left, right)
        | CExpression::ShiftRight(left, right)
        | CExpression::BitwiseAnd(left, right)
        | CExpression::BitwiseOr(left, right)
        | CExpression::BitwiseXor(left, right)
        | CExpression::Index(left, right) => {
            collect_c_expression_referenced_names(left, names);
            collect_c_expression_referenced_names(right, names);
        }
        CExpression::BitwiseNot(expression) => {
            collect_c_expression_referenced_names(expression, names);
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ConcreteMemoryRangeSeed {
    pub(super) base: Pointer,
    pub(super) bytes: u32,
    pub(super) element_width: u32,
}

pub(super) fn initial_call_state(
    function_name: &str,
    requires: &[Requirement],
    parameters: &[syntax::C0Parameter],
) -> Result<(CState, Vec<CExpression>), ClickError> {
    let mut arguments = Vec::new();

    for (index, parameter) in parameters.iter().enumerate() {
        match parameter.c_type() {
            C0Type::Int32Pointer => {
                arguments.push(c_pointer_value(Pointer {
                    block: EXTERNAL_ARGUMENT_MEMORY_BLOCK.into(),
                    offset: scale_int32_offset(
                        Bitvector32Term::Variable(Variable(
                            POINTER_ARGUMENT_VARIABLE_BASE + index as u64,
                        )),
                        4,
                    ),
                }));
            }
            C0Type::UInt8Pointer => {
                arguments.push(c_pointer_value(Pointer {
                    block: EXTERNAL_ARGUMENT_MEMORY_BLOCK.into(),
                    offset: scale_int32_offset(
                        Bitvector32Term::Variable(Variable(
                            POINTER_ARGUMENT_VARIABLE_BASE + index as u64,
                        )),
                        1,
                    ),
                }));
            }
            C0Type::Int32 => {
                arguments.push(CExpression::Value(CValue::Int32(
                    Bitvector32Term::Variable(Variable(arguments.len() as u64)),
                )));
            }
            C0Type::UInt8 => {
                arguments.push(CExpression::Value(CValue::UInt8(
                    Bitvector32Term::Variable(Variable(arguments.len() as u64)),
                )));
            }
            C0Type::Int32Array(_) | C0Type::UInt8Array(_) => {
                return Err(ClickError::new(format!(
                    "array parameter `{}` should have lowered to a pointer",
                    parameter.name()
                )));
            }
        }
    }

    let mut loadable_ranges = BTreeMap::new();
    for requirement in requires {
        if let Some((name, bytes)) = concrete_loadable_block(requirement, parameters, &arguments)? {
            loadable_ranges.insert(name, bytes);
        }
        if let Requirement::Resource(resource) = requirement.inner()
            && let Some((name, bytes)) =
                concrete_access_resource_block(resource, parameters, &arguments)?
        {
            loadable_ranges.insert(name, bytes);
        }
    }

    for name in requires.iter().filter_map(requirement_loadable_name) {
        if !parameters.iter().any(|parameter| parameter.name() == name) {
            return Err(ClickError::new(format!(
                "`loadable` names `{name}`, but `{}` has no such parameter",
                function_name
            )));
        }
    }

    let mut memory = CMemory::new();
    memory = memory_with_symbolic_loadable_cells(memory, &loadable_ranges);
    memory = materialize_symbolic_access_resource_cells(memory, requires, parameters, &arguments)?;
    let resources = resource_context_from_requirements(requires, parameters, &arguments, &memory)?;
    Ok((
        CState::new()
            .with_memory(memory)
            .with_resource_context(resources),
        arguments,
    ))
}

pub(super) fn memory_with_symbolic_loadable_cells(
    mut memory: CMemory,
    loadable_ranges: &BTreeMap<String, ConcreteMemoryRangeSeed>,
) -> CMemory {
    let base_memory = memory.clone();
    for range in loadable_ranges.values() {
        let mut offset: u32 = 0;
        match range.element_width {
            1 => {
                while offset < range.bytes {
                    let pointer = offset_pointer_by_elements(
                        range.base.clone(),
                        Bitvector32Term::Constant(offset),
                        1,
                    );
                    let value = CValue::UInt8(Bitvector32Term::MemoryLoad(
                        Box::new(base_memory.clone()),
                        Box::new(pointer.clone()),
                    ));
                    memory = memory.store(pointer, value);
                    offset += 1;
                }
            }
            _ => {
                while offset.checked_add(4).is_some_and(|end| end <= range.bytes) {
                    let pointer = offset_pointer_by_int32_elements(
                        range.base.clone(),
                        Bitvector32Term::Constant(offset / 4),
                    );
                    let value = CValue::Int32(Bitvector32Term::MemoryLoad(
                        Box::new(base_memory.clone()),
                        Box::new(pointer.clone()),
                    ));
                    memory = memory.store(pointer, value);
                    offset += 4;
                }
            }
        }
    }
    memory
}

fn materialize_symbolic_access_resource_cells(
    mut memory: CMemory,
    requires: &[Requirement],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Result<CMemory, ClickError> {
    for requirement in requires {
        let Requirement::Resource(ResourceClause::Read(segment) | ResourceClause::Write(segment)) =
            requirement.inner()
        else {
            continue;
        };
        memory = materialize_access_segment_cells(memory, segment, parameters, arguments)?;
    }
    Ok(memory)
}

fn materialize_access_segment_cells(
    mut memory: CMemory,
    segment: &ContractSegment,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Result<CMemory, ClickError> {
    let state = CState::new().with_memory(memory.clone());
    let Ok(segment) = evaluate_requirement_segment(parameters, arguments, &state, segment) else {
        return Ok(memory);
    };
    let (Bitvector32Term::Constant(start), Bitvector32Term::Constant(end)) =
        (&segment.start, &segment.end)
    else {
        return Ok(memory);
    };
    if end < start {
        return Err(ClickError::new(format!(
            "resource segment has an end before its start: {start}..{end}"
        )));
    }

    let element_width = contract_segment_element_width(parameters, &segment.source);
    let base_memory = memory.clone();
    for index in *start..*end {
        let pointer = offset_pointer_by_elements(
            segment.base.clone(),
            Bitvector32Term::Constant(index),
            element_width,
        );
        if matches!(memory.load(&pointer), CExpressionOutcome::Value(_)) {
            continue;
        }
        let load =
            Bitvector32Term::MemoryLoad(Box::new(base_memory.clone()), Box::new(pointer.clone()));
        let value = match element_width {
            1 => CValue::UInt8(load),
            _ => CValue::Int32(load),
        };
        memory = memory.store(pointer, value);
    }
    Ok(memory)
}

pub(super) fn requirement_propositions(
    requires: &[Requirement],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: &CMemory,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Vec<Proposition>, ClickError> {
    let mut propositions = Vec::new();
    for requirement in requires {
        let proposition = match requirement.inner() {
            Requirement::LoadableBytes { .. } | Requirement::LoadableSegment { .. } => {
                loadable_requirement_prop(requirement, parameters, arguments, memory)?
            }
            Requirement::Proposition(proposition) => requirement_proposition_prop(
                parameters,
                arguments,
                memory,
                proposition,
                predicate_environment,
                click_function_environment,
            )?,
            Requirement::Resource(resource) => {
                let Some(proposition) =
                    resource_clause_loadable_prop(resource, parameters, arguments, memory)?
                else {
                    continue;
                };
                proposition
            }
            Requirement::Labeled { .. } => unreachable!("requirement.inner() removes labels"),
        };
        propositions.push(proposition);
    }
    Ok(propositions)
}

pub(super) fn resource_context_from_requirements(
    requires: &[Requirement],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: &CMemory,
) -> Result<ResourceContext, ClickError> {
    let mut context = ResourceContext::new();
    for requirement in requires {
        if let Requirement::Resource(resource) = requirement.inner() {
            // This lowering path has no proposition assumptions yet. It builds
            // a provisional context; execution paths use checked composition
            // once assumptions are available.
            context = context.unchecked_with_fact(lower_resource_clause(
                resource, parameters, arguments, memory,
            )?);
        }
    }
    Ok(context)
}

pub(super) fn lower_resource_clause(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: &CMemory,
) -> Result<CResourceFact, ClickError> {
    let values =
        parameter_values(parameters, arguments).map_err(|error| ClickError::new(error.message))?;
    let state = CState::new().with_memory(memory.clone());
    lower_resource_clause_with_values(resource, &values, &state)
}

pub(super) fn lower_resource_clause_at_state(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
) -> Result<CResourceFact, ClickError> {
    let mut values =
        parameter_values(parameters, arguments).map_err(|error| ClickError::new(error.message))?;
    values.extend(
        state
            .locals()
            .object_values()
            .map(|(name, value)| (name.to_string(), value.clone())),
    );
    lower_resource_clause_with_values(resource, &values, state)
}

fn lower_resource_clause_with_values(
    resource: &ResourceClause,
    values: &BTreeMap<String, CValue>,
    state: &CState,
) -> Result<CResourceFact, ClickError> {
    match resource {
        ResourceClause::Read(segment) => {
            let range = lower_resource_segment_with_values("read", segment, values, state)?;
            Ok(CResourceFact::view_memory(range))
        }
        ResourceClause::Write(segment) => {
            let range = lower_resource_segment_with_values("write", segment, values, state)?;
            Ok(CResourceFact::own_memory(range))
        }
        ResourceClause::Declared {
            access,
            kind,
            name,
            arguments: resource_arguments,
            parameter_types,
        } => {
            let assumptions = Assumptions::new();
            let mut resource_values = Vec::new();
            if resource_arguments.len() != parameter_types.len() {
                return Err(ClickError::new(format!(
                    "resource `{name}` has malformed argument type metadata"
                )));
            }
            for (index, (argument, parameter_type)) in
                resource_arguments.iter().zip(parameter_types).enumerate()
            {
                let argument = resource_argument_to_c_expression(argument)?;
                let value =
                    evaluate_c_contract_expression(values, state, None, &assumptions, &argument)
                        .map_err(|message| {
                            ClickError::new(format!(
                                "could not lower resource `{name}` argument {index}: {message}"
                            ))
                        })?;
                if !c_value_matches_click_type(&value, *parameter_type) {
                    return Err(ClickError::new(format!(
                        "resource `{name}` argument {index} evaluated to {value:?}, which does not match {:?}",
                        parameter_type
                    )));
                }
                resource_values.push(value);
            }
            let resource = match kind {
                ResourceKind::Composite => CResource::Composite {
                    name: name.clone(),
                    arguments: resource_values,
                },
                ResourceKind::Token => CResource::Token {
                    name: name.clone(),
                    arguments: resource_values,
                },
            };
            Ok(match access {
                ResourceAccessMode::Own => CResourceFact::Own(resource),
                ResourceAccessMode::View => CResourceFact::View(resource),
            })
        }
    }
}

pub(super) fn resource_argument_to_c_expression(
    argument: &ContractExpression,
) -> Result<CExpression, ClickError> {
    match argument {
        ContractExpression::CFragment(expression) => Ok(expression.clone()),
        ContractExpression::Field { lowered, .. } => Ok(lowered.clone()),
        ContractExpression::CBinding(name) => Ok(CExpression::Variable(name.clone())),
        ContractExpression::Add(left, right) => Ok(CExpression::Add(
            Box::new(resource_argument_to_c_expression(left)?),
            Box::new(resource_argument_to_c_expression(right)?),
        )),
        ContractExpression::Subtract(left, right) => Ok(CExpression::Subtract(
            Box::new(resource_argument_to_c_expression(left)?),
            Box::new(resource_argument_to_c_expression(right)?),
        )),
        ContractExpression::Multiply(left, right) => Ok(CExpression::Multiply(
            Box::new(resource_argument_to_c_expression(left)?),
            Box::new(resource_argument_to_c_expression(right)?),
        )),
        ContractExpression::Divide(left, right) => Ok(CExpression::Divide(
            Box::new(resource_argument_to_c_expression(left)?),
            Box::new(resource_argument_to_c_expression(right)?),
        )),
        ContractExpression::Remainder(left, right) => Ok(CExpression::Remainder(
            Box::new(resource_argument_to_c_expression(left)?),
            Box::new(resource_argument_to_c_expression(right)?),
        )),
        ContractExpression::ShiftLeft(left, right) => Ok(CExpression::ShiftLeft(
            Box::new(resource_argument_to_c_expression(left)?),
            Box::new(resource_argument_to_c_expression(right)?),
        )),
        ContractExpression::ShiftRight(left, right) => Ok(CExpression::ShiftRight(
            Box::new(resource_argument_to_c_expression(left)?),
            Box::new(resource_argument_to_c_expression(right)?),
        )),
        ContractExpression::BitwiseAnd(left, right) => Ok(CExpression::BitwiseAnd(
            Box::new(resource_argument_to_c_expression(left)?),
            Box::new(resource_argument_to_c_expression(right)?),
        )),
        ContractExpression::BitwiseOr(left, right) => Ok(CExpression::BitwiseOr(
            Box::new(resource_argument_to_c_expression(left)?),
            Box::new(resource_argument_to_c_expression(right)?),
        )),
        ContractExpression::BitwiseXor(left, right) => Ok(CExpression::BitwiseXor(
            Box::new(resource_argument_to_c_expression(left)?),
            Box::new(resource_argument_to_c_expression(right)?),
        )),
        ContractExpression::BitwiseNot(expression) => Ok(CExpression::BitwiseNot(Box::new(
            resource_argument_to_c_expression(expression)?,
        ))),
        ContractExpression::Index(base, index) => Ok(CExpression::Index(
            Box::new(resource_argument_to_c_expression(base)?),
            Box::new(resource_argument_to_c_expression(index)?),
        )),
        ContractExpression::Old(_)
        | ContractExpression::At { .. }
        | ContractExpression::If { .. }
        | ContractExpression::RangeFold { .. }
        | ContractExpression::Let { .. }
        | ContractExpression::Call { .. } => Err(ClickError::new(
            "declared resource arguments currently support current-state C expressions only",
        )),
    }
}

fn lower_resource_segment_with_values(
    resource_name: &str,
    segment: &ContractSegment,
    values: &BTreeMap<String, CValue>,
    state: &CState,
) -> Result<CMemoryRange, ClickError> {
    if segment.state != ContractSegmentState::Current {
        return Err(ClickError::new(format!(
            "could not lower `{resource_name}` resource: resource segments cannot use `old(...)`"
        )));
    }
    // Resource ranges embed field loads symbolically (the canonical
    // `load(arg-memory@...)` spellings), so segment evaluation must not
    // demand concrete loadability.
    let assumptions = Assumptions::new()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads();
    let base = evaluate_c_contract_expression(values, state, None, &assumptions, &segment.base)
        .map_err(|message| {
            ClickError::new(format!(
                "could not lower `{resource_name}` resource: {message}"
            ))
        })?;
    let CValue::Pointer(base) = base else {
        return Err(ClickError::new(format!(
            "could not lower `{resource_name}` resource: segment base did not evaluate to a pointer"
        )));
    };
    let start = evaluate_c_contract_expression(values, state, None, &assumptions, &segment.start)
        .map_err(|message| {
        ClickError::new(format!(
            "could not lower `{resource_name}` resource: {message}"
        ))
    })?;
    let CValue::Int32(start) = start else {
        return Err(ClickError::new(format!(
            "could not lower `{resource_name}` resource: segment start did not evaluate to int32"
        )));
    };
    let end = evaluate_c_contract_expression(values, state, None, &assumptions, &segment.end)
        .map_err(|message| {
            ClickError::new(format!(
                "could not lower `{resource_name}` resource: {message}"
            ))
        })?;
    let CValue::Int32(end) = end else {
        return Err(ClickError::new(format!(
            "could not lower `{resource_name}` resource: segment end did not evaluate to int32"
        )));
    };
    if let (Bitvector32Term::Constant(start), Bitvector32Term::Constant(end)) = (&start, &end)
        && end < start
    {
        return Err(ClickError::new(format!(
            "`{resource_name}` segment has an end before its start: {start}..{end}"
        )));
    }
    Ok(CMemoryRange::new(base, start, end))
}

pub(super) fn loadable_requirement_prop(
    requirement: &Requirement,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: &CMemory,
) -> Result<Proposition, ClickError> {
    let (base, bytes) = loadable_base_and_bytes(requirement, parameters, arguments)?;
    Ok(Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base,
        bytes,
    })
}

pub(super) fn resource_clause_loadable_prop(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: &CMemory,
) -> Result<Option<Proposition>, ClickError> {
    let (segment, range) = match resource {
        ResourceClause::Read(segment) => {
            let lowered = lower_resource_clause(resource, parameters, arguments, memory)?;
            let range = lowered
                .memory_view_range()
                .expect("viewed memory clause should lower to viewed memory");
            (segment, range.clone())
        }
        ResourceClause::Write(segment) => {
            let lowered = lower_resource_clause(resource, parameters, arguments, memory)?;
            let range = lowered
                .memory_own_range()
                .expect("owned memory clause should lower to owned memory");
            (segment, range.clone())
        }
        ResourceClause::Declared { .. } => return Ok(None),
    };
    let element_width = contract_segment_element_width(parameters, segment);
    Ok(Some(memory_range_loadable_prop(
        memory,
        &range,
        element_width,
    )))
}

pub(super) fn memory_range_loadable_prop(
    memory: &CMemory,
    range: &CMemoryRange,
    element_width: u32,
) -> Proposition {
    let element_count = bitvector32_subtract(range.end().clone(), range.start().clone());
    let bytes = bitvector32_multiply(element_count, Bitvector32Term::Constant(element_width));
    Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: offset_pointer_by_elements(
            range.base().clone(),
            range.start().clone(),
            element_width,
        ),
        bytes,
    }
}

pub(super) fn requirement_loadable_name(requirement: &Requirement) -> Option<&str> {
    match requirement.inner() {
        Requirement::LoadableBytes { name, .. } => Some(name),
        Requirement::Labeled { .. }
        | Requirement::LoadableSegment { .. }
        | Requirement::Resource(_)
        | Requirement::Proposition(_) => None,
    }
}

pub(super) fn concrete_loadable_block(
    requirement: &Requirement,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Result<Option<(String, ConcreteMemoryRangeSeed)>, ClickError> {
    match requirement.inner() {
        Requirement::LoadableBytes { name, bytes } => {
            let Some(bytes) = range_bytes_constant(bytes) else {
                return Ok(None);
            };
            let Some((parameter, argument)) = parameters
                .iter()
                .zip(arguments)
                .find(|(parameter, _)| parameter.name() == name)
            else {
                return Ok(None);
            };
            let CExpression::Value(CValue::Pointer(base)) = argument else {
                return Ok(None);
            };
            Ok(Some((
                name.clone(),
                ConcreteMemoryRangeSeed {
                    base: base.clone(),
                    bytes,
                    element_width: parameter_element_width(parameter).unwrap_or(4),
                },
            )))
        }
        Requirement::LoadableSegment { segment } => {
            let state = CState::new();
            let Ok(segment) = evaluate_requirement_segment(parameters, arguments, &state, segment)
            else {
                return Ok(None);
            };
            if segment.base.offset != PointerOffsetTerm::Constant(0)
                || segment.start != Bitvector32Term::Constant(0)
            {
                return Ok(None);
            }
            let Bitvector32Term::Constant(end) = segment.end else {
                return Ok(None);
            };
            let element_width = contract_segment_element_width(parameters, &segment.source);
            let bytes = end
                .checked_mul(element_width)
                .ok_or_else(|| ClickError::new("`loadable` segment overflows byte count"))?;
            Ok(Some((
                format!("{:?}", segment.source),
                ConcreteMemoryRangeSeed {
                    base: segment.base,
                    bytes,
                    element_width,
                },
            )))
        }
        Requirement::Labeled { .. } | Requirement::Resource(_) | Requirement::Proposition(_) => {
            Ok(None)
        }
    }
}

pub(super) fn concrete_access_resource_block(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Result<Option<(String, ConcreteMemoryRangeSeed)>, ClickError> {
    let segment = match resource {
        ResourceClause::Read(segment) | ResourceClause::Write(segment) => segment,
        ResourceClause::Declared { .. } => return Ok(None),
    };
    let state = CState::new();
    let Ok(segment) = evaluate_requirement_segment(parameters, arguments, &state, segment) else {
        return Ok(None);
    };
    let (Bitvector32Term::Constant(start), Bitvector32Term::Constant(end)) =
        (&segment.start, &segment.end)
    else {
        return Ok(None);
    };
    if end < start {
        return Err(ClickError::new(format!(
            "resource segment has an end before its start: {start}..{end}"
        )));
    }
    let element_width = contract_segment_element_width(parameters, &segment.source);
    let element_count = end - start;
    let bytes = element_count
        .checked_mul(element_width)
        .ok_or_else(|| ClickError::new("`write` segment overflows byte count"))?;
    Ok(Some((
        format!("{:?}", segment.source),
        ConcreteMemoryRangeSeed {
            base: offset_pointer_by_elements(segment.base, segment.start, element_width),
            bytes,
            element_width,
        },
    )))
}

pub(super) fn loadable_base_and_bytes(
    requirement: &Requirement,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Result<(Pointer, Bitvector32Term), ClickError> {
    let parameter_values = parameter_values(parameters, arguments)?;

    match requirement.inner() {
        Requirement::LoadableBytes { name, bytes } => {
            let Some((_, argument)) = parameters
                .iter()
                .zip(arguments)
                .find(|(parameter, _)| parameter.name() == name)
            else {
                return Err(ClickError::new(format!(
                    "`loadable` names `{name}`, but no such parameter exists"
                )));
            };
            let CExpression::Value(CValue::Pointer(base)) = argument else {
                return Err(ClickError::new(format!(
                    "`loadable` names `{name}`, but it is not a pointer parameter"
                )));
            };
            Ok((base.clone(), lower_range_bytes(bytes, &parameter_values)?))
        }
        Requirement::LoadableSegment { segment } => {
            let state = CState::new();
            let segment = evaluate_requirement_segment(parameters, arguments, &state, segment)
                .map_err(|message| {
                    ClickError::new(format!("could not lower `loadable` segment: {message}"))
                })?;
            if let (Bitvector32Term::Constant(start), Bitvector32Term::Constant(end)) =
                (&segment.start, &segment.end)
                && end < start
            {
                return Err(ClickError::new(format!(
                    "`loadable` segment has an end before its start: {start}..{end}"
                )));
            }
            let element_count = bitvector32_subtract(segment.end.clone(), segment.start.clone());
            let element_width = contract_segment_element_width(parameters, &segment.source);
            let bytes =
                bitvector32_multiply(element_count, Bitvector32Term::Constant(element_width));
            Ok((
                offset_pointer_by_elements(segment.base, segment.start, element_width),
                bytes,
            ))
        }
        Requirement::Labeled { .. } | Requirement::Proposition(_) | Requirement::Resource(_) => {
            Err(ClickError::new("expected loadable requirement"))
        }
    }
}

pub(super) fn loadable_segment_prop(
    memory: &CMemory,
    segment: EvaluatedContractSegment,
    element_width: u32,
) -> Result<Proposition, ClickError> {
    if let (Bitvector32Term::Constant(start), Bitvector32Term::Constant(end)) =
        (&segment.start, &segment.end)
        && end < start
    {
        return Err(ClickError::new(format!(
            "`loadable` segment has an end before its start: {start}..{end}"
        )));
    }
    let element_count = bitvector32_subtract(segment.end.clone(), segment.start.clone());
    let bytes = bitvector32_multiply(element_count, Bitvector32Term::Constant(element_width));
    Ok(Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: offset_pointer_by_elements(segment.base, segment.start, element_width),
        bytes,
    })
}

pub(super) fn contract_segment_element_width(
    parameters: &[syntax::C0Parameter],
    segment: &ContractSegment,
) -> u32 {
    contract_expression_element_width(parameters, &segment.base).unwrap_or(4)
}

pub(super) fn contract_expression_element_width(
    parameters: &[syntax::C0Parameter],
    expression: &CExpression,
) -> Option<u32> {
    match expression {
        CExpression::Variable(name) => parameters
            .iter()
            .find(|parameter| parameter.name() == name)
            .and_then(|parameter| match parameter.c_type() {
                C0Type::Int32Pointer => Some(4),
                C0Type::UInt8Pointer => Some(1),
                _ => None,
            }),
        CExpression::Add(left, right) => contract_expression_element_width(parameters, left)
            .or_else(|| contract_expression_element_width(parameters, right)),
        CExpression::Subtract(left, _) => contract_expression_element_width(parameters, left),
        CExpression::TypedLoad { value_type, .. } => match value_type {
            CType::Int32Pointer => Some(4),
            CType::UInt8Pointer => Some(1),
            _ => None,
        },
        _ => None,
    }
}

pub(super) fn contract_segment_element_width_from_array_refs(
    array_refs: &ClickArrayRefs,
    segment: &ContractSegment,
) -> Option<u32> {
    contract_expression_element_width_from_array_refs(array_refs, &segment.base)
}

pub(super) fn contract_expression_element_width_from_array_refs(
    array_refs: &ClickArrayRefs,
    expression: &CExpression,
) -> Option<u32> {
    match expression {
        CExpression::Variable(name) => array_refs
            .get(name)
            .map(|array_ref| array_ref.element_type.byte_width()),
        CExpression::Add(left, right) => {
            contract_expression_element_width_from_array_refs(array_refs, left)
                .or_else(|| contract_expression_element_width_from_array_refs(array_refs, right))
        }
        CExpression::Subtract(left, _) => {
            contract_expression_element_width_from_array_refs(array_refs, left)
        }
        CExpression::TypedLoad { value_type, .. } => match value_type {
            CType::Int32Pointer => Some(4),
            CType::UInt8Pointer => Some(1),
            _ => None,
        },
        _ => None,
    }
}

fn parameter_element_width(parameter: &syntax::C0Parameter) -> Option<u32> {
    match parameter.c_type() {
        C0Type::Int32Pointer => Some(4),
        C0Type::UInt8Pointer => Some(1),
        _ => None,
    }
}

pub(super) fn range_bytes_constant(bytes: &RangeBytes) -> Option<u32> {
    match bytes {
        RangeBytes::Constant(value) => Some(*value),
        RangeBytes::Parameter(_) => None,
        RangeBytes::Add(left, right) => {
            Some(range_bytes_constant(left)?.wrapping_add(range_bytes_constant(right)?))
        }
        RangeBytes::Subtract(left, right) => {
            Some(range_bytes_constant(left)?.wrapping_sub(range_bytes_constant(right)?))
        }
        RangeBytes::Multiply(left, right) => {
            Some(range_bytes_constant(left)?.wrapping_mul(range_bytes_constant(right)?))
        }
    }
}

pub(super) fn lower_range_bytes(
    bytes: &RangeBytes,
    parameter_values: &BTreeMap<String, CValue>,
) -> Result<Bitvector32Term, ClickError> {
    match bytes {
        RangeBytes::Constant(value) => Ok(Bitvector32Term::Constant(*value)),
        RangeBytes::Parameter(name) => match parameter_values.get(name) {
            Some(CValue::Int32(bits)) => Ok(bits.clone()),
            Some(_) => Err(ClickError::new(format!(
                "`loadable` byte expression references pointer parameter `{name}`"
            ))),
            None => Err(ClickError::new(format!(
                "`loadable` byte expression references unknown parameter `{name}`"
            ))),
        },
        RangeBytes::Add(left, right) => Ok(bitvector32_add(
            lower_range_bytes(left, parameter_values)?,
            lower_range_bytes(right, parameter_values)?,
        )),
        RangeBytes::Subtract(left, right) => Ok(bitvector32_subtract(
            lower_range_bytes(left, parameter_values)?,
            lower_range_bytes(right, parameter_values)?,
        )),
        RangeBytes::Multiply(left, right) => Ok(bitvector32_multiply(
            lower_range_bytes(left, parameter_values)?,
            lower_range_bytes(right, parameter_values)?,
        )),
    }
}

pub(super) fn requirement_proposition_prop(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: &CMemory,
    proposition: &ClickProposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, ClickError> {
    let parameter_values = parameter_values(parameters, arguments)?;
    let array_refs = array_refs_for_parameters(parameters, &parameter_values, memory);
    let mut lowerer = KernelPropositionLowerer::new(
        parameter_values,
        array_refs,
        memory.clone(),
        predicate_environment,
        click_function_environment,
    );
    lowerer.lower_requirement_proposition(proposition)
}

pub(super) fn parameter_values(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Result<BTreeMap<String, CValue>, ClickError> {
    parameters
        .iter()
        .zip(arguments)
        .map(|(parameter, argument)| {
            let CExpression::Value(value) = argument else {
                return Err(ClickError::new(format!(
                    "could not build contract environment for parameter `{}`",
                    parameter.name()
                )));
            };
            Ok((parameter.name().to_string(), value.clone()))
        })
        .collect()
}

pub(super) fn array_refs_for_parameters(
    parameters: &[syntax::C0Parameter],
    values: &BTreeMap<String, CValue>,
    memory: &CMemory,
) -> ClickArrayRefs {
    parameters
        .iter()
        .filter_map(|parameter| {
            let element_type = click_array_element_type(parameter.c_type())?;
            let Some(CValue::Pointer(pointer)) = values.get(parameter.name()) else {
                return None;
            };
            Some((
                parameter.name().to_string(),
                ClickArrayRef {
                    memory: memory.clone(),
                    pointer: pointer.clone(),
                    element_type,
                },
            ))
        })
        .collect()
}

pub(super) struct KernelPropositionLowerer {
    values: BTreeMap<String, CValue>,
    array_refs: ClickArrayRefs,
    memory: CMemory,
    predicate_environment: PredicateEnvironment,
    click_function_environment: ClickFunctionEnvironment,
    active_functions: BTreeSet<String>,
    next_variable: u64,
}

impl KernelPropositionLowerer {
    pub(super) fn new(
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
            active_functions: BTreeSet::new(),
            next_variable: 2_000_000,
        }
    }

    pub(super) fn lower_requirement_proposition(
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
                let element_width = contract_segment_element_width_from_array_refs(
                    &self.array_refs,
                    &segment.source,
                )
                .unwrap_or(4);
                loadable_segment_prop(&self.memory, segment, element_width)
            }
            ClickProposition::Defined { expression } => {
                let expression = contract_expression_to_c_fragment(expression).ok_or_else(|| {
                    ClickError::new(
                        "`defined(...)` currently requires an expression without `old`, `at`, folds, lets, or Click function calls",
                    )
                })?;
                let state = self.values.iter().fold(
                    CState::new().with_memory(self.memory.clone()),
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
            ClickProposition::And(left, right) => Ok(Proposition::And(
                Box::new(self.lower_requirement_proposition(left)?),
                Box::new(self.lower_requirement_proposition(right)?),
            )),
            ClickProposition::Or(left, right) => Ok(Proposition::Or(
                Box::new(self.lower_requirement_proposition(left)?),
                Box::new(self.lower_requirement_proposition(right)?),
            )),
            ClickProposition::Not(body) => Ok(Proposition::Not(Box::new(
                self.lower_requirement_proposition(body)?,
            ))),
            ClickProposition::Implies(left, right) => Ok(Proposition::Implies(
                Box::new(self.lower_requirement_proposition(left)?),
                Box::new(self.lower_requirement_proposition(right)?),
            )),
            ClickProposition::ForAll { c_type, name, body } => {
                if *c_type != C0Type::Int32 {
                    return Err(ClickError::new("only `forall (int32 ...)` is supported"));
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
                    return Err(ClickError::new("only `exists (int32 ...)` is supported"));
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
                let item_value = CValue::Int32(Bitvector32Term::Variable(variable));
                let outer_values = self.values.clone();
                self.values.insert(item.clone(), item_value.clone());
                let body = match self.lower_requirement_proposition(body) {
                    Ok(body) => body,
                    Err(error) => {
                        self.values = outer_values;
                        return Err(error);
                    }
                };
                self.values = outer_values;
                let CValue::Int32(item_bits) = item_value else {
                    unreachable!("range `all` item value is always int32")
                };
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
                            let body = match self.lower_requirement_proposition(body) {
                                Ok(body) => body,
                                Err(error) => {
                                    self.values = outer_values;
                                    return Err(error);
                                }
                            };
                            proposition = disjunction(proposition, body);
                        }
                        self.values = outer_values;
                        Ok(proposition)
                    }
                    _ => {
                        let variable = Variable(self.next_variable);
                        self.next_variable += 1;
                        let item_value = CValue::Int32(Bitvector32Term::Variable(variable));
                        self.values.insert(item.clone(), item_value.clone());
                        let body = match self.lower_requirement_proposition(body) {
                            Ok(body) => body,
                            Err(error) => {
                                self.values = outer_values;
                                return Err(error);
                            }
                        };
                        self.values = outer_values;
                        let CValue::Int32(item_bits) = item_value else {
                            unreachable!("range `any` item value is always int32")
                        };
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
                let state = CState::new().with_memory(self.memory.clone());
                let program_point_states = ProgramPointStates::new();
                let lowered_arguments = lower_predicate_call_arguments_with_environment(
                    definition,
                    arguments,
                    &self.values,
                    &self.array_refs,
                    &state,
                    &state,
                    None,
                    &Assumptions::new(),
                    &self.predicate_environment,
                    &self.click_function_environment,
                    &program_point_states,
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
        })
    }

    fn lower_requirement_resource_subject(
        &mut self,
        resource: &ResourceSubject,
    ) -> Result<CResource, ClickError> {
        match resource {
            ResourceSubject::Memory(segment) => {
                let range = self.lower_requirement_segment(segment)?;
                Ok(CResource::Memory(CMemoryRange::new(
                    range.base,
                    range.start,
                    range.end,
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
            ContractExpression::Index(_, _) => Err(ClickError::new(
                "memory reads are not supported in `requires` propositions yet",
            )),
            ContractExpression::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let condition = self.lower_requirement_proposition(condition)?;
                let assumptions = Assumptions::new();
                if assumptions.proves(&condition) {
                    return self.lower_requirement_value(then_branch);
                }
                if assumptions_prove_proposition_false(&assumptions, &condition) {
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
                let program_point_states = ProgramPointStates::new();
                evaluate_click_function_call(
                    &self.click_function_environment.clone(),
                    name,
                    arguments,
                    &self.values,
                    &self.array_refs,
                    &state,
                    &state,
                    None,
                    &Assumptions::new(),
                    &self.predicate_environment.clone(),
                    &program_point_states,
                    &mut self.active_functions,
                )
                .map_err(ClickError::new)
            }
        }
    }

    pub(super) fn lower_requirement_c_expression(
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
                    &Assumptions::new(),
                )
                .map_err(ClickError::new)
            }
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
                    &Assumptions::new(),
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

pub(super) fn comparison_proposition(
    left: CValue,
    operator: ComparisonOperator,
    right: CValue,
) -> Result<Proposition, ClickError> {
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

pub(super) fn proposition_as_single_condition(
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

pub(super) fn assumptions_prove_proposition_false(
    assumptions: &Assumptions,
    proposition: &Proposition,
) -> bool {
    match proposition {
        Proposition::ConditionIs(condition, value) => {
            assumptions.proves(&Proposition::ConditionIs(condition.clone(), !*value))
        }
        _ => assumptions.proves(&Proposition::Not(Box::new(proposition.clone()))),
    }
}

pub(super) fn conditional_contract_value(
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

pub(super) fn true_proposition() -> Proposition {
    Proposition::ConditionIs(ConditionTerm::Constant(true), true)
}

pub(super) fn false_proposition() -> Proposition {
    Proposition::ConditionIs(ConditionTerm::Constant(false), true)
}

pub(super) fn conjunction(left: Proposition, right: Proposition) -> Proposition {
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

pub(super) fn disjunction(left: Proposition, right: Proposition) -> Proposition {
    match (&left, &right) {
        (Proposition::ConditionIs(ConditionTerm::Constant(false), true), _) => right,
        (_, Proposition::ConditionIs(ConditionTerm::Constant(false), true)) => left,
        (Proposition::ConditionIs(ConditionTerm::Constant(true), true), _)
        | (_, Proposition::ConditionIs(ConditionTerm::Constant(true), true)) => true_proposition(),
        _ => Proposition::Or(Box::new(left), Box::new(right)),
    }
}

pub(super) fn range_membership_proposition(
    start: Bitvector32Term,
    item: Bitvector32Term,
    end: Bitvector32Term,
) -> Proposition {
    conjunction(
        Proposition::ConditionIs(signed_less_equal(start, item.clone()), true),
        Proposition::ConditionIs(signed_less_than(item, end), true),
    )
}

pub(super) fn bounded_forall_int32(
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

pub(super) fn bounded_exists_int32(
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

pub(super) fn spec_range_membership_proposition(
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

pub(super) fn int32_term_value(value: CValue, label: &str) -> Result<Bitvector32Term, String> {
    let CValue::Int32(bits) = value else {
        return Err(format!("`{label}` is not int32"));
    };
    Ok(simp_bitvector(&bits))
}

pub(super) fn promoted_int32_term(value: &CValue) -> Option<Bitvector32Term> {
    match value {
        CValue::Int32(bits) | CValue::UInt8(bits) => Some(simp_bitvector(bits)),
        CValue::Pointer(_) => None,
    }
}

pub(super) fn concrete_fold_range(start: i32, end: i32) -> Result<std::ops::Range<i32>, String> {
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

pub(super) fn concrete_bound_from_term(
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

pub(super) fn fold_bound_variable(name: &str, salt: u64) -> Variable {
    let mut hash = 0xcbf2_9ce4_8422_2325_u64 ^ salt;
    for byte in name.bytes() {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x1000_0000_01b3);
    }
    Variable(3_000_000 + (hash % 1_000_000_000))
}

pub(super) fn symbolic_range_fold_value(
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

pub(super) fn lower_contract_add(left: CValue, right: CValue) -> Result<CValue, ClickError> {
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

pub(super) fn lower_contract_subtract(left: CValue, right: CValue) -> Result<CValue, ClickError> {
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

pub(super) fn lower_contract_multiply(left: CValue, right: CValue) -> Result<CValue, ClickError> {
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

pub(super) fn lower_contract_divide(left: CValue, right: CValue) -> Result<CValue, ClickError> {
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

pub(super) fn lower_contract_remainder(left: CValue, right: CValue) -> Result<CValue, ClickError> {
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

pub(super) fn lower_contract_shift_left(left: CValue, right: CValue) -> Result<CValue, ClickError> {
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

pub(super) fn lower_contract_shift_right(
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

pub(super) fn lower_contract_bitwise_binary(
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

pub(super) fn lower_contract_bitwise_not(value: CValue) -> Result<CValue, ClickError> {
    if let Some(term) = promoted_int32_term(&value) {
        Ok(CValue::Int32(bitvector32_not(term)))
    } else {
        Err(ClickError::new(format!(
            "cannot apply `~` to `{value:?}` in proposition"
        )))
    }
}

pub(super) fn bitvector32_add(left: Bitvector32Term, right: Bitvector32Term) -> Bitvector32Term {
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
        (_, Bitvector32Term::Constant(0)) => left,
        (Bitvector32Term::Constant(0), _) => right,
        _ => Bitvector32Term::Add(Box::new(left), Box::new(right)),
    }
}

pub(super) fn bitvector32_subtract(
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

pub(super) fn bitvector32_multiply(
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

pub(super) fn bitvector32_divide(
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

pub(super) fn bitvector32_remainder(
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

pub(super) fn bitvector32_shift_count(right: u32) -> Option<u32> {
    let right = right as i32;
    (0..32).contains(&right).then_some(right as u32)
}

pub(super) fn bitvector32_shift_left(
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

pub(super) fn bitvector32_shift_right(
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

pub(super) fn bitvector32_and(left: Bitvector32Term, right: Bitvector32Term) -> Bitvector32Term {
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

pub(super) fn bitvector32_or(left: Bitvector32Term, right: Bitvector32Term) -> Bitvector32Term {
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

pub(super) fn bitvector32_xor(left: Bitvector32Term, right: Bitvector32Term) -> Bitvector32Term {
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

pub(super) fn bitvector32_not(value: Bitvector32Term) -> Bitvector32Term {
    match value {
        Bitvector32Term::Constant(value) => Bitvector32Term::Constant(!value),
        Bitvector32Term::BitwiseNot(inner) => *inner,
        value => Bitvector32Term::BitwiseNot(Box::new(value)),
    }
}

pub(super) fn signed_less_than(left: Bitvector32Term, right: Bitvector32Term) -> ConditionTerm {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            ConditionTerm::Constant((*left as i32) < (*right as i32))
        }
        _ => ConditionTerm::Bitvector32SignedLessThan(Box::new(left), Box::new(right)),
    }
}

pub(super) fn signed_less_equal(left: Bitvector32Term, right: Bitvector32Term) -> ConditionTerm {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            ConditionTerm::Constant((*left as i32) <= (*right as i32))
        }
        _ => ConditionTerm::Bitvector32SignedLessEqual(Box::new(left), Box::new(right)),
    }
}

pub(super) fn signed_greater_than(left: Bitvector32Term, right: Bitvector32Term) -> ConditionTerm {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            ConditionTerm::Constant((*left as i32) > (*right as i32))
        }
        _ => ConditionTerm::Bitvector32SignedGreaterThan(Box::new(left), Box::new(right)),
    }
}

pub(super) fn signed_greater_equal(left: Bitvector32Term, right: Bitvector32Term) -> ConditionTerm {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            ConditionTerm::Constant((*left as i32) >= (*right as i32))
        }
        _ => ConditionTerm::Bitvector32SignedGreaterEqual(Box::new(left), Box::new(right)),
    }
}

pub(super) fn bitvector32_equal(left: Bitvector32Term, right: Bitvector32Term) -> ConditionTerm {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            ConditionTerm::Constant(left == right)
        }
        _ => ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
    }
}
