use super::*;

#[cfg(test)]
mod tests;

#[derive(Clone, Debug, Eq, PartialEq)]
struct DeclaredResourceInfo {
    fields: std::sync::Arc<BTreeMap<String, (usize, ClickType)>>,
    parameter_types: Vec<C0Type>,
    kind: ResourceKind,
    has_fields: bool,
}

// Only immutable surface syntax is shared. Lowered environments, authorities,
// and certificates must still be constructed in each verification session.
static STANDARD_LIBRARY: std::sync::OnceLock<Result<ClickFile, ClickError>> =
    std::sync::OnceLock::new();

#[cfg(test)]
static STANDARD_LIBRARY_PARSES: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);

fn standard_library() -> Result<&'static ClickFile, ClickError> {
    STANDARD_LIBRARY
        .get_or_init(|| {
            #[cfg(test)]
            STANDARD_LIBRARY_PARSES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            let file = expand_declared_resource_clauses(parser::parse_file_items(
                CLICK_STANDARD_LIBRARY,
            )?)?;
            if !file.verifying_sources().is_empty()
                || file.function_blocks().iter().any(|function| !function.is_external())
            {
                return Err(ClickError::new(
                    "internal Click standard library must not contain verifying sources or body-bearing C function specs",
                ));
            }
            Ok(file)
        })
        .as_ref()
        .map_err(Clone::clone)
}

pub(in crate::surface) fn combined_algebraic_type_definitions(
    file: &ClickFile,
) -> Result<Vec<AlgebraicTypeDefinition>, ClickError> {
    let mut definitions = standard_library()?.algebraic_type_definitions.clone();
    definitions.extend(file.algebraic_type_definitions().iter().cloned());
    Ok(definitions)
}

pub(in crate::surface) fn combined_external_function_blocks(
    file: &ClickFile,
) -> Result<Vec<FunctionBlock>, ClickError> {
    let mut function_blocks = standard_library()?.function_blocks().to_vec();
    function_blocks.extend(file.function_blocks().iter().cloned());
    Ok(function_blocks)
}

pub(in crate::surface) fn expand_declared_resource_clauses(
    mut file: ClickFile,
) -> Result<ClickFile, ClickError> {
    let mut resource_definitions = file
        .resource_definitions()
        .iter()
        .map(|definition| {
            Ok((
                definition.name().to_string(),
                DeclaredResourceInfo {
                    fields: std::sync::Arc::new(definition.fields().iter().enumerate()
                        .map(|(index, field)| (field.name().to_string(), (index, field.click_type().clone())))
                        .collect()),
                    has_fields: !definition.is_countable(),
                    parameter_types: definition
                        .parameters()
                        .iter()
                        .map(|parameter| {
                            parameter.click_type().c_type().ok_or_else(|| {
                                ClickError::new(format!(
                                    "resource `{}` parameter `{}` uses an algebraic type; algebraic resource arguments are not supported yet",
                                    definition.name(),
                                    parameter.name()
                                ))
                            })
                        })
                        .collect::<Result<Vec<_>, ClickError>>()?,
                    kind: if definition.composite_body().is_some() {
                        ResourceKind::Composite
                    } else {
                        ResourceKind::Token
                    },
                },
            ))
        })
        .collect::<Result<BTreeMap<_, _>, ClickError>>()?;
    resource_definitions
        .entry(CResourceFact::ALLOCATION_RESOURCE_NAME.to_string())
        .or_insert_with(|| DeclaredResourceInfo {
            fields: Default::default(),
            has_fields: false,
            parameter_types: vec![C0Type::Int32Pointer, C0Type::Int32],
            kind: ResourceKind::Token,
        });

    file.resource_definitions = file
        .resource_definitions
        .drain(..)
        .map(|definition| expand_declared_resource_definition(definition, &resource_definitions))
        .collect::<Result<Vec<_>, _>>()?;

    for predicate in &mut file.predicate_definitions {
        predicate.body =
            expand_declared_resource_proposition(predicate.body.clone(), &resource_definitions)?;
    }

    for function in &mut file.click_function_definitions {
        function.body =
            expand_declared_resource_expression(function.body.clone(), &resource_definitions)?;
        function.decreases = function
            .decreases
            .take()
            .map(|expression| {
                expand_declared_resource_expression(expression, &resource_definitions)
            })
            .transpose()?;
    }

    for contract in &mut file.contract_definitions {
        if let Some(parameters) = &mut contract.proof_parameters {
            for parameter in parameters {
                *parameter =
                    expand_declared_resource_clause(parameter.clone(), &resource_definitions)?;
            }
        }
        expand_declared_resources_in_function_block(
            &mut contract.function_block,
            &resource_definitions,
        )?;
    }

    for function in &mut file.function_blocks {
        expand_declared_resources_in_function_block(function, &resource_definitions)?;
    }

    for theorem in &mut file.theorem_definitions {
        theorem.requires = theorem
            .requires
            .drain(..)
            .map(|requirement| {
                expand_declared_resource_requirement(requirement, &resource_definitions)
            })
            .collect::<Result<Vec<_>, _>>()?;
        theorem.ensures = theorem
            .ensures
            .drain(..)
            .map(|clause| expand_declared_resource_ensure_clause(clause, &resource_definitions))
            .collect::<Result<Vec<_>, _>>()?;
    }

    Ok(file)
}

fn expand_declared_resources_in_function_block(
    function: &mut FunctionBlock,
    resource_definitions: &BTreeMap<String, DeclaredResourceInfo>,
) -> Result<(), ClickError> {
    function.decreases = function
        .decreases
        .take()
        .map(|decreases| match decreases {
            CFunctionDecrease::Numeric(expression) => Ok(CFunctionDecrease::Numeric(
                expand_declared_resource_expression(expression, resource_definitions)?,
            )),
            CFunctionDecrease::Resource(resource) => Ok(CFunctionDecrease::Resource(
                expand_declared_resource_clause(resource, &resource_definitions)?,
            )),
        })
        .transpose()?;
    function.requires = function
        .requires
        .drain(..)
        .map(|requirement| expand_declared_resource_requirement(requirement, &resource_definitions))
        .collect::<Result<Vec<_>, _>>()?;
    function.ensures = function
        .ensures
        .drain(..)
        .map(|clause| expand_declared_resource_ensure_clause(clause, &resource_definitions))
        .collect::<Result<Vec<_>, _>>()?;
    function.effects = function
        .effects
        .drain(..)
        .map(|clause| expand_declared_resource_effect_clause(clause, &resource_definitions))
        .collect::<Result<Vec<_>, _>>()?;
    function.constructs = function
        .constructs
        .drain(..)
        .map(|resource| expand_declared_resource_clause(resource, &resource_definitions))
        .collect::<Result<Vec<_>, _>>()?;
    function.structural_clauses = function
        .structural_clauses
        .drain(..)
        .map(|clause| expand_declared_resource_structural_clause(clause, &resource_definitions))
        .collect::<Result<Vec<_>, _>>()?;
    function.grouped_proof = function
        .grouped_proof
        .take()
        .map(|proof| expand_declared_resource_proof(proof, &resource_definitions))
        .transpose()?;
    Ok(())
}

fn expand_declared_resource_definition(
    mut definition: ResourceDefinition,
    resource_definitions: &BTreeMap<String, DeclaredResourceInfo>,
) -> Result<ResourceDefinition, ClickError> {
    if let Some(composite_body) = definition.composite_body {
        definition.composite_body = Some(expand_declared_composite_resource_body(
            composite_body,
            resource_definitions,
        )?);
    }
    Ok(definition)
}

fn expand_declared_composite_resource_body(
    composite_body: CompositeResourceBody,
    resource_definitions: &BTreeMap<String, DeclaredResourceInfo>,
) -> Result<CompositeResourceBody, ClickError> {
    Ok(CompositeResourceBody {
        children: composite_body.children,
        fields: composite_body.fields,
        matched: composite_body
            .matched
            .map(|matched| {
                Ok(ResourceMatchBody {
                    field: matched.field,
                    arms: matched
                        .arms
                        .into_iter()
                        .map(|arm| {
                            Ok(ResourceMatchArm {
                                type_name: arm.type_name,
                                variant: arm.variant,
                                bindings: arm.bindings,
                                body: expand_declared_composite_resource_body(
                                    arm.body,
                                    resource_definitions,
                                )?,
                            })
                        })
                        .collect::<Result<Vec<_>, ClickError>>()?,
                })
            })
            .transpose()?,
        witnesses: composite_body.witnesses.clone(),
        condition: composite_body
            .condition
            .map(|condition| expand_declared_resource_proposition(condition, resource_definitions))
            .transpose()?,
        contains: composite_body
            .contains
            .into_iter()
            .map(|resource| expand_declared_resource_clause(resource, resource_definitions))
            .collect::<Result<Vec<_>, _>>()?,
        facts: composite_body
            .facts
            .into_iter()
            .map(|fact| expand_declared_resource_proposition(fact, resource_definitions))
            .collect::<Result<Vec<_>, _>>()?,
    })
}

fn expand_declared_resource_requirement(
    requirement: Requirement,
    resource_definitions: &BTreeMap<String, DeclaredResourceInfo>,
) -> Result<Requirement, ClickError> {
    match requirement {
        Requirement::Labeled { label, requirement } => Ok(Requirement::Labeled {
            label,
            requirement: Box::new(expand_declared_resource_requirement(
                *requirement,
                resource_definitions,
            )?),
        }),
        Requirement::Proposition(ClickProposition::PredicateCall { name, arguments })
            if resource_definitions.contains_key(&name) =>
        {
            declared_resource_info(&name, arguments.len(), resource_definitions)?;
            Err(ClickError::new(format!(
                "`requires` accepts pure propositions only; use `owns {name}(...)`, `views {name}(...)`, or `consumes {name}(...)`"
            )))
        }
        Requirement::Resource(resource) => Ok(Requirement::Resource(
            expand_declared_resource_clause(resource, resource_definitions)?,
        )),
        Requirement::Proposition(proposition) => Ok(Requirement::Proposition(
            expand_declared_resource_proposition(proposition, resource_definitions)?,
        )),
        _ => Ok(requirement),
    }
}

fn expand_declared_resource_ensure_clause(
    mut clause: EnsureClause,
    resource_definitions: &BTreeMap<String, DeclaredResourceInfo>,
) -> Result<EnsureClause, ClickError> {
    clause.ensure = match clause.ensure {
        Ensure::Proposition(ClickProposition::PredicateCall { name, arguments })
            if resource_definitions.contains_key(&name) =>
        {
            declared_resource_info(&name, arguments.len(), resource_definitions)?;
            return Err(ClickError::new(format!(
                "`ensures` accepts pure propositions only; use `owns {name}(...)` or `produces {name}(...)`"
            )));
        }
        Ensure::Proposition(proposition) => Ensure::Proposition(
            expand_declared_resource_proposition(proposition, resource_definitions)?,
        ),
        Ensure::Resource(resource) => Ensure::Resource(expand_declared_resource_clause(
            resource,
            resource_definitions,
        )?),
    };
    clause.proof = expand_declared_resource_proof(clause.proof, resource_definitions)?;
    Ok(clause)
}

fn expand_declared_resource_effect_clause(
    mut clause: EffectClause,
    resource_definitions: &BTreeMap<String, DeclaredResourceInfo>,
) -> Result<EffectClause, ClickError> {
    clause.proof = expand_declared_resource_proof(clause.proof, resource_definitions)?;
    Ok(clause)
}

fn expand_declared_resource_structural_clause(
    mut clause: StructuralClause,
    resource_definitions: &BTreeMap<String, DeclaredResourceInfo>,
) -> Result<StructuralClause, ClickError> {
    clause.items = clause
        .items
        .into_iter()
        .map(|item| expand_declared_resource_structural_item(item, resource_definitions))
        .collect::<Result<Vec<_>, _>>()?;
    clause.initialize_proof = clause
        .initialize_proof
        .take()
        .map(|proof| expand_declared_resource_proof(proof, resource_definitions))
        .transpose()?;
    clause.preserve_proof = clause
        .preserve_proof
        .take()
        .map(|proof| expand_declared_resource_proof(proof, resource_definitions))
        .transpose()?;
    Ok(clause)
}

fn expand_declared_resource_structural_item(
    mut item: StructuralItem,
    resource_definitions: &BTreeMap<String, DeclaredResourceInfo>,
) -> Result<StructuralItem, ClickError> {
    item.claim = match item.claim {
        StructuralItemClaim::Proposition(proposition) => StructuralItemClaim::Proposition(
            expand_declared_resource_proposition(proposition, resource_definitions)?,
        ),
        StructuralItemClaim::Effect(effect) => StructuralItemClaim::Effect(effect),
    };
    item.proof = expand_declared_resource_proof(item.proof, resource_definitions)?;
    Ok(item)
}

fn expand_declared_resource_proof(
    proof: SourceProof,
    resource_definitions: &BTreeMap<String, DeclaredResourceInfo>,
) -> Result<SourceProof, ClickError> {
    match proof {
        SourceProof::Default => Ok(proof),
        SourceProof::Tactic(_) => Ok(proof),
        SourceProof::Script(tactics) => Ok(SourceProof::Script(
            tactics
                .into_iter()
                .map(|tactic| expand_declared_resource_tactic(tactic, resource_definitions))
                .collect::<Result<Vec<_>, _>>()?,
        )),
    }
}

fn expand_declared_resource_tactic(
    tactic: ProofTactic,
    resource_definitions: &BTreeMap<String, DeclaredResourceInfo>,
) -> Result<ProofTactic, ClickError> {
    match tactic {
        ProofTactic::ApplyTheorem(mut application) => {
            application.arguments = application
                .arguments
                .into_iter()
                .map(|argument| expand_declared_resource_expression(argument, resource_definitions))
                .collect::<Result<_, _>>()?;
            Ok(ProofTactic::ApplyTheorem(application))
        }
        ProofTactic::Witness(mut witness) => {
            witness.value =
                expand_declared_resource_expression(witness.value, resource_definitions)?;
            Ok(ProofTactic::Witness(witness))
        }
        ProofTactic::ApplyInduction {
            hypothesis,
            argument,
        } => Ok(ProofTactic::ApplyInduction {
            hypothesis,
            argument: expand_declared_resource_expression(argument, resource_definitions)?,
        }),
        ProofTactic::ApplyInductionUsing {
            hypothesis,
            argument,
            premises,
        } => Ok(ProofTactic::ApplyInductionUsing {
            hypothesis,
            argument: expand_declared_resource_expression(argument, resource_definitions)?,
            premises: premises
                .into_iter()
                .map(|premise| expand_declared_resource_proposition(premise, resource_definitions))
                .collect::<Result<_, _>>()?,
        }),
        ProofTactic::ArithmeticUsing(premises) => Ok(ProofTactic::ArithmeticUsing(
            premises
                .into_iter()
                .map(|premise| expand_declared_resource_proposition(premise, resource_definitions))
                .collect::<Result<_, _>>()?,
        )),
        ProofTactic::FrameUsing { region, premises } => Ok(ProofTactic::FrameUsing {
            region,
            premises: premises
                .into_iter()
                .map(|premise| expand_declared_resource_proposition(premise, resource_definitions))
                .collect::<Result<Vec<_>, _>>()?,
        }),
        ProofTactic::ApplyTheoremUsing {
            application,
            premises,
        } => Ok(ProofTactic::ApplyTheoremUsing {
            application: TheoremApplication {
                name: application.name,
                arguments: application
                    .arguments
                    .into_iter()
                    .map(|argument| {
                        expand_declared_resource_expression(argument, resource_definitions)
                    })
                    .collect::<Result<_, _>>()?,
            },
            premises: premises
                .into_iter()
                .map(|premise| expand_declared_resource_proposition(premise, resource_definitions))
                .collect::<Result<Vec<_>, _>>()?,
        }),
        ProofTactic::UnfoldResource(resource) => Ok(ProofTactic::UnfoldResource(
            expand_declared_resource_clause(resource, resource_definitions)?,
        )),
        ProofTactic::UnfoldFunction(application)
            if resource_definitions.contains_key(&application.name) =>
        {
            Ok(ProofTactic::UnfoldResource(
                expand_declared_resource_clause(
                    ResourceClause::Declared {
                        access: ResourceAccessMode::Own,
                        kind: ResourceKind::Token,
                        name: application.name,
                        arguments: application.arguments,
                        parameter_types: Vec::new(),
                    },
                    resource_definitions,
                )?,
            ))
        }
        ProofTactic::UnfoldFunction(mut application) => {
            application.arguments = application
                .arguments
                .into_iter()
                .map(|argument| expand_declared_resource_expression(argument, resource_definitions))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(ProofTactic::UnfoldFunction(application))
        }
        ProofTactic::ObserveResource(resource) => Ok(ProofTactic::ObserveResource(
            expand_declared_resource_clause(resource, resource_definitions)?,
        )),
        ProofTactic::FoldResource(resource) => Ok(ProofTactic::FoldResource(
            expand_declared_resource_clause(resource, resource_definitions)?,
        )),
        ProofTactic::ConstructResource(resource) => Ok(ProofTactic::ConstructResource(
            expand_declared_resource_clause(resource, resource_definitions)?,
        )),
        ProofTactic::Contradiction(proposition) => Ok(ProofTactic::Contradiction(
            expand_declared_resource_proposition(proposition, resource_definitions)?,
        )),
        ProofTactic::Extract(proposition) => Ok(ProofTactic::Extract(
            expand_declared_resource_proposition(proposition, resource_definitions)?,
        )),
        ProofTactic::Rewrite(proposition) => Ok(ProofTactic::Rewrite(
            expand_declared_resource_proposition(proposition, resource_definitions)?,
        )),
        ProofTactic::Transport { source, target } => Ok(ProofTactic::Transport {
            source: expand_declared_resource_proposition(source, resource_definitions)?,
            target: expand_declared_resource_proposition(target, resource_definitions)?,
        }),
        ProofTactic::TransportUsing {
            source,
            target,
            premises,
        } => Ok(ProofTactic::TransportUsing {
            source: expand_declared_resource_proposition(source, resource_definitions)?,
            target: expand_declared_resource_proposition(target, resource_definitions)?,
            premises: premises
                .into_iter()
                .map(|premise| expand_declared_resource_proposition(premise, resource_definitions))
                .collect::<Result<Vec<_>, _>>()?,
        }),
        ProofTactic::InstantiateUsing {
            quantified,
            argument,
            premises,
        } => Ok(ProofTactic::InstantiateUsing {
            quantified: expand_declared_resource_proposition(quantified, resource_definitions)?,
            argument: expand_declared_resource_expression(argument, resource_definitions)?,
            premises: premises
                .into_iter()
                .map(|premise| expand_declared_resource_proposition(premise, resource_definitions))
                .collect::<Result<Vec<_>, _>>()?,
        }),
        ProofTactic::SimpUsing(simp) => Ok(ProofTactic::SimpUsing(ProofSimpUsing {
            premises: simp
                .premises
                .into_iter()
                .map(|premise| expand_declared_resource_proposition(premise, resource_definitions))
                .collect::<Result<Vec<_>, _>>()?,
        })),
        ProofTactic::NormalizeUsing(premises) => Ok(ProofTactic::NormalizeUsing(
            premises
                .into_iter()
                .map(|premise| expand_declared_resource_proposition(premise, resource_definitions))
                .collect::<Result<Vec<_>, _>>()?,
        )),
        ProofTactic::Have(have) => Ok(ProofTactic::Have(ProofHave {
            proposition: expand_declared_resource_proposition(
                have.proposition,
                resource_definitions,
            )?,
            proof: expand_declared_resource_proof(have.proof, resource_definitions)?,
        })),
        ProofTactic::Open(open) => Ok(ProofTactic::Open(ProofOpen {
            resource: expand_declared_resource_clause(open.resource, resource_definitions)?,
            tactics: open
                .tactics
                .into_iter()
                .map(|tactic| expand_declared_resource_tactic(tactic, resource_definitions))
                .collect::<Result<Vec<_>, _>>()?,
        })),
        ProofTactic::If(proof_if) => Ok(ProofTactic::If(ProofIf {
            condition: expand_declared_resource_proposition(
                proof_if.condition,
                resource_definitions,
            )?,
            then_tactics: proof_if
                .then_tactics
                .into_iter()
                .map(|tactic| expand_declared_resource_tactic(tactic, resource_definitions))
                .collect::<Result<Vec<_>, _>>()?,
            else_tactics: proof_if
                .else_tactics
                .into_iter()
                .map(|tactic| expand_declared_resource_tactic(tactic, resource_definitions))
                .collect::<Result<Vec<_>, _>>()?,
        })),
        ProofTactic::Cases(proof_cases) => Ok(ProofTactic::Cases(ProofCases {
            disjunction: expand_declared_resource_proposition(
                proof_cases.disjunction,
                resource_definitions,
            )?,
            left_tactics: proof_cases
                .left_tactics
                .into_iter()
                .map(|tactic| expand_declared_resource_tactic(tactic, resource_definitions))
                .collect::<Result<Vec<_>, _>>()?,
            right_tactics: proof_cases
                .right_tactics
                .into_iter()
                .map(|tactic| expand_declared_resource_tactic(tactic, resource_definitions))
                .collect::<Result<Vec<_>, _>>()?,
        })),
        ProofTactic::StructuralInduct {
            parameter,
            hypothesis,
            arms,
        } => Ok(ProofTactic::StructuralInduct {
            parameter,
            hypothesis,
            arms: arms
                .into_iter()
                .map(|arm| {
                    Ok(ProofInductionArm {
                        type_name: arm.type_name,
                        variant: arm.variant,
                        bindings: arm.bindings,
                        tactics: arm
                            .tactics
                            .into_iter()
                            .map(|tactic| {
                                expand_declared_resource_tactic(tactic, resource_definitions)
                            })
                            .collect::<Result<Vec<_>, ClickError>>()?,
                    })
                })
                .collect::<Result<Vec<_>, ClickError>>()?,
        }),
        ProofTactic::Branch(proof_branch) => Ok(ProofTactic::Branch(ProofBranch {
            ensuring: proof_branch
                .ensuring
                .map(|assertions| {
                    assertions
                        .into_iter()
                        .map(|assertion| match assertion {
                            ProofAssertion::Fact(fact) => Ok(ProofAssertion::Fact(
                                expand_declared_resource_proposition(fact, resource_definitions)?,
                            )),
                            ProofAssertion::Resource(resource) => Ok(ProofAssertion::Resource(
                                expand_declared_resource_clause(resource, resource_definitions)?,
                            )),
                        })
                        .collect::<Result<Vec<_>, ClickError>>()
                })
                .transpose()?,
            then_tactics: proof_branch
                .then_tactics
                .into_iter()
                .map(|tactic| expand_declared_resource_tactic(tactic, resource_definitions))
                .collect::<Result<Vec<_>, _>>()?,
            else_tactics: proof_branch
                .else_tactics
                .into_iter()
                .map(|tactic| expand_declared_resource_tactic(tactic, resource_definitions))
                .collect::<Result<Vec<_>, _>>()?,
        })),
        ProofTactic::Loop(clause) => Ok(ProofTactic::Loop(
            expand_declared_resource_structural_clause(clause, resource_definitions)?,
        )),
        _ => Ok(tactic),
    }
}

fn expand_declared_resource_clause(
    resource: ResourceClause,
    resource_definitions: &BTreeMap<String, DeclaredResourceInfo>,
) -> Result<ResourceClause, ClickError> {
    match resource {
        ResourceClause::Named {
            mut binding,
            resource,
        } => {
            let ResourceClause::Declared {
                access: ResourceAccessMode::Own,
                name,
                arguments,
                ..
            } = *resource
            else {
                return Err(ClickError::new(
                    "named ownership requires a declared resource",
                ));
            };
            let info = declared_resource_info_with_fields(
                &name,
                arguments.len(),
                resource_definitions,
                true,
            )?;
            if !info.has_fields {
                return Err(ClickError::new(format!(
                    "resource `{name}` has no fields; use ordinary unnamed ownership"
                )));
            }
            if let Some(fields) = binding.fold_fields.take() {
                binding.fold_fields = Some(
                    fields
                        .into_iter()
                        .map(|(name, value)| {
                            Ok((
                                name,
                                expand_declared_resource_expression(value, resource_definitions)?,
                            ))
                        })
                        .collect::<Result<_, ClickError>>()?,
                );
            }
            Ok(ResourceClause::Named {
                binding,
                resource: Box::new(ResourceClause::Declared {
                    access: ResourceAccessMode::Own,
                    kind: info.kind,
                    name,
                    arguments: arguments
                        .into_iter()
                        .map(|arg| expand_declared_resource_expression(arg, resource_definitions))
                        .collect::<Result<_, _>>()?,
                    parameter_types: info.parameter_types,
                }),
            })
        }
        ResourceClause::Quantified { quantity, resource } => {
            reject_counted_field_resource(&resource, resource_definitions)?;
            Ok(ResourceClause::Quantified {
                quantity: expand_declared_resource_expression(quantity, resource_definitions)?,
                resource: Box::new(expand_declared_resource_clause(
                    *resource,
                    resource_definitions,
                )?),
            })
        }
        ResourceClause::Declared {
            access,
            kind: _,
            name,
            arguments,
            parameter_types,
        } if parameter_types.is_empty() => {
            let info = declared_resource_info(&name, arguments.len(), resource_definitions)?;
            if name == CResourceFact::ALLOCATION_RESOURCE_NAME && access == ResourceAccessMode::View
            {
                return Err(ClickError::new(
                    "allocation authority is owned and cannot be viewed or duplicated",
                ));
            }
            Ok(ResourceClause::Declared {
                access,
                kind: info.kind,
                name,
                arguments: arguments
                    .into_iter()
                    .map(|argument| {
                        expand_declared_resource_expression(argument, resource_definitions)
                    })
                    .collect::<Result<_, _>>()?,
                parameter_types: info.parameter_types,
            })
        }
        resource => Ok(resource),
    }
}

fn expand_declared_resource_subject(
    resource: ResourceSubject,
    resource_definitions: &BTreeMap<String, DeclaredResourceInfo>,
) -> Result<ResourceSubject, ClickError> {
    match resource {
        ResourceSubject::Declared {
            kind: _,
            name,
            arguments,
            parameter_types,
        } if parameter_types.is_empty() => {
            let info = declared_resource_info(&name, arguments.len(), resource_definitions)?;
            Ok(ResourceSubject::Declared {
                kind: info.kind,
                name,
                arguments: arguments
                    .into_iter()
                    .map(|argument| {
                        expand_declared_resource_expression(argument, resource_definitions)
                    })
                    .collect::<Result<_, _>>()?,
                parameter_types: info.parameter_types,
            })
        }
        resource => Ok(resource),
    }
}

fn expand_declared_resource_proposition(
    proposition: ClickProposition,
    resource_definitions: &BTreeMap<String, DeclaredResourceInfo>,
) -> Result<ClickProposition, ClickError> {
    match proposition {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => Ok(ClickProposition::Comparison {
            left: expand_declared_resource_expression(left, resource_definitions)?,
            operator,
            right: expand_declared_resource_expression(right, resource_definitions)?,
        }),
        ClickProposition::Defined { expression } => Ok(ClickProposition::Defined {
            expression: expand_declared_resource_expression(expression, resource_definitions)?,
        }),
        ClickProposition::Separate { left, right } => Ok(ClickProposition::Separate {
            left: expand_declared_resource_subject(left, resource_definitions)?,
            right: expand_declared_resource_subject(right, resource_definitions)?,
        }),
        ClickProposition::Contains { parent, child } => Ok(ClickProposition::Contains {
            parent: expand_declared_resource_subject(parent, resource_definitions)?,
            child: expand_declared_resource_subject(child, resource_definitions)?,
        }),
        ClickProposition::And(left, right) => Ok(ClickProposition::And(
            Box::new(expand_declared_resource_proposition(
                *left,
                resource_definitions,
            )?),
            Box::new(expand_declared_resource_proposition(
                *right,
                resource_definitions,
            )?),
        )),
        ClickProposition::Or(left, right) => Ok(ClickProposition::Or(
            Box::new(expand_declared_resource_proposition(
                *left,
                resource_definitions,
            )?),
            Box::new(expand_declared_resource_proposition(
                *right,
                resource_definitions,
            )?),
        )),
        ClickProposition::Implies(left, right) => Ok(ClickProposition::Implies(
            Box::new(expand_declared_resource_proposition(
                *left,
                resource_definitions,
            )?),
            Box::new(expand_declared_resource_proposition(
                *right,
                resource_definitions,
            )?),
        )),
        ClickProposition::Not(body) => Ok(ClickProposition::Not(Box::new(
            expand_declared_resource_proposition(*body, resource_definitions)?,
        ))),
        ClickProposition::At {
            selector,
            proposition,
        } => Ok(ClickProposition::At {
            selector,
            proposition: Box::new(expand_declared_resource_proposition(
                *proposition,
                resource_definitions,
            )?),
        }),
        ClickProposition::ForAll { c_type, name, body } => Ok(ClickProposition::ForAll {
            c_type,
            name,
            body: Box::new(expand_declared_resource_proposition(
                *body,
                resource_definitions,
            )?),
        }),
        ClickProposition::Exists { c_type, name, body } => Ok(ClickProposition::Exists {
            c_type,
            name,
            body: Box::new(expand_declared_resource_proposition(
                *body,
                resource_definitions,
            )?),
        }),
        ClickProposition::RangeAll {
            start,
            end,
            item,
            body,
        } => Ok(ClickProposition::RangeAll {
            start: expand_declared_resource_expression(start, resource_definitions)?,
            end: expand_declared_resource_expression(end, resource_definitions)?,
            item,
            body: Box::new(expand_declared_resource_proposition(
                *body,
                resource_definitions,
            )?),
        }),
        ClickProposition::RangeAny {
            start,
            end,
            item,
            body,
        } => Ok(ClickProposition::RangeAny {
            start: expand_declared_resource_expression(start, resource_definitions)?,
            end: expand_declared_resource_expression(end, resource_definitions)?,
            item,
            body: Box::new(expand_declared_resource_proposition(
                *body,
                resource_definitions,
            )?),
        }),
        ClickProposition::PredicateCall { name, arguments } => {
            Ok(ClickProposition::PredicateCall {
                name,
                arguments: arguments
                    .into_iter()
                    .map(|argument| {
                        expand_declared_resource_expression(argument, resource_definitions)
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            })
        }
        proposition => Ok(proposition),
    }
}

fn expand_declared_resource_expression(
    expression: ContractExpression,
    resource_definitions: &BTreeMap<String, DeclaredResourceInfo>,
) -> Result<ContractExpression, ClickError> {
    let recurse =
        |expression| expand_declared_resource_expression(expression, resource_definitions);
    Ok(match expression {
        ContractExpression::ResourceField(mut access) => {
            let info = resource_definitions
                .get(&access.resource_name)
                .ok_or_else(|| {
                    ClickError::new(format!("unknown resource `{}`", access.resource_name))
                })?;
            let (index, field) = info.fields.get(&access.field).ok_or_else(|| {
                ClickError::new(format!(
                    "resource `{}` has no field `{}`",
                    access.resource_name, access.field
                ))
            })?;
            access.field_index = *index;
            access.click_type = Some(field.clone());
            ContractExpression::ResourceField(access)
        }
        ContractExpression::AlgebraicConstructor {
            algebraic_type,
            variant,
            arguments,
        } => ContractExpression::AlgebraicConstructor {
            algebraic_type,
            variant,
            arguments: arguments
                .into_iter()
                .map(recurse)
                .collect::<Result<_, _>>()?,
        },
        ContractExpression::AlgebraicMatch { scrutinee, arms } => {
            ContractExpression::AlgebraicMatch {
                scrutinee: Box::new(recurse(*scrutinee)?),
                arms: arms
                    .into_iter()
                    .map(|mut arm| {
                        arm.body = recurse(arm.body)?;
                        Ok(arm)
                    })
                    .collect::<Result<_, ClickError>>()?,
            }
        }
        ContractExpression::SequenceLiteral(elements) => ContractExpression::SequenceLiteral(
            elements
                .into_iter()
                .map(recurse)
                .collect::<Result<_, _>>()?,
        ),
        ContractExpression::SequenceConcat(left, right) => ContractExpression::SequenceConcat(
            Box::new(recurse(*left)?),
            Box::new(recurse(*right)?),
        ),
        ContractExpression::ResourceCount(resource) => {
            reject_counted_field_resource(&resource, resource_definitions)?;
            let resource = expand_declared_resource_clause(*resource, resource_definitions)?;
            ContractExpression::ResourceCount(Box::new(resource))
        }
        ContractExpression::Field {
            base,
            field,
            lowered,
        } => ContractExpression::Field {
            base: Box::new(recurse(*base)?),
            field,
            lowered,
        },
        ContractExpression::Old(body) => ContractExpression::Old(Box::new(recurse(*body)?)),
        ContractExpression::At {
            selector,
            expression,
        } => ContractExpression::At {
            selector,
            expression: Box::new(recurse(*expression)?),
        },
        ContractExpression::Add(left, right) => {
            ContractExpression::Add(Box::new(recurse(*left)?), Box::new(recurse(*right)?))
        }
        ContractExpression::Subtract(left, right) => {
            ContractExpression::Subtract(Box::new(recurse(*left)?), Box::new(recurse(*right)?))
        }
        ContractExpression::Multiply(left, right) => {
            ContractExpression::Multiply(Box::new(recurse(*left)?), Box::new(recurse(*right)?))
        }
        ContractExpression::Divide(left, right) => {
            ContractExpression::Divide(Box::new(recurse(*left)?), Box::new(recurse(*right)?))
        }
        ContractExpression::Remainder(left, right) => {
            ContractExpression::Remainder(Box::new(recurse(*left)?), Box::new(recurse(*right)?))
        }
        ContractExpression::ShiftLeft(left, right) => {
            ContractExpression::ShiftLeft(Box::new(recurse(*left)?), Box::new(recurse(*right)?))
        }
        ContractExpression::ShiftRight(left, right) => {
            ContractExpression::ShiftRight(Box::new(recurse(*left)?), Box::new(recurse(*right)?))
        }
        ContractExpression::BitwiseAnd(left, right) => {
            ContractExpression::BitwiseAnd(Box::new(recurse(*left)?), Box::new(recurse(*right)?))
        }
        ContractExpression::BitwiseOr(left, right) => {
            ContractExpression::BitwiseOr(Box::new(recurse(*left)?), Box::new(recurse(*right)?))
        }
        ContractExpression::BitwiseXor(left, right) => {
            ContractExpression::BitwiseXor(Box::new(recurse(*left)?), Box::new(recurse(*right)?))
        }
        ContractExpression::BitwiseNot(body) => {
            ContractExpression::BitwiseNot(Box::new(recurse(*body)?))
        }
        ContractExpression::Index(base, index) => {
            ContractExpression::Index(Box::new(recurse(*base)?), Box::new(recurse(*index)?))
        }
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => ContractExpression::If {
            condition: Box::new(expand_declared_resource_proposition(
                *condition,
                resource_definitions,
            )?),
            then_branch: Box::new(recurse(*then_branch)?),
            else_branch: Box::new(recurse(*else_branch)?),
        },
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => ContractExpression::RangeFold {
            start: Box::new(recurse(*start)?),
            end: Box::new(recurse(*end)?),
            initial: Box::new(recurse(*initial)?),
            accumulator,
            item,
            body: Box::new(recurse(*body)?),
        },
        ContractExpression::Let {
            name,
            click_type,
            value,
            body,
        } => ContractExpression::Let {
            name,
            click_type,
            value: Box::new(recurse(*value)?),
            body: Box::new(recurse(*body)?),
        },
        ContractExpression::Call { name, arguments } => ContractExpression::Call {
            name,
            arguments: arguments
                .into_iter()
                .map(recurse)
                .collect::<Result<Vec<_>, _>>()?,
        },
        expression => expression,
    })
}

fn declared_resource_info(
    name: &str,
    actual: usize,
    resource_definitions: &BTreeMap<String, DeclaredResourceInfo>,
) -> Result<DeclaredResourceInfo, ClickError> {
    declared_resource_info_with_fields(name, actual, resource_definitions, false)
}

fn declared_resource_info_with_fields(
    name: &str,
    actual: usize,
    resource_definitions: &BTreeMap<String, DeclaredResourceInfo>,
    allow_fields: bool,
) -> Result<DeclaredResourceInfo, ClickError> {
    let Some(info) = resource_definitions.get(name) else {
        return Err(ClickError::new(format!("unknown resource `{name}`")));
    };
    let expected = info.parameter_types.len();
    if expected != actual {
        return Err(ClickError::new(format!(
            "resource `{name}` expects {expected} argument(s), got {actual}"
        )));
    }
    if info.has_fields && !allow_fields {
        return Err(ClickError::new(format!(
            "resource `{name}` has fields; bind it with `owns name: {name}(...);`"
        )));
    }
    Ok(info.clone())
}

fn reject_counted_field_resource(
    resource: &ResourceClause,
    definitions: &BTreeMap<String, DeclaredResourceInfo>,
) -> Result<(), ClickError> {
    match resource {
        ResourceClause::Declared { name, .. }
            if definitions.get(name).is_some_and(|info| info.has_fields) =>
        {
            Err(ClickError::new(format!(
                "resource `{name}` has fields and is not countable"
            )))
        }
        ResourceClause::Quantified { resource, .. } => {
            reject_counted_field_resource(resource, definitions)
        }
        _ => Ok(()),
    }
}

pub(in crate::surface) fn combined_predicate_definitions(
    file: &ClickFile,
) -> Result<Vec<PredicateDefinition>, ClickError> {
    let mut definitions = standard_library()?.predicate_definitions().to_vec();
    definitions.extend(file.predicate_definitions().iter().cloned());
    Ok(definitions)
}

pub(in crate::surface) fn combined_click_function_definitions(
    file: &ClickFile,
) -> Result<Vec<ClickFunctionDefinition>, ClickError> {
    let mut definitions = standard_library()?.click_function_definitions().to_vec();
    definitions.extend(file.click_function_definitions().iter().cloned());
    Ok(definitions)
}

pub(in crate::surface) fn combined_resource_definitions(
    file: &ClickFile,
) -> Result<Vec<ResourceDefinition>, ClickError> {
    let mut definitions = standard_library()?.resource_definitions().to_vec();
    definitions.extend(file.resource_definitions().iter().cloned());
    Ok(definitions)
}

pub(in crate::surface) fn combined_theorem_definitions(
    file: &ClickFile,
) -> Result<Vec<TheoremDefinition>, ClickError> {
    let mut definitions = standard_library()?.theorem_definitions().to_vec();
    definitions.extend(file.theorem_definitions().iter().cloned());
    Ok(definitions)
}

pub(in crate::surface) fn combined_theorem_definitions_with_stdlib_ensure_count(
    file: &ClickFile,
) -> Result<(Vec<TheoremDefinition>, usize), ClickError> {
    let mut definitions = standard_library()?.theorem_definitions().to_vec();
    let stdlib_ensure_count = definitions
        .iter()
        .map(|definition| definition.ensures().len())
        .sum();
    definitions.extend(file.theorem_definitions().iter().cloned());
    Ok((definitions, stdlib_ensure_count))
}
