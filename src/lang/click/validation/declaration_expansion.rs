use super::*;

#[derive(Clone, Debug, Eq, PartialEq)]
struct DeclaredResourceInfo {
    parameter_types: Vec<C0Type>,
    kind: ResourceKind,
}

type StandardLibraryDefinitions = (
    Vec<PredicateDefinition>,
    Vec<ClickFunctionDefinition>,
    Vec<ResourceDefinition>,
    Vec<TheoremDefinition>,
);

fn standard_library_definitions() -> Result<StandardLibraryDefinitions, ClickError> {
    let file = expand_declared_resource_clauses(parser::parse_file_items(CLICK_STANDARD_LIBRARY)?)?;
    if !file.verifying_sources().is_empty() || !file.function_blocks().is_empty() {
        return Err(ClickError::new(
            "internal Click standard library must not contain verifying sources or C function specs",
        ));
    }
    Ok((
        file.predicate_definitions().to_vec(),
        file.click_function_definitions().to_vec(),
        file.resource_definitions().to_vec(),
        file.theorem_definitions().to_vec(),
    ))
}

pub(in crate::lang::click) fn expand_declared_resource_clauses(
    mut file: ClickFile,
) -> Result<ClickFile, ClickError> {
    let mut resource_definitions = file
        .resource_definitions()
        .iter()
        .map(|definition| {
            (
                definition.name().to_string(),
                DeclaredResourceInfo {
                    parameter_types: definition
                        .parameters()
                        .iter()
                        .map(FunctionParameter::c_type)
                        .collect::<Vec<_>>(),
                    kind: if definition.multiplicity() == ResourceMultiplicity::Counted {
                        ResourceKind::Counted
                    } else if definition.composite_body().is_some() {
                        ResourceKind::Composite
                    } else {
                        ResourceKind::Token
                    },
                },
            )
        })
        .collect::<BTreeMap<_, _>>();
    resource_definitions
        .entry(CResourceFact::ALLOCATION_RESOURCE_NAME.to_string())
        .or_insert_with(|| DeclaredResourceInfo {
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

    for function in &mut file.function_blocks {
        function.decreases = function
            .decreases
            .take()
            .map(|decreases| match decreases {
                CFunctionDecrease::Numeric(expression) => {
                    Ok(CFunctionDecrease::Numeric(expression))
                }
                CFunctionDecrease::Resource(resource) => Ok(CFunctionDecrease::Resource(
                    expand_declared_resource_clause(resource, &resource_definitions)?,
                )),
            })
            .transpose()?;
        function.requires = function
            .requires
            .drain(..)
            .map(|requirement| {
                expand_declared_resource_requirement(requirement, &resource_definitions)
            })
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
    proof: Proof,
    resource_definitions: &BTreeMap<String, DeclaredResourceInfo>,
) -> Result<Proof, ClickError> {
    match proof {
        Proof::Default => Ok(proof),
        Proof::Tactic(_) => Ok(proof),
        Proof::Script(tactics) => Ok(Proof::Script(
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
        ProofTactic::StepUsing(premises) => Ok(ProofTactic::StepUsing(
            premises
                .into_iter()
                .map(|premise| expand_declared_resource_proposition(premise, resource_definitions))
                .collect::<Result<Vec<_>, _>>()?,
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
            application,
            premises: premises
                .into_iter()
                .map(|premise| expand_declared_resource_proposition(premise, resource_definitions))
                .collect::<Result<Vec<_>, _>>()?,
        }),
        ProofTactic::UnfoldResource(resource) => Ok(ProofTactic::UnfoldResource(
            expand_declared_resource_clause(resource, resource_definitions)?,
        )),
        ProofTactic::ObserveResource(resource) => Ok(ProofTactic::ObserveResource(
            expand_declared_resource_clause(resource, resource_definitions)?,
        )),
        ProofTactic::FoldResource(resource) => Ok(ProofTactic::FoldResource(
            expand_declared_resource_clause(resource, resource_definitions)?,
        )),
        ProofTactic::Contradiction(proposition) => Ok(ProofTactic::Contradiction(
            expand_declared_resource_proposition(proposition, resource_definitions)?,
        )),
        ProofTactic::Derive(derive) => Ok(ProofTactic::Derive(ProofDerive {
            premises: derive
                .premises
                .into_iter()
                .map(|premise| expand_declared_resource_proposition(premise, resource_definitions))
                .collect::<Result<Vec<_>, _>>()?,
        })),
        ProofTactic::Have(have) => Ok(ProofTactic::Have(ProofHave {
            proposition: expand_declared_resource_proposition(
                have.proposition,
                resource_definitions,
            )?,
            proof: expand_declared_resource_proof(have.proof, resource_definitions)?,
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
                arguments,
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
                arguments,
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
        ContractExpression::ResourceCount(resource) => {
            let resource = expand_declared_resource_clause(*resource, resource_definitions)?;
            if !matches!(
                resource,
                ResourceClause::Declared {
                    kind: ResourceKind::Counted,
                    ..
                }
            ) {
                return Err(ClickError::new("`count(...)` expects a counted resource"));
            }
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
            c_type,
            value,
            body,
        } => ContractExpression::Let {
            name,
            c_type,
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
    let Some(info) = resource_definitions.get(name) else {
        return Err(ClickError::new(format!("unknown resource `{name}`")));
    };
    let expected = info.parameter_types.len();
    if expected != actual {
        return Err(ClickError::new(format!(
            "resource `{name}` expects {expected} argument(s), got {actual}"
        )));
    }
    Ok(info.clone())
}

pub(in crate::lang::click) fn combined_predicate_definitions(
    file: &ClickFile,
) -> Result<Vec<PredicateDefinition>, ClickError> {
    let (mut definitions, _, _, _) = standard_library_definitions()?;
    definitions.extend(file.predicate_definitions().iter().cloned());
    Ok(definitions)
}

pub(in crate::lang::click) fn combined_click_function_definitions(
    file: &ClickFile,
) -> Result<Vec<ClickFunctionDefinition>, ClickError> {
    let (_, mut definitions, _, _) = standard_library_definitions()?;
    definitions.extend(file.click_function_definitions().iter().cloned());
    Ok(definitions)
}

pub(in crate::lang::click) fn combined_resource_definitions(
    file: &ClickFile,
) -> Result<Vec<ResourceDefinition>, ClickError> {
    let (_, _, mut definitions, _) = standard_library_definitions()?;
    definitions.extend(file.resource_definitions().iter().cloned());
    Ok(definitions)
}

pub(in crate::lang::click) fn combined_theorem_definitions(
    file: &ClickFile,
) -> Result<Vec<TheoremDefinition>, ClickError> {
    let (_, _, _, mut definitions) = standard_library_definitions()?;
    definitions.extend(file.theorem_definitions().iter().cloned());
    Ok(definitions)
}

pub(in crate::lang::click) fn combined_theorem_definitions_with_stdlib_ensure_count(
    file: &ClickFile,
) -> Result<(Vec<TheoremDefinition>, usize), ClickError> {
    let (_, _, _, mut definitions) = standard_library_definitions()?;
    let stdlib_ensure_count = definitions
        .iter()
        .map(|definition| definition.ensures().len())
        .sum();
    definitions.extend(file.theorem_definitions().iter().cloned());
    Ok((definitions, stdlib_ensure_count))
}
