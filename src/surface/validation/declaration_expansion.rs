use super::*;

#[cfg(test)]
mod tests;

#[derive(Clone, Debug, Eq, PartialEq)]
struct DeclaredResourceInfo {
    fields: std::sync::Arc<BTreeMap<String, (usize, ClickType)>>,
    parameter_types: Vec<C0Type>,
    kind: ResourceKind,
    has_fields: bool,
    /// Each matched-arm child slot of this resource and the resource that
    /// slot declares, or `None` when two arms give one slot name different
    /// resources. A child may name another declared resource, so the slot's
    /// family is a property of this definition rather than of the proof.
    child_slots: std::sync::Arc<BTreeMap<String, Option<String>>>,
}

/// Declared resources plus what the expansion has learned about the resource
/// instances a proof names. `let { slot: name } = unfold(parent)` introduces
/// `name` before any definition is available to the parser, so the parser
/// records the parent's family provisionally and the slot decides the real
/// one here.
struct DeclaredResourceScope {
    definitions: BTreeMap<String, DeclaredResourceInfo>,
    /// Instances introduced as matched-arm children, by identity. These
    /// override whatever family the parser recorded.
    children: std::cell::RefCell<BTreeMap<Variable, String>>,
    /// Every other instance family seen in declaration order.
    instances: std::cell::RefCell<BTreeMap<Variable, String>>,
    /// Names an unfold pattern bound to a scalar field's value. The parser
    /// allocated them an instance identity before the field was known.
    field_binders: std::cell::RefCell<BTreeSet<Variable>>,
}

impl DeclaredResourceScope {
    fn get(&self, name: &str) -> Option<&DeclaredResourceInfo> {
        self.definitions.get(name)
    }

    fn contains_key(&self, name: &str) -> bool {
        self.definitions.contains_key(name)
    }

    /// The resource of the instance `identity`, if the expansion has seen a
    /// declaration that fixes it.
    fn instance_resource(&self, identity: Variable) -> Option<String> {
        if let Some(name) = self.children.borrow().get(&identity) {
            return Some(name.clone());
        }
        self.instances.borrow().get(&identity).cloned()
    }

    /// Record the resource of `identity`. An explicit `fold(name(...), ...)`
    /// construction names its own resource, so it also replaces whatever
    /// child slot the identity was introduced by.
    fn record_instance(&self, identity: Variable, name: &str, construction: bool) {
        if construction {
            self.children.borrow_mut().remove(&identity);
        }
        if !self.children.borrow().contains_key(&identity) {
            self.instances
                .borrow_mut()
                .insert(identity, name.to_string());
        }
    }

    fn record_field_binder(&self, identity: Variable) {
        self.field_binders.borrow_mut().insert(identity);
    }

    fn record_child(&self, identity: Variable, name: &str) {
        self.children
            .borrow_mut()
            .insert(identity, name.to_string());
    }
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

/// The parsed standard-library function block whose declaration name is
/// `name`, if the library declares one. A recognized builtin effect is bound
/// to this exact declaration: matching a bare name would let an unrelated
/// user function acquire the effect when it merely shares the spelling.
pub(in crate::surface) fn standard_library_function_block(
    name: &str,
) -> Result<Option<FunctionBlock>, ClickError> {
    Ok(standard_library()?
        .function_blocks()
        .iter()
        .find(|function| function.signature().name() == name)
        .cloned())
}

/// Every matched-arm child slot of `definition`, mapped to the resource it
/// declares. A slot two arms spell with different resources maps to `None`;
/// the proof's own `fold` spelling then decides, and this pass checks
/// nothing about it.
fn matched_arm_child_slots(definition: &ResourceDefinition) -> BTreeMap<String, Option<String>> {
    let mut slots: BTreeMap<String, Option<String>> = BTreeMap::new();
    let Some(body) = definition.composite_body() else {
        return slots;
    };
    // An unmatched body's named children are its slots as well.
    let bodies = std::iter::once(body).chain(
        body.matched
            .iter()
            .flat_map(|matched| &matched.arms)
            .map(|arm| &arm.body),
    );
    for body in bodies {
        for clause in &body.contains {
            let ResourceClause::Named { binding, resource } = clause else {
                continue;
            };
            let ResourceClause::Declared { name, .. } = resource.as_ref() else {
                continue;
            };
            slots
                .entry(binding.name.clone())
                .and_modify(|existing| {
                    if existing.as_deref() != Some(name.as_str()) {
                        *existing = None;
                    }
                })
                .or_insert_with(|| Some(name.clone()));
        }
    }
    slots
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
                    child_slots: std::sync::Arc::new(matched_arm_child_slots(definition)),
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
            child_slots: Default::default(),
        });
    resource_definitions.insert(
        "mutex_guard".into(),
        DeclaredResourceInfo {
            fields: Default::default(),
            has_fields: false,
            parameter_types: vec![C0Type::VoidPointer],
            kind: ResourceKind::Token,
            child_slots: Default::default(),
        },
    );
    resource_definitions.insert(
        "mutex_live".into(),
        DeclaredResourceInfo {
            fields: Default::default(),
            has_fields: false,
            parameter_types: vec![C0Type::VoidPointer],
            kind: ResourceKind::Token,
            child_slots: Default::default(),
        },
    );
    let resource_definitions = DeclaredResourceScope {
        definitions: resource_definitions,
        children: Default::default(),
        instances: Default::default(),
        field_binders: Default::default(),
    };

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
    resource_definitions: &DeclaredResourceScope,
) -> Result<(), ClickError> {
    let declared_binders = function
        .requires
        .iter()
        .filter_map(|requirement| match requirement.inner() {
            Requirement::Resource(ResourceClause::Named { binding, .. }) => {
                Some(binding.name.clone())
            }
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    function.decreases = function
        .decreases
        .take()
        .map(|decreases| match decreases {
            CFunctionDecrease::Unresolved(expression) => {
                classify_function_decrease(expression, &declared_binders, resource_definitions)
            }
            CFunctionDecrease::Numeric(expression) => Ok(CFunctionDecrease::Numeric(
                expand_declared_resource_expression(expression, resource_definitions)?,
            )),
            CFunctionDecrease::Resource(resource) => Ok(CFunctionDecrease::Resource(
                expand_declared_resource_clause(resource, resource_definitions)?,
            )),
            CFunctionDecrease::Binder(name) => Ok(CFunctionDecrease::Binder(name)),
        })
        .transpose()?;
    function.requires = function
        .requires
        .drain(..)
        .map(|requirement| expand_declared_resource_requirement(requirement, resource_definitions))
        .collect::<Result<Vec<_>, _>>()?;
    function.ensures = function
        .ensures
        .drain(..)
        .map(|clause| expand_declared_resource_ensure_clause(clause, resource_definitions))
        .collect::<Result<Vec<_>, _>>()?;
    function.constructs = function
        .constructs
        .drain(..)
        .map(|resource| expand_declared_resource_clause(resource, resource_definitions))
        .collect::<Result<Vec<_>, _>>()?;
    function.structural_clauses = function
        .structural_clauses
        .drain(..)
        .map(|clause| expand_declared_resource_structural_clause(clause, resource_definitions))
        .collect::<Result<Vec<_>, _>>()?;
    function.grouped_proof = function
        .grouped_proof
        .take()
        .map(|proof| expand_declared_resource_proof(proof, resource_definitions))
        .transpose()?;
    Ok(())
}

fn expand_declared_resource_definition(
    mut definition: ResourceDefinition,
    resource_definitions: &DeclaredResourceScope,
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
    resource_definitions: &DeclaredResourceScope,
) -> Result<CompositeResourceBody, ClickError> {
    Ok(CompositeResourceBody {
        children: composite_body.children,
        fields: composite_body.fields,
        guarded_by: composite_body.guarded_by,
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
    resource_definitions: &DeclaredResourceScope,
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
    resource_definitions: &DeclaredResourceScope,
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

fn expand_declared_resource_structural_clause(
    mut clause: StructuralClause,
    resource_definitions: &DeclaredResourceScope,
) -> Result<StructuralClause, ClickError> {
    clause.items = clause
        .items
        .into_iter()
        .map(|item| expand_declared_resource_structural_item(item, resource_definitions))
        .collect::<Result<Vec<_>, _>>()?;
    clause.resources = clause
        .resources
        .into_iter()
        .map(|resource| expand_declared_resource_clause(resource, resource_definitions))
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
    // A `decreases` component is an ordinary contract expression now that the
    // slot takes pure expressions, so a resource field it reads needs the same
    // declared-resource expansion an invariant's does. Without it the field's
    // declared type never reaches the component and lowering refuses a
    // perfectly ordinary `decreases c.rank`.
    clause.decreases = clause
        .decreases
        .take()
        .map(|measure| {
            Ok::<_, ClickError>(TerminationMeasure::new(
                measure
                    .components()
                    .iter()
                    .cloned()
                    .map(|component| {
                        expand_declared_resource_expression(component, resource_definitions)
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            ))
        })
        .transpose()?;
    Ok(clause)
}

fn expand_declared_resource_structural_item(
    mut item: StructuralItem,
    resource_definitions: &DeclaredResourceScope,
) -> Result<StructuralItem, ClickError> {
    item.claim = expand_declared_resource_proposition(item.claim, resource_definitions)?;
    Ok(item)
}

fn expand_declared_resource_proof(
    proof: SourceProof,
    resource_definitions: &DeclaredResourceScope,
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

// Keep the recursive tactic dispatcher small. Each helper owns only one
// family of large syntax temporaries, so nested proof scripts do not retain
// every tactic variant's frame at once.
#[inline(never)]
fn expand_declared_resource_tactic(
    tactic: ProofTactic,
    resource_definitions: &DeclaredResourceScope,
) -> Result<ProofTactic, ClickError> {
    match tactic {
        tactic @ (ProofTactic::ApplyTheorem(_)
        | ProofTactic::Witness(_)
        | ProofTactic::ApplyInduction { .. }
        | ProofTactic::ApplyInductionUsing { .. }
        | ProofTactic::ApplyTheoremUsing { .. }
        | ProofTactic::UnfoldFunction(_)
        | ProofTactic::InstantiateUsing { .. }) => {
            expand_declared_resource_tactic_with_expressions(tactic, resource_definitions)
        }
        tactic @ (ProofTactic::ArithmeticUsing(_)
        | ProofTactic::Contradiction(_)
        | ProofTactic::Extract(_)
        | ProofTactic::Rewrite(_)
        | ProofTactic::Transport { .. }
        | ProofTactic::TransportUsing { .. }
        | ProofTactic::SimpUsing(_)
        | ProofTactic::NormalizeUsing(_)) => {
            expand_declared_resource_tactic_with_propositions(tactic, resource_definitions)
        }
        tactic @ (ProofTactic::UnfoldResource(_)
        | ProofTactic::ObserveResource(_)
        | ProofTactic::FoldResource(_)
        | ProofTactic::ConstructResource(_)
        | ProofTactic::Iterated(_)) => {
            expand_declared_resource_tactic_with_resources(tactic, resource_definitions)
        }
        tactic @ (ProofTactic::Have(_)
        | ProofTactic::Open(_)
        | ProofTactic::If(_)
        | ProofTactic::Match(_)
        | ProofTactic::Cases(_)
        | ProofTactic::StructuralInduct { .. }
        | ProofTactic::Branch(_)
        | ProofTactic::Loop(_)) => {
            expand_declared_resource_tactic_with_nested_proofs(tactic, resource_definitions)
        }
        tactic @ (ProofTactic::Both(_) | ProofTactic::CloseInvariantsBy(_)) => {
            expand_declared_resource_tactic_with_plain_scripts(tactic, resource_definitions)
        }
        ProofTactic::ArithmeticCertificate(certificate) => Ok(ProofTactic::ArithmeticCertificate(
            expand_declared_resource_certificate(certificate, resource_definitions)?,
        )),
        tactic => Ok(tactic),
    }
}

/// An explicit arithmetic certificate names resource fields in its premises,
/// definedness terms, and stated results exactly as the tactic `arithmetic()`
/// it expands does, so they are resolved against the declared resources the
/// same way: an expanded certificate over a field such as `r.start` lowers
/// its definedness premise as the smart tactic's own premise did.
#[inline(never)]
fn expand_declared_resource_certificate(
    certificate: ArithmeticCertificate,
    resource_definitions: &DeclaredResourceScope,
) -> Result<ArithmeticCertificate, ClickError> {
    let proposition =
        |proposition| expand_declared_resource_proposition(proposition, resource_definitions);
    let expression =
        |expression| expand_declared_resource_expression(expression, resource_definitions);
    let family = match certificate.family {
        ArithmeticCertificateFamily::Integer(integer) => {
            ArithmeticCertificateFamily::Integer(IntegerCertificate {
                nodes: integer
                    .nodes
                    .into_iter()
                    .map(|node| {
                        Ok(match node {
                            IntegerCertificateNode::Premise {
                                index,
                                proposition: premise,
                                result,
                            } => IntegerCertificateNode::Premise {
                                index,
                                proposition: proposition(premise)?,
                                result: proposition(result)?,
                            },
                            IntegerCertificateNode::Scale {
                                source,
                                coefficient,
                                result,
                            } => IntegerCertificateNode::Scale {
                                source,
                                coefficient: expression(coefficient)?,
                                result: proposition(result)?,
                            },
                            IntegerCertificateNode::Add {
                                left,
                                right,
                                result,
                            } => IntegerCertificateNode::Add {
                                left,
                                right,
                                result: proposition(result)?,
                            },
                            IntegerCertificateNode::EqualityToLessEqual {
                                source,
                                reverse,
                                result,
                            } => IntegerCertificateNode::EqualityToLessEqual {
                                source,
                                reverse,
                                result: proposition(result)?,
                            },
                            IntegerCertificateNode::EqualityFromBounds {
                                lower,
                                upper,
                                result,
                            } => IntegerCertificateNode::EqualityFromBounds {
                                lower,
                                upper,
                                result: proposition(result)?,
                            },
                            IntegerCertificateNode::Trivial { result } => {
                                IntegerCertificateNode::Trivial {
                                    result: proposition(result)?,
                                }
                            }
                        })
                    })
                    .collect::<Result<Vec<_>, ClickError>>()?,
                conclusion: integer.conclusion,
            })
        }
        ArithmeticCertificateFamily::SignedInt32(signed) => {
            ArithmeticCertificateFamily::SignedInt32(SignedInt32Certificate {
                nodes: signed
                    .nodes
                    .into_iter()
                    .map(|node| expand_declared_resource_signed_step(node, resource_definitions))
                    .collect::<Result<Vec<_>, ClickError>>()?,
                conclusion: signed.conclusion,
            })
        }
        ArithmeticCertificateFamily::Special(mut special) => {
            special.premises = special
                .premises
                .into_iter()
                .map(proposition)
                .collect::<Result<Vec<_>, ClickError>>()?;
            special.nodes = special
                .nodes
                .into_iter()
                .map(|node| {
                    Ok(match node {
                        SpecialArithmeticNode::SignedDefined {
                            width,
                            bounds,
                            result,
                        } => SpecialArithmeticNode::SignedDefined {
                            width,
                            bounds,
                            result: proposition(result)?,
                        },
                        other => other,
                    })
                })
                .collect::<Result<Vec<_>, ClickError>>()?;
            ArithmeticCertificateFamily::Special(special)
        }
    };
    Ok(ArithmeticCertificate { family })
}

fn expand_declared_resource_signed_step(
    step: SignedArithmeticStep,
    resource_definitions: &DeclaredResourceScope,
) -> Result<SignedArithmeticStep, ClickError> {
    let proposition =
        |proposition| expand_declared_resource_proposition(proposition, resource_definitions);
    let expression =
        |expression| expand_declared_resource_expression(expression, resource_definitions);
    Ok(match step {
        SignedArithmeticStep::Premise {
            index,
            proposition: premise,
            result,
        } => SignedArithmeticStep::Premise {
            index,
            proposition: proposition(premise)?,
            result: proposition(result)?,
        },
        SignedArithmeticStep::Scale {
            source,
            coefficient,
            result,
        } => SignedArithmeticStep::Scale {
            source,
            coefficient: expression(coefficient)?,
            result: proposition(result)?,
        },
        SignedArithmeticStep::Add {
            left,
            right,
            result,
        } => SignedArithmeticStep::Add {
            left,
            right,
            result: proposition(result)?,
        },
        SignedArithmeticStep::EqualityToLessEqual {
            source,
            reverse,
            result,
        } => SignedArithmeticStep::EqualityToLessEqual {
            source,
            reverse,
            result: proposition(result)?,
        },
        SignedArithmeticStep::EqualityFromBounds {
            lower,
            upper,
            result,
        } => SignedArithmeticStep::EqualityFromBounds {
            lower,
            upper,
            result: proposition(result)?,
        },
        SignedArithmeticStep::StrictFromDisequal {
            bound,
            disequal,
            result,
        } => SignedArithmeticStep::StrictFromDisequal {
            bound,
            disequal,
            result: proposition(result)?,
        },
        SignedArithmeticStep::Trivial { result } => SignedArithmeticStep::Trivial {
            result: proposition(result)?,
        },
        SignedArithmeticStep::Int32Range { result } => SignedArithmeticStep::Int32Range {
            result: proposition(result)?,
        },
        SignedArithmeticStep::IntervalFromAffine {
            source,
            term,
            lower,
            upper,
        } => SignedArithmeticStep::IntervalFromAffine {
            source,
            term: expression(term)?,
            lower,
            upper,
        },
        SignedArithmeticStep::IntervalFromAffineDirect {
            source,
            term,
            lower,
            upper,
        } => SignedArithmeticStep::IntervalFromAffineDirect {
            source,
            term: expression(term)?,
            lower,
            upper,
        },
        SignedArithmeticStep::IntervalAtom { term, lower, upper } => {
            SignedArithmeticStep::IntervalAtom {
                term: expression(term)?,
                lower,
                upper,
            }
        }
        SignedArithmeticStep::DefinedPremise { index, term } => {
            SignedArithmeticStep::DefinedPremise {
                index,
                term: expression(term)?,
            }
        }
        SignedArithmeticStep::IntervalCompare {
            left,
            right,
            comparison,
            result,
        } => SignedArithmeticStep::IntervalCompare {
            left,
            right,
            comparison,
            result: proposition(result)?,
        },
        SignedArithmeticStep::AffineConclusion {
            source,
            evidence,
            result,
        } => SignedArithmeticStep::AffineConclusion {
            source,
            evidence,
            result: proposition(result)?,
        },
        SignedArithmeticStep::AffineConclusionWithEvidence {
            source,
            left_evidence,
            right_evidence,
            result,
        } => SignedArithmeticStep::AffineConclusionWithEvidence {
            source,
            left_evidence,
            right_evidence,
            result: proposition(result)?,
        },
        step @ (SignedArithmeticStep::IntervalIntersect { .. }
        | SignedArithmeticStep::IntervalAdd { .. }
        | SignedArithmeticStep::IntervalAddBounded { .. }
        | SignedArithmeticStep::IntervalSubtract { .. }
        | SignedArithmeticStep::IntervalMultiply { .. }
        | SignedArithmeticStep::IntervalRemainder { .. }
        | SignedArithmeticStep::IntervalShiftLeft { .. }
        | SignedArithmeticStep::IntervalArithmeticShiftRight { .. }
        | SignedArithmeticStep::IntervalBitwiseAnd { .. }
        | SignedArithmeticStep::IntervalSignBitFlip { .. }) => step,
    })
}

/// A tactic whose children are ordinary scripts and nothing else.
///
/// `both` nests as deeply as a written conjunction does, so it gets its own
/// helper rather than sharing the nested-proof dispatcher's frame, which holds
/// one large syntax temporary per tactic family. `close_invariants() by { .. }`
/// joins it because generated closers are exactly such a conjunction, and a
/// resource field named inside one needs the same expansion every other script
/// gets.
#[inline(never)]
fn expand_declared_resource_tactic_with_plain_scripts(
    tactic: ProofTactic,
    resource_definitions: &DeclaredResourceScope,
) -> Result<ProofTactic, ClickError> {
    let expand = |tactics: Vec<ProofTactic>| {
        tactics
            .into_iter()
            .map(|tactic| expand_declared_resource_tactic(tactic, resource_definitions))
            .collect::<Result<Vec<_>, ClickError>>()
    };
    match tactic {
        ProofTactic::Both(proof_both) => Ok(ProofTactic::Both(ProofBoth {
            left_tactics: expand(proof_both.left_tactics)?,
            right_tactics: expand(proof_both.right_tactics)?,
        })),
        ProofTactic::CloseInvariantsBy(tactics) => {
            Ok(ProofTactic::CloseInvariantsBy(expand(tactics)?))
        }
        _ => unreachable!("tactic dispatched to the wrong declaration-expansion helper"),
    }
}

#[inline(never)]
fn expand_declared_resource_tactic_with_expressions(
    tactic: ProofTactic,
    resource_definitions: &DeclaredResourceScope,
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
            arguments,
        } => Ok(ProofTactic::ApplyInduction {
            hypothesis,
            arguments: arguments
                .into_iter()
                .map(|argument| expand_declared_resource_expression(argument, resource_definitions))
                .collect::<Result<_, _>>()?,
        }),
        ProofTactic::ApplyInductionUsing {
            hypothesis,
            arguments,
            premises,
        } => Ok(ProofTactic::ApplyInductionUsing {
            hypothesis,
            arguments: arguments
                .into_iter()
                .map(|argument| expand_declared_resource_expression(argument, resource_definitions))
                .collect::<Result<_, _>>()?,
            premises: premises
                .into_iter()
                .map(|premise| expand_declared_resource_proposition(premise, resource_definitions))
                .collect::<Result<_, _>>()?,
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
        _ => unreachable!("tactic dispatched to the wrong declaration-expansion helper"),
    }
}

#[inline(never)]
fn expand_declared_resource_tactic_with_propositions(
    tactic: ProofTactic,
    resource_definitions: &DeclaredResourceScope,
) -> Result<ProofTactic, ClickError> {
    match tactic {
        ProofTactic::ArithmeticUsing(premises) => Ok(ProofTactic::ArithmeticUsing(
            premises
                .into_iter()
                .map(|premise| expand_declared_resource_proposition(premise, resource_definitions))
                .collect::<Result<_, _>>()?,
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
                .collect::<Result<_, _>>()?,
        )),
        _ => unreachable!("tactic dispatched to the wrong declaration-expansion helper"),
    }
}

#[inline(never)]
fn expand_declared_resource_tactic_with_resources(
    tactic: ProofTactic,
    resource_definitions: &DeclaredResourceScope,
) -> Result<ProofTactic, ClickError> {
    match tactic {
        ProofTactic::UnfoldResource(resource) => Ok(ProofTactic::UnfoldResource(
            expand_declared_resource_clause(resource, resource_definitions)?,
        )),
        ProofTactic::ObserveResource(resource) => Ok(ProofTactic::ObserveResource(
            expand_declared_resource_clause(resource, resource_definitions)?,
        )),
        ProofTactic::FoldResource(resource) => Ok(ProofTactic::FoldResource(
            expand_declared_resource_clause(resource, resource_definitions)?,
        )),
        ProofTactic::ConstructResource(resource) => Ok(ProofTactic::ConstructResource(
            expand_declared_resource_clause(resource, resource_definitions)?,
        )),
        ProofTactic::Iterated(IteratedTactic::Gather(resource)) => {
            Ok(ProofTactic::Iterated(IteratedTactic::Gather(
                expand_declared_resource_clause(resource, resource_definitions)?,
            )))
        }
        ProofTactic::Iterated(IteratedTactic::Scatter(resource)) => {
            Ok(ProofTactic::Iterated(IteratedTactic::Scatter(
                expand_declared_resource_clause(resource, resource_definitions)?,
            )))
        }
        tactic @ ProofTactic::Iterated(IteratedTactic::Take(_) | IteratedTactic::Give(_)) => {
            Ok(tactic)
        }
        _ => unreachable!("tactic dispatched to the wrong declaration-expansion helper"),
    }
}

#[inline(never)]
fn expand_declared_resource_tactic_with_nested_proofs(
    tactic: ProofTactic,
    resource_definitions: &DeclaredResourceScope,
) -> Result<ProofTactic, ClickError> {
    match tactic {
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
        ProofTactic::Match(proof_match) => Ok(ProofTactic::Match(Box::new(ProofMatch {
            scrutinee: expand_declared_resource_expression(
                proof_match.scrutinee,
                resource_definitions,
            )?,
            arms: proof_match
                .arms
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
                            .collect::<Result<_, _>>()?,
                    })
                })
                .collect::<Result<_, ClickError>>()?,
        }))),
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
        _ => unreachable!("tactic dispatched to the wrong declaration-expansion helper"),
    }
}

/// Decides what a C function's parsed `decreases` expression names (D6).
///
/// Functions and resources share one namespace and declaration order creates
/// no scope, so the parser cannot make this decision; this pass can, because
/// it holds every declared resource and the function's own contract binders.
/// An application of a declared resource is a structural measure over that
/// entry resource, a bare contract resource binder is a structural measure
/// over the instance that binder names, and everything else stays the
/// existing numeric measure over an int32 parameter.
///
/// Cost is the one expression's head, not a search.
fn classify_function_decrease(
    expression: ContractExpression,
    declared_binders: &BTreeSet<String>,
    resource_definitions: &DeclaredResourceScope,
) -> Result<CFunctionDecrease, ClickError> {
    match &expression {
        ContractExpression::Call { name, arguments } if resource_definitions.contains_key(name) => {
            Ok(CFunctionDecrease::Resource(
                expand_declared_resource_clause(
                    ResourceClause::Declared {
                        access: ResourceAccessMode::View,
                        kind: ResourceKind::Token,
                        name: name.clone(),
                        arguments: arguments.clone(),
                        parameter_types: Vec::new(),
                    },
                    resource_definitions,
                )?,
            ))
        }
        ContractExpression::Binding(name)
        | ContractExpression::CBinding(name)
        | ContractExpression::CFragment(CExpression::Variable(name))
            if declared_binders.contains(name) =>
        {
            Ok(CFunctionDecrease::Binder(name.clone()))
        }
        _ => Ok(CFunctionDecrease::Numeric(
            expand_declared_resource_expression(expression, resource_definitions)?,
        )),
    }
}

fn expand_declared_resource_clause(
    resource: ResourceClause,
    resource_definitions: &DeclaredResourceScope,
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
            // The parent's family decides what its child slots are. An
            // explicit fold names it; for an unfolded child instance the
            // parser could only record the family it was unfolded from, so
            // prefer what an earlier declaration fixed.
            let construction = binding.fold_fields.is_some();
            let parent = if construction {
                name.clone()
            } else {
                resource_definitions
                    .instance_resource(binding.identity)
                    .unwrap_or_else(|| name.clone())
            };
            resource_definitions.record_instance(binding.identity, &name, construction);
            if let Some(children) = binding.child_bindings.as_ref() {
                let slots = resource_definitions
                    .get(&parent)
                    .map(|info| info.child_slots.clone())
                    .unwrap_or_default();
                let fields = resource_definitions
                    .get(&parent)
                    .map(|info| info.fields.clone())
                    .unwrap_or_default();
                for (slot, child, identity) in children.iter() {
                    // An unfold pattern may also name a scalar field: the
                    // binder is then a proof name for the field's folded
                    // value, not a child instance.
                    if let Some((_, field_type)) = fields.get(slot) {
                        if construction {
                            return Err(ClickError::new(format!(
                                "`{slot}` is a field of `{parent}`, not a child slot; supply it in the fold's field map"
                            )));
                        }
                        if !matches!(field_type, ClickType::C(_)) {
                            return Err(ClickError::new(format!(
                                "field `{slot}` of `{parent}` is not C-typed; an unfold pattern binds only C scalar and pointer fields, so read an algebraic field's payload with a proof `match` on `{}.{slot}` before the unfold",
                                binding.name
                            )));
                        }
                        resource_definitions.record_field_binder(*identity);
                        continue;
                    }
                    let Some(declared) = slots.get(slot) else {
                        return Err(ClickError::new(format!(
                            "resource `{parent}` has no child slot or field `{slot}`"
                        )));
                    };
                    let Some(declared) = declared else {
                        continue;
                    };
                    match resource_definitions.instance_resource(*identity) {
                        // An introduced child takes the slot's resource.
                        None => resource_definitions.record_child(*identity, declared),
                        Some(actual) if actual != *declared => {
                            return Err(ClickError::new(format!(
                                "child `{child}` is `{actual}`, but slot `{slot}` of `{parent}` owns `{declared}`"
                            )));
                        }
                        Some(_) => {}
                    }
                }
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
            if (name == CResourceFact::ALLOCATION_RESOURCE_NAME
                || name == "mutex_guard"
                || name == "mutex_live")
                && access == ResourceAccessMode::View
            {
                return Err(ClickError::new(format!(
                    "{name} authority is owned and cannot be viewed or duplicated"
                )));
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
    resource_definitions: &DeclaredResourceScope,
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
    resource_definitions: &DeclaredResourceScope,
) -> Result<ClickProposition, ClickError> {
    enum Frame {
        Visit(ClickProposition),
        BuildAt(SnapshotSelector),
        BuildAnd,
        BuildOr,
        BuildNot,
        BuildImplies,
        BuildForAll {
            click_type: ClickType,
            name: String,
            written_name: Option<String>,
        },
        BuildExists {
            click_type: ClickType,
            name: String,
            written_name: Option<String>,
        },
        BuildRangeAll {
            start: ContractExpression,
            end: ContractExpression,
            item: String,
            written_item: Option<String>,
        },
        BuildRangeAny {
            start: ContractExpression,
            end: ContractExpression,
            item: String,
            written_item: Option<String>,
        },
    }

    let mut frames = vec![Frame::Visit(proposition)];
    let mut expanded = Vec::new();
    while let Some(frame) = frames.pop() {
        match frame {
            Frame::Visit(proposition) => match proposition {
                ClickProposition::And(left, right) => {
                    frames.push(Frame::BuildAnd);
                    frames.push(Frame::Visit(*right));
                    frames.push(Frame::Visit(*left));
                }
                ClickProposition::Or(left, right) => {
                    frames.push(Frame::BuildOr);
                    frames.push(Frame::Visit(*right));
                    frames.push(Frame::Visit(*left));
                }
                ClickProposition::Implies(left, right) => {
                    frames.push(Frame::BuildImplies);
                    frames.push(Frame::Visit(*right));
                    frames.push(Frame::Visit(*left));
                }
                ClickProposition::Not(body) => {
                    frames.push(Frame::BuildNot);
                    frames.push(Frame::Visit(*body));
                }
                ClickProposition::At {
                    selector,
                    proposition,
                } => {
                    frames.push(Frame::BuildAt(selector));
                    frames.push(Frame::Visit(*proposition));
                }
                ClickProposition::ForAll {
                    click_type,
                    name,
                    written_name,
                    body,
                } => {
                    frames.push(Frame::BuildForAll {
                        click_type,
                        name,
                        written_name,
                    });
                    frames.push(Frame::Visit(*body));
                }
                ClickProposition::Exists {
                    click_type,
                    name,
                    written_name,
                    body,
                } => {
                    frames.push(Frame::BuildExists {
                        click_type,
                        name,
                        written_name,
                    });
                    frames.push(Frame::Visit(*body));
                }
                ClickProposition::RangeAll {
                    start,
                    end,
                    item,
                    written_item,
                    body,
                } => {
                    frames.push(Frame::BuildRangeAll {
                        start: expand_declared_resource_expression(start, resource_definitions)?,
                        end: expand_declared_resource_expression(end, resource_definitions)?,
                        item,
                        written_item,
                    });
                    frames.push(Frame::Visit(*body));
                }
                ClickProposition::RangeAny {
                    start,
                    end,
                    item,
                    written_item,
                    body,
                } => {
                    frames.push(Frame::BuildRangeAny {
                        start: expand_declared_resource_expression(start, resource_definitions)?,
                        end: expand_declared_resource_expression(end, resource_definitions)?,
                        item,
                        written_item,
                    });
                    frames.push(Frame::Visit(*body));
                }
                proposition => expanded.push(expand_declared_resource_proposition_one(
                    proposition,
                    resource_definitions,
                )?),
            },
            Frame::BuildAnd => {
                let right = expanded.pop().expect("expanded conjunction right operand");
                let left = expanded.pop().expect("expanded conjunction left operand");
                expanded.push(ClickProposition::And(Box::new(left), Box::new(right)));
            }
            Frame::BuildOr => {
                let right = expanded.pop().expect("expanded disjunction right operand");
                let left = expanded.pop().expect("expanded disjunction left operand");
                expanded.push(ClickProposition::Or(Box::new(left), Box::new(right)));
            }
            Frame::BuildImplies => {
                let right = expanded.pop().expect("expanded implication right operand");
                let left = expanded.pop().expect("expanded implication left operand");
                expanded.push(ClickProposition::Implies(Box::new(left), Box::new(right)));
            }
            Frame::BuildNot => {
                let body = expanded.pop().expect("expanded negation body");
                expanded.push(ClickProposition::Not(Box::new(body)));
            }
            Frame::BuildAt(selector) => {
                let proposition = expanded.pop().expect("expanded snapshot proposition");
                expanded.push(ClickProposition::At {
                    selector,
                    proposition: Box::new(proposition),
                });
            }
            Frame::BuildForAll {
                click_type,
                name,
                written_name,
            } => {
                let body = expanded.pop().expect("expanded universal body");
                expanded.push(ClickProposition::ForAll {
                    click_type,
                    name,
                    written_name,
                    body: Box::new(body),
                });
            }
            Frame::BuildExists {
                click_type,
                name,
                written_name,
            } => {
                let body = expanded.pop().expect("expanded existential body");
                expanded.push(ClickProposition::Exists {
                    click_type,
                    name,
                    written_name,
                    body: Box::new(body),
                });
            }
            Frame::BuildRangeAll {
                start,
                end,
                item,
                written_item,
            } => {
                let body = expanded.pop().expect("expanded range universal body");
                expanded.push(ClickProposition::RangeAll {
                    start,
                    end,
                    item,
                    written_item,
                    body: Box::new(body),
                });
            }
            Frame::BuildRangeAny {
                start,
                end,
                item,
                written_item,
            } => {
                let body = expanded.pop().expect("expanded range existential body");
                expanded.push(ClickProposition::RangeAny {
                    start,
                    end,
                    item,
                    written_item,
                    body: Box::new(body),
                });
            }
        }
    }
    Ok(expanded
        .pop()
        .expect("expanded proposition should have one root"))
}

fn expand_declared_resource_proposition_one(
    proposition: ClickProposition,
    resource_definitions: &DeclaredResourceScope,
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
        ClickProposition::ForAll {
            click_type: c_type,
            name,
            written_name,
            body,
        } => Ok(ClickProposition::ForAll {
            click_type: c_type,
            name,
            written_name,
            body: Box::new(expand_declared_resource_proposition(
                *body,
                resource_definitions,
            )?),
        }),
        ClickProposition::Exists {
            click_type: c_type,
            name,
            written_name,
            body,
        } => Ok(ClickProposition::Exists {
            click_type: c_type,
            name,
            written_name,
            body: Box::new(expand_declared_resource_proposition(
                *body,
                resource_definitions,
            )?),
        }),
        ClickProposition::RangeAll {
            start,
            end,
            item,
            written_item,
            body,
        } => Ok(ClickProposition::RangeAll {
            start: expand_declared_resource_expression(start, resource_definitions)?,
            end: expand_declared_resource_expression(end, resource_definitions)?,
            item,
            written_item,
            body: Box::new(expand_declared_resource_proposition(
                *body,
                resource_definitions,
            )?),
        }),
        ClickProposition::RangeAny {
            start,
            end,
            item,
            written_item,
            body,
        } => Ok(ClickProposition::RangeAny {
            start: expand_declared_resource_expression(start, resource_definitions)?,
            end: expand_declared_resource_expression(end, resource_definitions)?,
            item,
            written_item,
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
    resource_definitions: &DeclaredResourceScope,
) -> Result<ContractExpression, ClickError> {
    let mut add_depth = 0;
    let mut add_cursor = &expression;
    while let ContractExpression::Add(left, _) = add_cursor {
        add_depth += 1;
        add_cursor = left;
    }
    if add_depth > 0 {
        let mut operands = Vec::with_capacity(add_depth);
        let mut current = expression;
        while let ContractExpression::Add(left, right) = current {
            operands.push(*right);
            current = *left;
        }
        let mut expanded = expand_declared_resource_expression(current, resource_definitions)?;
        for operand in operands.into_iter().rev() {
            expanded = ContractExpression::Add(
                Box::new(expanded),
                Box::new(expand_declared_resource_expression(
                    operand,
                    resource_definitions,
                )?),
            );
        }
        return Ok(expanded);
    }
    // Peel a direct conditional chain before entering the large child match.
    // Conditions and sibling branches retain their source order while the
    // recursively nested `then` spine is rebuilt from the inside out.
    let mut conditionals = Vec::new();
    let mut expression = expression;
    while let ContractExpression::If {
        condition,
        then_branch,
        else_branch,
    } = expression
    {
        conditionals.push((
            expand_declared_resource_proposition(*condition, resource_definitions)?,
            expand_declared_resource_expression(*else_branch, resource_definitions)?,
        ));
        expression = *then_branch;
    }

    // Let chains are common in generated specifications and can be much
    // deeper than the surrounding expression tree. Peel consecutive lets
    // iteratively so expanding their bodies does not retain one large match
    // frame per binding.
    let mut lets = Vec::new();
    while let ContractExpression::Let {
        name,
        click_type,
        value,
        body,
    } = expression
    {
        lets.push((
            name,
            click_type,
            expand_declared_resource_expression(*value, resource_definitions)?,
        ));
        expression = *body;
    }
    let mut expanded = expand_declared_resource_expression_node(expression, resource_definitions)?;
    while let Some((name, click_type, value)) = lets.pop() {
        expanded = ContractExpression::Let {
            name,
            click_type,
            value: Box::new(value),
            body: Box::new(expanded),
        };
    }
    while let Some((condition, else_branch)) = conditionals.pop() {
        expanded = ContractExpression::If {
            condition: Box::new(condition),
            then_branch: Box::new(expanded),
            else_branch: Box::new(else_branch),
        };
    }
    Ok(expanded)
}

fn expand_declared_resource_expression_node(
    expression: ContractExpression,
    resource_definitions: &DeclaredResourceScope,
) -> Result<ContractExpression, ClickError> {
    match expression {
        ContractExpression::ResourceField(mut access) => {
            if resource_definitions
                .field_binders
                .borrow()
                .contains(&access.identity)
            {
                return Err(ClickError::new(format!(
                    "`{}` names the value of a resource field, not a resource instance",
                    access.owner
                )));
            }
            if let Some(name) = resource_definitions.children.borrow().get(&access.identity) {
                access.resource_name.clone_from(name);
            }
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
            Ok(ContractExpression::ResourceField(access))
        }
        ContractExpression::ResourceCount(resource) => {
            reject_counted_field_resource(&resource, resource_definitions)?;
            let resource = expand_declared_resource_clause(*resource, resource_definitions)?;
            Ok(ContractExpression::ResourceCount(Box::new(resource)))
        }
        expression @ (ContractExpression::SequenceConcat(..)
        | ContractExpression::Add(..)
        | ContractExpression::Subtract(..)
        | ContractExpression::Multiply(..)
        | ContractExpression::Divide(..)
        | ContractExpression::Remainder(..)
        | ContractExpression::ShiftLeft(..)
        | ContractExpression::ShiftRight(..)
        | ContractExpression::BitwiseAnd(..)
        | ContractExpression::BitwiseOr(..)
        | ContractExpression::BitwiseXor(..)
        | ContractExpression::Index(..)) => {
            expand_declared_resource_binary_expression(expression, resource_definitions)
        }
        expression => {
            expand_declared_resource_expression_children(expression, resource_definitions)
        }
    }
}

// Keep the recursive expression walk's large child-rewriting match out of the
// frame retained by each nested expression.
#[inline(never)]
fn expand_declared_resource_binary_expression(
    expression: ContractExpression,
    resource_definitions: &DeclaredResourceScope,
) -> Result<ContractExpression, ClickError> {
    let recurse =
        |expression| expand_declared_resource_expression(expression, resource_definitions);
    Ok(match expression {
        ContractExpression::SequenceConcat(left, right) => ContractExpression::SequenceConcat(
            Box::new(recurse(*left)?),
            Box::new(recurse(*right)?),
        ),
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
        ContractExpression::Index(base, index) => {
            ContractExpression::Index(Box::new(recurse(*base)?), Box::new(recurse(*index)?))
        }
        _ => unreachable!("non-binary contract expression"),
    })
}

// Keep the remaining recursive expression cases out of the frame retained by
// each nested expression.
#[inline(never)]
fn expand_declared_resource_expression_children(
    expression: ContractExpression,
    resource_definitions: &DeclaredResourceScope,
) -> Result<ContractExpression, ClickError> {
    let recurse =
        |expression| expand_declared_resource_expression(expression, resource_definitions);
    Ok(match expression {
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
        ContractExpression::Field {
            base,
            field,
            lowered,
            offset_bytes,
        } => ContractExpression::Field {
            base: Box::new(recurse(*base)?),
            field,
            lowered,
            offset_bytes,
        },
        ContractExpression::Old(body) => ContractExpression::Old(Box::new(recurse(*body)?)),
        ContractExpression::At {
            selector,
            expression,
        } => ContractExpression::At {
            selector,
            expression: Box::new(recurse(*expression)?),
        },
        ContractExpression::BitwiseNot(body) => {
            ContractExpression::BitwiseNot(Box::new(recurse(*body)?))
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
    resource_definitions: &DeclaredResourceScope,
) -> Result<DeclaredResourceInfo, ClickError> {
    declared_resource_info_with_fields(name, actual, resource_definitions, false)
}

fn declared_resource_info_with_fields(
    name: &str,
    actual: usize,
    resource_definitions: &DeclaredResourceScope,
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
    definitions: &DeclaredResourceScope,
) -> Result<(), ClickError> {
    match resource {
        ResourceClause::Declared { name, .. } if name == "mutex_live" => Err(ClickError::new(
            "`mutex_live` is exclusive and not countable",
        )),
        ResourceClause::Declared { name, .. } if name == "mutex_guard" => Err(ClickError::new(
            "`mutex_guard` is exclusive and not countable",
        )),
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
    definitions.extend(
        file.theorem_definitions()
            .iter()
            .map(clone_theorem_definition_iteratively),
    );
    Ok(definitions)
}

/// The standard library's theorem definitions in declaration order.
///
/// A verification uses these as dependency declarations; it does not re-prove
/// them. [`crate::surface::verify_standard_library`] is the one entry point that
/// proves them.
pub(in crate::surface) fn standard_library_theorem_definitions()
-> Result<&'static [TheoremDefinition], ClickError> {
    Ok(standard_library()?.theorem_definitions())
}

/// The declaration-order position of the named standard-library theorem.
pub(in crate::surface) fn standard_library_theorem_index(name: &str) -> Option<usize> {
    static INDEX: std::sync::OnceLock<BTreeMap<String, usize>> = std::sync::OnceLock::new();
    INDEX
        .get_or_init(|| {
            standard_library_theorem_definitions()
                .unwrap_or_default()
                .iter()
                .enumerate()
                .map(|(index, theorem)| (theorem.name().to_string(), index))
                .collect()
        })
        .get(name)
        .copied()
}
