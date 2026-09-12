//! Lexically scoped constructor elimination on unchanged execution frontiers.

use super::*;
use crate::kernel::proof::CheckedProofCasePartition;
use crate::kernel::{AlgebraicTermNode, AlgebraicValue, Term};

pub(in crate::surface::proof) struct ExecutionMatchPlan {
    partition: Arc<CheckedProofCasePartition>,
    source: ProofMatch,
    case_indices: Vec<usize>,
    bindings: Vec<PersistentMap<String, ContractExpression>>,
    integer_bindings: Vec<PersistentMap<String, crate::kernel::SpecIntegerExpression>>,
    parent_locals: ProofLocals,
    deferred_base: PersistentSequence<DeferredPostExecutionTactic>,
    excluded: Vec<Option<ProofCertificate>>,
    entry_cases: PersistentSequence<CaseAssumption>,
}

impl ExecutionMatchPlan {
    pub(in crate::surface::proof) fn excluded_certificate(
        &self,
        index: usize,
    ) -> Option<&ProofCertificate> {
        self.excluded[index].as_ref()
    }
    /// The arms this match still has to execute: every constructor whose arm
    /// was not closed by a checked `contradiction`.
    pub(in crate::surface::proof) fn live_cases(&self) -> Vec<usize> {
        (0..self.excluded.len())
            .filter(|&index| self.excluded[index].is_none())
            .collect()
    }

    /// True when exactly one constructor survives, so its arm runs directly on
    /// the parent frontier and never passes through a terminal join.
    pub(in crate::surface::proof) fn has_sole_live_case(&self) -> bool {
        self.excluded.iter().filter(|case| case.is_none()).count() == 1
    }

    /// The surface condition that names one side of a live-arm split: a match
    /// over the same scrutinee that yields `1` exactly on `left`. Excluded
    /// constructors are already impossible, so they take the `0` side.
    pub(in crate::surface::proof) fn condition(&self, left: &[usize]) -> ClickProposition {
        ClickProposition::Comparison {
            left: ContractExpression::AlgebraicMatch {
                scrutinee: Box::new(self.source.scrutinee.clone()),
                arms: self
                    .source
                    .arms
                    .iter()
                    .enumerate()
                    .map(|(index, arm)| AlgebraicMatchArm {
                        type_name: arm.type_name.clone(),
                        variant: arm.variant.clone(),
                        bindings: arm.bindings.clone(),
                        body: ContractExpression::CFragment(CExpression::Value(CValue::Int32(
                            Bitvector32Term::Constant(u32::from(left.contains(&index))),
                        ))),
                    })
                    .collect(),
            },
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CFragment(CExpression::Value(CValue::Int32(
                Bitvector32Term::Constant(1),
            ))),
        }
    }
}

/// Tags one deferred post-execution tactic, and everything a surface `if` or
/// `branch` nests inside it, with the match arm's binding scope.
///
/// Ordered finalization flattens those arms and applies each selected tactic
/// to the outcome proof, so a tactic written inside a nested arm reaches that
/// proof on its own. Tagging only the outermost entry left every nested
/// tactic without the arm's field bindings.
fn attach_arm_lexical_scope(
    tactic: &mut DeferredPostExecutionTactic,
    scope: &PersistentMap<String, ContractExpression>,
) {
    if tactic.lexical_bindings.is_none() {
        tactic.lexical_bindings = Some(scope.clone());
    }
    if let PostExecutionTactic::If {
        then_tactics,
        else_tactics,
        ..
    } = &mut tactic.tactic
    {
        for nested in then_tactics.iter_mut().chain(else_tactics.iter_mut()) {
            attach_arm_lexical_scope(nested, scope);
        }
    }
}

impl<'a> Proof<'a> {
    pub(in crate::surface::proof) fn begin_execution_match(&self) -> Self {
        Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state: self.state.clone(),
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: None,
                focused_branch: self.focused_branch_id(),
                depth: self.node.depth,
            }),
        }
    }

    pub(in crate::surface::proof) fn execution_match_arm_certificate(
        &self,
        marker: &ProofCheckpoint<'a>,
    ) -> Result<ProofCertificate, ClickError> {
        self.certificate_after_node(Some(&marker.node))
    }
    pub(in crate::surface::proof) fn with_surface_local_scope(
        &self,
        bindings: &PersistentMap<String, ContractExpression>,
    ) -> Self {
        let mut locals = self.state.locals().clone();
        locals.values = bindings.clone();
        self.with_kernel_state(self.state.with_locals(locals))
    }

    pub(in crate::surface::proof) fn plan_execution_match(
        &self,
        source: &ProofMatch,
    ) -> Result<ExecutionMatchPlan, ClickError> {
        let equation = ClickProposition::Comparison {
            left: source.scrutinee.clone(),
            operator: ComparisonOperator::Equal,
            right: source.scrutinee.clone(),
        };
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("proof `match` requires an execution frontier"))?;
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("proof `match` currently requires a C execution proof"));
        };
        let ClickProposition::Comparison {
            left: expression, ..
        } = self.substitute_fixed_state_locals_in_proposition(&equation)?
        else {
            unreachable!()
        };
        let values = parameter_values(context.parsed_function.parameters(), context.arguments)
            .map_err(|error| self.step_error(error.message))?;
        let array_refs = array_refs_for_parameters(
            context.parsed_function.parameters(),
            &values,
            execution.core.state.memory(),
        );
        let value = capture_fixed_state_algebraic_value(
            &expression,
            self.facts().assumptions(),
            &values,
            &array_refs,
            context.old_reference_state(&execution.core.frontier, &execution.core.state),
            &execution.core.state,
            &execution.presentation.recorded_snapshots,
            context.predicate_environment,
            context.click_function_environment,
        )
        .map_err(|message| {
            self.step_error(format!("could not lower match scrutinee: {message}"))
        })?;
        let variants = &value.algebraic_type.variants;
        if source.arms.len() != variants.len() {
            return Err(self.step_error("proof `match` must cover every constructor exactly once"));
        }
        let indices: BTreeMap<_, _> = variants
            .iter()
            .enumerate()
            .map(|(index, variant)| (variant.name.as_str(), index))
            .collect();
        let mut seen = BTreeSet::new();
        let mut case_indices = Vec::with_capacity(source.arms.len());
        for arm in &source.arms {
            let Some(&index) = indices.get(arm.variant.as_str()) else {
                return Err(self.step_error(format!(
                    "unknown match constructor `{}::{}`",
                    arm.type_name, arm.variant
                )));
            };
            if arm.type_name != value.algebraic_type.name || !seen.insert(index) {
                return Err(
                    self.step_error("proof `match` has a duplicate constructor or wrong datatype")
                );
            }
            if arm.bindings.len() != variants[index].fields.len() {
                return Err(self.step_error(format!(
                    "match constructor `{}` has the wrong number of field bindings",
                    arm.variant
                )));
            }
            let mut names = BTreeSet::new();
            for name in &arm.bindings {
                if name == "result"
                    || !names.insert(name)
                    || self.state.locals().values.contains_key(name)
                    || execution.core.state.locals().contains_name(name)
                {
                    return Err(
                        self.step_error(format!("match binding `{name}` is already in scope"))
                    );
                }
            }
            case_indices.push(index);
        }
        // AlgebraicVariable's existing lowering assigns one aligned namespace
        // slot per binder. The kernel, not this spelling, checks freshness.
        let first = self.state.locals().next_choice_variable.max(4_000_000);
        let first = 4_000_000 + (first - 4_000_000).div_ceil(65_536) * 65_536;
        let (partition, _, next) = execution.core.algebraic_case_partition(
            self.facts(), &value, context.function_environment, first, 65_536,
        ).ok_or_else(|| self.step_error("proof `match` requires a supported ADT at unchanged function entry, before C execution or resource unfolding"))?;
        let mut bindings = Vec::with_capacity(source.arms.len());
        let mut integer_bindings = Vec::with_capacity(source.arms.len());
        for (arm, &index) in source.arms.iter().zip(&case_indices) {
            let Some(Proposition::Equal(_, Term::Algebraic(constructor))) =
                partition.case_fact(index)
            else {
                unreachable!()
            };
            let AlgebraicTermNode::Constructor { fields, .. } = &constructor.node else {
                unreachable!()
            };
            let mut scope = self.state.locals().values.clone();
            let mut integer_scope = self.state.locals().integer_values.clone();
            for (name, field) in arm.bindings.iter().zip(fields) {
                let expression = match field {
                    AlgebraicValue::C(value) => {
                        ContractExpression::CFragment(CExpression::Value(value.clone()))
                    }
                    AlgebraicValue::Algebraic(value) => {
                        let AlgebraicTermNode::Variable(variable) = value.node else {
                            unreachable!()
                        };
                        ContractExpression::AlgebraicVariable {
                            name: name.clone(), binder_index: ((variable.0 - 4_000_000) / 65_536) as usize,
                            algebraic_type: AlgebraicTypeApplication {
                                rigid: value.algebraic_type.rigid, name: value.algebraic_type.name.clone(),
                                arguments: value.algebraic_type.arguments.iter().map(super::super::pure_theorems::click_type_from_algebraic_value_type).collect::<Result<_,_>>()?,
                            },
                        }
                    }
                    AlgebraicValue::Integer(value) => {
                        integer_scope = integer_scope.with_inserted(
                            name.clone(),
                            crate::kernel::SpecIntegerExpression::Term(value.clone()),
                        );
                        ContractExpression::Binding(name.clone())
                    }
                };
                scope = scope.with_inserted(name.clone(), expression);
            }
            bindings.push(scope);
            integer_bindings.push(integer_scope);
        }
        let mut parent_locals = self.state.locals().clone();
        parent_locals.next_choice_variable = next;
        let mut plan = ExecutionMatchPlan {
            partition,
            source: source.clone(),
            case_indices,
            bindings,
            integer_bindings,
            parent_locals,
            deferred_base: execution.presentation.post_execution_tactics.clone(),
            excluded: vec![None; source.arms.len()],
            entry_cases: execution.presentation.case_assumptions.clone(),
        };
        for (index, arm) in source.arms.iter().enumerate() {
            if let [ProofTactic::Contradiction(surface)] = arm.tactics.as_slice() {
                let scoped = self.enter_execution_match_arm(&plan, index)?;
                let fact =
                    scoped.lower_surface_proposition(surface, "constructor-arm contradiction")?;
                plan.partition = plan.partition.excluding_constructor_case(plan.case_indices[index], fact)
                    .ok_or_else(|| self.step_error("constructor-arm `contradiction` requires an exact fact and its negation in that arm"))?;
                plan.excluded[index] = Some(ProofCertificate::from_steps(vec![
                    ProofStep::Contradiction(surface.clone()),
                ])?);
            }
        }
        if plan.excluded.iter().all(Option::is_some) {
            return Err(
                self.step_error("proof match with every constructor excluded is not yet supported")
            );
        }
        Ok(plan)
    }

    pub(in crate::surface::proof) fn enter_execution_match_arm(
        &self,
        plan: &ExecutionMatchPlan,
        index: usize,
    ) -> Result<Self, ClickError> {
        let state = self
            .state
            .introduce_frontier_match_case(plan.partition.clone(), plan.case_indices[index])
            .map_err(|message| self.step_error(message))?;
        let mut locals = plan.parent_locals.clone();
        locals.values = plan.bindings[index].clone();
        locals.integer_values = plan.integer_bindings[index].clone();
        let arm = &plan.source.arms[index];
        let Some(Proposition::Equal(_, Term::Algebraic(constructor))) =
            plan.partition.case_fact(plan.case_indices[index])
        else {
            unreachable!()
        };
        let surface = ClickProposition::Comparison {
            left: plan.source.scrutinee.clone(),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::AlgebraicConstructor {
                algebraic_type: AlgebraicTypeApplication {
                    rigid: false,
                    name: constructor.algebraic_type.name.clone(),
                    arguments: constructor
                        .algebraic_type
                        .arguments
                        .iter()
                        .map(super::super::pure_theorems::click_type_from_algebraic_value_type)
                        .collect::<Result<_, _>>()?,
                },
                variant: arm.variant.clone(),
                arguments: arm
                    .bindings
                    .iter()
                    .map(|name| plan.bindings[index].get(name).unwrap().clone())
                    .collect(),
            },
        };
        let case = plan
            .partition
            .case_fact(plan.case_indices[index])
            .unwrap()
            .clone();
        let tactic_index = match self.context.as_ref() {
            ProofContext::Execution(context) => context.tactic_index,
            _ => unreachable!(),
        };
        let proof = self.with_kernel_state(state.with_locals(locals));
        let (proof, result) = proof.edit_execution_presentation(|presentation| {
            presentation
                .surface_propositions
                .record_lowering(&surface, &case)?;
            presentation.case_assumptions.push(CaseAssumption {
                tactic_index,
                condition: surface,
                value: true,
                fact: Some(case),
                at_function_entry: true,
            });
            Ok::<_, ClickError>(())
        })?;
        result?;
        Ok(proof)
    }

    pub(in crate::surface::proof) fn leave_execution_match_arm(
        &self,
        plan: &ExecutionMatchPlan,
    ) -> Result<Self, ClickError> {
        let scope = self.state.locals().values.clone();
        let (proof, result) = self.clone().edit_execution_presentation(|presentation| {
            let suffix = presentation
                .post_execution_tactics
                .suffix_since(&plan.deferred_base)
                .ok_or("match arm lost its deferred-tactic prefix")?;
            let mut deferred = plan.deferred_base.clone();
            for mut tactic in suffix {
                attach_arm_lexical_scope(&mut tactic, &scope);
                deferred.push(tactic);
            }
            presentation.post_execution_tactics = deferred;
            Ok::<_, &'static str>(())
        })?;
        result.map_err(|message| self.step_error(message))?;
        let mut locals = plan.parent_locals.clone();
        locals.next_choice_variable = locals
            .next_choice_variable
            .max(self.state.locals().next_choice_variable);
        let proof = if plan.has_sole_live_case() {
            // A sole live arm runs on the parent frontier, so unlike any
            // joined arm it never passed through merge_terminal_execution_join.
            // Restore the same outer routing scope here: case evidence is
            // retained in the trace, not added to the whole function's
            // contract requirements.
            proof
                .edit_execution_presentation(|presentation| {
                    presentation.case_assumptions = plan.entry_cases.clone();
                })?
                .0
        } else {
            proof
        };
        Ok(proof.with_kernel_state(proof.state.with_locals(locals)))
    }

    pub(in crate::surface::proof) fn finish_execution_match(
        &self,
        marker: &ProofCheckpoint<'a>,
        source: &ProofMatch,
        proofs: Vec<ProofCertificate>,
    ) -> Result<Self, ClickError> {
        if self.focused_branch_id() != marker.node.focused_branch
            || proofs.len() != source.arms.len()
        {
            return Err(
                self.step_error("match did not rejoin its exact parent and constructor family")
            );
        }
        let arms = source
            .arms
            .iter()
            .zip(proofs)
            .map(|(arm, proof)| CertificateInductionArm {
                type_name: arm.type_name.clone(),
                variant: arm.variant.clone(),
                bindings: arm.bindings.clone(),
                proof: Box::new(proof),
            })
            .collect();
        Ok(Self {
            site: self.site.clone(),
            context: marker.context.clone(),
            state: self.state.clone(),
            node: Arc::new(ProofNode {
                parent: Some(marker.node.clone()),
                focused_branch: self.focused_branch_id(),
                depth: marker.node.depth + 1,
                step: Some(Arc::new(ProofStep::Match {
                    scrutinee: source.scrutinee.clone(),
                    arms,
                })),
            }),
        })
    }

    pub(in crate::surface::proof) fn split_execution_match_group(
        &self,
        condition: ClickProposition,
    ) -> Result<(Self, ExecutionProofCaseSplit<'a>), ClickError> {
        let branch = self
            .focused_branch()
            .ok_or_else(|| self.step_error("match requires an open frontier"))?;
        let execution = branch
            .state
            .execution
            .clone()
            .ok_or_else(|| self.step_error("match requires execution state"))?;
        let (state, split, ids, path_facts) = self
            .state
            .split_frontier_match_group()
            .map_err(|_| self.step_error("match requires an execution frontier"))?
            .into_parts_with_facts();
        let successor = Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: None,
                focused_branch: self.focused_branch_id(),
                depth: self.node.depth,
            }),
        };
        let record = ExecutionProofCaseSplit {
            marker: successor.checkpoint(),
            split,
            arm_branches: ids,
            surface_condition: condition,
            base_facts: [branch.state.facts.clone(), branch.state.facts.clone()],
            base_executions: [execution.clone(), execution.clone()],
            path_facts,
            common_facts: branch.state.facts.clone(),
            parent_unfolds: branch.state.unfolded_predicates.clone(),
            execution_start_state: execution
                .core
                .frontier
                .execution_start_state(&execution.core.state)
                .clone(),
            parent_execution: execution,
        };
        Ok((successor, record))
    }
}
