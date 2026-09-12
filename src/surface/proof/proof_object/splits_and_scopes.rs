//! Logical/execution/outcome splits, joins, and `have`/`open` scopes.

use super::*;
use crate::surface::planning::proposition_search::PropositionSearch;

pub(in crate::surface::proof) struct CheckedBothSurfaceChild {
    surface: Option<ClickProposition>,
    introductions: Option<crate::kernel::LoweringIntroductions>,
}

impl<'a> Proof<'a> {
    fn recorded_surface_matches(&self, surface: &ClickProposition, target: &Proposition) -> bool {
        let matches = |map: &SurfacePropositionMap| {
            map.available_kernel_matching(surface, |kernel| {
                crate::kernel::proof::propositions_are_alpha_equal(kernel, target)
            })
            .is_some()
        };
        match self.context.as_ref() {
            ProofContext::Pure(context) => matches(&context.theorem_context.surface_requirements),
            ProofContext::FixedState(context) => matches(context.surface_propositions),
            ProofContext::Execution(_) => self
                .execution()
                .is_some_and(|execution| matches(&execution.presentation.surface_propositions)),
        }
    }

    /// Recovers a written body when the kernel obligation has a checked
    /// lowering guard in front of it. The generated display can re-lower a
    /// snapshot expression at the current state, so its wrapper's consequent
    /// is not itself evidence. The obligation's recorded head chain proves
    /// the wrapper, while invariant-body assembly supplies the one declared
    /// Surface body whose lowering is exactly the guarded consequent.
    fn recorded_guard_surface_child(
        &self,
        surface: &ClickProposition,
        target: &Proposition,
        recorded: &BothChildPresentation,
    ) -> Option<CheckedBothSurfaceChild> {
        if !crate::kernel::proof::propositions_are_alpha_equal(&recorded.kernel, target) {
            return None;
        }
        let mut cursor = target;
        let mut antecedent = None;
        for introduction in recorded.introductions.iter() {
            match introduction {
                crate::kernel::LoweringIntroduction::PathFactGuard
                | crate::kernel::LoweringIntroduction::ObligationGuard => {
                    let Proposition::Implies(left, body) = cursor else {
                        return None;
                    };
                    antecedent.get_or_insert(left.as_ref());
                    cursor = body;
                }
                // This adapter is specifically for a lowering-inserted
                // wrapper. A written connective must be handled by the
                // ordinary Surface structural presentation instead.
                crate::kernel::LoweringIntroduction::WrittenImplication
                | crate::kernel::LoweringIntroduction::WrittenNegation
                | crate::kernel::LoweringIntroduction::WrittenUniversal { .. } => return None,
            }
        }
        let antecedent = antecedent?;

        match surface {
            ClickProposition::Implies(surface_antecedent, _) => {
                let lowered = self
                    .lower_surface_proposition(surface_antecedent, "`both` guard antecedent")
                    .ok()?;
                if !crate::kernel::proof::propositions_are_alpha_equal(&lowered, antecedent) {
                    return None;
                }
            }
            _ => {
                let lowered = self
                    .lower_surface_proposition(surface, "`both` guarded body")
                    .ok()?;
                if !crate::kernel::proof::propositions_are_alpha_equal(&lowered, cursor) {
                    return None;
                }
            }
        }

        let candidate = recorded.surface.as_ref()?.clone();
        let lowered = self
            .lower_surface_proposition(&candidate, "`both` recorded guarded body")
            .ok()?;
        if !crate::kernel::proof::propositions_are_alpha_equal(&lowered, cursor) {
            return None;
        }
        Some(CheckedBothSurfaceChild {
            surface: Some(candidate),
            introductions: Some(recorded.introductions.iter().cloned().collect()),
        })
    }

    /// Computes the Surface spellings that may travel across a checked
    /// `both` split.  Lowering can insert a conjunct (notably an existential
    /// witness guard), so the written proposition is not necessarily shaped
    /// like the kernel conjunction.  A child is retained only when its
    /// candidate lowers alpha-equivalently to that actual kernel child.
    ///
    /// This is deliberately output-sized: there are at most two candidates
    /// and two kernel children.  It never searches ambient facts or treats a
    /// conjunct as a guard merely because it looks like one.
    pub(in crate::surface::proof) fn checked_both_surface_children(
        &self,
    ) -> Result<[CheckedBothSurfaceChild; 2], ClickError> {
        let Some(surface) = self.surface_goal() else {
            return Ok([
                CheckedBothSurfaceChild {
                    surface: None,
                    introductions: None,
                },
                CheckedBothSurfaceChild {
                    surface: None,
                    introductions: None,
                },
            ]);
        };
        let Some(Proposition::And(left, right)) = self.goal() else {
            return Err(
                self.step_error("`both` presentation correspondence requires a kernel conjunction")
            );
        };
        let witness_refinement_kernel = self
            .proposition_obligation()
            .and_then(|goal| goal.presentation.witness_refinement_kernel.as_ref());
        let kernel_children = [left.as_ref(), right.as_ref()];
        if let Some((surface_left, surface_right)) = surface_logical_children(surface, true) {
            // A written conjunction has ordered Surface children.  Preserve
            // that order even when the children are alpha-equal (and reject
            // a reversal), rather than treating it as an unordered match.
            let mut children = [None, None];
            let mut lowered_children = [None, None];
            for (index, candidate) in [&surface_left, &surface_right].into_iter().enumerate() {
                let Ok(lowered) =
                    self.lower_surface_proposition(candidate, "`both` presentation child")
                else {
                    continue;
                };
                lowered_children[index] = Some(lowered.clone());
                if !crate::kernel::proof::propositions_are_alpha_equal(
                    &lowered,
                    kernel_children[index],
                ) {
                    continue;
                }
                children[index] = Some(candidate.clone());
            }
            if children.iter().all(Option::is_some) {
                return Ok(children.map(|surface| CheckedBothSurfaceChild {
                    surface,
                    introductions: None,
                }));
            }
            // A fully lowerable reversal is a definite correspondence error;
            // do not let a set-like fallback silently swap written children.
            if lowered_children.iter().all(Option::is_some)
                && crate::kernel::proof::propositions_are_alpha_equal(
                    lowered_children[0].as_ref().unwrap(),
                    kernel_children[1],
                )
                && crate::kernel::proof::propositions_are_alpha_equal(
                    lowered_children[1].as_ref().unwrap(),
                    kernel_children[0],
                )
            {
                return Err(self.step_error(
                    "`both` cannot preserve its written conjunction: child order does not match",
                ));
            }
            if let Some(records) = self
                .proposition_obligation()
                .and_then(|goal| goal.presentation.both_children.as_deref())
            {
                let mut checked = [
                    children[0].clone().map(|surface| CheckedBothSurfaceChild {
                        surface: Some(surface),
                        introductions: None,
                    }),
                    children[1].clone().map(|surface| CheckedBothSurfaceChild {
                        surface: Some(surface),
                        introductions: None,
                    }),
                ];
                for index in 0..2 {
                    if checked[index].is_none() {
                        let surface_child = if index == 0 {
                            &surface_left
                        } else {
                            &surface_right
                        };
                        checked[index] = self.recorded_guard_surface_child(
                            surface_child,
                            kernel_children[index],
                            &records[index],
                        );
                    }
                }
                if checked.iter().all(|child| child.is_some()) {
                    return Ok(checked.map(Option::unwrap));
                }
            }
            if let Ok(children) = self.checked_whole_surface_child(surface, kernel_children) {
                return Ok(children.map(|surface| CheckedBothSurfaceChild {
                    surface,
                    introductions: None,
                }));
            }
            if witness_refinement_kernel.is_some_and(|recorded| {
                crate::kernel::proof::propositions_are_alpha_equal(
                    recorded,
                    &Proposition::And(
                        Box::new(kernel_children[0].clone()),
                        Box::new(kernel_children[1].clone()),
                    ),
                )
            }) {
                return Ok([
                    CheckedBothSurfaceChild {
                        surface: None,
                        introductions: None,
                    },
                    CheckedBothSurfaceChild {
                        surface: None,
                        introductions: None,
                    },
                ]);
            }
            return Err(self.step_error(
                "`both` cannot preserve its written conjunction: no checked child correspondence",
            ));
        }

        // A non-conjunct written body can be the semantic child of a
        // lowering-inserted guard.  It must match exactly one child: duplicate
        // kernel children are intentionally rejected as ambiguous.
        let Ok(lowered) = self.lower_surface_proposition(surface, "`both` presentation child")
        else {
            let parent = Proposition::And(
                Box::new(kernel_children[0].clone()),
                Box::new(kernel_children[1].clone()),
            );
            if self.recorded_surface_matches(surface, &parent) {
                return Ok([
                    CheckedBothSurfaceChild {
                        surface: None,
                        introductions: None,
                    },
                    CheckedBothSurfaceChild {
                        surface: None,
                        introductions: None,
                    },
                ]);
            }
            if witness_refinement_kernel.is_some_and(|recorded| {
                crate::kernel::proof::propositions_are_alpha_equal(
                    recorded,
                    &Proposition::And(
                        Box::new(kernel_children[0].clone()),
                        Box::new(kernel_children[1].clone()),
                    ),
                )
            }) {
                return Ok([
                    CheckedBothSurfaceChild {
                        surface: None,
                        introductions: None,
                    },
                    CheckedBothSurfaceChild {
                        surface: None,
                        introductions: None,
                    },
                ]);
            }
            return Err(self.step_error(
                "`both` cannot preserve its written goal: the candidate did not lower",
            ));
        };
        let matches = kernel_children
            .iter()
            .enumerate()
            .filter(|(_, child)| {
                crate::kernel::proof::propositions_are_alpha_equal(&lowered, child)
            })
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        if matches.len() != 1 {
            if crate::kernel::proof::propositions_are_alpha_equal(
                &lowered,
                &Proposition::And(
                    Box::new(kernel_children[0].clone()),
                    Box::new(kernel_children[1].clone()),
                ),
            ) {
                // The written proposition accounts for the complete
                // conjunction, not either child.  The checked split still
                // proves both kernel obligations; no child spelling can be
                // installed without changing the written claim.
                return Ok([
                    CheckedBothSurfaceChild {
                        surface: None,
                        introductions: None,
                    },
                    CheckedBothSurfaceChild {
                        surface: None,
                        introductions: None,
                    },
                ]);
            }
            return Err(self.step_error(
                "`both` cannot preserve its written goal: the kernel child correspondence is ambiguous",
            ));
        }
        let mut children = [
            CheckedBothSurfaceChild {
                surface: None,
                introductions: None,
            },
            CheckedBothSurfaceChild {
                surface: None,
                introductions: None,
            },
        ];
        children[matches[0]].surface = Some(surface.clone());
        Ok(children)
    }

    fn checked_whole_surface_child(
        &self,
        surface: &ClickProposition,
        kernel_children: [&Proposition; 2],
    ) -> Result<[Option<ClickProposition>; 2], ClickError> {
        let lowered = match self
            .lower_surface_proposition(surface, "`both` presentation conjunction")
        {
            Ok(lowered) => lowered,
            Err(_) => {
                let parent = Proposition::And(
                    Box::new(kernel_children[0].clone()),
                    Box::new(kernel_children[1].clone()),
                );
                if self.recorded_surface_matches(surface, &parent) {
                    return Ok([None, None]);
                }
                return Err(self.step_error(
                    "`both` cannot preserve its written conjunction: no checked child correspondence",
                ));
            }
        };
        let matches = kernel_children
            .iter()
            .enumerate()
            .filter(|(_, child)| {
                crate::kernel::proof::propositions_are_alpha_equal(&lowered, child)
            })
            .map(|(index, _)| index)
            .collect::<Vec<_>>();
        if matches.len() != 1 {
            return Err(self.step_error(
                "`both` cannot preserve its written conjunction: child order does not match",
            ));
        }
        let mut children = [None, None];
        children[matches[0]] = Some(surface.clone());
        Ok(children)
    }

    pub(in crate::surface::proof) fn apply_both_source(
        &self,
        both: &ProofBoth,
    ) -> Result<Self, ClickError> {
        self.try_authoritative_linear_script(&[ProofTactic::Both(both.clone())])?
            .ok_or_else(|| self.step_error("`both` requires complete proofs of both conjuncts"))
    }

    pub(in crate::surface::proof) fn split_focused_both(
        &self,
    ) -> Result<(Self, SplitId, [BranchId; 2]), ClickError> {
        let surface_children = self.checked_both_surface_children()?;
        let (state, split, ids) = self
            .state
            .split_proposition_both(|parent, left| {
                let mut child = parent.clone();
                let selected = &surface_children[usize::from(!left)];
                child.surface = selected.surface.clone().map(Arc::new);
                child.introductions = selected
                    .introductions
                    .clone()
                    .map_or_else(GoalIntroductions::default, GoalIntroductions::recorded);
                child.both_children = None;
                child
            })
            .map_err(|message| self.step_error(message))?
            .into_parts();
        Ok((
            Self {
                site: self.site.clone(),
                context: self.context.clone(),
                state,
                node: Arc::new(ProofNode {
                    parent: Some(self.node.clone()),
                    step: None,
                    focused_branch: self.focused_branch_id(),
                    depth: self.node.depth,
                }),
            },
            split,
            ids,
        ))
    }

    pub(in crate::surface::proof) fn join_focused_both(
        &self,
        marker: &ProofCheckpoint<'a>,
        split: SplitId,
        ids: [BranchId; 2],
    ) -> Result<Self, ClickError> {
        self.join_focused_branch(marker, split, ids, |left, right| ProofStep::Both {
            left_proof: Box::new(left),
            right_proof: Box::new(right),
        })
    }

    /// Splits the focused branch proposition goal into two labeled sibling case
    /// goals inside this same proof state.
    ///
    /// This is the in-`Proof` form of `cases`: the parent obligation's id is
    /// retired by the split, each arm owns the same claim under its exact
    /// disjunct in its own path-local context, and both siblings coexist in
    /// one goal collection — arms are proven by focusing each recorded id in
    /// turn on one lineage. The split marker node records this split
    /// instance; the join accepts only derivations that pass through it.
    pub(in crate::surface::proof) fn split_focused_cases(
        &self,
        disjunction: ClickProposition,
    ) -> Result<(Self, SplitId, [BranchId; 2]), ClickError> {
        let kernel = self.lower_surface_proposition(&disjunction, "`cases` disjunction")?;
        let (state, split, ids) = self
            .state
            .split_proposition_cases(kernel)
            .map_err(|error| match error {
                PropositionSplitError::Completed => {
                    self.step_error("`cases` follows a completed proof")
                }
                PropositionSplitError::NotProposition => {
                    self.step_error("`cases` requires a proposition goal")
                }
                PropositionSplitError::MissingDisjunction(kernel) => self.step_error(format!(
                    "`cases` requires its exact disjunction as an available fact: {kernel:?}"
                )),
                PropositionSplitError::ExpectedDisjunction(kernel) => {
                    self.step_error(format!("`cases` requires a disjunction, got {kernel:?}"))
                }
                PropositionSplitError::NonComplementaryCases => {
                    unreachable!("cases does not supply complementary branch facts")
                }
            })?
            .into_parts();
        Ok((
            Self {
                site: self.site.clone(),
                context: self.context.clone(),
                state,
                // The marker records the split instance in provenance; its
                // identity is what the join verifies (identity rule 3).
                node: Arc::new(ProofNode {
                    parent: Some(self.node.clone()),
                    step: None,
                    focused_branch: self.focused_branch_id(),
                    depth: self.node.depth,
                }),
            },
            split,
            ids,
        ))
    }

    /// Splits the focused branch proposition goal under a condition and its exact
    /// surface negation inside this same proof state: the in-`Proof` form of
    /// proof `if`. Unlike `cases`, the condition need not be an available
    /// fact beforehand.
    pub(in crate::surface::proof) fn split_focused_if(
        &self,
        condition: ClickProposition,
    ) -> Result<(Self, SplitId, [BranchId; 2]), ClickError> {
        let then_fact = self.lower_surface_proposition(&condition, "proof `if` condition")?;
        let else_surface = ClickProposition::Not(Box::new(condition.clone()));
        let else_fact = self.lower_surface_proposition(&else_surface, "proof `if` negation")?;
        let (state, split, ids) = self
            .state
            .split_proposition_if(then_fact, else_fact)
            .map_err(|error| match error {
                PropositionSplitError::Completed => {
                    self.step_error("`if` follows a completed proof")
                }
                PropositionSplitError::NotProposition => {
                    self.step_error("proof `if` requires a proposition goal")
                }
                PropositionSplitError::NonComplementaryCases => self.step_error(
                    "proof `if` condition and negation did not lower to complementary facts",
                ),
                PropositionSplitError::MissingDisjunction(_)
                | PropositionSplitError::ExpectedDisjunction(_) => {
                    unreachable!("proof if does not require a disjunction")
                }
            })?
            .into_parts();
        Ok((
            Self {
                site: self.site.clone(),
                context: self.context.clone(),
                state,
                node: Arc::new(ProofNode {
                    parent: Some(self.node.clone()),
                    step: None,
                    focused_branch: self.focused_branch_id(),
                    depth: self.node.depth,
                }),
            },
            split,
            ids,
        ))
    }

    /// Splits a proof path condition that exactly names the current C `if`
    /// and applies each arm's leading source step as a checked `Step` on
    /// that focused branch Proof, which decides the C `if` from the assumed case. The returned arms remain
    /// proof cases, so their source scopes may continue through the C join;
    /// only the branch-entry transition is selected here.
    pub(in crate::surface::proof) fn try_split_source_successor_if(
        &self,
        condition: &ClickProposition,
        arm_steps: [(usize, usize); 2],
    ) -> Result<Option<(Self, ExecutionProofCaseSplit<'a>)>, ClickError> {
        let Some(execution) = self.execution() else {
            return Ok(None);
        };
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Ok(None);
        };
        let statement_index = execution.core.frontier.next_statement_index;
        let (_, _, statement, _) = next_top_level_statement_from_frontier_position(
            execution.view(context),
            &execution.core.state,
            context.function,
            context.arguments,
            context.claim_label,
            context.tactic_index,
            "source proof `if`",
        )?;
        let CStatement::If {
            condition: c_condition,
            ..
        } = statement
        else {
            return Ok(None);
        };
        let source_fact = self.lower_surface_proposition(condition, "proof `if` condition")?;
        let c_surface = surface_c_condition(&c_condition);
        let c_fact = self.lower_surface_proposition(&c_surface, "current C `if` condition")?;
        if !path_condition_equivalent(&source_fact, &c_fact) {
            return Ok(None);
        }

        let (split, mut record) = self.split_focused_execution_if(condition.clone())?;
        record.surface_condition = surface_at_snapshot(
            &c_surface,
            &ProgramPointRef {
                region: CodeRegionRef::Statement(statement_index),
                kind: ProgramPointKind::Entry,
            },
        )?;
        let mut advanced = split;
        for (arm_index, take_then) in [(0usize, true), (1usize, false)] {
            let (_, source_index) = arm_steps[arm_index];
            advanced = advanced
                .focus_execution_if_arm(&record, take_then)?
                .apply_step_at(ProofStep::Step, source_index)?;
        }
        Ok(Some((advanced, record)))
    }

    /// Splits one retained execution frontier under an exhaustive proof-level
    /// condition. Both arms share the already-checked C state and receive only
    /// their respective logical polarity; subsequent statement steps remain
    /// independently checked on each sibling.
    pub(in crate::surface::proof) fn split_focused_execution_if(
        &self,
        condition: ClickProposition,
    ) -> Result<(Self, ExecutionProofCaseSplit<'a>), ClickError> {
        let branch_state = &self.focused_branch().expect("focused branch exists").state;
        let parent_execution = branch_state
            .execution
            .clone()
            .expect("an execution frontier owns its checked state");
        let then_fact = self.lower_surface_proposition(&condition, "proof `if` condition")?;
        let else_surface = ClickProposition::Not(Box::new(condition.clone()));
        let else_fact = self.lower_surface_proposition(&else_surface, "proof `if` negation")?;
        let ProofContext::Execution(context) = self.context.as_ref() else {
            unreachable!("an execution frontier has an execution context")
        };
        let at_function_entry = parent_execution.core.frontier.is_at_function_entry();
        let arm_presentation = |surface_fact: ClickProposition, fact: &Proposition, value: bool| {
            let mut presentation = parent_execution.presentation.clone();
            presentation
                .surface_propositions
                .record_lowering(&surface_fact, fact)?;
            presentation.case_assumptions.push(CaseAssumption {
                tactic_index: context.tactic_index,
                condition: condition.clone(),
                value,
                fact: Some(fact.clone()),
                at_function_entry,
            });
            Ok(presentation)
        };
        let presentations = [
            arm_presentation(condition.clone(), &then_fact, true)?,
            arm_presentation(else_surface, &else_fact, false)?,
        ];
        let (state, split, ids, path_facts) = self
            .state
            .split_frontier_if(then_fact, else_fact, presentations)
            .map_err(|error| match error {
                FrontierSplitError::Completed => {
                    self.step_error("proof `if` follows a completed proof")
                }
                FrontierSplitError::NotFrontier => self
                    .step_error("proof `if` cannot advance C execution inside a proposition proof"),
                FrontierSplitError::MissingExecution => {
                    self.step_error("execution-frontier proof lost its semantic state")
                }
                FrontierSplitError::NonComplementaryCases => self.step_error(
                    "proof `if` condition and negation did not lower to complementary facts",
                ),
                #[cfg(test)]
                FrontierSplitError::MissingDisjunction(_)
                | FrontierSplitError::ExpectedDisjunction(_) => {
                    unreachable!("proof if does not require a disjunction")
                }
            })?
            .into_parts_with_facts();
        let then_branch = state
            .open_branches()
            .get(ids[0])
            .expect("the kernel returned its open then branch");
        let else_branch = state
            .open_branches()
            .get(ids[1])
            .expect("the kernel returned its open else branch");
        let then_facts = then_branch.state.facts.clone();
        let else_facts = else_branch.state.facts.clone();
        let then_execution = then_branch
            .state
            .execution
            .clone()
            .expect("a kernel frontier split retains then execution");
        let else_execution = else_branch
            .state
            .execution
            .clone()
            .expect("a kernel frontier split retains else execution");
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
            base_facts: [then_facts, else_facts],
            base_executions: [then_execution, else_execution],
            path_facts,
            common_facts: branch_state.facts.clone(),
            parent_unfolds: branch_state.unfolded_predicates.clone(),
            parent_execution: parent_execution.clone(),
            execution_start_state: parent_execution
                .core
                .frontier
                .execution_start_state(&parent_execution.core.state)
                .clone(),
        };
        Ok((successor, record))
    }

    /// Splits one retained execution frontier under the two exact disjuncts
    /// of an available proposition. The disjunction is checked once at the
    /// split; each sibling receives only its own disjunct in its persistent
    /// fact context, and no semantic state is exported to a construction cursor.
    #[cfg(test)]
    pub(in crate::surface::proof) fn split_focused_execution_cases(
        &self,
        disjunction: ClickProposition,
    ) -> Result<(Self, ExecutionLogicalCasesSplit), ClickError> {
        let lowered = self.lower_surface_proposition(&disjunction, "`cases` disjunction")?;
        let (state, _, ids, path_facts) = self
            .state
            .split_frontier_cases(lowered)
            .map_err(|error| match error {
                FrontierSplitError::Completed => {
                    self.step_error("`cases` follows a completed proof")
                }
                FrontierSplitError::NotFrontier => {
                    self.step_error("`cases` cannot advance C execution inside a proposition proof")
                }
                FrontierSplitError::MissingExecution => {
                    self.step_error("execution-frontier proof lost its semantic state")
                }
                FrontierSplitError::MissingDisjunction(lowered) => self.step_error(format!(
                    "`cases` requires its exact disjunction as an available fact: {lowered:?}"
                )),
                FrontierSplitError::ExpectedDisjunction(lowered) => {
                    self.step_error(format!("`cases` requires a disjunction, got {lowered:?}"))
                }
                FrontierSplitError::NonComplementaryCases => {
                    unreachable!("execution cases does not supply complementary branch facts")
                }
            })?
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
        let record = ExecutionLogicalCasesSplit {
            arm_branches: ids,
            path_facts,
        };
        Ok((successor, record))
    }

    /// Focuses one arm of a logical execution-frontier `cases` split. The
    /// arm's exact disjunct is re-presented only as this focused branch operation's
    /// local fact delta.
    #[cfg(test)]
    pub(in crate::surface::proof) fn focus_execution_cases_arm(
        &self,
        record: &ExecutionLogicalCasesSplit,
        take_left: bool,
    ) -> Result<Self, ClickError> {
        let arm_index = usize::from(!take_left);
        let focused_branch = self.focus_branch(record.arm_branches[arm_index])?;
        let path_facts = record.path_facts[arm_index].clone();
        Ok(focused_branch.with_kernel_state(
            focused_branch
                .state
                .with_fact_deltas(path_facts.clone(), path_facts),
        ))
    }

    /// Applies one recursively driven proof-level execution `if` as an
    /// audited sibling-goal operation. Each callback must retire exactly its
    /// selected arm, either with terminal checked steps or another invocation
    /// of this operation. The returned node retains the structured `If`
    /// provenance directly on this Proof lineage.
    pub(in crate::surface::proof) fn apply_execution_if_with<Then, Else>(
        self,
        condition: ClickProposition,
        apply_then: Then,
        apply_else: Else,
    ) -> Result<Self, ClickError>
    where
        Then: FnOnce(Self) -> Result<Self, ClickError>,
        Else: FnOnce(Self) -> Result<Self, ClickError>,
    {
        let (split, record) = self.split_focused_execution_if(condition.clone())?;
        let then_done = apply_then(split.focus_execution_if_arm(&record, true)?)?;
        let else_done = apply_else(then_done.focus_execution_if_arm(&record, false)?)?;
        if then_done.is_at_function_exit() && else_done.is_at_function_exit() {
            else_done.join_focused_execution_if_terminal(&record)
        } else {
            else_done.join_focused_if(&record.marker, record.split, record.arm_branches, condition)
        }
    }

    /// Joins a completed in-`Proof` `if` split with one structured `If`
    /// step, under the same rules as [`Self::join_focused_cases`].
    pub(in crate::surface::proof) fn join_focused_if(
        &self,
        marker: &ProofCheckpoint<'a>,
        split: SplitId,
        ids: [BranchId; 2],
        condition: ClickProposition,
    ) -> Result<Self, ClickError> {
        self.join_focused_branch(marker, split, ids, |left, right| ProofStep::If {
            condition,
            then_proof: Box::new(left),
            else_proof: Box::new(right),
        })
    }

    /// Joins a completed in-`Proof` case split: both recorded sibling goals
    /// must be discharged, the derivation must pass through the split's
    /// exact marker, and the retained certificate embeds each arm's steps
    /// partitioned by the per-step goal attribution recorded when they were
    /// applied — never inferred from final states.
    pub(in crate::surface::proof) fn join_focused_cases(
        &self,
        marker: &ProofCheckpoint<'a>,
        split: SplitId,
        ids: [BranchId; 2],
        disjunction: ClickProposition,
    ) -> Result<Self, ClickError> {
        self.join_focused_branch(marker, split, ids, |left, right| ProofStep::Cases {
            disjunction,
            left_proof: Box::new(left),
            right_proof: Box::new(right),
        })
    }

    /// Splits the steps recorded since `marker` into per-arm certificates by
    /// the goal attribution stamped on each node when it was applied. The
    /// derivation must pass through the split's exact marker (foreign splits
    /// of the same root collide numerically but fail pointer identity), and
    /// every step in the region must be attributed to one of the two
    /// recorded arms.
    pub(super) fn partition_steps_since(
        &self,
        marker: &ProofCheckpoint<'a>,
        split: SplitId,
        ids: [BranchId; 2],
    ) -> Result<[Vec<ProofStep>; 2], ClickError> {
        let mut left_steps = Vec::new();
        let mut right_steps = Vec::new();
        let mut node = Some(self.node.clone());
        loop {
            let Some(current) = node else {
                return Err(self.step_error(format!(
                    "cannot join: the derivation did not pass through split {split:?}"
                )));
            };
            if Arc::ptr_eq(&current, &marker.node) {
                break;
            }
            if let Some(step) = &current.step {
                if current.focused_branch == ids[0] {
                    left_steps.push(step.as_ref().clone());
                } else if current.focused_branch == ids[1] {
                    right_steps.push(step.as_ref().clone());
                } else {
                    return Err(self.step_error(format!(
                        "cannot join: a step was attributed outside split {split:?}"
                    )));
                }
            }
            node = current.parent.clone();
        }
        left_steps.reverse();
        right_steps.reverse();
        Ok([left_steps, right_steps])
    }

    pub(super) fn join_focused_branch(
        &self,
        marker: &ProofCheckpoint<'a>,
        split: SplitId,
        ids: [BranchId; 2],
        step: impl FnOnce(ProofCertificate, ProofCertificate) -> ProofStep,
    ) -> Result<Self, ClickError> {
        let state = self
            .state
            .join_closed_split(split, ids, marker.node.focused_branch)
            .map_err(|error| match error {
                ProofJoinError::ArmIncomplete(arm) => {
                    let name = ["left", "right"][arm];
                    self.step_error(format!("cannot join `cases`: {name} arm is incomplete"))
                }
                ProofJoinError::InvalidSplit => {
                    self.step_error(format!("cannot join: invalid split identity {split:?}"))
                }
            })?;
        let [left_steps, right_steps] = self.partition_steps_since(marker, split, ids)?;
        let parent = marker.node.parent.clone().ok_or_else(|| {
            self.step_error("cannot join `cases`: the split marker lost its root")
        })?;
        Ok(Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: Arc::new(ProofNode {
                parent: Some(parent.clone()),
                step: Some(Arc::new(step(
                    ProofCertificate::from_steps(left_steps)?,
                    ProofCertificate::from_steps(right_steps)?,
                ))),
                focused_branch: marker.node.focused_branch,
                depth: parent.depth + 1,
            }),
        })
    }

    /// Opens a nested proof for one surface proposition. The body has a fresh
    /// provenance root but shares the persistent semantic fact index and
    /// immutable checking context with its enclosing proof.
    ///
    /// A fixed-state proof may open `have` either while refining a proposition or
    /// from its initial result frontier. The latter is the audited way for
    /// grouped contract finalization to prove one obligation, publish it as a
    /// checked fact, and then prove a dependent obligation without rebuilding
    /// or mutating an external fact context.
    pub(in crate::surface::proof) fn begin_have(
        &self,
        proposition: ClickProposition,
    ) -> Result<ProofScope<'a>, ClickError> {
        if self.state().open_branches().is_discharged() {
            return Err(self.step_error("`have` follows a completed proof"));
        }
        match (self.focused_obligation(), self.context.as_ref()) {
            (Some(Obligation::Proposition(_) | Obligation::FunctionOutcome(_)), _) => {}
            (
                Some(Obligation::Frontier(_)),
                ProofContext::FixedState(_) | ProofContext::Execution(_),
            ) => {}
            _ => {
                return Err(
                    self.step_error("`have` requires a proposition or fixed-state proof context")
                );
            }
        }
        let (kernel, kernel_introductions) =
            self.lower_surface_goal_recording_introductions(&proposition, "`have` proposition")?;
        // A post-execution unfold lets a predicate-call `have` prove the
        // predicate through its structural body. Pair that body kernel with
        // the same unfolded Surface view so `intro` retains binder names and
        // subsequent proof steps serialize an independently checkable
        // proof. Joining still publishes the opaque `kernel` named by the
        // enclosing Have step.
        let structural_proposition = if let ClickProposition::PredicateCall { name, .. } =
            &proposition
            && self.focused_branch_unfolds().contains(name)
        {
            let predicate_environment = match self.context.as_ref() {
                ProofContext::Pure(context) => context.predicate_environment,
                ProofContext::FixedState(context) => context.predicate_environment,
                ProofContext::Execution(context) => context.predicate_environment,
            };
            let active_unfolds = self.focused_branch_unfolds().to_vec();
            unfold_structural_invariant_proposition(
                predicate_environment,
                &proposition,
                &active_unfolds,
            )
            .map_err(|message| {
                self.step_error(format!("could not unfold `have` goal: {message}"))
            })?
        } else {
            proposition.clone()
        };
        let (body_kernel, body_introductions) = if structural_proposition == proposition {
            (kernel.clone(), kernel_introductions)
        } else {
            self.lower_surface_goal_recording_introductions(&structural_proposition, "`have` body")?
        };
        // A `have` stated at an execution frontier proves its goal from the
        // frontier's facts alone. After an explicit checked resource unfold,
        // materialize a selected separation goal from the compact composition
        // with the context's facts; before one, the composition is still
        // checked authority for what ownership alone proves (two ranges owned
        // at entry are disjoint), while a separation that needs call
        // postconditions stays lazy so source expansion preserves their
        // anchored rewrites.
        let at_frontier = matches!(self.focused_obligation(), Some(Obligation::Frontier(_)));
        let resource_unfolded = self
            .execution()
            .is_some_and(|execution| execution.presentation.resource_unfolded);
        let mut body_facts = if !at_frontier || resource_unfolded {
            self.facts().with_selected_resource_separation(&body_kernel)
        } else {
            self.facts()
                .with_selected_composition_separation(&body_kernel)
        };
        // A `have` stated at an execution frontier may use the frontier's
        // effect facts exactly as the shared mid-execution law offers them.
        if at_frontier && let Some(execution) = self.execution() {
            for fact in execution.core.effect_facts.iter() {
                if !body_facts.contains(fact.proposition()) {
                    body_facts = body_facts.with_kernel_checked_fact(fact.proposition().clone());
                }
            }
        }
        // A `have` at the frontier may also consume a fact available across
        // the frontier's certified effects, exactly as a statement step's
        // prerequisite may. Load names are not preserved across call-havoc and
        // store edges by path assumptions (see `CMemoryDerivation`), so the
        // cell an earlier fact names can carry a different load variable at
        // the frontier; the equality is proved in this path's context from the
        // goal's own snapshot-blind candidates, never by search.
        if at_frontier
            && !body_facts.contains(&body_kernel)
            && let Some(execution) = self.execution()
            && body_facts.exact_available_across_effects(&body_kernel, &execution.core.effect_facts)
        {
            body_facts = body_facts.with_kernel_checked_fact(body_kernel.clone());
        }
        // A pointer-valued field's load can be minted from a load-path pruned
        // snapshot, which records no DAG edge by design, so its renaming
        // across a call is proved only by the explicit preservation equality a
        // callee's postcondition states. The indexed load-variable chain is
        // the checked bridge for that; integer goals keep the exact rule above.
        if at_frontier
            && matches!(
                &body_kernel,
                Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(_, _), true)
            )
        {
            body_facts = body_facts.with_selected_load_equality_bridge(&body_kernel);
        }
        let selected_surface_separation = match &structural_proposition {
            ClickProposition::Separate { .. } => true,
            ClickProposition::At { proposition, .. } => {
                matches!(proposition.as_ref(), ClickProposition::Separate { .. })
            }
            _ => false,
        };
        if !at_frontier
            && selected_surface_separation
            && !body_facts.contains(&body_kernel)
            && body_facts.assumptions().proves(&body_kernel)
        {
            body_facts = body_facts.with_kernel_checked_fact(body_kernel.clone());
        }
        for name in self.focused_branch_unfolds().iter() {
            let recorded_bodies = match self.context.as_ref() {
                ProofContext::Pure(context) => context
                    .theorem_context
                    .surface_requirements
                    .kernels_written_by_predicate(name)
                    .cloned()
                    .collect::<Vec<_>>(),
                ProofContext::FixedState(context) => context
                    .surface_propositions
                    .kernels_written_by_predicate(name)
                    .cloned()
                    .collect::<Vec<_>>(),
                ProofContext::Execution(_) => self
                    .outcome_fixed_state_view()
                    .into_iter()
                    .flat_map(|view| view.surface_propositions.kernels_written_by_predicate(name))
                    .cloned()
                    .collect::<Vec<_>>(),
            };
            for recorded in recorded_bodies {
                if matches!(recorded, Proposition::ForAll { .. })
                    && body_facts.contains_top_level(&recorded)
                {
                    body_facts = body_facts.with_predicate_unfold_fact(recorded);
                }
            }
        }
        // Chosen-body projections are scoped to the proposition proof that
        // selected them. A nested `have` starts a fresh presentation scope;
        // otherwise an outer witness could make an unrelated `extract`
        // citation resolve against the wrong source epoch.
        let body_execution = self.branch_execution().map(|execution| {
            if execution.presentation.chosen_projection.is_none() {
                return execution.clone();
            }
            let mut execution = execution.as_ref().clone();
            execution.presentation.chosen_projection = None;
            Arc::new(execution)
        });
        let body_context = BranchState {
            facts: body_facts,
            unfolded_predicates: self.focused_branch_unfolds().clone(),
            execution: body_execution,
        };
        // An execution `have` borrows the current immutable frontier solely
        // as its proposition-lowering/theorem context, shared by identity on
        // the nested goal; a `have` stated at a function outcome borrows that
        // outcome's result-aware outcome proof data the same way. The nested goal
        // cannot publish a changed frontier or outcome: `join` restores the
        // exact root state. At a loop frontier it also retains the unfolded
        // proposition that the nested proof established.
        // Loop closure needs the actual statement proved by an unfolded
        // predicate `have`, not only its opaque name. Retain this local
        // output at a loop frontier; other scope interfaces are unchanged.
        let retained_body = (at_frontier
            && self.execution().is_some_and(|execution| {
                execution.core.frontier.region == ExecutionRegionKind::LoopBody
            })
            && structural_proposition != proposition)
            .then(|| (structural_proposition.clone(), body_kernel.clone()));
        let mut body_goal = match self.focused_outcome_data() {
            Some(outcome_data) => OpenBranch::surface_proposition_at_outcome(
                body_context,
                outcome_data.clone(),
                body_kernel.clone(),
                structural_proposition,
            ),
            None => OpenBranch::surface_proposition_in(
                body_context,
                body_kernel.clone(),
                structural_proposition,
            ),
        };
        if let Obligation::Proposition(body) = &mut body_goal.obligation
            && let Some(Obligation::Proposition(parent)) = self.focused_obligation()
        {
            body.surface_bindings = parent.surface_bindings.clone();
            body.introduced_antecedents = parent.introduced_antecedents.clone();
        }
        let body = Proof {
            site: self.site.nested(ProofStepBlock::Have),
            context: self.context.clone(),
            state: KernelProofObject::root(self.state().locals().clone(), body_goal),
            node: Arc::new(ProofNode {
                parent: None,
                step: None,
                focused_branch: BranchId::ROOT,
                depth: 0,
            }),
        };
        let scope = ProofScope {
            root: self.clone(),
            structure: Box::new(ProofScopeStructure::Have {
                proposition,
                kernel,
                retained_body,
            }),
            body,
            introduced_facts: Vec::new(),
        };
        // The lowering result is also the checked report used by the
        // presentation adapter. Validate it against the fresh body's actual
        // kernel goal before installing its presentation-only metadata.
        scope.with_reported_goal_introductions(&body_kernel, body_introductions)
    }

    /// Opens one composite resource body as an execution scope. Entry is an
    /// audited representation transition, not a separately serialized
    /// `unfold`; the child Proof starts fresh provenance and the eventual join
    /// records the child certificate inside one `Open` step.
    pub(in crate::surface::proof) fn begin_open(
        &self,
        resource: ResourceClause,
        source_index: usize,
    ) -> Result<ProofScope<'a>, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error("`open` requires an execution-frontier proof"));
        };
        self.require_execution_frontier("`open`")?;
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        if execution.presentation.chosen_projection.is_some() {
            execution.presentation.chosen_projection = None;
        }
        if execution.core.frontier.is_at_function_exit() {
            return Err(self.step_error("`open` must begin before execution reaches function exit"));
        }
        let before_facts = self.facts().clone();
        let checked = open_composite_resource_for_proof(
            context.resource_environment,
            &resource,
            context.parsed_function.parameters(),
            context.arguments,
            (*execution.core.state).clone(),
            self.facts().clone(),
            &mut execution.presentation.surface_propositions,
            context.predicate_environment,
            context.click_function_environment,
            context.claim_label,
            context.tactic_index,
        )?;
        execution
            .core
            .record_resource_rewrite(
                context.function,
                context.arguments,
                &before_facts,
                &checked.selected,
                &checked.state,
                &checked.facts,
            )
            .map_err(|message| {
                self.step_error(format!(
                    "kernel rejected checked resource `open`: {message}"
                ))
            })?;
        execution.core.state = checked.state.into();
        let introduced_facts = checked.added_facts.clone();
        let state = self
            .state
            .publish_checked_frontier_transition(
                checked.facts,
                execution,
                checked.added_facts.clone(),
                checked.added_facts,
            )
            .map_err(|error| self.execution_update_error("`open`", error))?;
        let body = Proof {
            site: self.site.nested(ProofStepBlock::Open),
            context: self.context.clone(),
            state,
            node: Arc::new(ProofNode {
                parent: None,
                step: None,
                focused_branch: self.focused_branch_id(),
                depth: 0,
            }),
        };
        Ok(ProofScope {
            root: self.clone(),
            structure: Box::new(ProofScopeStructure::Open {
                resource,
                source_index,
                preserve_exposed_body: checked.body_was_already_exposed,
            }),
            body,
            introduced_facts,
        })
    }
}
