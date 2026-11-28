//! Incremental successors of an already checked C return.

use super::*;

/// Inputs retained by the checked body producer. Opening a logical outcome
/// forks these inputs; subsequent exchanges never inspect the C event history.
#[derive(Clone)]
pub(crate) struct CheckedReturnSeed {
    completion: StatementOutcome,
    caller: ExecutionState,
    function: ProgramFunction,
    exit_function: Arc<ProgramFunction>,
    arguments: Arc<[ProgramExpression]>,
    candidate: crate::kernel::FunctionExecutionCandidate,
    transfer: Option<Arc<crate::kernel::functions::CheckedBoundaryResourceTransfer>>,
    context: Arc<CheckedReturnContext>,
}

impl CheckedReturnSeed {
    pub(super) fn new(
        core: &ExecutionProofCore,
        path: usize,
        candidates: &FunctionExecutionCandidates,
        candidate: &crate::kernel::FunctionExecutionCandidate,
        function: &ProgramFunction,
        completion: StatementOutcome,
        has_checked_entry: bool,
    ) -> Arc<Self> {
        let entry = has_checked_entry
            .then_some(core.function_entry.as_deref())
            .flatten();
        Arc::new(Self {
            context: Arc::new(CheckedReturnContext::from_candidate(
                core.execution_evidence[path]
                    .origin
                    .as_deref()
                    .cloned()
                    .unwrap_or_else(|| completion.clone()),
                candidate,
            )),
            completion,
            caller: entry.map_or_else(
                || candidates.state().clone(),
                |entry| entry.caller_state().clone(),
            ),
            exit_function: entry.map_or_else(
                || Arc::new(function.clone()),
                |entry| entry.function.clone(),
            ),
            function: function.clone(),
            arguments: candidates.arguments().to_vec().into(),
            candidate: candidate.clone(),
            transfer: entry.and_then(|entry| entry.boundary_transfer.clone()),
        })
    }
}

impl CheckedReturnSeed {
    pub(in crate::kernel) fn obligations(&self) -> &[crate::kernel::ProofObligation] {
        self.candidate.obligations()
    }
}

#[derive(Clone)]
pub(super) struct ReturnRewriteProducer {
    seed: Arc<CheckedReturnSeed>,
    completion: StatementOutcome,
    visible: FunctionOutcome,
    context: PureFactContext,
    base: PureFactStore,
    added: ExecutionFacts,
    publication: Arc<crate::kernel::PublishedFunctionOutcome>,
    outcome: super::super::OutcomeIdentity,
    applied_tactics: crate::persistent::PersistentMap<String, ()>,
}

impl ReturnRewriteProducer {
    pub(super) fn seed_context(&self) -> Arc<CheckedReturnContext> {
        self.seed.context.clone()
    }
    /// Retain the current ordinary goal's checked fact delta. Its proof
    /// operation owns these facts; re-proving them at the C return would lose
    /// post-return observations and contract-refinement case assumptions.
    fn accept_facts(&mut self, facts: &PureFactStore) -> Result<(), String> {
        let delta = facts
            .introduced_since(&self.base)
            .ok_or("return operation has a different fact lineage")?;
        for fact in delta {
            crate::instrumentation::record_deterministic_work(1);
            self.retain_fact(fact);
        }
        self.base = facts.clone();
        Ok(())
    }

    fn retain_fact(&mut self, fact: Proposition) {
        // Return evidence keeps the checked judgment and its read points.
        self.context = std::mem::take(&mut self.context)
            .assume_proposition(crate::kernel::canonical_condition_fact(&fact));
        self.added.push(ExecutionPureFact::new(fact));
    }

    pub(super) fn accept_proposition(
        &mut self,
        proof: &super::super::CheckedProposition,
        base: &PureFactStore,
    ) -> Result<(), String> {
        if !proof
            .outcome()
            .is_some_and(|outcome| outcome.identity.same_as(&self.outcome))
        {
            return Err("return proof belongs to another outcome".into());
        }
        // The ordinary proof operation owns these root facts. Retain its
        // checked delta instead of trying to prove its premises a second time
        // against the earlier C state (which lacks later observations).
        let delta = base
            .introduced_since(&self.base)
            .ok_or("return proof has a different fact lineage")?;
        let extra = proof
            .root_assumptions()
            .introduced_since(base)
            .ok_or("return proof has a different root context")?;
        for fact in delta.into_iter().chain(extra) {
            self.retain_fact(fact);
        }
        self.base = base.clone();
        self.retain_fact(proof.proposition().clone());
        Ok(())
    }

    /// The exchange has already constructed these outputs under the retained
    /// input context. Do not select or prove its resource body a second time.
    fn accept_rewrite(&mut self, rewrite: &CheckedResourceRewrite) -> Result<(), String> {
        self.accept_facts(&rewrite.before_facts)?;
        match &mut self.completion {
            StatementOutcome::Return { state, .. } | StatementOutcome::Normal(state) => {
                **state = rewrite.after_state.clone();
            }
            _ => return Err("return exchange requires a returning path".into()),
        }
        let visible = rewrite
            .return_observation
            .as_ref()
            .map(|observation| &observation.after)
            .or_else(|| {
                rewrite
                    .return_presentation
                    .as_ref()
                    .map(|presentation| &presentation.rewrite.after_state)
            });
        if let (Some(state), FunctionOutcome::Return { state: current, .. }) =
            (visible, &mut self.visible)
        {
            **current = state.clone();
        }
        for fact in rewrite
            .after_facts
            .introduced_since(&rewrite.before_facts)
            .ok_or("return exchange changed its fact lineage")?
        {
            self.retain_fact(fact);
        }
        if let Some(observation) = &rewrite.return_observation {
            for fact in &observation.semantic_facts {
                self.retain_fact(fact.clone());
            }
        }
        if let Some(presentation) = &rewrite.return_presentation {
            for fact in &presentation.published_facts {
                self.retain_fact(fact.clone());
            }
            for fact in presentation
                .rewrite
                .after_facts
                .introduced_since(&presentation.rewrite.before_facts)
                .ok_or("return presentation changed its fact lineage")?
            {
                self.retain_fact(fact);
            }
        }
        self.base = rewrite.after_facts.clone();
        Ok(())
    }

    pub(super) fn finish(&self) -> Result<CheckedReturnPath, ReturnPathRefusal> {
        let seed = &self.seed;
        let (outcome, obligations, borrows, deferred, error) =
            match crate::kernel::functions::checked_contract_exit_outcome_with_boundary_transfer(
                &seed.caller,
                &seed.exit_function,
                &seed.arguments,
                self.completion.clone(),
                self.visible.clone(),
                seed.candidate.obligations().to_vec(),
                &self.context,
                &mut ExecutionBudget::beside_live_state(),
                crate::kernel::functions::ResourceTransitionPurpose::FunctionBoundary,
                seed.transfer.as_deref(),
            ) {
                Ok(Ok(result)) => result,
                Ok(Err(error)) => (
                    FunctionOutcome::RuntimeError(error),
                    seed.candidate.obligations().to_vec(),
                    None,
                    false,
                    None,
                ),
                Err(_) => {
                    return Err(ReturnPathRefusal {
                        reason: "the rewritten return's exit operation hit an execution limit",
                        unjustified_fact: None,
                    });
                }
            };
        let mut path = self.publication.path().clone();
        path.facts.extend_shared(&self.added);
        path.post_assumptions = Some(self.context.clone());
        path.completion_origin = Some(self.visible.clone());
        path.obligations = obligations;
        path.borrow_evidence = crate::kernel::borrows::append_checked_borrow_evidence(
            seed.candidate.borrow_evidence(),
            borrows,
        );
        let specification = self.publication.specification();
        path.theorem = Theorem::new(crate::kernel::reasoning::wrap_proof_facts(
            Proposition::ProgramFunctionVerifies {
                state: Box::new(specification.state().clone()),
                function: Box::new(seed.function.clone()),
                arguments: specification.arguments().to_vec(),
                outcome: outcome.clone(),
            },
            &path.assumptions,
            &path.facts,
            seed.candidate.obligations(),
        ));
        let publication =
            self.publication
                .with_return_path(path.clone(), outcome, deferred, error.clone());
        Ok(CheckedReturnPath { path, publication })
    }
}

impl ExecutionProofCore {
    pub(crate) fn open_return_outcome(
        &mut self,
        index: usize,
        outcome: &super::super::OutcomeProofCore,
        facts: &PureFactStore,
    ) {
        if outcome.is_exceptional {
            return;
        }
        let Some(publication) = &outcome.publication else {
            return;
        };
        let seed = publication.return_seed().clone();
        self.return_producers.insert(
            index,
            ReturnRewriteProducer {
                completion: seed.completion.clone(),
                visible: seed.candidate.outcome().clone(),
                context: facts.assumptions().clone(),
                base: facts.clone(),
                added: ExecutionFacts::new(),
                seed,
                publication: publication.clone(),
                outcome: outcome.identity.clone(),
                applied_tactics: Default::default(),
            },
        );
    }

    pub(super) fn has_return_producer(
        &self,
        index: usize,
        outcome: &super::super::OutcomeIdentity,
    ) -> bool {
        self.return_producers
            .get(&index)
            .is_some_and(|producer| producer.outcome.same_as(outcome))
    }

    pub(crate) fn retain_return_tactic_dependencies(
        &self,
        path: usize,
        owner: &mut crate::kernel::ContractExecutionOwner,
    ) {
        if let Some(producer) = self.return_producers.get(&path) {
            owner.retain_applied_tactics(producer.applied_tactics.iter().map(|(name, ())| name));
        }
    }

    pub(crate) fn finish_prepared_return_tactic_application(
        &mut self,
        proved: &Self,
        proved_facts: &PureFactStore,
    ) -> Result<PureFactStore, String> {
        let prepared = Arc::unwrap_or_clone(
            self.prepared_tactic_application
                .take()
                .expect("a prepared return tactic"),
        );
        let (path, semantic_facts) = prepared.return_path.expect("a checked return path");
        let mut producer = proved
            .return_producers
            .get(&path)
            .ok_or("return tactic lost its outcome")?
            .clone();
        producer.accept_facts(proved_facts)?;
        let mut trace = proved
            .return_resource_rewrites
            .get(&path)
            .unwrap_or(&proved.execution_evidence[path])
            .clone();
        let before = trace.retained_state()?;
        let resources = before.resources().clone().with_constructed_exchange(
            prepared.before_state.resources(),
            prepared.after_state.resources(),
        )?;
        let mut retained = prepared
            .after_state
            .clone()
            .with_resource_context(resources);
        retained.keep_memory_of(before);
        retained.locals = before.locals().clone();
        retained.enclosing_frame_holds_locals = before.enclosing_frame_holds_locals;

        let StatementOutcome::Return { state, .. } = &mut producer.completion else {
            return Err("an outcome tactic application requires a return".into());
        };
        **state = retained.clone();
        let FunctionOutcome::Return { state, .. } = &mut producer.visible else {
            return Err("an outcome tactic application requires a visible return".into());
        };
        **state = prepared.after_state.clone();
        let facts = semantic_facts
            .iter()
            .fold(proved_facts.clone(), |facts, fact| {
                producer.retain_fact(fact.clone());
                facts.with_kernel_checked_fact(fact.clone())
            });
        producer.base = facts.clone();
        producer.applied_tactics.insert(prepared.name.clone(), ());
        self.return_producers.insert(path, producer);

        let application = CheckedTacticApplication {
            name: prepared.name,
            before_state: before.clone(),
            after_state: retained,
            return_effect: Some(ReturnTacticEffect {
                presented: Arc::new(prepared.after_state),
                facts: semantic_facts,
            }),
        };
        trace.push(CheckedExecutionEvent::TacticApplication(Box::new(
            application,
        )));
        self.return_resource_rewrites.insert(path, trace);
        Ok(facts)
    }

    pub(super) fn retain_return_facts(
        &mut self,
        index: usize,
        facts: &PureFactStore,
    ) -> Result<(), String> {
        if let Some(producer) = self.return_producers.get(&index) {
            let mut next = producer.clone();
            next.accept_facts(facts)?;
            self.return_producers.insert(index, next);
        }
        Ok(())
    }

    pub(super) fn push_return_rewrite(
        &mut self,
        index: usize,
        rewrite: CheckedResourceRewrite,
    ) -> Result<(), String> {
        if let Some(producer) = self.return_producers.get(&index) {
            let mut next = producer.clone();
            next.accept_rewrite(&rewrite)?;
            self.return_producers.insert(index, next);
        }
        let mut trace = self
            .return_resource_rewrites
            .get(&index)
            .unwrap_or(&self.execution_evidence[index])
            .clone();
        trace.push(CheckedExecutionEvent::ResourceRewrite(Box::new(rewrite)));
        self.return_resource_rewrites.insert(index, trace);
        Ok(())
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/proof/execution/return_producer.rs");
}
