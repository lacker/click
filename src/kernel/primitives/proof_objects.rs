use super::*;

impl Theorem {
    pub(in crate::kernel) fn new(proposition: Proposition) -> Self {
        Self { proposition }
    }

    pub fn proposition(&self) -> &Proposition {
        &self.proposition
    }
}

impl PropositionDerivation {
    pub fn conclusion(&self) -> &Proposition {
        &self.conclusion
    }

    pub fn context_premises(&self) -> Vec<Proposition> {
        let mut premises = BTreeSet::new();
        self.collect_context_premises(&mut premises);
        premises.into_iter().collect()
    }

    fn collect_context_premises(&self, premises: &mut BTreeSet<Proposition>) {
        fn collect_local_assumptions(
            proposition: &Proposition,
            assumptions: &mut BTreeSet<Proposition>,
        ) {
            if let Proposition::And(left, right) = proposition {
                collect_local_assumptions(left, assumptions);
                collect_local_assumptions(right, assumptions);
            } else {
                assumptions.insert(proposition.clone());
            }
        }

        match &self.rule {
            PropositionDerivationRule::ContextFree => {}
            PropositionDerivationRule::ContextualAtomic {
                premises: required, ..
            }
            | PropositionDerivationRule::Explosion { premises: required } => {
                premises.extend(required.pure_facts());
            }
            PropositionDerivationRule::And { left, right } => {
                left.collect_context_premises(premises);
                right.collect_context_premises(premises);
            }
            PropositionDerivationRule::OrLeft(proof)
            | PropositionDerivationRule::OrRight(proof)
            | PropositionDerivationRule::DoubleNegation(proof)
            | PropositionDerivationRule::ImpliesFalseAntecedent(proof)
            | PropositionDerivationRule::ForAllBody(proof) => {
                proof.collect_context_premises(premises);
            }
            PropositionDerivationRule::Implies { antecedent, body } => {
                let mut body_premises = BTreeSet::new();
                body.collect_context_premises(&mut body_premises);
                let mut local_assumptions = BTreeSet::new();
                collect_local_assumptions(antecedent, &mut local_assumptions);
                for local in local_assumptions {
                    body_premises.remove(&local);
                }
                premises.extend(body_premises);
            }
            PropositionDerivationRule::FiniteForAll { instances } => {
                for instance in instances {
                    instance.collect_context_premises(premises);
                }
            }
            PropositionDerivationRule::FiniteContextSplit {
                premises: range_premises,
                instances,
                ..
            } => {
                premises.extend(range_premises.pure_facts());
                for instance in instances {
                    instance.collect_context_premises(premises);
                }
            }
            PropositionDerivationRule::UpperBoundSplit {
                bound,
                variable,
                pivot,
                below,
                at,
            } => {
                premises.insert(Proposition::ConditionIs(bound.clone(), true));
                let variable = Bitvector32Term::Variable(*variable);
                for (proof, local) in [
                    (
                        below,
                        ConditionTerm::signed_less_than(variable.clone(), pivot.clone()),
                    ),
                    (at, ConditionTerm::equal(variable, pivot.clone())),
                ] {
                    let mut case_premises = BTreeSet::new();
                    proof.collect_context_premises(&mut case_premises);
                    case_premises.remove(&Proposition::ConditionIs(local, true));
                    premises.extend(case_premises);
                }
            }
            PropositionDerivationRule::DisjunctionCases { disjunction, cases } => {
                premises.insert(disjunction.clone());
                let mut case_propositions = Vec::new();
                collect_or_cases(disjunction, &mut case_propositions);
                for (case, local) in cases.iter().zip(case_propositions) {
                    let mut case_premises = BTreeSet::new();
                    case.collect_context_premises(&mut case_premises);
                    let mut local_assumptions = BTreeSet::new();
                    collect_local_assumptions(&local, &mut local_assumptions);
                    for local in local_assumptions {
                        case_premises.remove(&local);
                    }
                    premises.extend(case_premises);
                }
            }
        }
    }
}

impl Default for ExecutionBudget {
    fn default() -> Self {
        Self {
            expression_steps: 10_000,
            statement_steps: 10_000,
            function_calls: 1_000,
            loop_unrolls: 256,
            paths: 10_000,
            next_opaque_call: 0,
            next_verification_variable: 1_000_000,
        }
    }
}

impl ExecutionBudget {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_expression_steps(mut self, expression_steps: usize) -> Self {
        self.expression_steps = expression_steps;
        self
    }

    pub fn with_statement_steps(mut self, statement_steps: usize) -> Self {
        self.statement_steps = statement_steps;
        self
    }

    pub fn with_function_calls(mut self, function_calls: usize) -> Self {
        self.function_calls = function_calls;
        self
    }

    pub fn with_loop_unrolls(mut self, loop_unrolls: usize) -> Self {
        self.loop_unrolls = loop_unrolls;
        self
    }

    pub fn with_paths(mut self, paths: usize) -> Self {
        self.paths = paths;
        self
    }

    pub(crate) fn with_next_opaque_call(mut self, next_opaque_call: u64) -> Self {
        self.next_opaque_call = next_opaque_call;
        self
    }

    pub(crate) fn next_opaque_call(&self) -> u64 {
        self.next_opaque_call
    }

    pub(crate) fn with_next_verification_variable(
        mut self,
        next_verification_variable: u64,
    ) -> Self {
        self.next_verification_variable = 1_000_000 + next_verification_variable;
        self
    }

    pub(crate) fn next_verification_variable(&self) -> u64 {
        self.next_verification_variable - 1_000_000
    }

    pub(in crate::kernel) fn consume_expression_step(&mut self) -> ExecutionResult<()> {
        consume_budget(&mut self.expression_steps, ExecutionLimit::ExpressionSteps)
    }

    pub(in crate::kernel) fn consume_statement_step(&mut self) -> ExecutionResult<()> {
        consume_budget(&mut self.statement_steps, ExecutionLimit::StatementSteps)
    }

    pub(in crate::kernel) fn consume_function_call(&mut self) -> ExecutionResult<()> {
        consume_budget(&mut self.function_calls, ExecutionLimit::FunctionCalls)
    }

    pub(in crate::kernel) fn consume_loop_unroll(&mut self) -> ExecutionResult<()> {
        consume_budget(&mut self.loop_unrolls, ExecutionLimit::LoopUnrolls)
    }

    pub(in crate::kernel) fn consume_paths(&mut self, paths: usize) -> ExecutionResult<()> {
        if crate::instrumentation::deadline_exceeded() {
            return Err(ExecutionLimit::Deadline);
        }
        if self.paths < paths {
            return Err(ExecutionLimit::Paths);
        }
        self.paths -= paths;
        Ok(())
    }
}

pub(in crate::kernel) type ExecutionResult<T> = Result<T, ExecutionLimit>;

pub(in crate::kernel) fn consume_budget(
    remaining: &mut usize,
    limit: ExecutionLimit,
) -> ExecutionResult<()> {
    if crate::instrumentation::deadline_exceeded() {
        return Err(ExecutionLimit::Deadline);
    }
    if *remaining == 0 {
        return Err(limit);
    }
    *remaining -= 1;
    Ok(())
}
