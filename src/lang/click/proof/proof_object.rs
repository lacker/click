use super::pure_theorems::{PureTheoremContext, lower_pure_theorem_proposition};
use super::*;

use std::cmp::Ordering;
use std::sync::Arc;

/// Immutable checked proof state exposed to smart tactics.
///
/// This first vertical slice supports linear pure goals. The representation is
/// deliberately already persistent: cloning a `Proof` shares its semantic
/// state and derivation prefix, and applying a step copies only logarithmically
/// many fact-index nodes plus the step's own semantic delta.
#[derive(Clone)]
pub(super) struct Proof<'a> {
    context: Arc<PureProofContext<'a>>,
    state: Arc<PureProofState>,
    node: Arc<ProofNode>,
}

struct PureProofContext<'a> {
    claim_label: &'a str,
    theorem_context: &'a PureTheoremContext,
    predicate_environment: &'a PredicateEnvironment,
    click_function_environment: &'a ClickFunctionEnvironment,
    theorem_environment: &'a TheoremEnvironment,
}

struct PureProofState {
    facts: PersistentFactIndex,
    goal: Arc<Proposition>,
    complete: bool,
}

/// Private persistent provenance node. Smart tactics can retain a `Proof`,
/// but cannot manufacture one of these or detach semantic state from the step
/// that produced it.
struct ProofNode {
    parent: Option<Arc<ProofNode>>,
    step: Option<Arc<SimpleProofStep>>,
    depth: usize,
}

#[derive(Clone, Default)]
struct PersistentFactIndex {
    root: Option<Arc<FactNode>>,
}

struct FactNode {
    fact: Arc<Proposition>,
    left: Option<Arc<FactNode>>,
    right: Option<Arc<FactNode>>,
    height: u16,
}

impl<'a> Proof<'a> {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn for_pure_goal(
        claim_label: &'a str,
        requires: &[Proposition],
        goal: Proposition,
        theorem_context: &'a PureTheoremContext,
        predicate_environment: &'a PredicateEnvironment,
        click_function_environment: &'a ClickFunctionEnvironment,
        theorem_environment: &'a TheoremEnvironment,
    ) -> Self {
        let mut facts = PersistentFactIndex::default();
        for fact in requires {
            facts = facts.with_fact(fact.clone());
        }
        Self {
            context: Arc::new(PureProofContext {
                claim_label,
                theorem_context,
                predicate_environment,
                click_function_environment,
                theorem_environment,
            }),
            state: Arc::new(PureProofState {
                facts,
                goal: Arc::new(goal),
                complete: false,
            }),
            node: Arc::new(ProofNode {
                parent: None,
                step: None,
                depth: 0,
            }),
        }
    }

    pub(super) fn goal(&self) -> &Proposition {
        &self.state.goal
    }

    pub(super) fn is_complete(&self) -> bool {
        self.state.complete
    }

    /// Checks one explicit simple step and atomically returns the checked
    /// successor with that exact step retained as provenance.
    ///
    /// Failure allocates no reachable successor: `self` and all of its other
    /// descendants continue to share the unchanged ancestor state.
    pub(super) fn apply_step(&self, step: SimpleProofStep) -> Result<Self, ClickError> {
        if self.state.complete {
            return Err(self.step_error("a tactic follows a goal-closing step"));
        }

        let next_state = match &step {
            SimpleProofStep::ApplyTheoremUsing {
                application,
                premises,
            } => self.apply_theorem_using(application, premises)?,
            SimpleProofStep::Assumption => {
                if !self.state.facts.contains(self.goal()) {
                    return Err(self.step_error(format!(
                        "`assumption` requires the exact current goal as an available fact: {:?}",
                        self.goal()
                    )));
                }
                PureProofState {
                    facts: self.state.facts.clone(),
                    goal: self.state.goal.clone(),
                    complete: true,
                }
            }
            SimpleProofStep::Normalize => {
                if !normalizes_context_free(self.goal()) {
                    return Err(self.step_error(format!(
                        "`normalize` requires a context-free true goal: {:?}",
                        self.goal()
                    )));
                }
                PureProofState {
                    facts: self.state.facts.clone(),
                    goal: self.state.goal.clone(),
                    complete: true,
                }
            }
            _ => {
                return Err(self.step_error(
                    "this simple step has not yet migrated to the checked `Proof` API",
                ));
            }
        };

        Ok(Self {
            context: self.context.clone(),
            state: Arc::new(next_state),
            node: Arc::new(ProofNode {
                parent: Some(self.node.clone()),
                step: Some(Arc::new(step)),
                depth: self.node.depth + 1,
            }),
        })
    }

    pub(super) fn certificate(&self) -> ProofCertificate {
        let mut steps = Vec::with_capacity(self.node.depth);
        let mut node = Some(self.node.as_ref());
        while let Some(current) = node {
            if let Some(step) = &current.step {
                steps.push(step.as_ref().clone());
            }
            node = current.parent.as_deref();
        }
        steps.reverse();
        ProofCertificate::from_steps(steps)
    }

    fn apply_theorem_using(
        &self,
        application: &TheoremApplication,
        surface_premises: &[ClickProposition],
    ) -> Result<PureProofState, ClickError> {
        let context = self.context.as_ref();
        let explicit_premises = surface_premises
            .iter()
            .map(|premise| {
                lower_pure_theorem_proposition(
                    context.claim_label,
                    premise,
                    &context.theorem_context.values,
                    &context.theorem_context.array_refs,
                    &context.theorem_context.memory,
                    context.predicate_environment,
                    context.click_function_environment,
                )
                .map_err(|message| {
                    self.step_error(format!("could not lower `apply using` premise: {message}"))
                })
            })
            .collect::<Result<Vec<_>, _>>()?;

        for premise in &explicit_premises {
            if !self.state.facts.contains(premise) {
                return Err(self.step_error(format!(
                    "`apply using` requires an unavailable exact premise: {premise:?}"
                )));
            }
        }

        // The checker receives exactly the named premises, not the ambient
        // context. Its work is therefore independent of unrelated facts, and
        // it cannot silently search for an omitted theorem requirement.
        let state = CState::new().with_memory(context.theorem_context.memory.clone());
        let program_point_states = ProgramPointStates::new();
        let application_context = TheoremApplicationContext {
            values: &context.theorem_context.values,
            array_refs: &context.theorem_context.array_refs,
            pre_state: &state,
            post_state: &state,
            result: None,
            program_point_states: &program_point_states,
        };
        let applied = apply_theorem_applications_to_available(
            context.theorem_environment,
            &[(self.node.depth, application.clone())],
            context.claim_label,
            None,
            explicit_premises,
            &application_context,
            context.predicate_environment,
            context.click_function_environment,
            &[],
        )?;

        let mut facts = self.state.facts.clone();
        for fact in applied {
            facts = facts.with_fact(fact);
        }
        Ok(PureProofState {
            facts,
            goal: self.state.goal.clone(),
            complete: false,
        })
    }

    fn step_error(&self, message: impl Into<String>) -> ClickError {
        ClickError::new(format!(
            "`{}` proof step {}: {}",
            self.context.claim_label,
            self.node.depth,
            message.into()
        ))
    }

    #[cfg(test)]
    fn fact_lookup_comparisons(&self, fact: &Proposition) -> usize {
        self.state.facts.lookup_comparisons(fact)
    }
}

impl PersistentFactIndex {
    fn with_fact(&self, fact: Proposition) -> Self {
        let mut next = self.clone();
        if matches!(fact, Proposition::And(_, _)) {
            let mut conjuncts = Vec::new();
            collect_owned_atomic_conjuncts(&fact, &mut conjuncts);
            for conjunct in conjuncts {
                next.root = insert_fact_node(next.root.as_ref(), Arc::new(conjunct));
            }
        }
        next.root = insert_fact_node(next.root.as_ref(), Arc::new(fact));
        next
    }

    fn contains(&self, fact: &Proposition) -> bool {
        let mut node = self.root.as_ref();
        while let Some(current) = node {
            match fact.cmp(current.fact.as_ref()) {
                Ordering::Less => node = current.left.as_ref(),
                Ordering::Equal => return true,
                Ordering::Greater => node = current.right.as_ref(),
            }
        }
        false
    }

    #[cfg(test)]
    fn lookup_comparisons(&self, fact: &Proposition) -> usize {
        let mut comparisons = 0;
        let mut node = self.root.as_ref();
        while let Some(current) = node {
            comparisons += 1;
            match fact.cmp(current.fact.as_ref()) {
                Ordering::Less => node = current.left.as_ref(),
                Ordering::Equal => return comparisons,
                Ordering::Greater => node = current.right.as_ref(),
            }
        }
        comparisons
    }
}

fn collect_owned_atomic_conjuncts(fact: &Proposition, output: &mut Vec<Proposition>) {
    match fact {
        Proposition::And(left, right) => {
            collect_owned_atomic_conjuncts(left, output);
            collect_owned_atomic_conjuncts(right, output);
        }
        _ => output.push(fact.clone()),
    }
}

fn fact_node_height(node: Option<&Arc<FactNode>>) -> u16 {
    node.map_or(0, |node| node.height)
}

fn make_fact_node(
    fact: Arc<Proposition>,
    left: Option<Arc<FactNode>>,
    right: Option<Arc<FactNode>>,
) -> Arc<FactNode> {
    Arc::new(FactNode {
        fact,
        height: 1 + fact_node_height(left.as_ref()).max(fact_node_height(right.as_ref())),
        left,
        right,
    })
}

fn balance_fact_node(
    fact: Arc<Proposition>,
    left: Option<Arc<FactNode>>,
    right: Option<Arc<FactNode>>,
) -> Arc<FactNode> {
    let left_height = fact_node_height(left.as_ref());
    let right_height = fact_node_height(right.as_ref());
    if left_height > right_height + 1 {
        let left_node = left.as_ref().expect("left-heavy node has a left child");
        if fact_node_height(left_node.left.as_ref()) >= fact_node_height(left_node.right.as_ref()) {
            let new_right = make_fact_node(fact, left_node.right.clone(), right);
            return make_fact_node(
                left_node.fact.clone(),
                left_node.left.clone(),
                Some(new_right),
            );
        }
        let middle = left_node
            .right
            .as_ref()
            .expect("left-right-heavy node has a middle child");
        let new_left = make_fact_node(
            left_node.fact.clone(),
            left_node.left.clone(),
            middle.left.clone(),
        );
        let new_right = make_fact_node(fact, middle.right.clone(), right);
        return make_fact_node(middle.fact.clone(), Some(new_left), Some(new_right));
    }
    if right_height > left_height + 1 {
        let right_node = right.as_ref().expect("right-heavy node has a right child");
        if fact_node_height(right_node.right.as_ref()) >= fact_node_height(right_node.left.as_ref())
        {
            let new_left = make_fact_node(fact, left, right_node.left.clone());
            return make_fact_node(
                right_node.fact.clone(),
                Some(new_left),
                right_node.right.clone(),
            );
        }
        let middle = right_node
            .left
            .as_ref()
            .expect("right-left-heavy node has a middle child");
        let new_left = make_fact_node(fact, left, middle.left.clone());
        let new_right = make_fact_node(
            right_node.fact.clone(),
            middle.right.clone(),
            right_node.right.clone(),
        );
        return make_fact_node(middle.fact.clone(), Some(new_left), Some(new_right));
    }
    make_fact_node(fact, left, right)
}

fn insert_fact_node(node: Option<&Arc<FactNode>>, fact: Arc<Proposition>) -> Option<Arc<FactNode>> {
    let Some(node) = node else {
        return Some(make_fact_node(fact, None, None));
    };
    Some(match fact.as_ref().cmp(node.fact.as_ref()) {
        Ordering::Less => balance_fact_node(
            node.fact.clone(),
            insert_fact_node(node.left.as_ref(), fact),
            node.right.clone(),
        ),
        Ordering::Equal => node.clone(),
        Ordering::Greater => balance_fact_node(
            node.fact.clone(),
            node.left.clone(),
            insert_fact_node(node.right.as_ref(), fact),
        ),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn indexed_fact(index: u32) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessThan(
                Box::new(Bitvector32Term::Variable(Variable(0))),
                Box::new(Bitvector32Term::Constant(index)),
            ),
            true,
        )
    }

    #[test]
    fn proof_failure_preserves_ancestor_and_selected_provenance() {
        let goal = indexed_fact(7);
        let theorem_context = PureTheoremContext {
            memory: CMemory::new(),
            values: BTreeMap::new(),
            array_refs: BTreeMap::new(),
            requires: vec![goal.clone()],
        };
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        let root = Proof::for_pure_goal(
            "transactional",
            &theorem_context.requires,
            goal,
            &theorem_context,
            &predicate_environment,
            &click_function_environment,
            &theorem_environment,
        );
        let fork = root.clone();
        assert!(Arc::ptr_eq(&root.state, &fork.state));
        assert!(Arc::ptr_eq(&root.node, &fork.node));

        assert!(
            fork.apply_step(SimpleProofStep::Normalize).is_err(),
            "a symbolic comparison must not normalize to true"
        );
        assert!(!root.is_complete());
        assert!(root.certificate().steps().is_empty());

        let complete = root
            .apply_step(SimpleProofStep::Assumption)
            .expect("the exact root fact should close the goal");
        assert!(complete.is_complete());
        assert_eq!(
            complete.certificate().steps(),
            &[SimpleProofStep::Assumption]
        );
        assert!(!root.is_complete());
        assert!(root.certificate().steps().is_empty());
    }

    #[test]
    fn persistent_fact_lookup_scales_logarithmically() {
        let predicate_environment = PredicateEnvironment::new(&[]);
        let click_function_environment = ClickFunctionEnvironment::new(&[]);
        let theorem_environment = TheoremEnvironment::new(&[]);
        for size in [16_u32, 64, 256, 1024, 4096] {
            let requires = (0..size).map(indexed_fact).collect::<Vec<_>>();
            let goal = indexed_fact(size - 1);
            let theorem_context = PureTheoremContext {
                memory: CMemory::new(),
                values: BTreeMap::new(),
                array_refs: BTreeMap::new(),
                requires,
            };
            let proof = Proof::for_pure_goal(
                "scaling",
                &theorem_context.requires,
                goal.clone(),
                &theorem_context,
                &predicate_environment,
                &click_function_environment,
                &theorem_environment,
            );
            let shared = proof.clone();
            assert!(Arc::ptr_eq(&proof.state, &shared.state));
            assert!(Arc::ptr_eq(&proof.node, &shared.node));

            let comparisons = proof.fact_lookup_comparisons(&goal);
            let logarithmic_bound = 2 * (u32::BITS - size.leading_zeros()) as usize + 2;
            assert!(
                comparisons <= logarithmic_bound,
                "size {size} lookup took {comparisons} comparisons (bound {logarithmic_bound})"
            );

            let complete = shared
                .apply_step(SimpleProofStep::Assumption)
                .expect("fixed local step should succeed");
            assert!(complete.is_complete());
            assert!(Arc::ptr_eq(
                complete
                    .node
                    .parent
                    .as_ref()
                    .expect("successor has a parent"),
                &proof.node
            ));
            assert!(proof.certificate().steps().is_empty());
            assert_eq!(complete.certificate().steps().len(), 1);
        }
    }
}
