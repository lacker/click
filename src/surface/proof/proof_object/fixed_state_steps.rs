//! Fixed-state theorem application, witness/instantiate, rewrite, and
//! transport steps.

use super::*;
use crate::kernel::proof::fact_reasoning::{InstanceArgument, listed_equality_fact_is_available};
use crate::kernel::proof::{CheckedProofCasePartition, OutcomeEvidenceFork, OutcomeForkArm};

const MAX_CHOSEN_PROJECTION_WORK: usize = 4096;

fn proposition_at_connective_path<'a>(
    root: &'a Proposition,
    path: &[usize],
) -> Option<&'a Proposition> {
    let mut current = root;
    for direction in path {
        let Proposition::And(left, right) = current else {
            return None;
        };
        current = match direction {
            0 => left,
            1 => right,
            _ => return None,
        };
    }
    Some(current)
}

pub(super) fn projection_leaf_for_extract<'a>(
    leaves: &'a [ChosenProjectionLeaf],
    surface: &ClickProposition,
    chosen_body: &Proposition,
    source_id: &RequirementSourceId,
) -> Option<&'a ChosenProjectionLeaf> {
    let mut matching = leaves.iter().filter(|leaf| leaf.surface == *surface);
    let leaf = matching.next()?;
    if matching.next().is_some()
        || leaf.source_token.source_id != *source_id
        || proposition_at_connective_path(chosen_body, &leaf.source_token.connective_path)
            != Some(&leaf.kernel)
    {
        return None;
    }
    Some(leaf)
}

#[cfg(test)]
mod projection_path_tests {
    use super::*;

    fn source_id() -> RequirementSourceId {
        RequirementSourceId {
            owner: CallerSourceOwnerId::ordinary("path-test.c", "f"),
            outer_ordinal: 0,
        }
    }

    fn surface_leaf() -> ClickProposition {
        ClickProposition::Comparison {
            left: ContractExpression::ProgramExpression(ProgramExpression::Value(
                ProgramValue::Int32(MachineTerm::constant(0)),
            )),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::ProgramExpression(ProgramExpression::Value(
                ProgramValue::Int32(MachineTerm::constant(0)),
            )),
        }
    }

    fn kernel_leaf(value: bool) -> Proposition {
        Proposition::ConditionIs(ConditionTerm::Constant(value), true)
    }

    fn leaf(id: RequirementSourceId, path: Vec<usize>, value: bool) -> ChosenProjectionLeaf {
        ChosenProjectionLeaf {
            source_token: ProjectionSourceToken {
                source_id: id,
                connective_path: path,
            },
            surface: surface_leaf(),
            kernel: kernel_leaf(value),
        }
    }

    #[test]
    fn projection_paths_are_iterative_and_fail_closed() {
        let left = kernel_leaf(true);
        let middle = kernel_leaf(false);
        let right = kernel_leaf(true);
        let body = Proposition::And(
            Box::new(Proposition::And(
                Box::new(left.clone()),
                Box::new(middle.clone()),
            )),
            Box::new(right.clone()),
        );
        assert_eq!(
            proposition_at_connective_path(&body, &[0, 1]),
            Some(&middle)
        );
        assert_eq!(proposition_at_connective_path(&body, &[1]), Some(&right));
        assert_eq!(proposition_at_connective_path(&body, &[2]), None);
        assert_eq!(proposition_at_connective_path(&body, &[0, 0, 0]), None);
    }

    #[test]
    fn projection_leaf_selection_rejects_duplicate_surface_and_bad_tokens() {
        let id = source_id();
        let body = Proposition::And(Box::new(kernel_leaf(true)), Box::new(kernel_leaf(true)));
        let duplicate = vec![
            leaf(id.clone(), vec![0], true),
            leaf(id.clone(), vec![1], true),
        ];
        assert!(projection_leaf_for_extract(&duplicate, &surface_leaf(), &body, &id).is_none());

        let malformed_path = vec![leaf(id.clone(), vec![2], true)];
        assert!(
            projection_leaf_for_extract(&malformed_path, &surface_leaf(), &body, &id).is_none()
        );
        let wrong_id = RequirementSourceId {
            outer_ordinal: 1,
            ..id.clone()
        };
        let wrong_token = vec![leaf(wrong_id, vec![0], true)];
        assert!(projection_leaf_for_extract(&wrong_token, &surface_leaf(), &body, &id).is_none());
    }
}

/// A source-sized decision graph. Both arms point to the shared continuation;
/// walking an arm never visits the syntax or outcomes of its sibling.
type OutcomeBindings = PersistentMap<String, ContractExpression>;

// Nodes select their lexical match by source occurrence. Shared continuation
// nodes keep their enclosing scope, so arm bindings cannot escape the arm.

struct OutcomeCase<'a> {
    scope: Option<usize>,
    lexical_bindings: Option<&'a OutcomeBindings>,
    occurrence: usize,
    fingerprint: u64,
    condition: &'a ClickProposition,
    /// `condition` is a `cases` disjunction whose two sides the arms take,
    /// rather than an `if` condition and its negation.
    disjunction: bool,
    execution_route: Option<usize>,
    arms: [Option<usize>; 2],
}

/// A constructor `match` in the decision graph: each live constructor case
/// takes the arm written for it.
struct OutcomeMatch<'a> {
    scope: Option<usize>,
    lexical_bindings: Option<&'a OutcomeBindings>,
    occurrence: usize,
    source: &'a ProofMatch,
    arms: Vec<Option<usize>>,
}

enum OutcomeNode<'a> {
    Have {
        scope: Option<usize>,
        occurrence: usize,
        source: &'a DeferredPostExecutionTactic,
        next: Option<usize>,
    },
    Case(OutcomeCase<'a>),
    Match(OutcomeMatch<'a>),
}

fn outcome_case_region<'a>(
    tactics: &'a [DeferredPostExecutionTactic],
    next: Option<usize>,
    nodes: &mut Vec<OutcomeNode<'a>>,
) -> Option<usize> {
    outcome_case_region_in_scope(tactics, next, nodes, None)
}

fn outcome_case_region_in_scope<'a>(
    tactics: &'a [DeferredPostExecutionTactic],
    mut next: Option<usize>,
    nodes: &mut Vec<OutcomeNode<'a>>,
    scope: Option<usize>,
) -> Option<usize> {
    for tactic in tactics.iter().rev() {
        match &tactic.tactic {
            PostExecutionTactic::If {
                condition,
                disjunction,
                execution_route,
                then_tactics,
                else_tactics,
            } => {
                let arms = [
                    outcome_case_region_in_scope(then_tactics, next, nodes, scope),
                    outcome_case_region_in_scope(else_tactics, next, nodes, scope),
                ];
                nodes.push(OutcomeNode::Case(OutcomeCase {
                    scope,
                    lexical_bindings: tactic.lexical_bindings.as_ref(),
                    occurrence: tactic.source_index,
                    fingerprint: ExecutionBranchDecisions::key(condition),
                    condition,
                    disjunction: *disjunction,
                    execution_route: *execution_route,
                    arms,
                }));
                next = Some(nodes.len() - 1);
            }
            PostExecutionTactic::Match { source, arms } => {
                let arms = arms
                    .iter()
                    .map(|arm| {
                        outcome_case_region_in_scope(arm, next, nodes, Some(tactic.source_index))
                    })
                    .collect();
                nodes.push(OutcomeNode::Match(OutcomeMatch {
                    scope,
                    lexical_bindings: tactic.lexical_bindings.as_ref(),
                    occurrence: tactic.source_index,
                    source,
                    arms,
                }));
                next = Some(nodes.len() - 1);
            }
            PostExecutionTactic::Have(_) if next.is_some() => {
                nodes.push(OutcomeNode::Have {
                    scope,
                    occurrence: tactic.source_index,
                    source: tactic,
                    next,
                });
                next = Some(nodes.len() - 1);
            }
            _ => {}
        }
    }
    next
}

/// Where one path's constructor cases for a deferred `match` come from:
/// given the match, the path's query facts and the authority facts, the
/// checked partition of the scrutinee's value on the path and each written
/// arm's case and bindings.
type OutcomeMatchPartition<'f> = dyn Fn(
        &ProofMatch,
        &ProofFacts,
        &ProofFacts,
        Option<&OutcomeBindings>,
    ) -> Result<super::match_cases::OutcomeMatchCases, ClickError>
    + 'f;

/// Partitions one path at a deferred `match`: the path's scrutinee value
/// splits into the live constructor cases, and each case continues in the
/// arm written for it, with that arm and its bindings recorded on the path.
#[allow(clippy::too_many_arguments)]
fn partition_outcome_match(
    nodes: &[OutcomeNode<'_>],
    node: &OutcomeMatch<'_>,
    authority: &ProofFacts,
    query: &ProofFacts,
    facts: &mut Vec<Proposition>,
    provenance: OutcomeProvenance,
    lower: &impl Fn(
        &ClickProposition,
        &[Proposition],
        Option<&OutcomeBindings>,
    ) -> Result<Proposition, ClickError>,
    match_cases: &OutcomeMatchPartition<'_>,
    prove: &impl Fn(
        &ClickProposition,
        Option<&DeferredPostExecutionTactic>,
        &ProofFacts,
        &OutcomeProvenance,
        Option<&OutcomeBindings>,
    ) -> Result<(Proposition, ProofCertificate), ClickError>,
    emit: &mut impl FnMut(&[Proposition], OutcomeProvenance),
) -> Result<OutcomeEvidenceFork, ClickError> {
    let bindings = node.lexical_bindings.or_else(|| {
        node.scope.and_then(|scope| {
            provenance
                .match_arms
                .get(&scope)
                .map(|(_, bindings)| bindings)
        })
    });
    let cases = match_cases(node.source, query, authority, bindings)?;
    let mut arms = Vec::new();
    for case in cases.partition.live_cases() {
        let (written, (_, bindings)) = cases
            .arms
            .iter()
            .enumerate()
            .find(|(_, (arm_case, _))| *arm_case == case)
            .ok_or_else(|| ClickError::new("a `match` constructor case has no written arm"))?;
        let arm_facts = cases
            .partition
            .facts_for_case(case)
            .ok_or_else(|| ClickError::new("a `match` constructor case has no facts"))?;
        let added = cases
            .partition
            .case_fact(case)
            .into_iter()
            .chain(cases.partition.additions_for_case(case))
            .cloned()
            .collect::<Vec<_>>();
        let mut child = provenance.clone();
        child.match_arms = child
            .match_arms
            .with_inserted(node.occurrence, (written, bindings.clone()));
        let arm_query = added.iter().fold(query.clone(), |query, fact| {
            query.with_kernel_checked_fact(fact.clone())
        });
        let old_len = facts.len();
        facts.extend(added);
        let then = partition_outcome_cases(
            nodes,
            node.arms[written],
            &arm_facts,
            &arm_query,
            facts,
            child,
            lower,
            match_cases,
            prove,
            emit,
        );
        facts.truncate(old_len);
        arms.push(OutcomeForkArm {
            case,
            facts: arm_facts,
            then: then?,
        });
    }
    Ok(OutcomeEvidenceFork::Split {
        partition: cases.partition,
        arms,
    })
}

/// The case one arm of a post-execution split stands for, as it records it
/// on the path: an `if` arm records its condition's polarity, a `cases` arm
/// that its own disjunct holds.
struct OutcomeArmCase<'a> {
    surface: &'a ClickProposition,
    lowered: &'a Proposition,
    value: bool,
}

#[allow(clippy::too_many_arguments)]
fn descend_outcome_case(
    nodes: &[OutcomeNode<'_>],
    node: &OutcomeCase<'_>,
    arm_case: OutcomeArmCase<'_>,
    take_then: bool,
    authority: &ProofFacts,
    query: &ProofFacts,
    facts: &mut Vec<Proposition>,
    provenance: OutcomeProvenance,
    fact: Option<Proposition>,
    lower: &impl Fn(
        &ClickProposition,
        &[Proposition],
        Option<&OutcomeBindings>,
    ) -> Result<Proposition, ClickError>,
    match_cases: &OutcomeMatchPartition<'_>,
    prove: &impl Fn(
        &ClickProposition,
        Option<&DeferredPostExecutionTactic>,
        &ProofFacts,
        &OutcomeProvenance,
        Option<&OutcomeBindings>,
    ) -> Result<(Proposition, ProofCertificate), ClickError>,
    emit: &mut impl FnMut(&[Proposition], OutcomeProvenance),
) -> Result<OutcomeEvidenceFork, ClickError> {
    let mut child = provenance;
    child.branch_decisions.push(ExecutionBranchDecision {
        fingerprint: std::sync::OnceLock::from(ExecutionBranchDecisions::key(arm_case.surface)),
        condition: arm_case.surface.clone(),
        value: arm_case.value,
    });
    child
        .surface_propositions
        .record_lowering(arm_case.surface, arm_case.lowered)?;
    let old_len = facts.len();
    if let Some(fact) = fact {
        facts.push(fact);
    }
    let result = partition_outcome_cases(
        nodes,
        node.arms[usize::from(!take_then)],
        authority,
        query,
        facts,
        child,
        lower,
        match_cases,
        prove,
        emit,
    );
    facts.truncate(old_len);
    result
}

#[allow(clippy::too_many_arguments)]
fn partition_outcome_cases(
    nodes: &[OutcomeNode<'_>],
    next: Option<usize>,
    authority: &ProofFacts,
    query: &ProofFacts,
    facts: &mut Vec<Proposition>,
    provenance: OutcomeProvenance,
    lower: &impl Fn(
        &ClickProposition,
        &[Proposition],
        Option<&OutcomeBindings>,
    ) -> Result<Proposition, ClickError>,
    match_cases: &OutcomeMatchPartition<'_>,
    prove: &impl Fn(
        &ClickProposition,
        Option<&DeferredPostExecutionTactic>,
        &ProofFacts,
        &OutcomeProvenance,
        Option<&OutcomeBindings>,
    ) -> Result<(Proposition, ProofCertificate), ClickError>,
    emit: &mut impl FnMut(&[Proposition], OutcomeProvenance),
) -> Result<OutcomeEvidenceFork, ClickError> {
    // Flat source haves are a sequence, not nested proof branches. Consume
    // them iteratively so a long explicit certificate does not grow the stack.
    // The enclosing arm owns the facts buffer's push/pop boundary.
    let mut next = next;
    let mut provenance = provenance;
    let mut authority = authority.clone();
    let mut query = query.clone();
    let index = loop {
        check_verification_deadline()?;
        let Some(index) = next else {
            emit(facts, provenance);
            return Ok(OutcomeEvidenceFork::Keep);
        };
        let OutcomeNode::Have {
            scope,
            occurrence,
            source,
            next: continuation,
        } = &nodes[index]
        else {
            break index;
        };
        next = *continuation;
        if provenance.checked_haves.get(occurrence).is_some() {
            continue;
        }
        let PostExecutionTactic::Have(have) = &source.tactic else {
            unreachable!("a have node retains its source have")
        };
        let bindings = scope.and_then(|scope| {
            provenance
                .match_arms
                .get(&scope)
                .map(|(_, bindings)| bindings)
        });
        let (kernel, checked) = prove(
            &have.proposition,
            Some(source),
            &query,
            &provenance,
            bindings,
        )?;
        provenance
            .surface_propositions
            .record_lowering(&have.proposition, &kernel)?;
        provenance.checked_haves = provenance
            .checked_haves
            .with_inserted(*occurrence, Arc::new(checked));
        facts.push(kernel.clone());
        authority = authority.with_kernel_checked_fact(kernel.clone());
        query = query.with_kernel_checked_fact(kernel);
    };
    let authority = &authority;
    let query = &query;
    let node = match &nodes[index] {
        OutcomeNode::Have { .. } => unreachable!("the linear prefix was consumed"),
        OutcomeNode::Case(node) => node,
        OutcomeNode::Match(node) => {
            return partition_outcome_match(
                nodes,
                node,
                authority,
                query,
                facts,
                provenance,
                lower,
                match_cases,
                prove,
                emit,
            );
        }
    };
    // Retained C and proof case decisions already choose this source arm.
    // Consult them at every nested node, not only at the root: re-lowering
    // a short-circuit condition can otherwise lose its checked truth value
    // and fork an inconsistent descendant. A `cases` arm recorded that its
    // own disjunct holds.
    let arm_surfaces = if node.disjunction {
        let Some((left, right)) = crate::surface::split_case_disjunction(node.condition) else {
            return Err(ClickError::new(
                "a post-execution `cases` split is not on a disjunction",
            ));
        };
        Some([left, right])
    } else {
        None
    };
    let recorded = match (node.execution_route, &arm_surfaces) {
        (Some(position), _) => Some(
            provenance
                .branch_decisions
                .value_for_route(position, node.condition)?,
        ),
        (None, None) => provenance
            .branch_decisions
            .value_for_key(node.condition, node.fingerprint)?,
        (None, Some([left, right])) => {
            let holds = |surface: &ClickProposition| {
                provenance
                    .branch_decisions
                    .value_for_key(surface, ExecutionBranchDecisions::key(surface))
                    .map(|value| value == Some(true))
            };
            if holds(left)? {
                Some(true)
            } else if holds(right)? {
                Some(false)
            } else {
                None
            }
        }
    };
    if let Some(value) = recorded {
        return partition_outcome_cases(
            nodes,
            node.arms[usize::from(!value)],
            authority,
            query,
            facts,
            provenance,
            lower,
            match_cases,
            prove,
            emit,
        );
    }
    let bindings = node.lexical_bindings.or_else(|| {
        node.scope.and_then(|scope| {
            provenance
                .match_arms
                .get(&scope)
                .map(|(_, bindings)| bindings)
        })
    });
    let lowered = lower(node.condition, facts, bindings)?;
    // The two cases: an `if` condition and its negation, or the two sides
    // of the `cases` disjunction as it lowered.
    let negated_surface;
    let (cases, case_surfaces) = match &arm_surfaces {
        None => {
            negated_surface = ClickProposition::Not(Box::new(node.condition.clone()));
            (
                [
                    crate::kernel::canonical_condition_fact(&lowered),
                    crate::kernel::canonical_condition_fact(&Proposition::Not(Box::new(
                        lowered.clone(),
                    ))),
                ],
                [node.condition, &negated_surface],
            )
        }
        Some([left, right]) => {
            let Proposition::Or(left_fact, right_fact) = &lowered else {
                return Err(ClickError::new(
                    "a post-execution `cases` disjunction did not lower to a disjunction",
                ));
            };
            (
                [left_fact.as_ref().clone(), right_fact.as_ref().clone()],
                [left, right],
            )
        }
    };
    let arm_case = |index: usize| match &arm_surfaces {
        None => OutcomeArmCase {
            surface: node.condition,
            lowered: &lowered,
            value: index == 0,
        },
        Some(_) => OutcomeArmCase {
            surface: case_surfaces[index],
            lowered: &cases[index],
            value: true,
        },
    };
    let decided = |fact: &Proposition| {
        crate::kernel::proof::fact_reasoning::holds_by_lookup_or_decision(query.assumptions(), fact)
    };
    // A case the path's facts already decide selects its arm. For `cases`
    // that is a disjunct the facts establish.
    let known = if decided(&cases[0]) {
        Some(true)
    } else if decided(&cases[1]) {
        Some(false)
    } else {
        None
    };
    if let Some(take_then) = known {
        let index = usize::from(!take_then);
        return descend_outcome_case(
            nodes,
            node,
            arm_case(index),
            take_then,
            authority,
            query,
            facts,
            provenance,
            None,
            lower,
            match_cases,
            prove,
            emit,
        );
    }
    // Prove exhaustiveness before introducing either arm's assumption.
    // The driver retains the ordinary nested proof for source expansion.
    let existing_partition =
        CheckedProofCasePartition::check(authority, cases[0].clone(), cases[1].clone());
    let mut provenance = provenance;
    let proved_authority;
    let proved_query;
    let (authority, query) = if node.disjunction && existing_partition.is_none() {
        let bindings = node.lexical_bindings.or_else(|| {
            node.scope.and_then(|scope| {
                provenance
                    .match_arms
                    .get(&scope)
                    .map(|(_, bindings)| bindings)
            })
        });
        let (kernel, have) = prove(node.condition, None, query, &provenance, bindings)?;
        provenance
            .surface_propositions
            .record_lowering(node.condition, &kernel)?;
        provenance.case_obligations = provenance
            .case_obligations
            .with_inserted(node.occurrence, Arc::new(have));
        facts.push(kernel.clone());
        proved_authority = authority.with_kernel_checked_fact(kernel.clone());
        proved_query = query.with_kernel_checked_fact(kernel);
        (&proved_authority, &proved_query)
    } else {
        (authority, query)
    };
    let [positive, negative] = cases.clone();
    let partition = existing_partition.or_else(|| {
        CheckedProofCasePartition::check(authority, positive.clone(), negative.clone())
    })
        .ok_or_else(|| {
            ClickError::new(match &arm_surfaces {
                None => "post-execution case split did not produce complementary case facts"
                    .to_string(),
                Some(_) => format!(
                    "`cases` after execution requires its exact disjunction as an available fact on each outcome path: `{}`",
                    crate::surface::diagnostics::describe_click_proposition(node.condition)
                ),
            })
        })?;
    let arm_facts = [
        authority.with_kernel_checked_fact(positive.clone()),
        authority.with_kernel_checked_fact(negative.clone()),
    ];
    let then_arm = descend_outcome_case(
        nodes,
        node,
        arm_case(0),
        true,
        &arm_facts[0],
        &query.with_kernel_checked_fact(positive.clone()),
        facts,
        provenance.clone(),
        Some(positive),
        lower,
        match_cases,
        prove,
        emit,
    )?;
    let else_arm = descend_outcome_case(
        nodes,
        node,
        arm_case(1),
        false,
        &arm_facts[1],
        &query.with_kernel_checked_fact(negative.clone()),
        facts,
        provenance,
        Some(negative),
        lower,
        match_cases,
        prove,
        emit,
    )?;
    Ok(OutcomeEvidenceFork::binary(
        partition,
        arm_facts,
        [then_arm, else_arm],
    ))
}

/// An instantiated application whose arguments and conclusions are retained.
/// Only the driver may publish it, after proving its collected prerequisites.
pub(in crate::surface::proof) struct PreparedTheoremApplication {
    conclusions: Vec<Proposition>,
    pub(in crate::surface::proof) obligations: Vec<UnresolvedRequirement>,
}

impl<'a> Proof<'a> {
    pub(super) fn apply_theorem_using(
        &self,
        application: &TheoremApplication,
        surface_premises: &[ClickProposition],
    ) -> Result<CheckedFocusedTransition, ClickError> {
        #[cfg(test)]
        let _operation = crate::kernel::search::FastOperationScope::enter("apply_theorem_using");
        let resolved_application = self.resolve_theorem_application(application)?;
        let surface_premises = surface_premises
            .iter()
            .map(|premise| self.substitute_fixed_state_locals_in_proposition(premise))
            .collect::<Result<Vec<_>, _>>()?;
        crate::surface::proof::theorem_application::with_application_source(application, || {
            match self.context.as_ref() {
                ProofContext::Pure(context) => {
                    self.apply_pure_theorem_using(context, &resolved_application, &surface_premises)
                }
                ProofContext::FixedState(context) => self.apply_fixed_state_theorem_using(
                    &FixedStateOperationView::from_fixed_state(context),
                    &resolved_application,
                    &surface_premises,
                ),
                // A focused branch function-outcome goal applies theorems through the
                // fixed-state checker, reading its data from the goal; the effect
                // context is the frontier-wide set required by theorem checking.
                ProofContext::Execution(_) if self.focused_outcome_data().is_some() => {
                    let view = self
                        .outcome_fixed_state_view_with_effects(OutcomeEffectContext::Frontier)
                        .expect("a focused outcome judgment resolves its fixed-state view");
                    self.apply_fixed_state_theorem_using(
                        &view,
                        &resolved_application,
                        &surface_premises,
                    )
                }
                ProofContext::Execution(context) => self.apply_execution_theorem_using(
                    context,
                    &resolved_application,
                    &surface_premises,
                ),
            }
        })
    }

    pub(in crate::surface::proof) fn prepare_theorem_application(
        &self,
        application: &TheoremApplication,
    ) -> Result<PreparedTheoremApplication, ClickError> {
        #[cfg(test)]
        let _operation =
            crate::kernel::search::FastOperationScope::enter("prepare_theorem_application");
        if matches!(self.context.as_ref(), ProofContext::Execution(_))
            && self.is_at_function_exit()
            && self.focused_outcome_data().is_none()
        {
            return Err(self.step_error("returned theorem applications require an outcome proof"));
        }
        let (prepared, probe) =
            crate::surface::proof::execution_planning::probe_step_obligations(|| {
                crate::surface::proof::theorem_application::with_application_preparation(|| {
                    self.apply_theorem_using(application, &[])
                })
            });
        Ok(PreparedTheoremApplication {
            conclusions: prepared?.checked_facts,
            obligations: probe.recorded,
        })
    }

    pub(in crate::surface::proof) fn finish_prepared_theorem_application(
        &self,
        prepared: PreparedTheoremApplication,
        application: &TheoremApplication,
        premises: Vec<ClickProposition>,
    ) -> Result<Self, ClickError> {
        #[cfg(test)]
        let _operation =
            crate::kernel::search::FastOperationScope::enter("finish_prepared_theorem_application");
        let mut facts = self.facts().clone();
        let mut added = Vec::new();
        for conclusion in &prepared.conclusions {
            if !facts.contains(conclusion) {
                added.push(conclusion.clone());
            }
            facts = facts.with_kernel_checked_fact(conclusion.clone());
        }
        let complete = self.goal().is_some_and(|goal| {
            facts.introduced_goal_available(goal)
                || listed_equality_fact_is_available(goal, &prepared.conclusions)
        });
        let transition = self.checked_fact_transition(
            self.state().locals().clone(),
            facts,
            complete,
            added,
            prepared.conclusions,
        );
        let state = self.publish_checked_transition(transition)?;
        Ok(Self {
            site: self.site.clone(),
            context: self.context.clone(),
            state,
            node: ProofNode::step_child(
                &self.node,
                self.focused_branch_id(),
                Arc::new(ProofStep::ApplyTheoremUsing {
                    application: application.clone(),
                    premises,
                }),
            ),
        })
    }

    pub(super) fn apply_pure_theorem_using(
        &self,
        context: &PureProofContext<'_>,
        application: &TheoremApplication,
        surface_premises: &[ClickProposition],
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let lowered_premises = surface_premises
            .iter()
            .map(|premise| self.lower_surface_proposition(premise, "`apply using` premise"))
            .collect::<Result<Vec<_>, _>>()?;

        let mut explicit_premises = Vec::new();
        for (premise, surface) in lowered_premises.iter().zip(surface_premises) {
            if !self.facts().listed_premise_available(premise, &[], false) {
                return Err(self.step_error(format!(
                    "`apply using` requires an unavailable exact premise: `{}`",
                    crate::surface::diagnostics::describe_click_proposition(surface)
                )));
            }
            // Citing a stated range cites both of its halves, exactly as in
            // a fixed-state `apply using`.
            crate::surface::proof::theorem_application::cite_range_extent_guards(
                premise,
                &mut explicit_premises,
                |guard| self.facts().exact_available_across_effects(guard, &[]),
            );
            if !explicit_premises.contains(premise) {
                explicit_premises.push(premise.clone());
            }
        }

        // The checker receives exactly the named premises, not the ambient
        // context. Its work is therefore independent of unrelated facts, and
        // it cannot silently search for an omitted theorem requirement.
        let state = ExecutionState::new().with_memory(context.theorem_context.memory.clone());
        let recorded_states = RecordedStates::new();
        let mut integer_values = context.theorem_context.integer_values.clone();
        for name in application
            .arguments
            .iter()
            .flat_map(contract_expression_referenced_names)
            .collect::<BTreeSet<_>>()
        {
            if let Some(value) = self.local_integer_values().get(&name) {
                integer_values = integer_values.with_inserted(name, value.clone());
            }
        }
        let algebraic_values = application
            .arguments
            .iter()
            .flat_map(contract_expression_referenced_names)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .filter_map(|name| {
                self.local_algebraic_values()
                    .get(&name)
                    .cloned()
                    .or_else(|| {
                        context
                            .structural_induction_setup
                            .as_ref()?
                            .algebraic_values
                            .get(&name)
                            .cloned()
                    })
                    .map(|value| (name, value))
            })
            .collect();
        let application_context = TheoremApplicationContext {
            values: &context.theorem_context.values,
            array_refs: &context.theorem_context.array_refs,
            algebraic_values: &algebraic_values,
            pre_state: &state,
            post_state: &state,
            result: None,
            recorded_states: &recorded_states,
            integer_values: &integer_values,
            pointer_element_widths: BTreeMap::new(),
        };
        let unfolded_predicates = self.active_unfolded_predicates();
        let explicit_premises = unfold_available_predicate_facts(
            context.spec_definitions,
            &unfolded_predicates,
            &explicit_premises,
        )
        .map_err(|message| self.step_error(message))?;
        // An explicit `using` list supplies both argument-domain evidence
        // and the theorem's premises; omitted guards cannot leak in from
        // the surrounding proof context.
        let lowering_assumptions =
            if crate::surface::proof::theorem_application::preparing_application() {
                self.facts()
                    .assumptions()
                    .clone()
                    .retaining_argument_obligations()
            } else {
                assumptions_from_propositions(&explicit_premises)
            };
        let applied = instantiate_theorem_application_with_assumptions(
            context.theorem_environment,
            application,
            context.claim_label,
            None,
            self.node.depth,
            &explicit_premises,
            &lowering_assumptions,
            &application_context,
            context.spec_definitions,
            &unfolded_predicates,
        )?;

        let mut facts = self.facts().clone();
        let mut added_facts = Vec::new();
        for fact in &applied {
            if !facts.contains(fact) {
                added_facts.push(fact.clone());
            }
            facts = facts.with_kernel_checked_fact(fact.clone());
        }
        // Only the selected theorem's checked conclusions participate in
        // this representation bridge; ambient candidate matching stays unchanged.
        let complete = self.goal().is_some_and(|goal| {
            facts.introduced_goal_available(goal)
                || listed_equality_fact_is_available(goal, &applied)
        });
        Ok(self.checked_fact_transition(
            self.state().locals().clone(),
            facts,
            complete,
            added_facts,
            applied,
        ))
    }

    pub(super) fn apply_fixed_state_theorem_using(
        &self,
        view: &FixedStateOperationView<'_>,
        application: &TheoremApplication,
        surface_premises: &[ClickProposition],
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let unfolded_predicates = self.active_unfolded_predicates();
        let algebraic_values = application
            .arguments
            .iter()
            .flat_map(contract_expression_referenced_names)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .filter_map(|name| {
                self.local_algebraic_values()
                    .get(&name)
                    .cloned()
                    .map(|value| (name, value))
            })
            .collect();
        let checked = check_fixed_state_theorem_application_using_facts(
            view.theorem_environment,
            application,
            surface_premises,
            view.claim_label,
            view.tactic_index,
            self.facts(),
            view.parameter_binding,
            view.fixed_state,
            &self.local_integer_values(),
            &algebraic_values,
            view.surface_propositions,
            &unfolded_predicates,
            view.effect_facts,
            view.spec_definitions,
        )?;
        let complete = self.goal().is_some_and(|goal| {
            checked.facts.introduced_goal_available(goal)
                || listed_equality_fact_is_available(goal, &checked.checked_facts)
        });
        Ok(self.checked_fact_transition(
            self.state().locals().clone(),
            checked.facts,
            complete,
            checked.added_facts,
            checked.checked_facts,
        ))
    }

    pub(super) fn apply_execution_theorem_using(
        &self,
        context: &ExecutionProofContext<'a>,
        application: &TheoremApplication,
        surface_premises: &[ClickProposition],
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let pre_state = context
            .old_reference_state(&execution.core.frontier, &execution.core.state)
            .clone();
        let algebraic_values = application
            .arguments
            .iter()
            .flat_map(contract_expression_referenced_names)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .filter_map(|name| {
                self.local_algebraic_values()
                    .get(&name)
                    .cloned()
                    .map(|value| (name, value))
            })
            .collect();
        let checked = check_fixed_state_theorem_application_using_facts(
            context.theorem_environment,
            application,
            surface_premises,
            context.claim_label,
            context.tactic_index,
            self.facts(),
            context.parameter_binding(),
            FixedStateFrame::new(
                &pre_state,
                &execution.core.state,
                None,
                &execution.presentation.recorded_states,
            ),
            &self.local_integer_values(),
            &algebraic_values,
            &execution.presentation.surface_propositions,
            &execution.core.unfolded_predicates,
            &execution.core.effect_facts,
            context.spec_definitions,
        )?;
        let complete = self.goal().is_some_and(|goal| {
            checked.facts.introduced_goal_available(goal)
                || listed_equality_fact_is_available(goal, &checked.checked_facts)
        });
        Ok(self.checked_execution_transition(
            checked.facts,
            complete,
            execution,
            checked.added_facts,
            checked.checked_facts,
        ))
    }

    pub(super) fn apply_fixed_state_choose(
        &self,
        choice: &ProofChoice,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        if let ProofContext::Pure(context) = self.context.as_ref() {
            let index = match &choice.source {
                ProofFactSource::Requirement(index) => *index,
                ProofFactSource::Invariant(_) => {
                    return Err(
                        self.step_error("pure `choose` does not have a loop invariant source")
                    );
                }
            };
            if matches!(
                context.theorem_context.requires.get(index),
                Some(Proposition::Exists {
                    sort: Sort::Algebraic(_),
                    ..
                })
            ) {
                return self.apply_pure_algebraic_choose(choice);
            }
            return self.apply_pure_integer_choose(choice);
        }
        let frontier = matches!(self.focused_obligation(), Some(Obligation::Frontier(_)));
        let view = match self.context.as_ref() {
            ProofContext::FixedState(context) => FixedStateOperationView::from_fixed_state(context),
            // A choice on a judgment stated at a function outcome selects
            // its requirement source through the outcome view.
            ProofContext::Execution(_) if self.focused_outcome_data().is_some() => self
                .outcome_fixed_state_view()
                .expect("a focused outcome judgment resolves its fixed-state view"),
            ProofContext::Execution(_) if frontier => self
                .execution_frontier_fixed_state_view()
                .expect("a focused execution frontier resolves its fixed-state view"),
            ProofContext::Execution(_) => self
                .execution_proposition_fixed_state_view()
                .ok_or_else(|| {
                    self.step_error("`choose` requires a fixed-state proposition proof")
                })?,
            _ => return Err(self.step_error("`choose` requires a fixed-state proposition proof")),
        };
        if !frontier {
            self.proposition_goal("`choose` requires a proposition goal")?;
        }
        if choice.name == "result"
            || view.fixed_state.state.locals().contains_name(&choice.name)
            || self.state().locals().values.contains_key(&choice.name)
        {
            return Err(self.step_error(format!("`{}` is already in scope", choice.name)));
        }

        if let ProofFactSource::Invariant(index) = choice.source {
            return self.apply_fixed_state_invariant_choose(choice, &view, index);
        }

        let source_ordinal = match &choice.source {
            ProofFactSource::Requirement(index) => {
                if *index >= view.original_requirements.len() {
                    return Err(self.step_error(format!(
                        "requirement {index} is out of range; function has {} requirement(s)",
                        view.original_requirements.len()
                    )));
                }
                *index
            }
            ProofFactSource::Invariant(_) => unreachable!("handled above"),
        };
        // A caller source always names the immutable entry vector from which
        // its principal fact index was minted, including at function exit.
        let caller_requirement_facts: Option<&[Proposition]> = match self.context.as_ref() {
            ProofContext::Execution(context) => {
                Some(context.constants.execution_start_facts.as_slice())
            }
            _ => None,
        };
        let source_facts =
            caller_requirement_facts.unwrap_or_else(|| view.requirement_facts.as_slice());
        let source_selection = match self.context.as_ref() {
            ProofContext::Execution(context) => {
                let owner = context
                    .constants
                    .caller_source_owner
                    .as_ref()
                    .ok_or_else(|| {
                        self.step_error("`choose` source has no ordinary caller identity")
                    })?;
                let source_id = RequirementSourceId {
                    owner: owner.clone(),
                    outer_ordinal: source_ordinal,
                };
                let selection = context
                    .constants
                    .caller_requirement_index
                    .lookup_source_requirement(&source_id)
                    .ok_or_else(|| {
                        self.step_error(format!(
                            "requirement {source_ordinal} has no unique principal entry fact"
                        ))
                    })?;
                if selection.source_id != source_id
                    || selection.principal_fact_index >= source_facts.len()
                    || source_facts.get(selection.principal_fact_index)
                        != Some(&selection.principal_fact)
                {
                    return Err(self.step_error(format!(
                        "requirement {source_ordinal} does not match its retained entry fact"
                    )));
                }
                let Some(entry_state) = context.constants.function_entry_state.as_ref() else {
                    return Err(self.step_error("`choose` source has no function-entry state"));
                };
                if selection.entry_memory_state
                    != crate::kernel::MemoryStateIdentity::of(entry_state.memory())
                {
                    return Err(self.step_error(format!(
                        "requirement {source_ordinal} does not match the function-entry state"
                    )));
                }
                Some(selection)
            }
            // Standalone fixed-state proofs have no ordinary caller owner.
            // Their existing direct requirement vector remains authoritative;
            // they cannot create a retained execution projection.
            _ => None,
        };
        let source_fact_index = source_selection
            .as_ref()
            .map_or(source_ordinal, |selection| selection.principal_fact_index);
        let mut source = source_facts
            .get(source_fact_index)
            .cloned()
            .ok_or_else(|| {
                self.step_error(format!("requirement {source_ordinal} was not available"))
            })?;
        let unfolded_predicates = self.active_unfolded_predicates();
        if !matches!(source, Proposition::Exists { .. }) && !unfolded_predicates.is_empty() {
            source = unfold_predicates_in_proposition(
                view.spec_definitions,
                &unfolded_predicates,
                &source,
                self.facts().assumptions(),
            )
            .map_err(|message| self.step_error(message))?;
        }
        let checked_source = source.clone();
        let Proposition::Exists {
            var, sort, body, ..
        } = source
        else {
            return Err(self.step_error("`choose` source is not an existential proposition"));
        };
        let chosen_variable = self
            .state
            .fresh_existential_witness(&body, Variable(self.state().locals().next_choice_variable))
            .map_err(|_| self.step_error("`choose` could not allocate a fresh witness"))?;
        let chosen = match sort {
            sort if sort.machine_integer_type().is_some() => sort
                .machine_integer_type()
                .unwrap()
                .symbolic_value(chosen_variable),
            sort if sort.pointer_type().is_some() => sort
                .symbolic_pointer_value(chosen_variable)
                .expect("pointer choice sort"),
            _ => return Err(self.step_error("unsupported existential choice sort")),
        };
        let chosen_fact = match &chosen {
            crate::kernel::integer_c_value!(value) => {
                substitute_int32_variable_in_proposition(&body, var, value.clone())
            }
            ProgramValue::Pointer(pointer) => {
                crate::kernel::substitute_pointer_value_in_proposition(&body, var, pointer)
                    .map_err(|error| self.step_error(&error))?
            }
            _ => unreachable!("unsupported choice sort above"),
        };
        let mut locals = self.state().locals().clone();
        locals.set_values(locals.values.with_inserted(
            choice.name.clone(),
            ContractExpression::ProgramExpression(ProgramExpression::Value(chosen.clone())),
        ));
        locals.next_choice_variable = chosen_variable.0.saturating_add(1);
        let added_facts = if self.facts().contains_top_level(&chosen_fact) {
            Vec::new()
        } else {
            vec![chosen_fact.clone()]
        };
        let facts = self
            .facts()
            .with_kernel_checked_fact(chosen_fact.clone())
            .with_reserved_variables([chosen_variable]);
        let mut transition =
            self.checked_fact_transition(locals, facts, false, added_facts, vec![chosen_fact]);
        if let Some(projection) = self.build_chosen_projection(
            &view,
            source_facts
                .get(source_fact_index)
                .expect("validated requirement source index")
                .clone(),
            checked_source,
            source_selection.as_ref(),
            chosen_variable,
            choice,
            &chosen,
        )? && let Some(branch) = transition.branch.as_mut()
            && let Some(execution) = branch.state.execution.as_deref()
        {
            let mut execution = execution.clone();
            execution.presentation.chosen_projection = Some(projection);
            branch.state.execution = Some(Arc::new(execution));
        }
        Ok(transition)
    }

    pub(super) fn apply_let_satisfy(
        &self,
        binding: &ProofLetSatisfy,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        if binding.bindings.is_empty() {
            return Err(self.step_error("`obtain (...)` needs at least one binding"));
        }
        for (name, _) in &binding.bindings {
            if name == "result"
                || self.state().locals().values.contains_key(name)
                || self.state().locals().integer_values.get(name).is_some()
                || self.state().locals().algebraic_values.get(name).is_some()
                || match self.context.as_ref() {
                    ProofContext::Pure(context) => {
                        context.theorem_context.values.contains_key(name)
                            || context.theorem_context.integer_values.get(name).is_some()
                    }
                    ProofContext::FixedState(context) => {
                        context.fixed_state.state.locals().contains_name(name)
                            || context
                                .parameter_binding
                                .parameters
                                .iter()
                                .any(|parameter| parameter.name() == name)
                    }
                    ProofContext::Execution(context) => {
                        context
                            .parsed_function
                            .parameters()
                            .iter()
                            .any(|parameter| parameter.name() == name)
                            || self.execution().is_some_and(|execution| {
                                execution.core.state.locals().contains_name(name)
                            })
                    }
                }
            {
                return Err(self.step_error(format!("`{name}` is already in scope")));
            }
        }
        let source = self.lower_surface_proposition(&binding.proposition, "let-satisfy source")?;
        let opened = self
            .state
            .check_exists_bindings(
                &source,
                binding.bindings.len(),
                Variable(self.state().locals().next_choice_variable),
            )
            .map_err(|error| match error {
                PropositionCloseError::IntegerChoiceSourceUnavailable => self
                    .step_error("required existential fact is not available")
                    .with_missing_tactic_requirement(
                        crate::surface::printing::authored_click_proposition(&binding.proposition),
                    ),
                PropositionCloseError::IntegerChoiceWrongSort => self.step_error(
                    "`obtain (...)` has more binders than the available existential, or an unsupported binder type",
                ),
                PropositionCloseError::IntegerChoiceFresheningExhausted => {
                    self.step_error("`obtain (...)` could not allocate fresh bindings")
                }
                _ => self.step_error("could not open the stated existential"),
            })?;
        let mut locals = self.state().locals().clone();
        let mut facts = self.facts().clone();
        let mut added = Vec::new();
        let mut checked = Vec::new();
        let first_opened = opened.first().cloned();
        for ((name, _), (fact, variable, sort)) in binding.bindings.iter().zip(opened) {
            match sort {
                Sort::Integer => {
                    locals.set_integer_values(locals.integer_values.with_inserted(
                        name.clone(),
                        crate::kernel::SpecIntegerExpression::Term(
                            crate::kernel::IntegerTerm::var(variable),
                        ),
                    ));
                }
                sort if sort.machine_integer_type().is_some() => {
                    locals.set_values(
                        locals.values.with_inserted(
                            name.clone(),
                            ContractExpression::ProgramExpression(ProgramExpression::Value(
                                sort.machine_integer_type()
                                    .unwrap()
                                    .symbolic_value(variable),
                            )),
                        ),
                    );
                }
                sort if sort.pointer_type().is_some() => {
                    locals.set_values(
                        locals.values.with_inserted(
                            name.clone(),
                            ContractExpression::ProgramExpression(ProgramExpression::Value(
                                sort.symbolic_pointer_value(variable)
                                    .expect("pointer choice sort"),
                            )),
                        ),
                    );
                }
                Sort::Algebraic(algebraic_type) => {
                    locals.set_values(
                        locals
                            .values
                            .with_inserted(name.clone(), ContractExpression::Binding(name.clone())),
                    );
                    locals.set_algebraic_values(locals.algebraic_values.with_inserted(
                        name.clone(),
                        crate::kernel::SpecAlgebraicExpression {
                            algebraic_type,
                            node: crate::kernel::SpecAlgebraicExpressionNode::Variable(variable),
                        },
                    ));
                }
                _ => unreachable!("kernel rejected unsupported existential sort"),
            }
            locals.next_choice_variable = variable.0.saturating_add(1);
            if !facts.contains_top_level(&fact) {
                added.push(fact.clone());
            }
            facts = facts
                .with_kernel_checked_fact(fact.clone())
                .with_reserved_variables([variable]);
            checked.push(fact);
        }
        // The opened body is spelled as written, under the names just bound,
        // for premise lookups; see `ProofLocals::surface_facts`.
        let mut written_body = Some(&binding.proposition);
        for _ in &binding.bindings {
            written_body = match written_body {
                Some(ClickProposition::Exists { body, .. }) => Some(body.as_ref()),
                _ => None,
            };
        }
        // A spelling is an index, not authority: a body whose written shape
        // does not record is left unspelled rather than failing the step.
        if let (Some(written_body), Some(body)) = (written_body, checked.last()) {
            let mut spelled = locals.surface_facts.clone();
            if spelled.record_lowering(written_body, body).is_ok() {
                locals.surface_facts = spelled;
            }
        }
        let mut transition = self.checked_fact_transition(locals, facts, false, added, checked);
        // Every machine-integer witness projects as `int32` does: a C string's
        // `size_t` length is chosen the same way as an `int32` index.
        if let Some((chosen_body, variable, sort)) = first_opened
            && (sort.machine_integer_type().is_some()
                || matches!(
                    sort,
                    Sort::ProgramPointer(_) | Sort::ProgramObjectPointer(_, _)
                ))
            && let Some(projection) =
                self.build_existential_projection(binding, &chosen_body, variable, &sort)?
            && let Some(branch) = transition.branch.as_mut()
            && let Some(execution) = branch.state.execution.as_deref()
        {
            let mut execution = execution.clone();
            execution.presentation.existential_projection = Some(projection);
            branch.state.execution = Some(Arc::new(execution));
        }
        Ok(transition)
    }

    fn build_existential_projection(
        &self,
        binding: &ProofLetSatisfy,
        chosen_body: &Proposition,
        chosen_variable: Variable,
        sort: &Sort,
    ) -> Result<Option<ExistentialProjection>, ClickError> {
        let entry_selector = ProgramPointSelector::ProgramPoint(ProgramPointRef {
            region: CodeRegionRef::Function,
            kind: ProgramPointKind::Entry,
        });
        if !matches!(&binding.proposition, ClickProposition::At { selector, .. } if *selector == entry_selector)
        {
            return Ok(None);
        }
        let Some(context) = self.execution_context() else {
            return Ok(None);
        };
        let Some(entry_state) = context.constants.function_entry_state.as_ref() else {
            return Ok(None);
        };
        let Some(view) = self
            .execution_proposition_fixed_state_view()
            .or_else(|| self.execution_frontier_fixed_state_view())
        else {
            return Ok(None);
        };
        let (name, _) = &binding.bindings[0];
        let chosen = match sort {
            sort if sort.machine_integer_type().is_some() => sort
                .machine_integer_type()
                .unwrap()
                .symbolic_value(chosen_variable),
            sort if sort.pointer_type().is_some() => sort
                .symbolic_pointer_value(chosen_variable)
                .expect("pointer choice sort"),
            _ => return Ok(None),
        };
        let bound_names = BTreeMap::from([(chosen_variable, name.clone())]);
        let mut pending = vec![(chosen_body.clone(), Vec::new())];
        let mut leaves = Vec::new();
        let mut work = 0usize;
        while let Some((proposition, path)) = pending.pop() {
            check_verification_deadline()?;
            work = work.saturating_add(1);
            if work > MAX_CHOSEN_PROJECTION_WORK {
                return Err(self.step_error(
                    "opened existential body is too large to retain a bounded source projection",
                ));
            }
            match proposition {
                Proposition::And(left, right) => {
                    let mut right_path = path.clone();
                    right_path.push(1);
                    pending.push((*right, right_path));
                    let mut left_path = path;
                    left_path.push(0);
                    pending.push((*left, left_path));
                }
                leaf => {
                    let Some(surface) = crate::surface::proof::surface_synthesis::synthesize_source_projection_proposition_with_bound_variable_names(
                        &leaf,
                        view.parameter_binding,
                        entry_state,
                        &bound_names,
                    ) else {
                        continue;
                    };
                    let surface = surface_at_program_point(&surface, &entry_selector)?;
                    let validation_surface = substitute_click_proposition(
                        &surface,
                        &BTreeMap::from([(
                            name.clone(),
                            ContractExpression::ProgramExpression(ProgramExpression::Value(
                                chosen.clone(),
                            )),
                        )]),
                    )
                    .map_err(|message| self.step_error(message))?;
                    let lowered = lower_fixed_state_proposition_with_assumptions(
                        &validation_surface,
                        self.facts().assumptions(),
                        view.parameter_binding,
                        FixedStateFrame::new(
                            view.fixed_state.pre_state,
                            view.fixed_state.pre_state,
                            None,
                            view.fixed_state.recorded_states,
                        ),
                        view.spec_definitions,
                    )
                    .map_err(|message| self.step_error(message))?;
                    // A quantified leaf re-lowers with fresh binders, so it
                    // is the same proposition up to alpha-renaming.
                    if lowered == leaf
                        || crate::kernel::proof::propositions_are_alpha_equal(&lowered, &leaf)
                    {
                        leaves.push(ExistentialProjectionLeaf {
                            connective_path: path,
                            surface,
                            kernel: leaf,
                        });
                    }
                }
            }
        }
        Ok((!leaves.is_empty()).then_some(ExistentialProjection {
            chosen_body: chosen_body.clone(),
            chosen_name: name.clone(),
            chosen_variable,
            source_memory_state: crate::kernel::MemoryStateIdentity::of(entry_state.memory()),
            leaves,
        }))
    }

    fn apply_fixed_state_invariant_choose(
        &self,
        choice: &ProofChoice,
        view: &FixedStateOperationView<'_>,
        index: usize,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Err(self.step_error(
                "`choose(... from invariant N)` is available only in a loop preservation proof",
            ));
        };
        let bundle = context
            .constants
            .invariant_body_context
            .as_deref()
            .ok_or_else(|| {
                self.step_error(
                    "`choose(... from invariant N)` is available only in a loop preservation proof",
                )
            })?;
        if index >= bundle.declared_invariant_surfaces.len() {
            return Err(self.step_error(format!(
                "invariant {index} is out of range; loop has {} invariant(s)",
                bundle.declared_invariant_surfaces.len()
            )));
        }
        let iteration_index = bundle.declared_invariant_surfaces.len() + index;
        let surface = bundle
            .loop_head_premises
            .get(iteration_index)
            .ok_or_else(|| {
                self.step_error(format!(
                    "invariant {index} has no retained iteration-entry spelling"
                ))
            })?;
        let source = view
            .surface_propositions
            .available_kernel_matching(surface, |kernel| self.facts().contains_top_level(kernel))
            .cloned()
            .ok_or_else(|| {
                self.step_error(format!(
                    "invariant {index} is not available at this proof point"
                ))
            })?;
        let Proposition::Exists {
            var,
            sort: Sort::Algebraic(algebraic_type),
            body,
            ..
        } = source
        else {
            return Err(self.step_error(
                "`choose(... from invariant N)` currently requires an algebraic existential invariant",
            ));
        };
        let chosen_variable = self
            .state
            .fresh_existential_witness(&body, Variable(self.state().locals().next_choice_variable))
            .map_err(|_| self.step_error("`choose` could not allocate a fresh witness"))?;
        let chosen = crate::kernel::AlgebraicTerm {
            algebraic_type: algebraic_type.clone(),
            node: crate::kernel::AlgebraicTermNode::Variable(chosen_variable),
        };
        let fact = crate::kernel::reasoning::substitute_algebraic_variable_in_proposition(
            &body, var, &chosen,
        );
        let mut locals = self.state().locals().clone();
        locals.set_values(locals.values.with_inserted(
            choice.name.clone(),
            ContractExpression::Binding(choice.name.clone()),
        ));
        locals.set_algebraic_values(locals.algebraic_values.with_inserted(
            choice.name.clone(),
            crate::kernel::SpecAlgebraicExpression {
                algebraic_type,
                node: crate::kernel::SpecAlgebraicExpressionNode::Variable(chosen_variable),
            },
        ));
        locals.next_choice_variable = chosen_variable.0.saturating_add(1);
        let added = (!self.facts().contains_top_level(&fact))
            .then(|| fact.clone())
            .into_iter()
            .collect();
        let facts = self
            .facts()
            .with_kernel_checked_fact(fact.clone())
            .with_reserved_variables([chosen_variable]);
        Ok(self.checked_fact_transition(locals, facts, false, added, vec![fact]))
    }

    /// Retains the source spelling of a chosen existential's body leaves for
    /// the narrow `extract` adapter.  The record is deliberately built from
    /// the selected source only; it never consults ambient facts or asks the
    /// kernel to establish a new proposition.
    fn build_chosen_projection(
        &self,
        view: &FixedStateOperationView<'_>,
        source_requirement: Proposition,
        checked_source: Proposition,
        source_selection: Option<&CallerRequirementSelection>,
        chosen_variable: Variable,
        choice: &ProofChoice,
        chosen: &ProgramValue,
    ) -> Result<Option<ChosenProjection>, ClickError> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return Ok(None);
        };
        let Some(source_selection) = source_selection else {
            return Ok(None);
        };
        // The source ID and final fact position are independent: do not
        // recover an apparently equal requirement from another declaration
        // or from an ambient fact.
        if source_selection.principal_fact != source_requirement {
            return Ok(None);
        }
        let Some(entry_state) = context.constants.function_entry_state.as_ref() else {
            return Ok(None);
        };
        let source_memory_state =
            crate::kernel::MemoryStateIdentity::of(view.fixed_state.pre_state.memory());
        if source_memory_state != crate::kernel::MemoryStateIdentity::of(entry_state.memory()) {
            return Ok(None);
        }
        let source_selector = ProgramPointSelector::ProgramPoint(ProgramPointRef {
            region: CodeRegionRef::Function,
            kind: ProgramPointKind::Entry,
        });
        // The body passed by `apply_fixed_state_choose` is the existential
        // body before substitution. Build the substituted body from the
        // selected requirement, preserving the original binder identity.
        let instantiated = match (&checked_source, chosen) {
            (Proposition::Exists { var, body, .. }, crate::kernel::integer_c_value!(value)) => {
                substitute_int32_variable_in_proposition(body, *var, value.clone())
            }
            (Proposition::Exists { var, body, .. }, ProgramValue::Pointer(pointer)) => {
                crate::kernel::substitute_pointer_value_in_proposition(body, *var, pointer)
                    .map_err(|error| self.step_error(&error))?
            }
            _ => return Ok(None),
        };
        #[cfg(test)]
        let projection_allocations_before = persistent_node_allocations();
        let mut leaves = Vec::new();
        let mut pending = vec![(instantiated, Vec::new())];
        let bound_names = BTreeMap::from([(chosen_variable, choice.name.clone())]);
        let mut work = 0usize;
        while let Some((proposition, connective_path)) = pending.pop() {
            check_verification_deadline()?;
            work = work.saturating_add(1);
            if work > MAX_CHOSEN_PROJECTION_WORK {
                return Err(self.step_error(
                    "chosen existential body is too large to retain a bounded source projection",
                ));
            }
            match proposition {
                Proposition::And(left, right) => {
                    let mut right_path = connective_path.clone();
                    right_path.push(1);
                    pending.push((*right, right_path));
                    let mut left_path = connective_path;
                    left_path.push(0);
                    pending.push((*left, left_path));
                    continue;
                }
                leaf => {
                    let Some(surface) =
                        crate::surface::proof::surface_synthesis::synthesize_source_projection_proposition_with_bound_variable_names(
                            &leaf,
                            view.parameter_binding,
                            entry_state,
                            &bound_names,
                        )
                    else {
                        // Retain the exact subset of leaves that can
                        // round-trip at this source boundary. Every retained
                        // leaf is checked below; an unsynthesizable sibling
                        // does not invalidate those independent identities.
                        continue;
                    };
                    let surface = surface_at_program_point(&surface, &source_selector)?;
                    let validation_surface = substitute_click_proposition(
                        &surface,
                        &BTreeMap::from([(
                            choice.name.clone(),
                            ContractExpression::ProgramExpression(ProgramExpression::Value(
                                chosen.clone(),
                            )),
                        )]),
                    )
                    .map_err(|message| {
                        self.step_error(format!(
                            "could not substitute chosen existential body leaf: {message}"
                        ))
                    })?;
                    let lowered = lower_fixed_state_proposition_with_assumptions(
                        &validation_surface,
                        self.facts().assumptions(),
                        view.parameter_binding,
                        FixedStateFrame::new(
                            view.fixed_state.pre_state,
                            view.fixed_state.pre_state,
                            None,
                            view.fixed_state.recorded_states,
                        ),
                        view.spec_definitions,
                    )
                    .map_err(|message| {
                        self.step_error(format!(
                            "could not lower chosen existential body leaf: {message}"
                        ))
                    })?;
                    if lowered != leaf {
                        // A surface leaf is usable only when it lowers back
                        // to this exact selected kernel leaf.
                        continue;
                    }
                    leaves.push(ChosenProjectionLeaf {
                        source_token: ProjectionSourceToken {
                            source_id: source_selection.source_id.clone(),
                            connective_path,
                        },
                        surface,
                        kernel: leaf,
                    });
                }
            }
        }
        #[cfg(test)]
        CHOSEN_PROJECTION_WALK_WORK.with(|count| {
            count.set((
                work,
                persistent_node_allocations() - projection_allocations_before,
            ));
        });
        Ok((!leaves.is_empty()).then_some(ChosenProjection {
            source_id: source_selection.source_id.clone(),
            principal_fact_index: source_selection.principal_fact_index,
            source_token: ProjectionSourceToken {
                source_id: source_selection.source_id.clone(),
                connective_path: Vec::new(),
            },
            source_proposition: source_selection.source_proposition.clone(),
            source_requirement,
            checked_source,
            chosen_name: choice.name.clone(),
            chosen_variable,
            source_memory_state,
            source_selector,
            leaves,
        }))
    }

    fn apply_pure_integer_choose(
        &self,
        choice: &ProofChoice,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let ProofContext::Pure(context) = self.context.as_ref() else {
            unreachable!()
        };
        if context
            .theorem_context
            .integer_values
            .get(&choice.name)
            .is_some()
            || context.theorem_context.values.contains_key(&choice.name)
            || self
                .state()
                .locals()
                .integer_values
                .get(&choice.name)
                .is_some()
            || self.state().locals().values.get(&choice.name).is_some()
        {
            return Err(self.step_error(format!("`{}` is already in scope", choice.name)));
        }
        let index = match &choice.source {
            ProofFactSource::Requirement(index) => *index,
            ProofFactSource::Invariant(_) => {
                return Err(self.step_error("pure `choose` does not have a loop invariant source"));
            }
        };
        let source = context
            .theorem_context
            .requires
            .get(index)
            .cloned()
            .ok_or_else(|| self.step_error(format!("requirement {index} is out of range")))?;
        let (fact, chosen_variable) =
            self.state
                .check_integer_exists_choice(
                    &source,
                    Variable(self.state().locals().next_choice_variable),
                )
                .map_err(|error| match error {
                    PropositionCloseError::IntegerChoiceSourceUnavailable => self
                        .step_error("Integer choose source is not an exact available requirement"),
                    PropositionCloseError::IntegerChoiceWrongSort => self.step_error(
                        "pure `choose` currently requires an Integer existential requirement",
                    ),
                    PropositionCloseError::IntegerChoiceFresheningExhausted => {
                        self.step_error("pure `choose` could not allocate a fresh Integer witness")
                    }
                    _ => self.step_error("could not apply Integer choice"),
                })?;
        let chosen = crate::kernel::IntegerTerm::var(chosen_variable);
        let mut locals = self.state().locals().clone();
        locals.set_integer_values(locals.integer_values.with_inserted(
            choice.name.clone(),
            crate::kernel::SpecIntegerExpression::Term(chosen),
        ));
        locals.next_choice_variable = chosen_variable.0.saturating_add(1);
        let added = (!self.facts().contains_top_level(&fact))
            .then(|| fact.clone())
            .into_iter()
            .collect();
        let facts = self
            .facts()
            .with_kernel_checked_fact(fact.clone())
            .with_reserved_variables([chosen_variable]);
        Ok(self.checked_fact_transition(locals, facts, false, added, vec![fact]))
    }

    fn apply_pure_algebraic_choose(
        &self,
        choice: &ProofChoice,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let ProofContext::Pure(context) = self.context.as_ref() else {
            unreachable!()
        };
        if context.theorem_context.values.contains_key(&choice.name)
            || context
                .theorem_context
                .integer_values
                .get(&choice.name)
                .is_some()
            || self.state().locals().values.get(&choice.name).is_some()
            || self
                .state()
                .locals()
                .integer_values
                .get(&choice.name)
                .is_some()
            || self
                .state()
                .locals()
                .algebraic_values
                .get(&choice.name)
                .is_some()
        {
            return Err(self.step_error(format!("`{}` is already in scope", choice.name)));
        }
        let index = match &choice.source {
            ProofFactSource::Requirement(index) => *index,
            ProofFactSource::Invariant(_) => {
                return Err(self.step_error("pure `choose` does not have a loop invariant source"));
            }
        };
        let source = context
            .theorem_context
            .requires
            .get(index)
            .cloned()
            .ok_or_else(|| self.step_error(format!("requirement {index} is out of range")))?;
        if !self.facts().contains_top_level(&source) {
            return Err(
                self.step_error("algebraic choose source is not an exact available requirement")
            );
        }
        let Proposition::Exists {
            var,
            sort: Sort::Algebraic(algebraic_type),
            body,
            ..
        } = source
        else {
            return Err(self.step_error(
                "pure algebraic `choose` requires an algebraic existential requirement",
            ));
        };
        let chosen_variable = self
            .state
            .fresh_existential_witness(&body, Variable(self.state().locals().next_choice_variable))
            .map_err(|_| self.step_error("`choose` could not allocate a fresh witness"))?;
        let chosen = crate::kernel::AlgebraicTerm {
            algebraic_type: algebraic_type.clone(),
            node: crate::kernel::AlgebraicTermNode::Variable(chosen_variable),
        };
        let fact = crate::kernel::reasoning::substitute_algebraic_variable_in_proposition(
            &body, var, &chosen,
        );
        let mut locals = self.state().locals().clone();
        locals.set_values(locals.values.with_inserted(
            choice.name.clone(),
            ContractExpression::Binding(choice.name.clone()),
        ));
        locals.set_algebraic_values(locals.algebraic_values.with_inserted(
            choice.name.clone(),
            crate::kernel::SpecAlgebraicExpression {
                algebraic_type,
                node: crate::kernel::SpecAlgebraicExpressionNode::Variable(chosen_variable),
            },
        ));
        locals.next_choice_variable = chosen_variable.0.saturating_add(1);
        let added = (!self.facts().contains_top_level(&fact))
            .then(|| fact.clone())
            .into_iter()
            .collect();
        let facts = self
            .facts()
            .with_kernel_checked_fact(fact.clone())
            .with_reserved_variables([chosen_variable]);
        Ok(self.checked_fact_transition(locals, facts, false, added, vec![fact]))
    }

    pub(super) fn apply_fixed_state_witness(
        &self,
        witness: &ProofWitness,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        if matches!(self.context.as_ref(), ProofContext::Pure(_)) {
            return match self.proposition_goal("`witness` requires a proposition goal")? {
                Proposition::Exists {
                    sort: Sort::Algebraic(_),
                    ..
                } => self.apply_pure_algebraic_witness(witness),
                Proposition::Exists {
                    sort:
                        Sort::ProgramInt32
                        | Sort::ProgramInt64
                        | Sort::ProgramInteger(_)
                        | Sort::ProgramPointer(_)
                        | Sort::ProgramObjectPointer(_, _),
                    ..
                } => self.apply_pure_machine_witness(witness),
                _ => self.apply_pure_integer_witness(witness),
            };
        }
        let view = match self.context.as_ref() {
            ProofContext::FixedState(context) => FixedStateOperationView::from_fixed_state(context),
            // A witness refinement on a judgment stated at a function
            // outcome reads the outcome's result-aware data.
            ProofContext::Execution(_) if self.focused_outcome_data().is_some() => self
                .outcome_fixed_state_view()
                .expect("a focused outcome judgment resolves its fixed-state view"),
            ProofContext::Execution(_) => self
                .execution_proposition_fixed_state_view()
                .ok_or_else(|| {
                    self.step_error("`witness` requires a fixed-state proposition proof")
                })?,
            _ => return Err(self.step_error("`witness` requires a fixed-state proposition proof")),
        };
        let goal = self
            .proposition_goal("`witness` requires a proposition goal")?
            .clone();
        let unfolded_predicates = self.active_unfolded_predicates();
        let goal = unfold_predicates_in_proposition(
            view.spec_definitions,
            &unfolded_predicates,
            &goal,
            self.facts().assumptions(),
        )
        .map_err(|message| self.step_error(format!("could not unfold witness goal: {message}")))?;
        let values = parameter_values(view.parameter_binding)
            .map_err(|error| self.step_error(error.message))?;
        let array_refs = array_refs_for_parameters(
            view.parameter_binding.parameters,
            &values,
            view.fixed_state.state.memory(),
        );
        let (values, array_refs) =
            contract_environment_at_state(&values, &array_refs, view.fixed_state.state);
        let checked_witness = ProofWitness::single(
            witness.name().to_string(),
            self.substitute_fixed_state_locals_in_expression(witness.value())?,
        );
        if let Proposition::Exists {
            name,
            var,
            sort: Sort::Algebraic(algebraic_type),
            body,
        } = &goal
        {
            if name != witness.name() {
                return Err(self.step_error(format!(
                    "`witness` binds `{name}`, but proof provided `{}`",
                    witness.name()
                )));
            }
            let names = contract_expression_referenced_names(checked_witness.value());
            let algebraic_values = names
                .into_iter()
                .filter_map(|name| {
                    self.local_algebraic_values()
                        .get(&name)
                        .cloned()
                        .map(|value| (name, value))
                })
                .collect();
            let value = capture_fixed_state_algebraic_value(
                checked_witness.value(),
                self.facts().assumptions(),
                ContractEnvironment::new(&values, &array_refs),
                algebraic_values,
                view.fixed_state.pre_state,
                view.fixed_state.state,
                view.fixed_state.recorded_states,
                view.spec_definitions,
            )
            .map_err(|message| {
                self.step_error(format!("could not capture algebraic witness: {message}"))
            })?;
            if &value.algebraic_type != algebraic_type {
                return Err(self.step_error("algebraic witness has the wrong datatype"));
            }
            let proposition =
                crate::kernel::reasoning::substitute_algebraic_variable_in_proposition(
                    body, *var, &value,
                );
            let surface_goal = match self.surface_goal() {
                Some(ClickProposition::Exists {
                    name,
                    written_name,
                    body,
                    ..
                }) if written_name.as_ref().unwrap_or(name) == witness.name() => {
                    let substitutions = BTreeMap::from([(name.clone(), witness.value().clone())]);
                    Some(
                        substitute_click_proposition(body, &substitutions).map_err(|message| {
                            self.step_error(format!(
                                "could not instantiate algebraic witness goal: {message}"
                            ))
                        })?,
                    )
                }
                _ => None,
            };
            let context = self.refined_branch_state(self.facts().clone());
            return Ok(CheckedFocusedTransition::replacing(
                self.state().locals().clone(),
                Some(self.refined_proposition(context, proposition, surface_goal, true)),
                Vec::new(),
                Vec::new(),
            ));
        }
        let value = evaluate_witness_tactic_value(
            &checked_witness,
            view.claim_label,
            0,
            view.tactic_index,
            ContractEnvironment::new(&values, &array_refs),
            view.fixed_state.pre_state,
            view.fixed_state.state,
            view.fixed_state.result,
            self.facts().assumptions(),
            view.spec_definitions,
            view.fixed_state.recorded_states,
        )?;
        let goal = apply_witness_tactic(
            &checked_witness,
            value,
            goal,
            view.claim_label,
            0,
            view.tactic_index,
        )?;
        let surface_goal = match self.surface_goal() {
            Some(ClickProposition::Exists {
                name,
                written_name,
                body,
                ..
            }) if written_name.as_ref().unwrap_or(name) == witness.name() => {
                let substitutions = BTreeMap::from([(name.clone(), witness.value().clone())]);
                Some(
                    substitute_click_proposition(body, &substitutions).map_err(|message| {
                        self.step_error(format!(
                            "could not instantiate Surface witness goal: {message}"
                        ))
                    })?,
                )
            }
            Some(ClickProposition::RangeAny {
                start,
                end,
                item,
                written_item,
                body,
            }) if written_item.as_ref().unwrap_or(item) == witness.name() => {
                let substitutions = BTreeMap::from([(item.clone(), witness.value().clone())]);
                let start =
                    substitute_contract_expression(start, &substitutions).map_err(|message| {
                        self.step_error(format!(
                            "could not instantiate Surface range start: {message}"
                        ))
                    })?;
                let end =
                    substitute_contract_expression(end, &substitutions).map_err(|message| {
                        self.step_error(format!(
                            "could not instantiate Surface range end: {message}"
                        ))
                    })?;
                let value = substitute_contract_expression(witness.value(), &substitutions)
                    .map_err(|message| {
                        self.step_error(format!(
                            "could not instantiate Surface range witness: {message}"
                        ))
                    })?;
                let body =
                    substitute_click_proposition(body, &substitutions).map_err(|message| {
                        self.step_error(format!(
                            "could not instantiate Surface range witness goal: {message}"
                        ))
                    })?;
                Some(ClickProposition::And(
                    Box::new(ClickProposition::And(
                        Box::new(ClickProposition::Comparison {
                            left: start,
                            operator: ComparisonOperator::LessEqual,
                            right: value.clone(),
                        }),
                        Box::new(ClickProposition::Comparison {
                            left: value,
                            operator: ComparisonOperator::LessThan,
                            right: end,
                        }),
                    )),
                    Box::new(body),
                ))
            }
            _ => None,
        };
        let context = self.refined_branch_state(self.facts().clone());
        Ok(CheckedFocusedTransition::replacing(
            self.state().locals().clone(),
            Some(self.refined_proposition(context, goal, surface_goal, true)),
            Vec::new(),
            Vec::new(),
        ))
    }

    fn apply_pure_machine_witness(
        &self,
        witness: &ProofWitness,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let ProofContext::Pure(context) = self.context.as_ref() else {
            unreachable!()
        };
        let goal = self
            .proposition_goal("`witness` requires a proposition goal")?
            .clone();
        let checked_witness = ProofWitness::single(
            witness.name().to_owned(),
            self.substitute_fixed_state_locals_in_expression(witness.value())?,
        );
        let non_machine_type = match checked_witness.value() {
            ContractExpression::Binding(name)
                if context.theorem_context.integer_values.get(name).is_some()
                    || self.local_integer_values().get(name).is_some() =>
            {
                Some("Integer".to_owned())
            }
            ContractExpression::AlgebraicVariable { algebraic_type, .. }
            | ContractExpression::AlgebraicConstructor { algebraic_type, .. } => {
                Some(crate::surface::validation::describe_click_type(
                    &ClickType::Algebraic(algebraic_type.clone()),
                ))
            }
            _ => None,
        };
        if let Some(actual) = non_machine_type {
            let expected = match &goal {
                Proposition::Exists { sort, .. } if sort.machine_integer_type().is_some() => {
                    sort.machine_integer_type().unwrap().program_type()
                }
                Proposition::Exists {
                    sort:
                        Sort::ProgramPointer(interface_type)
                        | Sort::ProgramObjectPointer(interface_type, _),
                    ..
                } => *interface_type,
                _ => unreachable!("pure machine witness dispatch requires a C binder"),
            };
            return Err(self.step_error(format!(
                "witness `{}` has the wrong type: expected {}, got {actual}",
                witness.name(),
                describe_interface_type(
                    crate::surface::generics::interface_type_from_program_type(expected)
                ),
            )));
        }
        // Capture only the written value using the theorem's retained memory
        // and lexical bindings, then use the same typed instantiation as a
        // fixed-state witness. No assumption or proof of the body is added.
        let names = contract_expression_referenced_names(checked_witness.value());
        let values = names
            .iter()
            .filter_map(|name| {
                context
                    .theorem_context
                    .values
                    .get(name)
                    .map(|value| (name.clone(), value.clone()))
            })
            .collect();
        let arrays = names
            .iter()
            .filter_map(|name| {
                context
                    .theorem_context
                    .array_refs
                    .get(name)
                    .map(|value| (name.clone(), value.clone()))
            })
            .collect();
        let algebraic_values = names
            .iter()
            .filter_map(|name| {
                self.local_algebraic_values()
                    .get(name)
                    .cloned()
                    .or_else(|| {
                        context
                            .structural_induction_setup
                            .as_ref()?
                            .algebraic_values
                            .get(name)
                            .cloned()
                    })
                    .map(|value| (name.clone(), value))
            })
            .collect();
        let state = ExecutionState::new().with_memory(context.theorem_context.memory.clone());
        let value = evaluate_fixed_state_expression_through_kernel_with_algebraic_values(
            checked_witness.value(),
            self.facts().assumptions(),
            ContractEnvironment::new(&values, &arrays),
            algebraic_values,
            FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
            context.spec_definitions,
            &BTreeSet::new(),
        )
        .map_err(|message| {
            self.step_error(format!(
                "could not evaluate witness `{}`: {message}",
                witness.name(),
            ))
        })?;
        let proposition = apply_witness_tactic(
            &checked_witness,
            value,
            goal,
            self.claim_label(),
            0,
            self.certificate().steps().len(),
        )
        .map_err(|error| self.attach_step_diagnostic(error))?;
        let surface_goal = match self.surface_goal() {
            Some(ClickProposition::Exists {
                name,
                written_name,
                body,
                ..
            }) if written_name.as_ref().unwrap_or(name) == witness.name() => {
                let substitutions = BTreeMap::from([(name.clone(), witness.value().clone())]);
                Some(
                    substitute_click_proposition(body, &substitutions).map_err(|message| {
                        self.step_error(format!(
                            "could not instantiate machine witness goal: {message}"
                        ))
                    })?,
                )
            }
            _ => None,
        };
        let branch = self.refined_branch_state(self.facts().clone());
        Ok(CheckedFocusedTransition::replacing(
            self.state().locals().clone(),
            Some(self.refined_proposition(branch, proposition, surface_goal, true)),
            Vec::new(),
            Vec::new(),
        ))
    }

    fn apply_pure_integer_witness(
        &self,
        witness: &ProofWitness,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let goal = self
            .proposition_goal("`witness` requires a proposition goal")?
            .clone();
        let Proposition::Exists {
            name,
            var,
            sort: Sort::Integer,
            body,
        } = goal
        else {
            return Err(self.step_error(
                "pure `witness` currently requires an Integer existential proposition",
            ));
        };
        if name != witness.name() {
            return Err(self.step_error(format!(
                "`witness` binds `{name}`, but proof provided `{}`",
                witness.name()
            )));
        }
        let value = self.capture_pure_integer_witness(witness.value())?;
        let proposition =
            crate::kernel::substitute_integer_variable_in_pure_proposition(&body, var, &value)
                .map_err(|error| {
                    self.step_error(format!("could not apply Integer witness: {error}"))
                })?;
        let surface_goal = match self.surface_goal() {
            Some(ClickProposition::Exists {
                name,
                written_name,
                body,
                ..
            }) if written_name.as_ref().unwrap_or(name) == witness.name() => {
                let substitutions = BTreeMap::from([(name.clone(), witness.value().clone())]);
                Some(
                    substitute_click_proposition(body, &substitutions).map_err(|message| {
                        self.step_error(format!(
                            "could not instantiate Integer witness goal: {message}"
                        ))
                    })?,
                )
            }
            _ => None,
        };
        let context = self.refined_branch_state(self.facts().clone());
        Ok(CheckedFocusedTransition::replacing(
            self.state().locals().clone(),
            Some(self.refined_proposition(context, proposition, surface_goal, true)),
            Vec::new(),
            Vec::new(),
        ))
    }

    fn apply_pure_algebraic_witness(
        &self,
        witness: &ProofWitness,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let goal = self
            .proposition_goal("`witness` requires a proposition goal")?
            .clone();
        let Proposition::Exists {
            name,
            var,
            sort: Sort::Algebraic(algebraic_type),
            body,
        } = goal
        else {
            return Err(self.step_error(
                "pure algebraic `witness` requires an algebraic existential proposition",
            ));
        };
        if name != witness.name() {
            return Err(self.step_error(format!(
                "`witness` binds `{name}`, but proof provided `{}`",
                witness.name()
            )));
        }
        let value = self.capture_pure_algebraic_witness(witness.value())?;
        if value.algebraic_type != algebraic_type {
            return Err(self.step_error("algebraic witness has the wrong datatype"));
        }
        let proposition = crate::kernel::reasoning::substitute_algebraic_variable_in_proposition(
            &body, var, &value,
        );
        let surface_goal = match self.surface_goal() {
            Some(ClickProposition::Exists {
                name,
                written_name,
                body,
                ..
            }) if written_name.as_ref().unwrap_or(name) == witness.name() => {
                let substitutions = BTreeMap::from([(name.clone(), witness.value().clone())]);
                Some(
                    substitute_click_proposition(body, &substitutions).map_err(|message| {
                        self.step_error(format!(
                            "could not instantiate algebraic witness goal: {message}"
                        ))
                    })?,
                )
            }
            _ => None,
        };
        let context = self.refined_branch_state(self.facts().clone());
        Ok(CheckedFocusedTransition::replacing(
            self.state().locals().clone(),
            Some(self.refined_proposition(context, proposition, surface_goal, true)),
            Vec::new(),
            Vec::new(),
        ))
    }

    pub(super) fn capture_pure_algebraic_witness(
        &self,
        expression: &ContractExpression,
    ) -> Result<crate::kernel::AlgebraicTerm, ClickError> {
        let ProofContext::Pure(context) = self.context.as_ref() else {
            unreachable!()
        };
        let expression = self.substitute_fixed_state_locals_in_expression(expression)?;
        let mut names = BTreeSet::new();
        collect_contract_expression_referenced_names(&expression, &mut names);
        let values: BTreeMap<_, _> = names
            .iter()
            .filter_map(|name| {
                context
                    .theorem_context
                    .values
                    .get(name)
                    .map(|value| (name.clone(), value.clone()))
            })
            .collect();
        let arrays: BTreeMap<_, _> = names
            .iter()
            .filter_map(|name| {
                context
                    .theorem_context
                    .array_refs
                    .get(name)
                    .map(|value| (name.clone(), value.clone()))
            })
            .collect();
        let state = ExecutionState::new().with_memory(context.theorem_context.memory.clone());
        let algebraic_values = names
            .iter()
            .filter_map(|name| {
                self.local_algebraic_values()
                    .get(name)
                    .cloned()
                    .or_else(|| {
                        context
                            .structural_induction_setup
                            .as_ref()?
                            .algebraic_values
                            .get(name)
                            .cloned()
                    })
                    .map(|value| (name.clone(), value))
            })
            .collect();
        capture_fixed_state_algebraic_value(
            &expression,
            self.facts().assumptions(),
            ContractEnvironment::new(&values, &arrays),
            algebraic_values,
            &state,
            &state,
            &RecordedStates::new(),
            context.spec_definitions,
        )
        .map_err(|message| {
            self.step_error(format!("could not capture algebraic witness: {message}"))
        })
    }

    fn capture_pure_integer_witness(
        &self,
        expression: &ContractExpression,
    ) -> Result<crate::kernel::IntegerTerm, ClickError> {
        let ProofContext::Pure(context) = self.context.as_ref() else {
            unreachable!()
        };
        let expression = self.substitute_fixed_state_locals_in_expression(expression)?;
        let expression = &expression;
        let mut names = BTreeSet::new();
        collect_contract_expression_referenced_names(expression, &mut names);
        let mut integers = context.theorem_context.integer_values.clone();
        for name in &names {
            if let Some(value) = self.state().locals().integer_values.get(name) {
                integers = integers.with_inserted(name.clone(), value.clone());
            }
        }
        let promoted = crate::surface::proof::surface_lowering::promote_integer_expression(
            expression,
            &integers,
            &crate::persistent::PersistentMap::default(),
        );
        if let Ok(crate::kernel::SpecIntegerExpression::Term(value)) =
            crate::surface::lowering::lower_contract_integer_to_spec(&promoted, &integers)
        {
            return Ok(value);
        }
        let values: BTreeMap<_, _> = names
            .iter()
            .filter_map(|name| {
                context
                    .theorem_context
                    .values
                    .get(name)
                    .map(|value| (name.clone(), value.clone()))
            })
            .collect();
        let algebraic = names
            .iter()
            .filter_map(|name| {
                context
                    .structural_induction_setup
                    .as_ref()?
                    .algebraic_values
                    .get(name)
                    .map(|value| (name.clone(), value.clone()))
            })
            .collect();
        let arrays: BTreeMap<_, _> = names
            .iter()
            .filter_map(|name| {
                context
                    .theorem_context
                    .array_refs
                    .get(name)
                    .map(|value| (name.clone(), value.clone()))
            })
            .collect();
        let state = ExecutionState::new().with_memory(context.theorem_context.memory.clone());
        let states = crate::surface::proof::fixed_state_proofs::FixedStateLowering::new(
            ContractEnvironment::new(&values, &arrays),
            &state,
            &state,
            None,
        );
        let spec = crate::surface::lowering::elaborate_fixed_state_proposition_with_algebraic_and_integer_values(
            &ClickProposition::Comparison { left: promoted, operator: ComparisonOperator::Equal, right: ContractExpression::IntegerLiteral("0".into()) },
            states.element_types, BTreeMap::new(), &states.entry_state, states.entry_values, states.current_values,
            algebraic, &integers, None, &RecordedStates::new(),
            context.spec_definitions, BTreeSet::new(),
            BTreeMap::new(),).map_err(|message| self.step_error(format!("could not lower Integer witness: {message}")))?;
        let crate::kernel::SpecProposition::IntegerComparison { left, .. } = spec else {
            return Err(self.step_error("witness must be an Integer expression"));
        };
        crate::kernel::capture_spec_integer_value(
            &states.lowering_state,
            &left,
            Some(&states.entry_state),
            self.facts().assumptions(),
        )
        .map_err(|refusal| {
            let message =
                crate::surface::proof_diagnostics::render::describe_spec_capture_refusal(&refusal);
            self.step_error(format!("could not capture Integer witness: {message}"))
        })
    }

    /// Capture only the written argument in the current proof context. Pure
    /// proofs use their retained theorem memory and bindings, without creating
    /// a fixed-state proof or rebuilding an assumption context.
    fn capture_instantiate_argument(
        &self,
        argument: &ContractExpression,
        binder: &Sort,
    ) -> Result<InstanceArgument, ClickError> {
        if *binder == Sort::Integer {
            return self
                .capture_instantiate_integer_argument(argument)
                .map(InstanceArgument::Integer);
        }
        let argument = self.substitute_fixed_state_locals_in_expression(argument)?;
        let value = if let ProofContext::Pure(context) = self.context.as_ref() {
            let names = contract_expression_referenced_names(&argument);
            if let Some(name) = names.iter().find(|name| {
                self.local_integer_values().get(*name).is_some()
                    || context.theorem_context.integer_values.get(*name).is_some()
            }) {
                return Err(self.step_error(format!(
                    "`instantiate` argument requires int32 values; `{name}` is an Integer binding"
                )));
            }
            let values = names
                .iter()
                .filter_map(|name| {
                    context
                        .theorem_context
                        .values
                        .get(name)
                        .map(|value| (name.clone(), value.clone()))
                })
                .collect();
            let arrays = names
                .iter()
                .filter_map(|name| {
                    context
                        .theorem_context
                        .array_refs
                        .get(name)
                        .map(|value| (name.clone(), value.clone()))
                })
                .collect();
            let algebraic_values = names
                .iter()
                .filter_map(|name| {
                    self.local_algebraic_values()
                        .get(name)
                        .cloned()
                        .or_else(|| {
                            context
                                .structural_induction_setup
                                .as_ref()?
                                .algebraic_values
                                .get(name)
                                .cloned()
                        })
                        .map(|value| (name.clone(), value))
                })
                .collect();
            let state = ExecutionState::new().with_memory(context.theorem_context.memory.clone());
            evaluate_fixed_state_expression_through_kernel_with_algebraic_values(
                &argument,
                self.facts().assumptions(),
                ContractEnvironment::new(&values, &arrays),
                algebraic_values,
                FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
                context.spec_definitions,
                &BTreeSet::new(),
            )
        } else {
            let view = match self.context.as_ref() {
                ProofContext::FixedState(context) => {
                    FixedStateOperationView::from_fixed_state(context)
                }
                // An instantiation on a judgment stated at a function outcome
                // evaluates its argument and quantified fact in that outcome's
                // result-aware fixed-state environment.
                ProofContext::Execution(_) if self.focused_outcome_data().is_some() => self
                    .outcome_fixed_state_view()
                    .expect("a focused outcome judgment resolves its fixed-state view"),
                // A leading nested `have` is a proposition proof at the
                // execution frontier. It evaluates the quantified fact and
                // argument in that outcome's fixed-state environment without
                // exporting or checking execution state.
                ProofContext::Execution(_) => self
                    .execution_proposition_fixed_state_view()
                    .ok_or_else(|| {
                        self.step_error("`instantiate` requires a fixed-state proposition proof")
                    })?,
                _ => {
                    return Err(
                        self.step_error("`instantiate` requires a fixed-state proposition proof")
                    );
                }
            };
            let parameter_values = parameter_values(view.parameter_binding)
                .map_err(|error| self.step_error(error.message))?;
            let array_refs = array_refs_for_parameters(
                view.parameter_binding.parameters,
                &parameter_values,
                view.fixed_state.state.memory(),
            );
            let (values, array_refs) = contract_environment_at_state(
                &parameter_values,
                &array_refs,
                view.fixed_state.state,
            );
            let algebraic_values = contract_expression_referenced_names(&argument)
                .into_iter()
                .filter_map(|name| {
                    self.local_algebraic_values()
                        .get(&name)
                        .cloned()
                        .map(|value| (name, value))
                })
                .collect();
            evaluate_fixed_state_expression_through_kernel_with_algebraic_values(
                &argument,
                self.facts().assumptions(),
                ContractEnvironment::new(&values, &array_refs),
                algebraic_values,
                view.fixed_state,
                view.spec_definitions,
                &BTreeSet::new(),
            )
        }
        .map_err(|message| {
            self.step_error(format!(
                "could not evaluate `instantiate` argument: {message}"
            ))
        })?;
        let uint64 = Sort::ProgramInteger(crate::kernel::MachineIntegerType::UInt64);
        match (binder, value) {
            (Sort::ProgramInt32, ProgramValue::Int32(argument)) => {
                Ok(InstanceArgument::Machine(argument))
            }
            (binder, ProgramValue::UInt64(argument)) if *binder == uint64 => {
                Ok(InstanceArgument::Machine(argument))
            }
            (
                Sort::ProgramPointer(_) | Sort::ProgramObjectPointer(_, _),
                ProgramValue::Pointer(pointer),
            ) => Ok(InstanceArgument::Pointer(pointer)),
            (binder, _) if *binder == uint64 => {
                Err(self.step_error("`instantiate` argument did not evaluate to uint64"))
            }
            (Sort::ProgramPointer(_) | Sort::ProgramObjectPointer(_, _), _) => {
                Err(self.step_error("`instantiate` argument did not evaluate to a pointer"))
            }
            _ => Err(self.step_error("`instantiate` argument did not evaluate to int32")),
        }
    }

    /// An `Integer` binder's argument, captured as a mathematical value in
    /// the current proof context: the theorem's and the proof's `Integer`
    /// bindings in a pure proof, the fixed-state environment otherwise.
    fn capture_instantiate_integer_argument(
        &self,
        argument: &ContractExpression,
    ) -> Result<crate::kernel::IntegerTerm, ClickError> {
        if matches!(self.context.as_ref(), ProofContext::Pure(_)) {
            return self.capture_pure_integer_witness(argument);
        }
        let argument = self.substitute_fixed_state_locals_in_expression(argument)?;
        let view = match self.context.as_ref() {
            ProofContext::FixedState(context) => FixedStateOperationView::from_fixed_state(context),
            ProofContext::Execution(_) if self.focused_outcome_data().is_some() => self
                .outcome_fixed_state_view()
                .expect("a focused outcome judgment resolves its fixed-state view"),
            ProofContext::Execution(_) => self
                .execution_proposition_fixed_state_view()
                .ok_or_else(|| {
                    self.step_error("`instantiate` requires a fixed-state proposition proof")
                })?,
            ProofContext::Pure(_) => unreachable!("handled above"),
        };
        let parameter_values = parameter_values(view.parameter_binding)
            .map_err(|error| self.step_error(error.message))?;
        let array_refs = array_refs_for_parameters(
            view.parameter_binding.parameters,
            &parameter_values,
            view.fixed_state.state.memory(),
        );
        let (values, array_refs) =
            contract_environment_at_state(&parameter_values, &array_refs, view.fixed_state.state);
        capture_fixed_state_integer_expression(
            &argument,
            &self.local_integer_values(),
            self.facts().assumptions(),
            ContractEnvironment::new(&values, &array_refs),
            view.fixed_state,
            view.spec_definitions,
        )
        .map_err(|message| {
            self.step_error(format!(
                "could not capture `instantiate` argument: {message}"
            ))
        })
    }

    pub(super) fn apply_fixed_state_instantiate_using(
        &self,
        surface_quantified: &ClickProposition,
        argument: &ContractExpression,
        surface_premises: Option<&[ClickProposition]>,
    ) -> Result<KernelProofHandle, ClickError> {
        let surface_quantified =
            self.substitute_fixed_state_locals_in_proposition(surface_quantified)?;
        let explicit_premises = surface_premises
            .map(|premises| {
                premises
                    .iter()
                    .map(|surface| {
                        self.lower_cited_surface_proposition(surface, "`instantiate using` premise")
                    })
                    .collect::<Result<Vec<_>, _>>()
            })
            .transpose()?;
        let bare = surface_premises.is_none();
        let surface_premises = surface_premises.unwrap_or_default();
        let lowered_quantified = self.lower_cited_surface_proposition(
            &surface_quantified,
            "`instantiate` quantified fact",
        )?;
        // The argument has the binder's type. A fact that is not a universal
        // is refused by the kernel below; it is read as `int32` here.
        let binder = match &lowered_quantified {
            Proposition::ForAll { sort, .. } => sort.clone(),
            _ => Sort::ProgramInt32,
        };
        let argument = self.capture_instantiate_argument(argument, &binder)?;
        // Freeze the evaluated argument so `old`/`at` inside the quantified
        // body cannot reinterpret a source memory expression at another point.
        // An `Integer` instance keeps no frozen spelling: the recorded
        // lowering below is optional, and only C values have a fragment form.
        let surface_argument = match &argument {
            InstanceArgument::Machine(value) => Some(ContractExpression::ProgramExpression(
                ProgramExpression::Value(
                    if binder == Sort::ProgramInteger(crate::kernel::MachineIntegerType::UInt64) {
                        ProgramValue::UInt64(value.clone())
                    } else {
                        ProgramValue::Int32(value.clone())
                    },
                ),
            )),
            InstanceArgument::Pointer(pointer) => Some(ContractExpression::ProgramExpression(
                ProgramExpression::Value(ProgramValue::Pointer(pointer.clone())),
            )),
            InstanceArgument::Integer(_) => None,
        };

        let checked = self.state
            .apply_instantiate(lowered_quantified, argument, explicit_premises.as_deref())
            .map_err(|error| match error {
                PropositionCloseError::NotProposition => {
                    self.step_error("`instantiate` requires a proposition goal")
                }
                PropositionCloseError::InstantiatePremiseUnavailable(index, premise) => {
                    let written = surface_premises.get(index).map_or_else(
                        || self.render_diagnostic_proposition(&premise),
                        describe_click_proposition,
                    );
                    self.step_error(format!(
                        "`instantiate using` premise {} `{written}` is not an available exact fact",
                        index + 1
                    ))
                }
                PropositionCloseError::InstantiateQuantifiedUnavailable => {
                    self.step_error(format!(
                        "`instantiate` quantified fact is not exactly available: {}",
                        describe_click_proposition(&surface_quantified)
                    ))
                }
                PropositionCloseError::InstantiateInvalid(
                    crate::kernel::proof::fact_reasoning::ForallInstantiationError::MissingGuard(
                        missing,
                    ),
                ) if bare => {
                    self.step_error_with_requirement(
                        "`instantiate` without `using` needs each instantiated guard as an exact fact; prove the missing guard first with `have`, or list the facts it follows from with `using { ... }`",
                        None,
                        Some(("missing exact guard", Box::new(missing), None)),
                    )
                }
                PropositionCloseError::InstantiateInvalid(message) => self.step_error(format!(
                    "`instantiate` failed: {}",
                    format_forall_instantiation_error(message, &|missing| {
                        self.render_diagnostic_proposition(missing)
                    })
                )),
                _ => unreachable!("kernel returned an unrelated instantiate error"),
            })?;
        // Keep the kernel-checked conclusion's spelling in the same immutable
        // proof scope. This index supplies no fact and is optional when the
        // written shape cannot be recorded.
        if (matches!(self.context.as_ref(), ProofContext::FixedState(_))
            || self.focused_outcome_data().is_some())
            && let ClickProposition::ForAll { name, body, .. } = &surface_quantified
            && let Some(surface_argument) = surface_argument
            && let [conclusion] = checked.state().checked_facts()
            && let Ok(mut written) = substitute_click_proposition(
                body,
                &BTreeMap::from([(name.clone(), surface_argument)]),
            )
        {
            while let ClickProposition::Implies(_, next) = written {
                written = *next;
            }
            let mut locals = checked.state().locals().clone();
            let mut spelled = locals.checked_lowerings.clone();
            if spelled.record_lowering(&written, conclusion).is_ok() {
                locals.checked_lowerings = spelled;
                return Ok(checked.with_locals(locals));
            }
        }
        Ok(checked)
    }

    pub(super) fn apply_rewrite(
        &self,
        surface_equality: &ClickProposition,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        match self.context.as_ref() {
            ProofContext::Pure(_) => self.apply_pure_rewrite(surface_equality),
            ProofContext::FixedState(context) => self.apply_fixed_state_rewrite(
                &FixedStateOperationView::from_fixed_state(context),
                surface_equality,
            ),
            ProofContext::Execution(_) if self.focused_outcome_data().is_some() => {
                let view = self
                    .outcome_fixed_state_view()
                    .expect("a focused outcome judgment resolves its fixed-state view");
                self.apply_fixed_state_rewrite(&view, surface_equality)
            }
            // A nested execution `have` is still a proposition proof. It
            // borrows the execution context only for lowering; its scope join
            // restores the exact outer frontier after this checked rewrite.
            ProofContext::Execution(_) if self.goal().is_some() => {
                self.apply_pure_rewrite(surface_equality)
            }
            ProofContext::Execution(_) => {
                Err(self.step_error("`rewrite` requires a proposition proof"))
            }
        }
    }

    // Keep lowering's large proposition temporaries out of the common rewrite
    // dispatcher frame; the expansion small-stack test pins this boundary.
    #[inline(never)]
    pub(super) fn apply_pure_rewrite(
        &self,
        surface_equality: &ClickProposition,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let goal = Box::new(
            self.proposition_goal("`rewrite` requires a proposition goal")?
                .clone(),
        );
        let equality =
            Box::new(self.lower_surface_proposition(surface_equality, "`rewrite` equality")?);
        self.finish_rewrite(goal, equality, surface_equality, || {
            self.diagnostic_naming_tables()
        })
    }

    /// The names a diagnostic spells this proof's lowered terms with: a pure
    /// theorem's parameters, or the locals of the execution state a nested
    /// `have` reads, so a refusal never prints a kernel variable where the
    /// reader wrote a name.
    /// [`Self::diagnostic_naming_tables`], deferred to rendering when the
    /// proof's parameter binding shares its lists.
    pub(in crate::surface::proof) fn diagnostic_naming(&self) -> super::DiagnosticNaming {
        let deferred = |state: &ExecutionState, binding: ParameterBinding<'_>| {
            binding.naming.map(|naming| {
                super::DiagnosticNaming::LocalsThenParameters(state.clone(), naming.clone())
            })
        };
        let deferred = match self.context.as_ref() {
            ProofContext::Pure(_) => None,
            ProofContext::FixedState(context) => {
                deferred(context.fixed_state.state, context.parameter_binding)
            }
            ProofContext::Execution(context) => self
                .execution()
                .and_then(|execution| deferred(&execution.core.state, context.parameter_binding())),
        };
        deferred.unwrap_or_else(|| {
            let (names, values) = self.diagnostic_naming_tables();
            super::DiagnosticNaming::Tables(names, values)
        })
    }

    pub(in crate::surface::proof) fn diagnostic_naming_tables(
        &self,
    ) -> (
        Vec<crate::languages::interface::ImportedParameter>,
        Vec<ProgramExpression>,
    ) {
        // The state's locals first, then the entry parameters: a local names
        // the value it holds here, and a parameter the value it was entered
        // with, and either may be what a lowered term reads.
        let with_locals = |state: &ExecutionState,
                           parameters: &[crate::languages::interface::ImportedParameter],
                           arguments: &[ProgramExpression]| {
            let (mut names, mut values) = crate::surface::diagnostics::local_naming_tables(state);
            names.extend(parameters.iter().cloned());
            values.extend(arguments.iter().cloned());
            (names, values)
        };
        match self.context.as_ref() {
            ProofContext::Pure(context) => {
                crate::surface::diagnostics::value_naming_tables(&context.theorem_context.values)
            }
            ProofContext::FixedState(context) => with_locals(
                context.fixed_state.state,
                context.parameter_binding.parameters,
                context.parameter_binding.arguments,
            ),
            ProofContext::Execution(context) => match self.execution() {
                Some(execution) => with_locals(
                    &execution.core.state,
                    context.parsed_function.parameters(),
                    context.arguments,
                ),
                None => (
                    context.parsed_function.parameters().to_vec(),
                    context.arguments.to_vec(),
                ),
            },
        }
    }

    // Keep fixed-state lowering and unfold temporaries out of the common rewrite
    // dispatcher frame; the expansion small-stack test pins this boundary.
    #[inline(never)]
    pub(super) fn apply_fixed_state_rewrite(
        &self,
        view: &FixedStateOperationView<'_>,
        surface_equality: &ClickProposition,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let unfolded_predicates = self.active_unfolded_predicates();
        let goal = Box::new(
            unfold_predicates_in_proposition(
                view.spec_definitions,
                &unfolded_predicates,
                self.proposition_goal("`rewrite` requires a proposition goal")?,
                self.facts().assumptions(),
            )
            .map_err(|message| {
                self.step_error(format!("could not unfold `rewrite` goal: {message}"))
            })?,
        );
        let lookup = |map: &SurfacePropositionMap, surface: &ClickProposition| {
            map.available_kernel_matching(surface, |kernel| {
                self.facts().materialization_available(kernel)
            })
            .map(|kernel| Box::new(kernel.clone()))
            .or_else(|| {
                let reverse = reverse_surface_equality(surface)?;
                let kernel = map.available_kernel_matching(&reverse, |kernel| {
                    self.facts().materialization_available(kernel)
                })?;
                reverse_kernel_equality(kernel.clone()).map(Box::new)
            })
        };
        // Authored spellings keep their existing precedence and remain the
        // spelling used to present the rewritten goal. Normalize only the
        // separate checked lookup key and the fresh-lowering fallback.
        let equality = if let Some(recorded) = lookup(view.surface_propositions, surface_equality) {
            recorded
        } else {
            let normalized = self.substitute_fixed_state_locals_in_proposition(surface_equality)?;
            let recorded = (matches!(self.context.as_ref(), ProofContext::FixedState(_))
                || self.focused_outcome_data().is_some())
            .then(|| lookup(&self.state().locals().checked_lowerings, &normalized))
            .flatten();
            match recorded {
                Some(equality) => equality,
                None => Box::new(
                    lower_fixed_state_proposition_with_assumptions(
                        &normalized,
                        self.facts().assumptions(),
                        view.parameter_binding,
                        view.fixed_state,
                        view.spec_definitions,
                    )
                    .map_err(|message| {
                        let source =
                            crate::surface::printing::source_click_proposition(surface_equality);
                        let source: String = source.chars().take(1024).collect();
                        self.step_error(format!(
                            "could not lower `rewrite` equality: {message}\n  equality: {source}"
                        ))
                    })?,
                ),
            }
        };
        let equality = Box::new(
            unfold_predicates_in_proposition(
                view.spec_definitions,
                &unfolded_predicates,
                &equality,
                self.facts().assumptions(),
            )
            .map_err(|message| {
                self.step_error(format!("could not unfold `rewrite` equality: {message}"))
            })?,
        );
        self.finish_rewrite(goal, equality, surface_equality, || {
            let (mut parameters, mut arguments) =
                crate::surface::diagnostics::local_naming_tables(view.fixed_state.state);
            parameters.extend(view.parameter_binding.parameters.iter().cloned());
            arguments.extend(view.parameter_binding.arguments.iter().cloned());
            (parameters, arguments)
        })
    }

    // Keep the by-value goal/equality pair in the rewrite worker rather than
    // every caller's frame; the expansion small-stack test pins this boundary.
    #[inline(never)]
    pub(super) fn finish_rewrite(
        &self,
        goal: Box<Proposition>,
        equality: Box<Proposition>,
        surface_equality: &ClickProposition,
        // Naming can scan unrelated locals. Construct these tables only
        // on refusal, preserving the selected fixed state's diagnostic names.
        naming_tables: impl FnOnce() -> (
            Vec<crate::languages::interface::ImportedParameter>,
            Vec<ProgramExpression>,
        ),
    ) -> Result<CheckedFocusedTransition, ClickError> {
        // Name both sides: a rewrite that finds nothing to replace is
        // almost always an equality whose left side lowered to a different
        // term than the goal's (a load of another width, a value where the
        // goal has a load), which only the two lowered forms show.
        // An equality written over exact observations, `22208 ==
        // to_integer(n)`, is stated as its native comparison but rewrites the
        // Integer terms it was written over. Its sides are read as the
        // Integer operands of the same comparison written as an order, which
        // keeps each observation's signedness; that Integer equality is a
        // reading of the native fact, tried first, and the native form only
        // when it does not apply.
        let observed_reading = match surface_equality {
            ClickProposition::Comparison {
                left,
                operator: ComparisonOperator::Equal,
                right,
            } if crate::surface::proof::smart_closures::observes_exact_value(left)
                || crate::surface::proof::smart_closures::observes_exact_value(right) =>
            {
                let order = ClickProposition::Comparison {
                    left: left.clone(),
                    operator: ComparisonOperator::LessEqual,
                    right: right.clone(),
                };
                self.lower_integer_surface_proposition(&order, "`rewrite` equality")
                    .ok()
                    .map(|lowered| {
                        crate::kernel::machine_integer::comparison::integer_observations_of_native_comparison(
                            &lowered,
                        )
                        .into_iter()
                        .next()
                        .unwrap_or(lowered)
                    })
                    .and_then(|reading| match reading {
                        Proposition::ConditionIs(
                            ConditionTerm::IntegerLessEqual(left, right),
                            true,
                        ) => Some(Proposition::ConditionIs(
                            ConditionTerm::integer_equal((*left).clone(), (*right).clone()),
                            true,
                        )),
                        _ => None,
                    })
                    .and_then(|reading| {
                        self.facts()
                            .check_equality_rewrite(&goal, &reading)
                            .ok()
                            .filter(|rewritten| rewritten.proposition() != goal.as_ref())
                    })
            }
            _ => None,
        };
        let checked = match observed_reading {
            Some(rewritten) => Ok(rewritten),
            None => self.facts().check_equality_rewrite(&goal, &equality),
        };
        let mut rewritten = checked.map_err(|message| {
            let (parameters, arguments) = naming_tables();
            let mut reason = message;
            if let Some(mismatch) =
                crate::surface::diagnostics::describe_proposition_version_mismatch(
                    &goal,
                    &[equality.as_ref()],
                    "the equality was stated",
                    ParameterBinding::new(&parameters, &arguments),
                )
            {
                reason.push_str(&format!("\n  {mismatch}"));
            }
            // The structured diagnostic renders the requested equality and
            // current goal together, with the same names and label map as
            // premises and trace additions.
            self.step_error_with_requirement(
                reason,
                None,
                Some(("equality", equality.clone(), None)),
            )
        })?;
        let surface_goal = self.surface_goal().and_then(|surface_goal| {
            let checked_candidate = |candidate: ClickProposition| {
                self.lower_surface_proposition_direct(&candidate, "rewritten Surface goal")
                    .ok()
                    .filter(|lowered| rewritten.try_present_as(lowered))
                    .map(|_| candidate)
            };
            let mut checked_candidate = checked_candidate;
            rewrite_click_proposition_by_surface_equality(surface_goal, surface_equality)
                .and_then(&mut checked_candidate)
                .or_else(|| {
                    crate::surface::lowering::rewrite_surface_equality_preserving_states(
                        surface_goal,
                        surface_equality,
                    )
                    .and_then(checked_candidate)
                })
        });
        let surface_goal = surface_goal.or_else(|| self.spelled_goal(rewritten.proposition()));
        let presentation = self.refinement_presentation(surface_goal, None);
        let (obligation, facts) =
            rewritten.into_obligation(presentation, self.refinement_outcome());
        let branch = OpenBranch::new(
            Obligation::Proposition(obligation),
            self.refined_branch_state(facts),
        );
        Ok(CheckedFocusedTransition::replacing(
            self.state().locals().clone(),
            Some(branch),
            Vec::new(),
            Vec::new(),
        ))
    }

    pub(super) fn apply_extract(
        &self,
        surface: &ClickProposition,
    ) -> Result<KernelProofHandle, ClickError> {
        let proposition = match self.chosen_projection_for_extract(surface)? {
            Some(proposition) => proposition,
            None => self.lower_cited_surface_proposition(surface, "`extract` proposition")?,
        };
        self.state.apply_extract(proposition).map_err(|error| match error {
            // Lowering need not retain source names; the refusal concerns
            // the citation the user wrote, rather than its anonymous terms.
            PropositionCloseError::ExtractUnavailable => self.step_error(format!(
                "`extract` proposition is not a proper conjunct, a checked disjunction projection, a discharged implication consequent, or a field equality of an exact same-constructor equality: {}",
                crate::surface::printing::source_click_proposition(surface)
            )),
            PropositionCloseError::Unavailable => {
                self.step_error("`extract` requires an open proof branch")
            }
            _ => unreachable!("kernel returned an unrelated extract error"),
        })
    }

    /// Resolves an `extract` citation only through the current chosen
    /// existential's checked presentation record.  Returning the recorded
    /// kernel leaf does not grant authority: `ProofState::apply_extract`
    /// still performs the exact proper-conjunct membership check.
    fn chosen_projection_for_extract(
        &self,
        surface: &ClickProposition,
    ) -> Result<Option<Proposition>, ClickError> {
        if let Some(leaf) = self.existential_projection_for_extract(surface)? {
            return Ok(Some(leaf));
        }
        let Some(Obligation::Proposition(_)) = self.focused_obligation() else {
            return Ok(None);
        };
        let Some(execution) = self.execution() else {
            return Ok(None);
        };
        let Some(view) = self.execution_proposition_fixed_state_view() else {
            return Ok(None);
        };
        let entry_memory_state = self
            .execution_context()
            .and_then(|context| context.constants.function_entry_state.as_ref())
            .map(|state| crate::kernel::MemoryStateIdentity::of(state.memory()));
        let expected_selector = ProgramPointSelector::ProgramPoint(ProgramPointRef {
            region: CodeRegionRef::Function,
            kind: ProgramPointKind::Entry,
        });
        let Some(projection) = execution.presentation.chosen_projection.as_ref() else {
            return Ok(None);
        };
        let Some(context) = self.execution_context() else {
            return Ok(None);
        };
        let Some(retained_source) = context
            .constants
            .caller_requirement_index
            .lookup_source_requirement(&projection.source_id)
        else {
            return Ok(None);
        };
        if projection.source_token.source_id != projection.source_id
            || !projection.source_token.connective_path.is_empty()
            || retained_source.source_id != projection.source_id
            || retained_source.principal_fact_index != projection.principal_fact_index
            || retained_source.principal_fact != projection.source_requirement
            || retained_source.source_proposition != projection.source_proposition
            || context
                .constants
                .execution_start_facts
                .get(projection.principal_fact_index)
                != Some(&projection.source_requirement)
            || entry_memory_state != Some(projection.source_memory_state)
            || retained_source.entry_memory_state != projection.source_memory_state
            || projection.source_selector != expected_selector
        {
            return Ok(None);
        }
        let mut checked_source = projection.source_requirement.clone();
        let unfolded_predicates = self.active_unfolded_predicates();
        if !matches!(checked_source, Proposition::Exists { .. }) && !unfolded_predicates.is_empty()
        {
            checked_source = unfold_predicates_in_proposition(
                view.spec_definitions,
                &unfolded_predicates,
                &checked_source,
                self.facts().assumptions(),
            )
            .map_err(|message| self.step_error(message))?;
        }
        if checked_source != projection.checked_source {
            return Ok(None);
        }
        let Some(binding) = self.local_binding(&projection.chosen_name) else {
            return Ok(None);
        };
        if !binding_names_chosen_variable(binding, projection.chosen_variable) {
            return Ok(None);
        }
        let surface = self.substitute_fixed_state_locals_in_proposition(surface)?;
        let chosen_body = match checked_source {
            Proposition::Exists { var, body, .. } => match binding {
                ContractExpression::ProgramExpression(ProgramExpression::Value(
                    ProgramValue::Int32(_),
                )) => substitute_int32_variable_in_proposition(
                    &body,
                    var,
                    MachineTerm::Variable(projection.chosen_variable),
                ),
                ContractExpression::ProgramExpression(ProgramExpression::Value(
                    ProgramValue::Pointer(pointer),
                )) => crate::kernel::substitute_pointer_value_in_proposition(&body, var, pointer)
                    .map_err(|error| self.step_error(&error))?,
                _ => return Ok(None),
            },
            _ => return Ok(None),
        };
        let Some(leaf) = projection_leaf_for_extract(
            &projection.leaves,
            &surface,
            &chosen_body,
            &projection.source_id,
        ) else {
            return Ok(None);
        };
        Ok(Some(leaf.kernel.clone()))
    }

    fn existential_projection_for_extract(
        &self,
        surface: &ClickProposition,
    ) -> Result<Option<Proposition>, ClickError> {
        if !matches!(self.focused_obligation(), Some(Obligation::Proposition(_))) {
            return Ok(None);
        }
        let Some(projection) = self
            .execution()
            .and_then(|execution| execution.presentation.existential_projection.as_ref())
        else {
            return Ok(None);
        };
        let Some(entry_state) = self
            .execution_context()
            .and_then(|context| context.constants.function_entry_state.as_ref())
        else {
            return Ok(None);
        };
        if projection.source_memory_state
            != crate::kernel::MemoryStateIdentity::of(entry_state.memory())
            || !self.facts().contains_top_level(&projection.chosen_body)
        {
            return Ok(None);
        }
        let Some(binding) = self.local_binding(&projection.chosen_name) else {
            return Ok(None);
        };
        if !binding_names_chosen_variable(binding, projection.chosen_variable) {
            return Ok(None);
        }
        // A leaf names the chosen binder, which the citation may already
        // spell as its bound value; compare both after the same substitution.
        let cited = self.substitute_fixed_state_locals_in_proposition(surface)?;
        let mut leaf_surfaces = Vec::with_capacity(projection.leaves.len());
        for leaf in &projection.leaves {
            leaf_surfaces.push(self.substitute_fixed_state_locals_in_proposition(&leaf.surface)?);
        }
        let mut matches = projection
            .leaves
            .iter()
            .zip(&leaf_surfaces)
            .filter(|(leaf, leaf_surface)| leaf.surface == cited || **leaf_surface == cited)
            .map(|(leaf, _)| leaf);
        let leaf = match (matches.next(), matches.next()) {
            (Some(leaf), None) => leaf,
            _ => return Ok(None),
        };
        if proposition_at_connective_path(&projection.chosen_body, &leaf.connective_path)
            != Some(&leaf.kernel)
        {
            return Ok(None);
        }
        Ok(Some(leaf.kernel.clone()))
    }

    /// The fixed-state data a result-aware checker consumes, resolved
    /// either from a fixed-state proof's borrowed context or from a focused branch
    /// function-outcome goal on an execution proof. This is the goal-aware
    /// fixed-state view: outcome goals own their result, post-state, surface
    /// lowerings, and effect facts, and borrow the frontier state for the
    /// remaining program-outcome proof data.
    pub(in crate::surface::proof) fn outcome_fixed_state_view(
        &self,
    ) -> Option<FixedStateOperationView<'_>> {
        self.outcome_fixed_state_view_with_effects(OutcomeEffectContext::Path)
    }

    /// Fixed-state data for a proposition scope opened on an execution
    /// frontier before a function outcome exists. The nested goal borrows the
    /// frontier state solely for lowering and requirement selection;
    /// checked fixed-state steps can refine only that proposition and proof-local
    /// bindings.
    pub(in crate::surface::proof) fn execution_fixed_state_view(
        &self,
    ) -> Option<FixedStateOperationView<'_>> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return None;
        };
        let execution = self.focused_branch()?.state.execution.as_deref()?;
        Some(FixedStateOperationView {
            claim_label: context.claim_label,
            tactic_index: context.tactic_index,
            effect_facts: &execution.core.effect_facts,
            parameter_binding: context.parameter_binding(),
            fixed_state: FixedStateFrame::new(
                context.old_reference_state(&execution.core.frontier, &execution.core.state),
                &execution.core.state,
                None,
                &execution.presentation.recorded_states,
            ),
            surface_propositions: &execution.presentation.surface_propositions,
            spec_definitions: SpecDefinitions::new(
                context.spec_definitions.predicates,
                context.spec_definitions.functions,
            ),
            theorem_environment: context.theorem_environment,
            original_requirements: context.function_block.requires(),
            requirement_facts: FixedStateFacts::List(&context.constants.execution_start_facts),
        })
    }

    pub(in crate::surface::proof) fn execution_proposition_fixed_state_view(
        &self,
    ) -> Option<FixedStateOperationView<'_>> {
        let Obligation::Proposition(goal) = self.focused_obligation()? else {
            return None;
        };
        if goal.outcome.is_some() {
            return None;
        }
        self.execution_fixed_state_view()
    }

    /// Fixed-state data for a top-level `choose` on the execution frontier.
    /// Unlike a nested proposition proof, this operation refines the entry
    /// facts and proof-local bindings without needing a proposition goal of
    /// its own.
    pub(in crate::surface::proof) fn execution_frontier_fixed_state_view(
        &self,
    ) -> Option<FixedStateOperationView<'_>> {
        matches!(self.focused_obligation(), Some(Obligation::Frontier(_)))
            .then(|| self.execution_fixed_state_view())
            .flatten()
    }

    /// The focused branch judgment's result-aware outcome proof data: a function-outcome
    /// goal owns its data, and a proposition judgment stated at an outcome
    /// borrows that outcome's data by identity.
    pub(in crate::surface::proof) fn focused_outcome_data(&self) -> Option<&Arc<OutcomeProofData>> {
        match self.focused_obligation()? {
            Obligation::FunctionOutcome(goal) => Some(&goal.data),
            Obligation::Proposition(goal) => goal.outcome.as_ref(),
            Obligation::Frontier(_) => None,
        }
    }

    /// Selects the edge of the checked call split `depth` nested `outcomes`
    /// inside the outermost one. The labels were derived from the exact
    /// source shape and checked outcome when the outcome goal was created,
    /// not from a user assertion.
    pub(in crate::surface::proof) fn checked_call_returned(
        &self,
        depth: usize,
    ) -> Result<bool, ClickError> {
        self.focused_outcome_data()
            .and_then(|data| data.call_routes.get(depth).copied())
            .ok_or_else(|| {
                self.step_error("`outcomes` requires a checked returned/threw call edge")
            })
    }

    /// The arm the `match` deferred at `occurrence` took on the focused
    /// outcome path, and that arm's field bindings.
    pub(in crate::surface::proof) fn checked_outcome_match_arm(
        &self,
        occurrence: usize,
    ) -> Result<(usize, PersistentMap<String, ContractExpression>), ClickError> {
        if !matches!(
            self.focused_obligation(),
            Some(Obligation::FunctionOutcome(_))
        ) {
            return Err(self.step_error("post-execution `match` requires a focused outcome goal"));
        }
        self.focused_outcome_data()
            .expect("a focused outcome judgment resolves its proof data")
            .match_arms
            .get(&occurrence)
            .cloned()
            .ok_or_else(|| {
                self.step_error("this outcome path records no arm for the post-execution `match`")
            })
    }

    /// Decides one explicit post-execution `if` from the focused branch outcome's
    /// exact fact context. The syntax driver may use the returned polarity to
    /// choose which source arm to visit, but it cannot manufacture a fact or
    /// successor: both alternatives are lowered and the kernel assumptions
    /// must establish exactly one of them on this `Proof` path.
    pub(in crate::surface::proof) fn checked_outcome_if_value(
        &self,
        condition: &ClickProposition,
        execution_route: Option<usize>,
    ) -> Result<bool, ClickError> {
        if !matches!(
            self.focused_obligation(),
            Some(Obligation::FunctionOutcome(_))
        ) {
            return Err(self.step_error("post-execution `if` requires a focused outcome goal"));
        }
        let data = self
            .focused_outcome_data()
            .expect("a focused outcome judgment resolves its proof data");
        if let Some(position) = execution_route {
            return data.branch_decisions.value_for_route(position, condition);
        }
        let mut recorded_value = None;
        for decision in data.branch_decisions.iter() {
            if &decision.condition != condition {
                continue;
            }
            if recorded_value.is_some_and(|value| value != decision.value) {
                return Err(self.step_error(
                    "focused outcome records both sides of the post-execution `if` condition",
                ));
            }
            recorded_value = Some(decision.value);
        }
        if let Some(value) = recorded_value {
            return Ok(value);
        }
        let negative_surface = ClickProposition::Not(Box::new(condition.clone()));
        let positive =
            self.lower_surface_proposition(condition, "post-execution `if` condition")?;
        let negative =
            self.lower_surface_proposition(&negative_surface, "post-execution `if` negation")?;
        let assumptions = self.facts().assumptions();
        let positive_holds = self.facts().contains(&positive)
            || crate::kernel::proof::fact_reasoning::holds_by_lookup_or_decision(
                assumptions,
                &positive,
            );
        let negative_holds = self.facts().contains(&negative)
            || crate::kernel::proof::fact_reasoning::holds_by_lookup_or_decision(
                assumptions,
                &negative,
            )
            || fact_conflicts_with_assumptions(&positive, assumptions);
        match (positive_holds, negative_holds) {
            (true, false) => Ok(true),
            (false, true) => Ok(false),
            (false, false) => Err(self.step_error(format!(
                "focused outcome does not decide the post-execution `if` condition: `{}`",
                crate::surface::diagnostics::describe_click_proposition(condition)
            ))),
            (true, true) => Err(self.step_error(
                "focused outcome proves both sides of the post-execution `if` condition",
            )),
        }
    }

    /// Decides which arm of a `cases` after execution this focused outcome
    /// takes: `true` for the left side of `disjunction`. A recorded
    /// decision chooses the arm the path entered; otherwise a disjunct the
    /// outcome's facts establish does. Like `checked_outcome_if_value` this
    /// only selects source; the arm's tactics are checked on the path.
    pub(in crate::surface::proof) fn checked_outcome_cases_value(
        &self,
        disjunction: &ClickProposition,
        execution_route: Option<usize>,
    ) -> Result<bool, ClickError> {
        if !matches!(
            self.focused_obligation(),
            Some(Obligation::FunctionOutcome(_))
        ) {
            return Err(self.step_error("post-execution `cases` requires a focused outcome goal"));
        }
        let data = self
            .focused_outcome_data()
            .expect("a focused outcome judgment resolves its proof data");
        if let Some(position) = execution_route {
            return data.branch_decisions.value_for_route(position, disjunction);
        }
        let (left, right) =
            crate::surface::split_case_disjunction(disjunction).ok_or_else(|| {
                self.step_error("a post-execution `cases` split is not on a disjunction")
            })?;
        for (surface, value) in [(&left, true), (&right, false)] {
            if data
                .branch_decisions
                .value_for_key(surface, ExecutionBranchDecisions::key(surface))?
                == Some(true)
            {
                return Ok(value);
            }
        }
        let assumptions = self.facts().assumptions();
        for (surface, value) in [(&left, true), (&right, false)] {
            let fact = self.lower_surface_proposition(surface, "post-execution `cases` case")?;
            if self.facts().contains(&fact)
                || crate::kernel::proof::fact_reasoning::holds_by_lookup_or_decision(
                    assumptions,
                    &fact,
                )
            {
                return Ok(value);
            }
        }
        Err(self.step_error(format!(
            "focused outcome does not decide which side of the `cases` disjunction holds: `{}`",
            crate::surface::diagnostics::describe_click_proposition(disjunction)
        )))
    }

    pub(in crate::surface::proof) fn post_execution_if_is_path_decided(
        &self,
        condition: &ClickProposition,
        disjunction: bool,
    ) -> Result<bool, ClickError> {
        self.require_execution_frontier("post-execution `if`")?;
        let execution = self
            .execution()
            .ok_or_else(|| self.step_error("post-execution `if` lost its execution frontier"))?;
        if !execution.core.frontier.is_at_function_exit() {
            return Err(self.step_error("post-execution `if` requires function exit"));
        }
        let checked =
            execution.core.frontier.execution().ok_or_else(|| {
                self.step_error("post-execution `if` has no checked execution paths")
            })?;
        let sides = if disjunction {
            Some(
                crate::surface::split_case_disjunction(condition).ok_or_else(|| {
                    self.step_error("a post-execution `cases` split is not on a disjunction")
                })?,
            )
        } else {
            None
        };
        for path_index in 0..checked.paths().len() {
            check_verification_deadline()?;
            let provenance = execution.provenance_for_outcome(path_index);
            // A `cases` arm records that its own disjunct holds.
            if let Some((left, right)) = &sides {
                let holds = |surface: &ClickProposition| {
                    provenance
                        .branch_decisions
                        .value_for_key(surface, ExecutionBranchDecisions::key(surface))
                        .map(|value| value == Some(true))
                };
                if !holds(left)? && !holds(right)? {
                    return Ok(false);
                }
                continue;
            }
            let mut recorded = None;
            for decision in provenance.branch_decisions.iter() {
                if &decision.condition != condition {
                    continue;
                }
                if recorded.is_some_and(|value| value != decision.value) {
                    return Err(self.step_error(
                        "checked execution path records both sides of the post-execution `if` condition",
                    ));
                }
                recorded = Some(decision.value);
            }
            if recorded.is_none() {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Resolves the view with the caller's effect-availability context: the
    /// transport checker consumes the path's own execution facts, while the
    /// theorem checker consumes the frontier-wide effect set.
    pub(in crate::surface::proof) fn outcome_fixed_state_view_with_effects(
        &self,
        effects: OutcomeEffectContext,
    ) -> Option<FixedStateOperationView<'_>> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return None;
        };
        let data = self.focused_outcome_data()?;
        let execution = self.focused_branch()?.state.execution.as_deref()?;
        Some(FixedStateOperationView {
            claim_label: context.claim_label,
            tactic_index: context.tactic_index,
            effect_facts: match effects {
                OutcomeEffectContext::Path => data.core.effect_facts.as_ref(),
                OutcomeEffectContext::Frontier => &execution.core.effect_facts,
            },
            parameter_binding: context.parameter_binding(),
            fixed_state: FixedStateFrame::new(
                context.old_reference_state(&execution.core.frontier, &execution.core.state),
                &data.core.state,
                Some(data.core.result.as_ref()),
                &data.recorded_states,
            ),
            surface_propositions: &data.surface_propositions,
            spec_definitions: SpecDefinitions::new(
                context.spec_definitions.predicates,
                context.spec_definitions.functions,
            ),
            theorem_environment: context.theorem_environment,
            original_requirements: context.function_block.requires(),
            requirement_facts: FixedStateFacts::List(&context.constants.execution_start_facts),
        })
    }

    pub(super) fn apply_transport_using(
        &self,
        source: &ClickProposition,
        target: &ClickProposition,
        premises: &[ClickProposition],
    ) -> Result<CheckedFocusedTransition, ClickError> {
        match self.context.as_ref() {
            ProofContext::FixedState(context) => self.apply_fixed_state_transport_using(
                source,
                target,
                premises,
                &FixedStateOperationView::from_fixed_state(context),
            ),
            // A focused branch function-outcome goal transports result-aware facts
            // through the same fixed-state checker, reading its data from the goal.
            ProofContext::Execution(_) if self.focused_outcome_data().is_some() => {
                let view = self
                    .outcome_fixed_state_view()
                    .expect("a focused outcome judgment resolves its fixed-state view");
                self.apply_fixed_state_transport_using(source, target, premises, &view)
            }
            // A nested `have` at an execution frontier is a proposition
            // judgment borrowing that outcome's fixed-state environment. Keep
            // goal-local binder substitutions (`intro` variables) on the
            // fixed-state operation instead of routing through the outer execution
            // transport, which has no proposition-goal bindings.
            ProofContext::Execution(_) if self.goal().is_some() => {
                let view = self
                    .execution_proposition_fixed_state_view()
                    .ok_or_else(|| {
                        self.step_error(
                            "`transport using` requires a fixed-state proposition proof",
                        )
                    })?;
                self.apply_fixed_state_transport_using(source, target, premises, &view)
            }
            ProofContext::Execution(context) => {
                self.apply_execution_transport_using(source, target, premises, context)
            }
            ProofContext::Pure(_) => self.apply_pure_transport_using(source, target, premises),
        }
    }

    /// The surface spellings recorded for this context's kernel facts.
    ///
    /// One place, so a diagnostic that wants to name a fact the way the proof
    /// wrote it reads the record premise selection already reads.
    pub(in crate::surface::proof) fn context_surface_propositions(
        &self,
    ) -> Option<&SurfacePropositionMap> {
        match self.context.as_ref() {
            ProofContext::Pure(context) => Some(&context.theorem_context.surface_requirements),
            ProofContext::FixedState(context) => Some(context.surface_propositions),
            ProofContext::Execution(_) => match self.focused_outcome_data() {
                Some(data) => Some(&data.surface_propositions),
                None => Some(&self.execution()?.presentation.surface_propositions),
            },
        }
    }

    /// Report the actual native checker result separately from source proof
    /// construction. Search-stage failures are retained by the solve driver;
    /// absence of a certificate is not evidence of a missing extent premise.
    pub(in crate::surface::proof) fn unproved_loadable_range_goal_reason(&self) -> Option<String> {
        let goal = self.surface_goal()?;
        loadable_surface_range_endpoints(goal)?;
        let target = describe_click_proposition(goal);
        let accepted = match self.goal()? {
            Proposition::MemoryLoadable {
                memory,
                base,
                bytes,
                wide: true,
            } => self
                .facts()
                .assumptions()
                .proves_native_memory_loadable(memory, base, bytes),
            _ => {
                return Some(format!(
                    "no checked source proof was constructed for `{target}`"
                ));
            }
        };
        Some(if accepted {
            format!(
                "`{target}` is accepted by the kernel native view checker in the current proof context, but `solve` did not construct a checked source proof"
            )
        } else {
            format!(
                "the kernel native view checker did not establish `{target}` in the current proof context; `solve` did not construct a checked source proof"
            )
        })
    }

    /// `transport(source, target) using { ... }` inside a pure theorem.
    ///
    /// A pure theorem has no C state, so everything the fixed-state checker
    /// reads from one — `old(...)`, `at(...)`, recorded lowerings, certified
    /// call and store effects, resource observations — has nothing to consult
    /// here. What is left is the part of the rule that never mentioned a
    /// state: every listed premise must be an exact available fact, the source
    /// must follow from exactly those premises, and the target must follow
    /// from the source under them. That last question is
    /// [`certified_fact_transport_reaches`] with no landing memory, the same
    /// function the fixed-state checker asks, so a pure theorem and a C proof
    /// accept the same conclusions from the same facts — including the
    /// memory-loadability decision, which both reach through the kernel's
    /// atomic derivation.
    pub(super) fn apply_pure_transport_using(
        &self,
        source: &ClickProposition,
        target: &ClickProposition,
        premises: &[ClickProposition],
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let mut explicit_premises = Vec::new();
        for surface_premise in premises {
            let premise =
                self.lower_cited_surface_proposition(surface_premise, "`transport using` premise")?;
            if !self.facts().listed_premise_available(&premise, &[], true) {
                return Err(self.step_error_with_requirement(
                    "`transport using` requires an exact premise",
                    None,
                    Some(("required transport premise", Box::new(premise), None)),
                ));
            }
            if !explicit_premises.contains(&premise) {
                explicit_premises.push(premise);
            }
        }
        let source = self.lower_cited_surface_proposition(source, "`transport` source")?;
        let selected_assumptions =
            crate::surface::verification::assumptions_from_propositions(&explicit_premises);
        if !exact_fact_is_available(&source, &explicit_premises)
            && !separation_bridged_fact_is_available(
                &source,
                &explicit_premises,
                &selected_assumptions,
                &[],
            )
            && crate::kernel::search::ProofSearch::derive_atomic_proposition(
                &(selected_assumptions),
                &source,
            )
            .is_none()
        {
            return Err(self.step_error(format!(
                "`transport using` requires a source derivable from its explicit facts: {}",
                self.render_diagnostic_proposition(&source)
            )));
        }
        let target = self.lower_cited_surface_proposition(target, "`transport` target")?;
        let transport_assumptions = selected_assumptions.assume_proposition(source.clone());
        if !self.facts().available_across_effects(&target, &[])
            && !certified_fact_transport_reaches(&source, &target, None, &transport_assumptions)
        {
            return Err(self.step_error(format!(
                "`transport using` target does not follow from the source fact and the listed premises\n  source: {}\n  target: {}",
                self.render_diagnostic_proposition(&source),
                self.render_diagnostic_proposition(&target)
            )));
        }
        let mut facts = self.facts().clone();
        let added_facts = if facts.contains(&target) {
            Vec::new()
        } else {
            vec![target.clone()]
        };
        let checked_facts = vec![source, target.clone()];
        facts = facts.with_kernel_checked_fact(target);
        let complete = self.goal().is_some_and(|goal| facts.contains(goal));
        Ok(self.checked_fact_transition(
            self.state().locals().clone(),
            facts,
            complete,
            added_facts,
            checked_facts,
        ))
    }

    fn attach_transport_check_error(&self, error: ClickError) -> ClickError {
        if let Some(required) = error.unresolved_requirement() {
            let (reason, label) = if required.context.as_deref() == Some("checked transport target")
            {
                (error.raw_summary(), "checked transport target")
            } else {
                (
                    "`transport using` requires an exact premise",
                    "required transport premise",
                )
            };
            self.step_error_with_requirement(
                reason,
                None,
                Some((label, Box::new(required.proposition.clone()), None)),
            )
        } else {
            self.attach_step_diagnostic(error)
        }
    }

    pub(super) fn apply_fixed_state_transport_using(
        &self,
        source: &ClickProposition,
        target: &ClickProposition,
        premises: &[ClickProposition],
        view: &FixedStateOperationView<'_>,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let (source, target, premises) = if premises.is_empty() {
            (source.clone(), target.clone(), premises.to_vec())
        } else {
            (
                self.substitute_fixed_state_locals_in_proposition(source)?,
                self.substitute_fixed_state_locals_in_proposition(target)?,
                premises
                    .iter()
                    .map(|premise| self.substitute_fixed_state_locals_in_proposition(premise))
                    .collect::<Result<Vec<_>, _>>()?,
            )
        };
        let checked = check_fixed_state_fact_transport_using_facts(
            &source,
            &target,
            &premises,
            view.claim_label,
            view.tactic_index,
            self.facts(),
            view.effect_facts,
            view.parameter_binding,
            view.fixed_state,
            view.surface_propositions,
            view.spec_definitions,
        )
        .map_err(|error| self.attach_transport_check_error(error))?;
        let mut facts = self.facts().clone();
        let added_facts = if facts.contains(&checked.target) {
            Vec::new()
        } else {
            vec![checked.target.clone()]
        };
        let checked_facts = vec![checked.source, checked.target.clone()];
        facts = facts.with_kernel_checked_fact(checked.target);
        // A focused branch outcome goal records the checker-owned source and target
        // lowerings atomically with its fact successor; the drain no longer
        // has to re-record them into a caller-owned map for this path.
        if let Some(Obligation::FunctionOutcome(goal)) = self.focused_obligation() {
            let mut updated = goal.clone();
            let mut data = (*updated.data).clone();
            data.surface_propositions
                .record_lowering(&source, &checked_facts[0])?;
            data.surface_propositions
                .record_lowering(&target, &checked_facts[1])?;
            updated.data = Arc::new(data);
            let branch_state = &self.focused_branch().expect("focused branch exists").state;
            // The transport above already established this exact target.
            // Retain its proposition judgment under the pre-transport facts,
            // as a completed `have` does, so subsequent return folds consume
            // the derivation rather than treating its conclusion as a new
            // ambient assumption. Close the operation directly from its
            // completed transport judgment.
            let transport_root = KernelProofObject::root(
                self.state().locals().clone(),
                OpenBranch::surface_proposition_at_outcome(
                    branch_state.clone(),
                    goal.data.clone(),
                    checked_facts[1].clone(),
                    target.clone(),
                ),
            );
            let completion = transport_root
                .publish_checked_result(self.state().locals().clone(), None, Vec::new(), Vec::new())
                .map_err(|_| self.step_error("checked transport lost its proposition judgment"))?
                .completed_proposition()
                .ok_or_else(|| {
                    self.step_error("checked transport did not close its proposition")
                })?;
            let mut execution = branch_state
                .execution
                .as_ref()
                .ok_or_else(|| self.step_error("return transport lost its execution evidence"))?
                .as_ref()
                .clone();
            execution
                .core
                .record_return_proposition(goal.path_index, completion, self.facts())
                .map_err(|message| self.step_error(message))?;
            let state = BranchState {
                facts,
                unfolded_predicates: branch_state.unfolded_predicates.clone(),
                execution: Some(Arc::new(execution)),
            };
            return Ok(CheckedFocusedTransition::replacing(
                self.state().locals().clone(),
                Some(OpenBranch::function_outcome(updated, state)),
                added_facts,
                checked_facts,
            ));
        }
        let complete = self.goal().is_some_and(|goal| facts.contains(goal));
        let mut locals = self.state().locals().clone();
        if matches!(self.context.as_ref(), ProofContext::FixedState(_))
            || self.focused_outcome_data().is_some()
        {
            let mut spelled = locals.checked_lowerings.clone();
            if spelled.record_lowering(&source, &checked_facts[0]).is_ok()
                && spelled.record_lowering(&target, &checked_facts[1]).is_ok()
            {
                locals.checked_lowerings = spelled;
            }
        }
        Ok(self.checked_fact_transition(locals, facts, complete, added_facts, checked_facts))
    }

    pub(super) fn apply_execution_transport_using(
        &self,
        source: &ClickProposition,
        target: &ClickProposition,
        premises: &[ClickProposition],
        context: &ExecutionProofContext<'a>,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        // Resolve only the named operands, as other proposition operations
        // do. Model-match pointers are proof bindings, not C local names.
        let source = self.substitute_fixed_state_locals_in_proposition(source)?;
        let target = self.substitute_fixed_state_locals_in_proposition(target)?;
        let premises = premises
            .iter()
            .map(|premise| self.substitute_fixed_state_locals_in_proposition(premise))
            .collect::<Result<Vec<_>, _>>()?;
        // A nested proposition proof stated at this frontier may transport
        // facts as well; the successor below preserves the goal's kind.
        let mut execution = self
            .execution()
            .cloned()
            .ok_or_else(|| self.step_error("execution-frontier proof lost its semantic state"))?;
        let proof_facts = self.facts();
        execution
            .core
            .register_current_call_views(proof_facts.assumptions());
        let checked_call_events = execution.core.checked_call_events();
        let _checked_call_event_scope =
            crate::kernel::CheckedCallEventScope::start_registering_views(&checked_call_events);
        let pre_state = context
            .old_reference_state(&execution.core.frontier, &execution.core.state)
            .clone();
        let checked = check_fixed_state_fact_transport_using_facts(
            &source,
            &target,
            &premises,
            context.claim_label,
            context.tactic_index,
            self.facts(),
            &execution.core.effect_facts,
            context.parameter_binding(),
            FixedStateFrame::new(
                &pre_state,
                &execution.core.state,
                None,
                &execution.presentation.recorded_states,
            ),
            &execution.presentation.surface_propositions,
            context.spec_definitions,
        )
        .map_err(|error| self.attach_transport_check_error(error))?;
        execution
            .presentation
            .surface_propositions
            .record_lowering(&source, &checked.source)?;
        execution
            .presentation
            .surface_propositions
            .record_lowering(&target, &checked.target)?;
        let mut facts = self.facts().clone();
        let added_facts = if facts.contains(&checked.target) {
            Vec::new()
        } else {
            vec![checked.target.clone()]
        };
        let checked_facts = vec![checked.source, checked.target.clone()];
        facts = facts.with_kernel_checked_fact(checked.target);
        let complete = self.goal().is_some_and(|goal| facts.contains(goal));
        Ok(self.checked_execution_transition(
            facts,
            complete,
            execution,
            added_facts,
            checked_facts,
        ))
    }
}

#[cfg(test)]
mod outcome_case_tests {
    use super::*;

    #[test]
    fn repeated_execution_decisions_keep_exact_routes_with_logarithmic_lookup() {
        let condition = ClickProposition::PredicateCall {
            name: "repeated_guard".to_string(),
            arguments: Vec::new(),
        };
        let wrong = ClickProposition::PredicateCall {
            name: "other_guard".to_string(),
            arguments: Vec::new(),
        };
        for size in [8usize, 32, 128, 512] {
            let mut decisions = ExecutionBranchDecisions::default();
            for position in 0..size {
                decisions.push(ExecutionBranchDecision {
                    fingerprint: std::sync::OnceLock::new(),
                    condition: condition.clone(),
                    value: position % 2 == 0,
                });
                decisions.record_route(
                    position,
                    Arc::new(ExecutionBranchDecision {
                        fingerprint: std::sync::OnceLock::new(),
                        condition: condition.clone(),
                        value: position % 2 == 0,
                    }),
                );
            }
            let mut comparisons = 0;
            for position in 0..size {
                assert_eq!(
                    decisions.value_for_route(position, &condition).unwrap(),
                    position % 2 == 0
                );
                comparisons += decisions.by_route.lookup_comparisons(&position);
            }
            assert!(comparisons <= size * (2 * size.ilog2() as usize + 1));
            assert!(decisions.value_for_route(size, &condition).is_err());
            assert!(decisions.value_for_route(0, &wrong).is_err());
            assert!(
                decisions.value(&condition).is_err(),
                "an unspecified occurrence stays ambiguous"
            );
        }
    }

    #[test]
    fn branch_decision_fingerprint_collisions_do_not_select_an_unrelated_case() {
        let selected = ClickProposition::PredicateCall {
            name: "selected".to_string(),
            arguments: Vec::new(),
        };
        let unrelated = ClickProposition::PredicateCall {
            name: "unrelated".to_string(),
            arguments: Vec::new(),
        };
        let mut decisions = ExecutionBranchDecisions::default();
        // Simulate a fingerprint collision: opposite values of a different
        // source condition must neither choose nor contradict this case.
        decisions.by_condition = decisions.by_condition.with_inserted(
            ExecutionBranchDecisions::key(&selected),
            vec![
                Arc::new(ExecutionBranchDecision {
                    fingerprint: std::sync::OnceLock::new(),
                    condition: unrelated.clone(),
                    value: false,
                }),
                Arc::new(ExecutionBranchDecision {
                    fingerprint: std::sync::OnceLock::new(),
                    condition: unrelated,
                    value: true,
                }),
                Arc::new(ExecutionBranchDecision {
                    fingerprint: std::sync::OnceLock::new(),
                    condition: selected.clone(),
                    value: true,
                }),
            ],
        );
        assert_eq!(decisions.value(&selected).unwrap(), Some(true));
    }

    #[test]
    fn nested_case_partition_work_visits_only_reached_nodes() {
        for size in [4, 8, 16, 32] {
            let conditions = (0..size)
                .map(|index| ClickProposition::PredicateCall {
                    name: format!("case_{index}"),
                    arguments: Vec::new(),
                })
                .collect::<Vec<_>>();
            let nodes = conditions
                .iter()
                .enumerate()
                .map(|(index, condition)| {
                    OutcomeNode::Case(OutcomeCase {
                        scope: None,
                        lexical_bindings: None,
                        occurrence: index,
                        fingerprint: ExecutionBranchDecisions::key(condition),
                        condition,
                        disjunction: false,
                        execution_route: None,
                        arms: [
                            if index + 1 < size {
                                Some(index + 1)
                            } else {
                                None
                            },
                            None,
                        ],
                    })
                })
                .collect::<Vec<_>>();
            let visits = std::cell::Cell::new(0);
            let mut leaves = 0;
            let mut facts = Vec::new();
            let root = ProofFacts::default();
            partition_outcome_cases(
                &nodes,
                Some(0),
                &root,
                &root,
                &mut facts,
                OutcomeProvenance {
                    terminal_statement_case: None,
                    checked_leaf_facts: None,
                    loop_return: None,
                    call_routes: Vec::new(),
                    branch_decisions: ExecutionBranchDecisions::default(),
                    match_arms: PersistentMap::default(),
                    case_obligations: PersistentMap::default(),
                    checked_haves: PersistentMap::default(),
                    surface_propositions: SurfacePropositionMap::default(),
                    recorded_states: RecordedStates::default(),
                    generated_load_bindings: PersistentMap::default(),
                },
                &|condition, _, _| {
                    visits.set(visits.get() + 1);
                    let ClickProposition::PredicateCall { name, .. } = condition else {
                        unreachable!()
                    };
                    Ok(Proposition::Predicate {
                        name: name.clone(),
                        arguments: Vec::new(),
                    })
                },
                &|_, _, _, _| unreachable!("the graph has no match"),
                &|_, _, _, _, _| unreachable!("the graph has no proposition obligations"),
                &mut |_, _| leaves += 1,
            )
            .unwrap();
            assert_eq!(visits.get(), size, "case-lowering work at size {size}");
            assert_eq!(
                leaves,
                size + 1,
                "no unrelated sibling combinations at size {size}"
            );
            assert!(facts.is_empty(), "each arm restores the shared fact cursor");
        }
    }

    #[cfg(test)]
    mod scaling_tests {
        include!(
            "../../../scaling_tests/surface/proof/proof_object/fixed_state_steps/outcome_case_tests.rs"
        );
    }
}

/// The written endpoints of a `loadable(base[start..end])` surface segment.
fn loadable_surface_range_endpoints(
    proposition: &ClickProposition,
) -> Option<(ContractExpression, ContractExpression)> {
    let ClickProposition::Loadable { segment } = proposition else {
        return None;
    };
    segment
        .surface_range()
        .map(|(_, start, end)| (start.clone(), end.clone()))
}

/// Whether a proof-local binding is the symbolic value `choose` introduced
/// for `variable`: a machine integer of any width, or a pointer offset.
fn binding_names_chosen_variable(binding: &ContractExpression, variable: Variable) -> bool {
    match binding {
        ContractExpression::ProgramExpression(ProgramExpression::Value(ProgramValue::Pointer(
            pointer,
        ))) => pointer.pointer().offset == PointerOffsetTerm::Variable(variable),
        ContractExpression::ProgramExpression(ProgramExpression::Value(value)) => {
            crate::kernel::MachineIntegerType::from_program_type(value.program_type())
                .is_some_and(|integer| *value == integer.symbolic_value(variable))
        }
        _ => false,
    }
}

#[path = "../driver/outcome_cases.rs"]
mod outcome_cases_driver;
