//! Simple-step dispatch (`apply_step`) and checked frame application.

use super::*;
use crate::kernel::LoweringIntroduction;
use crate::kernel::{CompareRelation, MachineIntegerType};
use crate::kernel::{binary_term, unary_term};
use crate::kernel::{
    bits32_constant, constant_i64, constant_u32, constant_u64, int32_constant, int64_constant,
    uint64_constant,
};

fn is_positive_predecessor_goal(proposition: &crate::kernel::Proposition) -> bool {
    let Some((
        crate::kernel::OldConditionTerm::Compare {
            format: crate::kernel::MachineIntegerType::Int32,
            relation: crate::kernel::CompareRelation::LessThan,
            left,
            right,
        },
        true,
    )) = proposition.old_condition()
    else {
        return false;
    };
    let binary_term!(Int32, Subtract, value, amount) = left.as_ref() else {
        return false;
    };
    signed_atom_matches(value, right) && matches!(amount.as_ref(), bits32_constant!(1))
}

fn signed_atom_matches(
    left: &crate::kernel::OldMachineTerm,
    right: &crate::kernel::OldMachineTerm,
) -> bool {
    let left = crate::kernel::canonical_term(left);
    let right = crate::kernel::canonical_term(right);
    let mut pending = vec![(&left, &right)];
    let mut visited = 0usize;
    while let Some((left, right)) = pending.pop() {
        visited += 1;
        if visited > 4096 {
            return false;
        }
        match (left, right) {
            (int32_constant!(left), int32_constant!(right))
                if constant_u32(*left) == constant_u32(*right) => {}
            (int64_constant!(left), int64_constant!(right))
                if constant_i64(*left) == constant_i64(*right) => {}
            (uint64_constant!(left), uint64_constant!(right))
                if constant_u64(*left) == constant_u64(*right) => {}
            (
                crate::kernel::OldMachineTerm::Variable(left),
                crate::kernel::OldMachineTerm::Variable(right),
            ) if left == right => {}
            (left, right)
                if let (Some(left), Some(right)) = (
                    crate::kernel::proof::signed_arithmetic::SignedArithmeticAtom::from_term(left),
                    crate::kernel::proof::signed_arithmetic::SignedArithmeticAtom::from_term(right),
                ) =>
            {
                if left != right {
                    return false;
                }
            }
            (
                binary_term!(Int32, Add, left, right),
                binary_term!(Int32, Add, other_left, other_right),
            )
            | (
                binary_term!(Int32, Subtract, left, right),
                binary_term!(Int32, Subtract, other_left, other_right),
            )
            | (
                binary_term!(Int32, Multiply, left, right),
                binary_term!(Int32, Multiply, other_left, other_right),
            )
            | (
                binary_term!(Int32, Remainder, left, right),
                binary_term!(Int32, Remainder, other_left, other_right),
            ) => {
                pending.push((left, other_left));
                pending.push((right, other_right));
            }
            _ => return false,
        }
    }
    true
}

fn signed_term_constant_value(term: &crate::kernel::OldMachineTerm) -> Option<i64> {
    enum Task<'a> {
        Visit(&'a crate::kernel::OldMachineTerm),
        Combine(bool),
    }
    let mut pending = vec![Task::Visit(term)];
    let mut values = Vec::new();
    while let Some(task) = pending.pop() {
        match task {
            Task::Visit(term) => match term {
                bits32_constant!(value) => {
                    values.push(Some(constant_u32(*value) as i32 as i64));
                }
                binary_term!(Int32, Add, left, right) => {
                    pending.push(Task::Combine(true));
                    pending.push(Task::Visit(right));
                    pending.push(Task::Visit(left));
                }
                binary_term!(Int32, Subtract, left, right) => {
                    if signed_atom_matches(left, right) {
                        values.push(Some(0));
                    } else {
                        pending.push(Task::Combine(false));
                        pending.push(Task::Visit(right));
                        pending.push(Task::Visit(left));
                    }
                }
                _ => values.push(None),
            },
            Task::Combine(add) => {
                let right = values.pop()??;
                let left = values.pop()??;
                values.push(if add {
                    left.checked_add(right)
                } else {
                    left.checked_sub(right)
                });
            }
        }
    }
    values.pop().flatten()
}
/// What arithmetic over the empty list of `close() using {}` says in place of
/// "the listed premises": it listed none, and it never reads the context for
/// them.
const BARE_ARITHMETIC_HINT: &str = "`close() using {}` reads no facts from the context, so list the facts the goal depends on in its `using { ... }`";

/// How `arithmetic` read each listed premise while planning over the Integer
/// linear fragment, written in the reader's own spelling.
///
/// A premise outside the fragment is skipped rather than refused, so a reader
/// whose evidence never entered the planner has to be told which premises did.
/// The two lists are the whole story: no ambient fact participates.
fn describe_integer_premise_reading(
    premises: &[crate::kernel::Proposition],
    surface_premises: &[SyntaxProposition],
) -> String {
    use crate::kernel::proof::integer_arithmetic::integer_affine_claim;
    let spelled = |index: usize| match surface_premises.get(index) {
        Some(premise) => format!(
            "{index}: `{}`",
            crate::surface::printing::source_click_proposition(premise)
        ),
        None => format!("{index}"),
    };
    let (read, skipped): (Vec<_>, Vec<_>) =
        (0..premises.len()).partition(|index| integer_affine_claim(&premises[*index]).is_some());
    let mut description = String::new();
    if read.is_empty() {
        description.push_str(
            "\n  no listed premise was read as an Integer linear claim, so nothing was combined",
        );
    } else {
        description.push_str(&format!(
            "\n  read as Integer linear claims: {}",
            read.iter()
                .copied()
                .map(spelled)
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }
    if !skipped.is_empty() {
        description.push_str(&format!(
            "\n  skipped, not an Integer linear claim: {}",
            skipped
                .iter()
                .copied()
                .map(spelled)
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }
    description
}

/// Classify the failure of the bounded arithmetic planner without reviving a
/// whole-goal checker.  The planner intentionally returns only `None`; this
/// small, iterative shape scan keeps the established diagnostics useful for
/// unsupported nonlinear products and for goals whose machine operations lack
/// enough definedness evidence.
fn signed_goal_shape_flags(goal: &crate::kernel::Proposition) -> Option<(bool, bool)> {
    let (condition, value) = match goal {
        crate::kernel::Proposition::ConditionIs(condition, value) => (condition, *value),
        crate::kernel::Proposition::Not(body) => match body.as_ref() {
            crate::kernel::Proposition::ConditionIs(condition, value) => (condition, !*value),
            _ => return None,
        },
        _ => return None,
    };
    let (left, right) = match condition.old_form() {
        crate::kernel::OldConditionTerm::Compare {
            format: crate::kernel::MachineIntegerType::Int32,
            relation: crate::kernel::CompareRelation::LessThan,
            left,
            right,
        }
        | crate::kernel::OldConditionTerm::Compare {
            format: crate::kernel::MachineIntegerType::Int32,
            relation: crate::kernel::CompareRelation::LessEqual,
            left,
            right,
        }
        | crate::kernel::OldConditionTerm::Compare {
            format: crate::kernel::MachineIntegerType::Int32,
            relation: crate::kernel::CompareRelation::GreaterThan,
            left,
            right,
        }
        | crate::kernel::OldConditionTerm::Compare {
            format: crate::kernel::MachineIntegerType::Int32,
            relation: crate::kernel::CompareRelation::GreaterEqual,
            left,
            right,
        }
        | crate::kernel::OldConditionTerm::Compare {
            format:
                crate::kernel::MachineIntegerType::Int32 | crate::kernel::MachineIntegerType::UInt32,
            relation: crate::kernel::CompareRelation::Equal,
            left,
            right,
        } if value => (left.as_ref(), right.as_ref()),
        crate::kernel::OldConditionTerm::Compare {
            format: crate::kernel::MachineIntegerType::Int32,
            relation: crate::kernel::CompareRelation::LessThan,
            left,
            right,
        }
        | crate::kernel::OldConditionTerm::Compare {
            format: crate::kernel::MachineIntegerType::Int32,
            relation: crate::kernel::CompareRelation::LessEqual,
            left,
            right,
        }
        | crate::kernel::OldConditionTerm::Compare {
            format: crate::kernel::MachineIntegerType::Int32,
            relation: crate::kernel::CompareRelation::GreaterThan,
            left,
            right,
        }
        | crate::kernel::OldConditionTerm::Compare {
            format: crate::kernel::MachineIntegerType::Int32,
            relation: crate::kernel::CompareRelation::GreaterEqual,
            left,
            right,
        }
        | crate::kernel::OldConditionTerm::Compare {
            format:
                crate::kernel::MachineIntegerType::Int32 | crate::kernel::MachineIntegerType::UInt32,
            relation: crate::kernel::CompareRelation::Equal,
            left,
            right,
        } => (left.as_ref(), right.as_ref()),
        crate::kernel::OldConditionTerm::Compare {
            format: crate::kernel::MachineIntegerType::UInt32,
            relation:
                relation @ (crate::kernel::CompareRelation::LessThan
                | crate::kernel::CompareRelation::LessEqual
                | crate::kernel::CompareRelation::GreaterThan
                | crate::kernel::CompareRelation::GreaterEqual),
            left,
            right,
        } if *relation != crate::kernel::CompareRelation::Equal => (left.as_ref(), right.as_ref()),
        _ => return None,
    };
    let mut machine_operation = false;
    let mut nonlinear = false;
    let mut pending = vec![left, right];
    while let Some(term) = pending.pop() {
        match term {
            binary_term!(Int32, Add, left, right)
            | binary_term!(Int32, Subtract, left, right)
            | binary_term!(Int32, Multiply, left, right)
            | binary_term!(Int32, Divide, left, right)
            | binary_term!(Int32, Remainder, left, right)
            | binary_term!(Int32, ShiftLeft, left, right)
            | binary_term!(Int32, ShiftRight, left, right)
            | binary_term!(UInt32, ShiftRight, left, right) => {
                machine_operation = true;
                if matches!(term, binary_term!(Int32, Multiply, _, _))
                    && signed_term_constant_value(left).is_none()
                    && signed_term_constant_value(right).is_none()
                {
                    nonlinear = true;
                }
                pending.push(left);
                pending.push(right);
            }
            // Bitwise operations are total. Inspect their operands for
            // partial arithmetic, but do not invent an overflow obligation
            // for the mask or the unsigned-order sign-bit xor itself.
            binary_term!(Int32, BitwiseAnd, left, right)
            | binary_term!(Int32, BitwiseOr, left, right)
            | binary_term!(Int32, BitwiseXor, left, right) => {
                pending.push(left);
                pending.push(right);
            }
            unary_term!(Int32, BitwiseNot, inner) => {
                pending.push(inner);
            }
            crate::kernel::OldMachineTerm::PureFunctionApplication { arguments, .. } => {
                pending.extend(arguments.iter());
            }
            _ => {}
        }
    }
    Some((nonlinear, machine_operation))
}

/// Whether a held `uint32` order goal has a plain variable as an operand.
fn unsigned_order_names_a_variable(goal: &crate::kernel::Proposition) -> bool {
    matches!(&goal, condition_source_0 @ crate::kernel::Proposition::ConditionIs(
            _,
            true,
        ) if matches!(condition_source_0.old_condition(), Some((crate::kernel::OldConditionTerm::Compare {
                format: crate::kernel::MachineIntegerType::UInt32,
                relation: crate::kernel::CompareRelation::LessThan
                    | crate::kernel::CompareRelation::LessEqual
                    | crate::kernel::CompareRelation::GreaterThan
                    | crate::kernel::CompareRelation::GreaterEqual,
                left,
                right,
            }, _)) if (matches!(left.as_ref(), crate::kernel::OldMachineTerm::Variable(_))
            || matches!(right.as_ref(), crate::kernel::OldMachineTerm::Variable(_)))))
}

/// The step as `click expand` writes it, for a step with a `using` list,
/// which a search chose when the step came from a smart tactic or an elided
/// form.
fn chosen_step_text(step: &ProofStep) -> Option<String> {
    if !matches!(
        step,
        ProofStep::ApplyTheoremUsing { .. } | ProofStep::ApplyPlannedTheorem { .. }
    ) {
        return None;
    }
    let certificate = ProofCertificate::from_steps(vec![step.clone()]).ok()?;
    let text =
        crate::surface::printing::format_partial_tactic_sequence(&certificate.to_proof_tactics());
    Some(text.split_whitespace().collect::<Vec<_>>().join(" "))
}

impl<'a> Proof<'a> {
    /// Under `CLICK_RAISE_LOWER_CENSUS`, records whether each fact this step
    /// added, and the goal it leaves focused, raises to a checked Surface form.
    fn record_raise_lower_census(&self, next: &Self, tactic: &str, written: bool) {
        use crate::surface::proof::raise_lower_census as census;
        // A step that closes its goal leaves no proof state to hold its
        // facts, and raising reads the focused goal's facts.
        if next.focused_branch().is_none() || next.focused_discharged() {
            return;
        }
        let added = self
            .focused_branch()
            .zip(next.focused_branch())
            .and_then(|(before, after)| after.state.facts.introduced_since(&before.state.facts));
        let added = added
            .as_deref()
            .unwrap_or_else(|| next.state().added_facts());
        // Kernel authority is checked context, not a proof-state fact.
        for fact in added
            .iter()
            .filter(|fact| !fact.is_kernel_authority())
            .take(64)
        {
            // The census charges no tactic budget and keeps no search note,
            // so the proof and its report are the run's without it.
            let scope = crate::surface::proof::attempt::search_scope("raise-lower census");
            let spelled = crate::instrumentation::without_charging(|| {
                crate::kernel::search::ProofSearch::resolve_solve_premises(
                    next,
                    std::slice::from_ref(fact),
                    &[],
                )
                .is_some_and(|spelled| spelled.len() == 1)
            });
            drop(scope.finish());
            census::record(
                spelled,
                "fact",
                &census::kind(fact),
                self.claim_label(),
                tactic,
                written,
                &next.render_kernel_proposition(fact),
            );
        }
        if let Some(goal) = next.goal() {
            census::record(
                next.surface_goal().is_some(),
                "goal",
                &census::kind(goal),
                self.claim_label(),
                tactic,
                written,
                &next.render_kernel_proposition(goal),
            );
        }
    }

    /// Under `CLICK_RAISE_LOWER`, raises each fact this step added, and the
    /// goal it leaves focused, at the step's fixed state, lowers the spelling
    /// again, and records how the round trip ended.
    fn record_raise_lower_audit(&self, next: &Self, tactic: &str) {
        if next.focused_branch().is_none() || next.focused_discharged() {
            return;
        }
        let added = self
            .focused_branch()
            .zip(next.focused_branch())
            .and_then(|(before, after)| after.state.facts.introduced_since(&before.state.facts));
        let added = added
            .as_deref()
            .unwrap_or_else(|| next.state().added_facts());
        let facts = added
            .iter()
            .filter(|fact| !fact.is_kernel_authority())
            .take(64)
            .map(|fact| ("fact", fact));
        let goal = next.goal().map(|goal| ("goal", goal));
        for (role, original) in facts.chain(goal) {
            next.record_raise_lower_proposition(role, original, tactic);
        }
    }

    /// Audits one whole proposition in the proof that holds it.
    pub(super) fn record_raise_lower_proposition(
        &self,
        role: &str,
        original: &Proposition,
        tactic: &str,
    ) {
        use crate::surface::proof::raise_lower_audit::{self as audit, RoundTrip};
        use crate::surface::proof::raise_lower_census::kind;
        let scope = crate::surface::proof::attempt::search_scope("raise-lower audit");
        let ((outcome, raised, lowered), reasons) = audit::collecting_reasons(|| {
            crate::instrumentation::without_charging(|| {
                // A pure proof (a theorem, a lemma, a termination check) raises
                // and lowers in its own context; only a program proof needs a
                // fixed state to raise at.
                if !matches!(self.context.as_ref(), super::ProofContext::Pure(_))
                    && self.premise_fixed_state_view().is_none()
                {
                    return (RoundTrip::NoState, String::new(), String::new());
                }
                // Raise as goal presentation does: with the path's recorded
                // points and its entry state, so `at(point, ..)`, `old(..)`
                // and `<call>.result` forms are available.
                let Some(surface) = self.structural_proposition_candidate(original) else {
                    return (RoundTrip::Unraised, String::new(), String::new());
                };
                let raised = crate::surface::printing::source_click_proposition(&surface);
                let lowered = self.lower_proposition_spelling(&surface);
                match lowered {
                    Err(_) => (RoundTrip::Unlowered, raised, String::new()),
                    Ok(lowered) => match audit::classify(original, &lowered) {
                        RoundTrip::Differs => (
                            RoundTrip::Differs,
                            raised,
                            self.render_kernel_proposition(&lowered),
                        ),
                        outcome => (outcome, raised, String::new()),
                    },
                }
            })
        });
        drop(scope.finish());
        audit::record(
            outcome,
            role,
            &kind(original),
            self.claim_label(),
            tactic,
            &self.render_kernel_proposition(original),
            &raised,
            &lowered,
            &reasons,
        );
    }

    /// Retain the call spelling for a checked call in the proof trace.
    fn trace_call_source(
        &self,
        step: &ProofStep,
    ) -> Option<crate::surface::proof_trace::TraceCallSource> {
        let ProofContext::Execution(context) = self.context.as_ref() else {
            return None;
        };
        let call = match step {
            ProofStep::StepCall(transport) => transport.to_string(),
            ProofStep::StepContract(application) => format!("step({})", application.name),
            ProofStep::Step | ProofStep::StepBind(_) => {
                let execution = self.execution()?;
                let (_, _, statement, _) = next_top_level_statement_from_frontier_position(
                    execution.view(),
                    &execution.core.state,
                    context.function,
                    context.arguments,
                    context.claim_label,
                    context.tactic_index,
                    "step",
                )
                .ok()?;
                let callee = match statement {
                    ProgramStatement::CallConstruct { function_name, .. }
                    | ProgramStatement::Call { function_name, .. }
                    | ProgramStatement::CallResult { function_name, .. } => function_name,
                    _ => return None,
                };
                format!("step({callee}(...))")
            }
            _ => return None,
        };
        Some(crate::surface::proof_trace::TraceCallSource { call })
    }

    /// Read only the changed fact/resource keys, and only under an explicit
    /// trace request. The checked successor and its certificate are untouched.
    pub(super) fn record_checked_trace_step(
        &self,
        next: &Self,
        tactic: &str,
        call_source: Option<crate::surface::proof_trace::TraceCallSource>,
        chosen: Option<String>,
        fact_limit: usize,
        read_checkpoint: Option<&crate::kernel::ReadEqualityCheckpoint>,
        cell_walks: Vec<crate::kernel::TransportCellWalkDiagnostic>,
    ) {
        // A read follows at most one recorded transition; show the walks this
        // step made that stopped without reaching the value, at that limit or
        // at a transition not shown separate, not every query.
        let history_stops = cell_walks
            .into_iter()
            .filter(|walk| {
                matches!(
                    walk.reason,
                    "hop limit reached" | "step not proved separate from the queried bytes"
                )
            })
            .take(TRACE_HISTORY_STOP_LIMIT)
            .collect();
        let location = self
            .site()
            .path()
            .unwrap_or_else(|| format!("checked step {}", next.node.depth));
        let mut detail = crate::surface::proof_trace::TraceStep {
            header: format!(
                "\n    {location}: {}",
                call_source
                    .as_ref()
                    .map_or(tactic, |call| call.call.as_str())
            ),
            source_tactic_path: self.site().source_tactic_path(),
            call_source,
            facts: Vec::new(),
            more_facts: 0,
            frontier: None,
            load: None,
            read_equalities: Vec::new(),
            read_context_changed: false,
            transport: None,
            resources: Vec::new(),
            more_resources: 0,
            origin: crate::surface::proof_trace::smart_origin(),
            chosen,
            forgotten_cells: Vec::new(),
            history_stops,
        };
        if tactic == "transport"
            && let [source, target] = next.state().checked_facts()
        {
            detail.transport = Some([
                next.checked_trace_fact(source.clone()),
                next.checked_trace_fact(target.clone()),
            ]);
        }
        if let Some(checkpoint) = read_checkpoint
            && let Some(branch) = next.focused_branch().or_else(|| self.focused_branch())
        {
            let admitted = branch
                .state
                .facts
                .assumptions()
                .read_equalities_since(checkpoint);
            detail.read_context_changed = admitted.context_changed;
            detail.read_equalities = admitted
                .equalities
                .into_iter()
                .map(|kernel| next.checked_trace_fact(kernel))
                .collect();
        }
        let added = self
            .focused_branch()
            .zip(next.focused_branch())
            .and_then(|(before, after)| after.state.facts.introduced_since(&before.state.facts));
        let added = added
            .as_deref()
            .unwrap_or_else(|| next.state().added_facts());
        let visible = added
            .iter()
            .filter(|fact| crate::surface::proof_trace::visible_checked_fact(fact));
        for fact in visible.clone().take(fact_limit) {
            detail.facts.push(next.checked_trace_fact(fact.clone()));
        }
        detail.more_facts = visible.count().saturating_sub(fact_limit);
        if let (Some(before), Some(after)) = (self.branch_execution(), next.branch_execution()) {
            // The cells this step dropped beside its own stores: the diff of
            // the two memories visits only the changed cells, and at most
            // `TRACE_FORGOTTEN_CELL_LIMIT` pairs are kept.
            detail.forgotten_cells =
                crate::kernel::search::store_separation::cells_forgotten_beside_stores(
                    before.core.state.memory(),
                    after.core.state.memory(),
                    TRACE_FORGOTTEN_CELL_LIMIT,
                )
                .into_iter()
                .map(
                    |forgotten| crate::surface::proof_trace::TraceForgottenCell {
                        spelled: [&forgotten.cell, &forgotten.store].map(|pointer| {
                            crate::surface::diagnostics::describe_source_cell_at_state(
                                pointer,
                                &before.core.state,
                            )
                        }),
                        cell: forgotten.cell,
                        store: forgotten.store,
                        indices_differ: forgotten.indices_differ,
                    },
                )
                .collect();
            let before_frontier = &before.core.frontier;
            let after_frontier = &after.core.frontier;
            let before_position = trace_frontier(before_frontier);
            let after_position = trace_frontier(after_frontier);
            if before_position != after_position && detail.call_source.is_none() {
                detail.frontier = Some(
                    match self.context.as_ref() {
                        ProofContext::Execution(context) => {
                            next_top_level_statement_from_frontier_position(
                                before.view(),
                                &before.core.state,
                                context.function,
                                context.arguments,
                                context.claim_label,
                                context.tactic_index,
                                "step",
                            )
                            .ok()
                            .map(|(_, _, statement, _)| {
                                format!("steps through: {}", trace_statement_head(&statement))
                            })
                        }
                        _ => None,
                    }
                    .unwrap_or_else(|| {
                        format!("C frontier: {before_position} -> {after_position}")
                    }),
                );
            }
            // Inspect only this accepted step's new evidence, never its history.
            // The statement theorem retains the actual read state after entry
            // initialization and resource preparation, which the frontier alone
            // need not represent.
            if let (Some(old), Some(new)) = (
                before.core.execution_evidence.get(0),
                after.core.execution_evidence.get(0),
            ) {
                for event in new.recent(new.len().saturating_sub(old.len())) {
                    let crate::kernel::proof::CheckedExecutionEvent::Statement(theorem) = event
                    else {
                        continue;
                    };
                    let mut conclusion = theorem.proposition();
                    while let Proposition::Implies(_, body) = conclusion {
                        conclusion = body;
                    }
                    detail.load =
                        trace_function_pointer_load(conclusion, self.facts().assumptions());
                    break;
                }
            }
            let reached_state = after.core.reached_state();
            let before = before.core.reached_state().resources();
            let after = after.core.reached_state().resources();
            if let Some(changed) = after.changed_facts_since(before) {
                for fact in changed.iter().take(8) {
                    let old = before.exact_count(fact);
                    let new = after.exact_count(fact);
                    if old != new {
                        let description = match self.context.as_ref() {
                            ProofContext::Execution(context) => {
                                trace_resource_fact(fact, context, reached_state)
                            }
                            _ => crate::surface::proof_diagnostics::render::render_resource_fact_diagnostic(
                                fact,
                                ParameterBinding::default(),
                            ),
                        };
                        detail
                            .resources
                            .push(crate::surface::proof_trace::TraceResourceChange {
                                before: old,
                                after: new,
                                description,
                            });
                    }
                }
                if changed.len() > 8 {
                    detail.more_resources = changed.len() - 8;
                }
            }
        }
        crate::surface::proof_trace::record(
            crate::surface::proof_trace::trace_node_key(&next.node),
            detail,
        );
    }

    /// Apply exact facts and the selected live-partition separation rule.
    /// No ambient compositions or candidate resources are enumerated.
    pub(super) fn apply_known(&self) -> Result<KernelProofHandle, ClickError> {
        let context = match self.context.as_ref() {
            ProofContext::FixedState(_) => PropositionKnownContext::Pure,
            ProofContext::Execution(_) => PropositionKnownContext::Materialized,
            ProofContext::Pure(_) => PropositionKnownContext::Exact,
        };
        // A completed outcome owns its post-state; the execution branch may
        // still retain an earlier frontier. Never use that stale partition.
        let resources = match self.context.as_ref() {
            ProofContext::Pure(_) => None,
            ProofContext::FixedState(context) => Some(context.fixed_state.state.resources()),
            ProofContext::Execution(_) => match self.focused_outcome_data() {
                Some(outcome) => Some(outcome.core.state.resources()),
                None => self
                    .execution()
                    .map(|execution| execution.core.state.resources()),
            },
        };
        let state = if let (Some(goal), Some(resources)) = (self.goal(), resources) {
            let facts = self
                .facts()
                .with_exact_partition_separation(goal, resources);
            self.state
                .replace_focused_obligation_and_facts(
                    self.focused_obligation()
                        .expect("a proposition goal is focused")
                        .clone(),
                    facts,
                )
                .map_err(|_| self.step_error("known requires an open goal"))?
        } else {
            self.state.clone()
        };
        state
            .apply_known(context)
            .map_err(|error| match error {
                PropositionCloseError::NotProposition => {
                    self.step_error("`known` requires a proposition goal")
                }
                PropositionCloseError::Unavailable => {
                    let detail = self
                        .goal()
                        .map(|goal| format!(": current goal is {}", describe_known_goal(goal)))
                        .unwrap_or_default();
                    self.step_error(format!(
                        "`known` requires the current goal as an available semantic fact{detail}"
                    ))
                }
                PropositionCloseError::UnavailableSide(side) => {
                    self.step_error_with_requirement(
                        "`known` closes a conjunction when every side is an available fact and a disjunction when one side is; a required side is not available",
                        None,
                        Some(("missing exact fact", Box::new(side), None)),
                    )
                }
                _ => unreachable!("kernel returned an unrelated known error"),
            })
    }

    #[inline(never)]
    pub(super) fn apply_close_bounds(
        &self,
        surface_premises: &[SyntaxProposition],
    ) -> Result<KernelProofHandle, ClickError> {
        let premises = surface_premises
            .iter()
            .map(|premise| self.lower_cited_surface_proposition(premise, "selected bound"))
            .collect::<Result<Vec<_>, _>>()?;
        self.state
            .apply_close_bounds(&premises)
            .map_err(|message| self.step_error(message))
    }

    pub(in crate::surface::proof) fn arithmetic_refusal(
        &self,
        surface_premises: &[SyntaxProposition],
    ) -> Result<Proof<'a>, ClickError> {
        // A ranking decrease compares the loop-head value with its checked
        // predecessor.  At the back edge the ordinary spelling of a loop
        // invariant re-lowers against the post-body state, whereas this
        // obligation's `n` is the retained iteration-entry value.  Preserve
        // that distinction in the certificate's source premises; the
        // state annotation is checked by the normal direct lowering path.
        let anchored_surface_premises = if self.goal().is_some_and(is_positive_predecessor_goal)
            && let ProofContext::Execution(context) = self.context.as_ref()
            && let Some(bundle) = context.constants.invariant_body_context.as_deref()
            && let Some(selector) = bundle.iteration_entry_selector.as_ref()
        {
            surface_premises
                .iter()
                .map(|premise| {
                    surface_at_program_point(premise, selector).unwrap_or_else(|_| premise.clone())
                })
                .collect::<Vec<_>>()
        } else {
            surface_premises.to_vec()
        };
        let premises = anchored_surface_premises
            .iter()
            .map(|premise| self.lower_cited_surface_proposition(premise, "`close() using` premise"))
            .collect::<Result<Vec<_>, _>>()?;
        for (index, premise) in premises.iter().enumerate() {
            if !self.facts().listed_premise_available(premise, &[], false) {
                return Err(self.step_error(format!(
                    "`close() using` premise {index} is not exactly available"
                )));
            }
        }
        // A checked rewrite can outlive its syntactic goal template. Recover
        // the arithmetic claim from the actual goal and the root's indexed
        // parameter values, without scanning parameters at every step.
        // A goal in the mathematical `Integer` linear fragment never reaches
        // the signed int32 planner, so reporting that planner's precondition
        // for it names a fragment the goal is not in and sends the reader
        // hunting for an int32 mistake. Say which fragment was recognized and
        // how each listed premise was read inside it.
        if let Some(goal) = self.goal()
            && crate::kernel::proof::integer_arithmetic::written_integer_affine_claim(goal)
        {
            if let Some(plan) = crate::surface::checking::plan_arithmetic(
                crate::surface::checking::ArithmeticEngine::IntegerAffine,
                goal,
                &premises,
            )
            .and_then(crate::surface::checking::ArithmeticPlan::integer_affine)
            {
                return Err(self.step_error(format!(
                    "arithmetic found a {}-node Integer composition, but could not emit its ordinary proof; this is a Click rendering gap, not a missing premise",
                    plan.nodes.len()
                )));
            }
            if premises.is_empty() {
                return Err(self.step_error(format!(
                    "arithmetic read the current goal as an Integer linear claim, which does not hold on its own; {BARE_ARITHMETIC_HINT}"
                )));
            }
            return Err(self.step_error(format!(
                "arithmetic read the current goal as an Integer linear claim; no combination of the listed premises proves it{}",
                describe_integer_premise_reading(&premises, &anchored_surface_premises)
            )));
        }
        if let Some(goal) = self.goal() {
            let unsigned_order = crate::surface::checking::is_unsigned_order_goal(goal);
            if crate::kernel::proof::signed_arithmetic::signed_arithmetic_claim(goal).is_none()
                && !unsigned_order
            {
                return Err(self.step_error(
                    "arithmetic requires a supported signed int32 comparison or equality goal",
                ));
            }
            if let Some((nonlinear, machine_operation)) = signed_goal_shape_flags(goal) {
                if nonlinear {
                    return Err(self.step_error(
                        "arithmetic requires a supported signed int32 comparison or equality goal",
                    ));
                }
                // A `uint32` order over a plain variable is decided from the
                // operands' signed intervals, which owe no definedness; the
                // useful failure is then the premises, not an operation.
                if machine_operation && !(unsigned_order && unsigned_order_names_a_variable(goal)) {
                    if premises.is_empty() {
                        return Err(self.step_error(format!(
                            "arithmetic cannot establish that every int32 operation in the current goal is defined without overflow from the goal alone; {BARE_ARITHMETIC_HINT}"
                        )));
                    }
                    return Err(self.step_error(
                        "arithmetic cannot establish that every int32 operation in the current goal is defined without overflow from exactly the listed premises",
                    ));
                }
            }
            if premises.is_empty() {
                return Err(self.step_error(format!(
                    "current goal does not follow by arithmetic alone; {BARE_ARITHMETIC_HINT}"
                )));
            }
            if premises
                .iter()
                .all(crate::surface::checking::signed_arithmetic_premise_supported)
            {
                return Err(self.step_error(
                    "current goal does not follow from exactly the listed arithmetic premises (exactly the listed premises were insufficient)",
                ));
            }
        }
        if premises.is_empty() {
            return Err(self.step_error(format!(
                "arithmetic could not construct an ordinary arithmetic proof from the goal alone; {BARE_ARITHMETIC_HINT}"
            )));
        }
        Err(self.step_error(
            "arithmetic could not construct an ordinary arithmetic proof from exactly the listed premises",
        ))
    }

    /// One explicit footprint-preservation operation. No premise discovery.
    fn apply_preserve(
        &self,
        separation: &SyntaxProposition,
    ) -> Result<KernelProofHandle, ClickError> {
        let _reads = crate::kernel::TransportReadScope::enter();
        let separation =
            self.lower_surface_proposition_direct(separation, "preserve separation")?;
        let fields = crate::kernel::TransportFieldScope::enter();
        let goal = self.surface_goal().ok_or_else(|| {
            self.step_error("preserve requires a spelled read-equality or definedness goal")
        })?;
        self.lower_surface_proposition_direct(goal, "preserve goal")?;
        let field = fields.selected().map_err(|e| self.step_error(e))?;
        self.state
            .apply_preserve(&separation, field)
            .map_err(|e| self.step_error(e))
    }

    pub(in crate::surface::proof) fn lower_integer_surface_proposition(
        &self,
        surface: &SyntaxProposition,
        description: &str,
    ) -> Result<Proposition, ClickError> {
        match self.context.as_ref() {
            ProofContext::Pure(context) => {
                let mut names = BTreeSet::new();
                collect_click_proposition_referenced_names(surface, &mut names);
                let mut integer_values = context.theorem_context.integer_values.clone();
                for name in &names {
                    crate::instrumentation::record_deterministic_work(1);
                    if let Some(value) = self.state().locals().integer_values.get(name) {
                        integer_values = integer_values.with_inserted(name.clone(), value.clone());
                    }
                }
                let promoted = self.proposition_obligation().map_or_else(
                    || surface.clone(),
                    |goal| {
                        crate::surface::proof::surface_lowering::promote_integer_comparison(
                            surface,
                            &integer_values,
                            &goal.surface_bindings,
                        )
                    },
                );
                if let Ok(proposition) =
                    crate::surface::lower_integer_arithmetic_proposition(&promoted, &integer_values)
                {
                    return Ok(proposition);
                }
                // Read the written observations directly: a recorded native
                // alias no longer identifies their signed or unsigned type.
                // The Integer-only path above remains independent of unrelated
                // theorem state.
                self.lower_surface_proposition_direct(&promoted, description)
            }
            _ => self.lower_surface_proposition_direct(surface, description),
        }
    }

    /// The focused universal goal with its binder respelled `name`, for
    /// a named introduction. The name must be new.
    fn universal_goal_renamed_for_intro(
        &self,
        name: &SurfaceBinder,
    ) -> Result<SyntaxProposition, ClickError> {
        if !matches!(self.goal(), Some(Proposition::ForAll { .. })) {
            return Err(self.step_error(format!(
                "use `intro({name}) {{ ... }}` for a `forall` goal. To introduce an implication premise, write `intro() {{ ... }}`"
            )));
        }
        // A range quantifier keeps its variable in the lambda:
        // `(lo..hi).all(|k| { ... })`.
        let (binder, body, c_typed) = match self.surface_goal() {
            Some(SyntaxProposition::ForAll {
                click_type,
                name: binder,
                body,
                ..
            }) => (binder, body, matches!(click_type, ClickType::Program(_))),
            Some(SyntaxProposition::RangeAll { item, body, .. }) => (item, body, false),
            _ => {
                return Err(self.step_error(format!(
                    "`intro({name}) {{ ... }}` requires a goal written as `forall (x: T) {{ ... }}` or `(lo..hi).all(|x| {{ ... }})`. Use `intro() {{ ... }}` to keep the quantifier's name"
                )));
            }
        };
        // Generated identities denote one introduction, rather than a source
        // spelling that can shadow another value under an `outer.` alias.
        if matches!(name, SurfaceBinder::Generated(_)) {
            let locals = self.state.locals();
            let bound = locals.values.get(name).is_some()
                || locals.integer_values.get(name).is_some()
                || locals.algebraic_values.get(name).is_some()
                || self
                    .proposition_obligation()
                    .is_some_and(|goal| goal.surface_bindings.get(name).is_some());
            if bound {
                return Err(self.step_error(format!(
                    "`{name}` is already introduced here; use a fresh generated binder identity"
                )));
            }
        }
        if binder == name {
            return Ok(self.surface_goal().expect("matched above").clone());
        }
        let mut referenced = BinderSet::new();
        crate::surface::lowering::collect_click_proposition_referenced_binders(
            body,
            &mut referenced,
        );
        let (names, _) = self.diagnostic_naming_tables();
        let locals = self.state.locals();
        let in_scope = referenced.contains(name)
            || names.iter().any(|parameter| parameter.name() == name)
            || locals.integer_values.get(name).is_some()
            || locals.algebraic_values.get(name).is_some()
            || self
                .focused_obligation()
                .is_some_and(|obligation| match obligation {
                    Obligation::Proposition(goal) => goal.surface_bindings.get(name).is_some(),
                    _ => false,
                });
        if in_scope {
            return Err(self.step_error(format!(
                "`intro({name})`: `{name}` is already in scope here; choose a name that is not"
            )));
        }
        let replacement = match (c_typed, name.written()) {
            (true, Some(name)) => SyntaxTerm::ProgramBinding(name.into()),
            _ => name.reference(),
        };
        let renaming = BTreeMap::from([(binder.clone(), replacement)]);
        let body = crate::surface::lowering::substitute_click_proposition(body, &renaming)
            .map_err(|message| self.step_error(message))?;
        Ok(match self.surface_goal() {
            Some(SyntaxProposition::RangeAll { start, end, .. }) => SyntaxProposition::RangeAll {
                start: start.clone(),
                end: end.clone(),
                item: name.clone(),
                written_item: None,
                body: Box::new(body),
            },
            Some(SyntaxProposition::ForAll { click_type, .. }) => SyntaxProposition::ForAll {
                click_type: click_type.clone(),
                name: name.clone(),
                written_name: None,
                body: Box::new(body),
            },
            _ => unreachable!("matched as a quantifier above"),
        })
    }

    // Preserve the rule/dispatcher frame boundary described above; `intro`
    // owns several by-value proposition variants.
    #[inline(never)]
    pub(super) fn apply_intro(
        &self,
        rename: Option<SurfaceBinder>,
    ) -> Result<KernelProofHandle, ClickError> {
        // A named introduction respells the universal goal's binder before the
        // ordinary introduction runs, so every binding below is made under
        // the chosen name and the remaining goal is written in terms of it.
        let renamed_surface = rename
            .as_ref()
            .map(|name| self.universal_goal_renamed_for_intro(name))
            .transpose()?;
        let mut integer_binding = None;
        let mut machine_binding = None;
        let mut algebraic_binding = None;
        let mut antecedent_spelling = None;
        let state = self
            .state
            .apply_intro(|current, introduction, introduced| {
                let mut surface_bindings = current.surface_bindings.clone();
                let mut introduced_antecedents = current.introduced_antecedents.clone();
                let renamed_recorded = match (rename.as_ref(), current.introductions.head()) {
                    (
                        Some(name),
                        Some(LoweringIntroduction::WrittenUniversal {
                            variable,
                            pointer,
                            integer,
                            ..
                        }),
                    ) => Some(LoweringIntroduction::WrittenUniversal {
                        name: name.into(),
                        variable: *variable,
                        pointer: *pointer,
                        integer: *integer,
                    }),
                    _ => None,
                };
                let recorded = renamed_recorded
                    .as_ref()
                    .or_else(|| current.introductions.head());
                let current_surface = renamed_surface
                    .as_ref()
                    .or(current.surface.as_deref());
                let introduced_name = match (&introduction, recorded, current_surface) {
                    (
                        PropositionIntroduction::Universal { .. },
                        Some(LoweringIntroduction::WrittenUniversal { name, .. }),
                        _,
                    ) => Some(SurfaceBinder::from(name)),
                    (
                        PropositionIntroduction::Universal { .. },
                        _,
                        Some(SyntaxProposition::ForAll { name, .. }),
                    ) => Some(SurfaceBinder::from(name)),
                    (
                        PropositionIntroduction::Universal { .. },
                        None,
                        Some(SyntaxProposition::RangeAll { item, .. }),
                    ) => Some(item.clone()),
                    _ => None,
                };
                if let Some(name) = introduced_name {
                    if let PropositionIntroduction::Universal { variable, .. } = &introduction
                        && let Some(Proposition::ForAll { sort, .. }) = self.goal()
                        && let Some(ty) = sort.machine_integer_type()
                    {
                        let value = ty.symbolic_value(*variable);
                        if crate::kernel::program_narrow_integer_range(&value).is_some() {
                            machine_binding = Some((name.clone(), *variable, value));
                        }
                    }
                    let previous = current.surface_bindings.get(&name).cloned().or_else(|| {
                        let value = match self.context.as_ref() {
                            ProofContext::Pure(context) => {
                                name.written().and_then(|name|context.theorem_context.values.get(name)).cloned().map(ProgramExpression::Value)
                            }
                            ProofContext::FixedState(context) => context
                                .parameter_binding.parameters
                                .iter()
                                .zip(context.parameter_binding.arguments)
                                .find(|(parameter, _)| parameter.name() == name)
                                .map(|(_, argument)| argument.clone()),
                            ProofContext::Execution(context) => context
                                .parsed_function
                                .parameters()
                                .iter()
                                .zip(context.arguments)
                                .find(|(parameter, _)| parameter.name() == name)
                                .map(|(_, argument)| argument.clone()),
                        };
                        value.map(SyntaxTerm::ProgramExpression)
                    });
                    if let Some(previous) = previous {
                        let mut depth = 1;
                        loop {
                            let alias = format!("{}{}", "outer.".repeat(depth), name);
                            let Some(older) = current.surface_bindings.get(&alias) else {
                                break;
                            };
                            surface_bindings = surface_bindings.with_inserted(
                                format!("{}{}", "outer.".repeat(depth + 1), name),
                                older.clone(),
                            );
                            depth += 1;
                        }
                        surface_bindings =
                            surface_bindings.with_inserted(format!("outer.{name}"), previous);
                    }
                }
                let surface = match (recorded, introduction, current_surface) {
                    // Lowering inserts implications that guard a body with a
                    // path fact it established or with a load obligation the
                    // state did not discharge. Neither has a Surface
                    // connective, so the written goal stays focused while
                    // `intro` exposes one such kernel implication.
                    (
                        Some(
                            LoweringIntroduction::PathFactGuard
                            | LoweringIntroduction::ObligationGuard,
                        ),
                        PropositionIntroduction::Implication,
                        Some(surface),
                    ) => Some(Arc::new(surface.clone())),
                    // A written implication consumes the written connective.
                    // The pair `intro` just checked is retained here, with
                    // its structural conjuncts, so a later citation does not
                    // re-lower the antecedent under the fact context this
                    // step changed.
                    (
                        Some(LoweringIntroduction::WrittenImplication),
                        PropositionIntroduction::Implication,
                        Some(surface),
                    ) => match written_implication_consequent(surface) {
                        Some(WrittenAntecedent::Implication {
                            antecedent,
                            consequent,
                        }) => {
                            if let Some(kernel) = introduced {
                                introduced_antecedents = retain_introduced_antecedent(
                                    &introduced_antecedents,
                                    &antecedent,
                                    kernel,
                                );
                                antecedent_spelling = Some((antecedent.clone(), kernel.clone()));
                            }
                            Some(Arc::new(consequent))
                        }
                        // A range quantifier writes no implication of its
                        // own: its kernel form is the binder followed by the
                        // range guard, whose consequent is the written body.
                        Some(WrittenAntecedent::RangeGuard { body }) => Some(Arc::new(body)),
                        None => Some(Arc::new(surface.clone())),
                    },
                    (
                        Some(LoweringIntroduction::WrittenUniversal {
                            name,
                            pointer,
                            integer,
                            ..
                        }),
                        PropositionIntroduction::Universal {
                            variable,
                            pointer: introduced_pointer,
                            object_class,
                            algebraic,
                        },
                        surface,
                    ) => {
                        if *integer {
                            integer_binding = Some((name.clone(), variable));
                        } else if let Some(ref algebraic_type) = algebraic {
                            algebraic_binding =
                                Some((SurfaceBinder::from(name), variable, algebraic_type.clone()));
                        }
                        // The binding names the exact variable the kernel
                        // bound the body to, not the one lowering first
                        // chose: `intro` freshens the binder away from
                        // ambient facts.
                        let value = match (pointer, introduced_pointer) {
                            (true, Some(interface_type)) => {
                                ProgramValue::typed_pointer(Address::symbolic(variable), interface_type).with_pointer_object_class(object_class)
                            }
                            _ => match self.proposition_goal("`intro` requires a proposition goal").expect("intro checked its goal") {
                                Proposition::ForAll { sort, .. } if sort.machine_integer_type().is_some() => sort.machine_integer_type().unwrap().symbolic_value(variable),
                                _ => ProgramValue::Int32(OldMachineTerm::Variable(variable)),
                            },
                        };
                        if algebraic.is_some() {
                            surface_bindings = surface_bindings.with_inserted(
                                name.clone(),
                                SurfaceBinder::from(name).reference(),
                            );
                        } else if !*integer {
                            surface_bindings = surface_bindings.with_inserted(
                                name.clone(),
                                SyntaxTerm::ProgramExpression(ProgramExpression::Value(value)),
                            );
                        }
                        surface.and_then(written_universal_body).map(Arc::new)
                    }
                    // No lowering head chain was recorded for this goal, so
                    // refine the written form structurally, as before.
                    (None, PropositionIntroduction::Implication, Some(surface)) => {
                        surface_implication_parts(surface)
                            .map(|(_, consequent)| Arc::new(consequent))
                            .or_else(|| Some(Arc::new(surface.clone())))
                    }
                    (
                        None,
                        PropositionIntroduction::Universal {
                            variable,
                            algebraic,
                            ..
                        },
                        Some(SyntaxProposition::ForAll { name, body, .. }),
                    ) => {
                        if let Some(algebraic_type) = algebraic {
                            algebraic_binding =
                                Some((SurfaceBinder::from(name), variable, algebraic_type.clone()));
                            surface_bindings = surface_bindings.with_inserted(
                                name.clone(),
                                SurfaceBinder::from(name).reference(),
                            );
                        } else if matches!(
                            self.goal(),
                            Some(Proposition::ForAll {
                                sort: crate::kernel::Sort::Integer,
                                ..
                            })
                        ) {
                            integer_binding = Some((name.kernel_name(), variable));
                        } else {
                            surface_bindings = surface_bindings.with_inserted(
                                name.clone(),
                                SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                                    match self.proposition_goal("`intro` requires a proposition goal").expect("intro checked its goal") {
                                        Proposition::ForAll { sort, .. } if sort.machine_integer_type().is_some() => sort.machine_integer_type().unwrap().symbolic_value(variable),
                                        _ => ProgramValue::Int32(OldMachineTerm::Variable(variable)),
                                    },
                                )),
                            );
                        }
                        Some(Arc::new(body.as_ref().clone()))
                    }
                    // A range quantifier stated where no lowering head chain
                    // was recorded (a `have` at an execution frontier) names
                    // its variable like a written `forall`. Its range guard
                    // is the next introduction, so the remaining written goal
                    // is that guard implying the body, which the
                    // implication arm above then refines to the body.
                    (
                        None,
                        PropositionIntroduction::Universal {
                            variable,
                            algebraic: None,
                            ..
                        },
                        Some(SyntaxProposition::RangeAll {
                            start,
                            end,
                            item,
                            body,
                            ..
                        }),
                    ) => {
                        surface_bindings = surface_bindings.with_inserted(
                            item.clone(),
                            SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                                match self.proposition_goal("`intro` requires a proposition goal").expect("intro checked its goal") {
                                    Proposition::ForAll { sort, .. } if sort.machine_integer_type().is_some() => sort.machine_integer_type().unwrap().symbolic_value(variable),
                                    _ => ProgramValue::Int32(OldMachineTerm::Variable(variable)),
                                },
                            )),
                        );
                        let bound = item.reference();
                        let guard = SyntaxProposition::And(
                            Box::new(SyntaxProposition::Comparison {
                                left: start.clone(),
                                operator: ComparisonOperator::LessEqual,
                                right: bound.clone(),
                            }),
                            Box::new(SyntaxProposition::Comparison {
                                left: bound,
                                operator: ComparisonOperator::LessThan,
                                right: end.clone(),
                            }),
                        );
                        Some(Arc::new(SyntaxProposition::Implies(
                            Box::new(guard),
                            body.clone(),
                        )))
                    }
                    _ => None,
                };
                PropositionPresentation {
                    surface,
                    surface_bindings,
                    introductions: current.introductions.advanced(),
                    introduced_antecedents,
                    both_children: None,
                    witness_refinement_kernel: current.witness_refinement_kernel.clone(),
                    generated_surface: current.generated_surface,
                }
            })
            .map_err(|error| match error {
                PropositionCloseError::NotProposition => {
                    self.step_error("`intro` requires a proposition goal")
                }
                PropositionCloseError::ExpectedIntroduction(goal) => self.step_error(format!(
                    "`intro` requires an implication or universal goal, got {}",
                    describe_known_goal(&goal)
                )),
                PropositionCloseError::IntegerFresheningExhausted => {
                    self.step_error("`intro` requires a fresh Integer binder variable")
                }
                PropositionCloseError::UniversalWitnessFresheningExhausted => self.step_error(
                    "`intro` requires a fresh witness identity for the universal's bound variable, and this proof has used every one the reserved witness range holds",
                ),
                _ => unreachable!("kernel returned an unrelated intro error"),
            })?;
        if algebraic_binding.is_none()
            && integer_binding.is_none()
            && antecedent_spelling.is_none()
            && machine_binding.is_none()
        {
            return Ok(state);
        }
        let mut locals = state.locals().clone();
        if let Some((name, variable, algebraic_type)) = algebraic_binding {
            locals.set_algebraic_values(locals.algebraic_values.with_inserted(
                name,
                crate::kernel::SpecAlgebraicExpression {
                    algebraic_type,
                    node: crate::kernel::SpecAlgebraicExpressionNode::Variable(variable),
                },
            ));
        } else if let Some((name, variable)) = integer_binding {
            locals.set_integer_values(locals.integer_values.with_inserted(
                name,
                crate::kernel::SpecIntegerExpression::Term(crate::kernel::IntegerTerm::var(
                    variable,
                )),
            ));
        }
        // The kernel's type bounds are born with the introduced name. Record
        // their spellings with this bounded delta, without searching ambient
        // facts or asking individual premise consumers to recover the name.
        if let Some((name, variable, value)) = machine_binding {
            let _name_scope = super::super::surface_synthesis::folds::Binding::enter(
                (
                    super::super::surface_synthesis::folds::BinderCarrier::Program,
                    variable,
                ),
                name.clone(),
            );
            let names = BTreeMap::new();
            let source_state = ExecutionState::new();
            let _ = value;
            for fact in state.state().added_facts() {
                let surface = super::super::surface_synthesis::synthesize_surface_proposition_with_bound_variable_names(
                    fact, ParameterBinding::default(), &source_state, &names,
                ).ok_or_else(|| self.step_error("an introduced type bound has no Surface form"))?;
                locals
                    .surface_facts
                    .record_lowering(&surface, fact)
                    .map_err(|error| {
                        self.step_error(format!("could not record introduced type bound: {error}"))
                    })?;
            }
        }
        // The introduced antecedent is spelled for premise lookups, as a
        // pure `have` is; see `ProofLocals::surface_facts`. A spelling is an
        // index, not authority: one that does not record is left out rather
        // than failing the step.
        if let Some((surface, kernel)) = &antecedent_spelling {
            let mut spelled = locals.surface_facts.clone();
            if spelled.record_lowering(surface, kernel).is_ok() {
                locals.surface_facts = spelled;
            }
        }
        Ok(state.with_locals(locals))
    }

    #[inline(never)]
    fn apply_induct(
        &self,
        parameter: &str,
        hypothesis: &str,
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let ProofContext::Pure(context) = self.context.as_ref() else {
            return Err(self.step_error("`induct` requires a pure theorem proof"));
        };
        let Some(setup) = context.induction_setup.as_ref() else {
            return Err(self.step_error("`induct` is not active for this pure theorem"));
        };
        if parameter != setup.parameter || hypothesis != setup.hypothesis {
            return Err(self.step_error("induction step does not match the theorem setup"));
        }
        let expected_goal =
            self.lower_surface_proposition(&setup.surface_goal, "induction theorem goal")?;
        if self.goal() != Some(&expected_goal) {
            return Err(self.step_error("`induct` requires the original theorem goal"));
        }
        if setup.structural_parameters.is_some() {
            if self.state().locals().induction_active {
                return Err(self.step_error("induction hypothesis was already introduced"));
            }
            let value = setup
                .structural_root
                .as_ref()
                .expect("checked structural parameter");
            if value.algebraic_type.rigid {
                return Err(self.step_error("structural induction requires a datatype; this is a Click library primitive type with no constructors"));
            }
            let mut locals = self.state().locals().clone();
            locals.induction_active = true;
            return Ok(self.checked_fact_transition(
                locals,
                self.facts().clone(),
                false,
                Vec::new(),
                Vec::new(),
            ));
        }
        match context.theorem_context.values.get(parameter) {
            Some(ProgramValue::Int32(current)) => {
                let nonnegative = Proposition::condition_is(
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterEqual,
                        left: Box::new(current.clone()),
                        right: Box::new(OldMachineTerm::constant(0)),
                    },
                    true,
                );
                if !self.facts().contains(&nonnegative)
                    && !self.facts().has_nonnegative_induction_domain(current)
                {
                    return Err(self.step_error(format!(
                        "`induct({parameter})` requires a proof that `{parameter}` is nonnegative"
                    )));
                }
            }
            // Every native unsigned value is in the well-founded domain.
            Some(ProgramValue::UInt64(_)) => {}
            _ => return Err(self.step_error("induction parameter must have type int32 or uint64")),
        }
        let quantified = super::super::pure_theorems::pure_induction_hypothesis(
            setup,
            context.theorem_context,
            context.spec_definitions,
        )?;
        if self.facts().contains(&quantified) {
            return Err(self.step_error("induction hypothesis was already introduced"));
        }
        let facts = self.facts().with_kernel_checked_fact(quantified.clone());
        Ok(self.checked_fact_transition(
            self.state().locals().clone(),
            facts,
            false,
            vec![quantified.clone()],
            vec![quantified],
        ))
    }

    #[inline(never)]
    fn apply_induction(
        &self,
        hypothesis: &str,
        arguments: &[SyntaxTerm],
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let ProofContext::Pure(context) = self.context.as_ref() else {
            return Err(self.step_error("induction application requires a pure theorem proof"));
        };
        if context
            .induction_setup
            .as_ref()
            .is_some_and(|setup| setup.structural_parameters.is_some())
        {
            return self.apply_structural_induction_hypothesis(hypothesis, arguments);
        }
        let Some(setup) = context.induction_setup.as_ref() else {
            return Err(self.step_error("induction hypothesis is not active"));
        };
        if hypothesis != setup.hypothesis {
            return Err(self.step_error(format!("unknown induction hypothesis `{hypothesis}`")));
        }
        // Measure induction quantifies one scalar variable: its hypothesis
        // holds every other theorem parameter at its current value.
        let [argument] = arguments else {
            return Err(self.step_error(format!(
                "induction hypothesis `{hypothesis}` expects one argument"
            )));
        };
        let premises =
            super::super::pure_theorems::induction_application_surface_premises(setup, argument)?;
        let mut explicit_premises = Vec::with_capacity(premises.len());
        for premise in premises {
            let lowered = self.lower_cited_surface_proposition(&premise, "induction premise")?;
            if matches!(
                crate::surface::checking::normalize_proposition(&lowered),
                crate::surface::checking::NormalizedProposition::True
            ) {
                continue;
            }
            let cited = if crate::kernel::proof::fact_reasoning::order_claim_forms(&lowered)
                .iter()
                .chain(std::iter::once(&lowered))
                .any(|form| self.facts().contains(form))
            {
                lowered
            } else {
                // Native arithmetic can be stated using its Integer observations.
                let observed =
                    super::super::smart_closures::observed_native_arithmetic(&lowered, &premise);
                let cited = self.lower_cited_surface_proposition(&observed, "induction premise")?;
                if !self.facts().contains(&cited) {
                    return Err(self.step_error(format!(
                        "induction hypothesis `{hypothesis}` found no available fact for premise `{}`",
                        crate::surface::diagnostics::describe_click_proposition(&observed),
                    ))
                    .with_spelled_requirement(cited, observed, format!("induction hypothesis `{hypothesis}` premise")));
                }
                cited
            };
            crate::surface::proof::theorem_application::cite_range_span_guards(
                &cited,
                &mut explicit_premises,
                |guard| self.facts().exact_available_across_effects(guard, &[]),
            );
            if !explicit_premises.contains(&cited) {
                explicit_premises.push(cited);
            }
        }

        let state = ExecutionState::at_point(&context.theorem_context.point);
        let mut active_functions = BTreeSet::new();
        let value = evaluate_contract_expression_with_environment(
            &context.theorem_context.values,
            &context.theorem_context.array_refs,
            &state,
            &state,
            None,
            self.facts().assumptions(),
            argument,
            context.spec_definitions,
            &RecordedStates::new(),
            &mut active_functions,
        )
        .map_err(|message| {
            self.step_error(format!("could not evaluate induction argument: {message}"))
        })?;
        let argument = match (context.theorem_context.values.get(&setup.parameter), value) {
            (Some(ProgramValue::Int32(_)), ProgramValue::Int32(argument))
            | (Some(ProgramValue::UInt64(_)), ProgramValue::UInt64(argument)) => argument,
            _ => return Err(self.step_error("induction argument must have the measure's type")),
        };
        let quantified = super::super::pure_theorems::pure_induction_hypothesis(
            setup,
            context.theorem_context,
            context.spec_definitions,
        )?;
        self.state
            .apply_induction_instance(
                quantified,
                crate::kernel::proof::fact_reasoning::InstanceArgument::Machine(argument),
                &explicit_premises,
            )
            .map(|state| {
                // `apply_induction_instance` has performed the complete kernel
                // premise/order/conclusion check. Publish its exact fact
                // delta through the same Proof transition used by ordinary
                // quantified instantiation.
                let added_facts = state.state().checked_facts().to_vec();
                let mut facts = self.facts().clone();
                for fact in &added_facts {
                    facts = facts.with_kernel_checked_fact(fact.clone());
                }
                let complete = self.goal().is_some_and(|goal| facts.contains(goal));
                self.checked_fact_transition(
                    self.state().locals().clone(),
                    facts,
                    complete,
                    added_facts.clone(),
                    added_facts,
                )
            })
            .map_err(|error| match error {
                PropositionCloseError::NotProposition => {
                    self.step_error("induction application requires a proposition goal")
                }
                PropositionCloseError::InductionPremiseUnavailable(premise) => {
                    self.step_error(format!(
                        "induction premise is not exactly available: {}",
                        self.render_diagnostic_proposition(&premise)
                    ))
                }
                PropositionCloseError::InstantiateQuantifiedUnavailable => {
                    self.step_error("induction hypothesis is not exactly available")
                }
                PropositionCloseError::InstantiateInvalid(error) => {
                    use crate::kernel::proof::fact_reasoning::ForallInstantiationError;
                    let obligation = match &error {
                        ForallInstantiationError::MissingGuard(guard) => {
                            Some(ProofObligation::verification_condition(guard.clone()))
                        }
                        _ => None,
                    };
                    let error = self.step_error(format!(
                        "`apply` of the induction hypothesis failed: {}",
                        crate::surface::proof::format_forall_instantiation_error(
                            error,
                            &|missing| self.render_diagnostic_proposition(missing),
                        )
                    ));
                    match obligation {
                        Some(obligation) => error.with_unresolved_requirement(&obligation),
                        None => error,
                    }
                }
                _ => unreachable!("kernel returned an unrelated induction error"),
            })
    }

    fn apply_structural_induction_hypothesis(
        &self,
        hypothesis: &str,
        arguments: &[SyntaxTerm],
    ) -> Result<CheckedFocusedTransition, ClickError> {
        let application = self.structural_induction_instance(hypothesis, arguments)?;
        let explicit_premises = &application.kernel_premises;
        if let Some((missing, surface)) = explicit_premises
            .iter()
            .zip(&application.surface_premises)
            .find(|(premise, _)| !self.facts().listed_premise_available(premise, &[], true))
        {
            return Err(self
                .step_error(format!(
                    "induction premise is not exactly available: {}",
                    self.render_diagnostic_proposition(missing)
                ))
                .with_spelled_requirement(
                    missing.clone(),
                    surface.clone(),
                    format!("induction hypothesis `{hypothesis}` premise"),
                ));
        }
        let instantiated = self
            .facts()
            .with_kernel_checked_fact(application.implication.clone());
        if !instantiated.contains(&application.conclusion)
            && !instantiated.contains_discharged_implication_consequent(&application.conclusion)
        {
            if let Some(guard) = explicit_premises
                .iter()
                .flat_map(crate::kernel::stated_loadable_span_guards)
                .find(|guard| !self.facts().listed_premise_available(guard, &[], true))
            {
                return Err(self
                    .step_error(format!(
                        "induction range needs an established span: {}",
                        self.render_diagnostic_proposition(&guard),
                    ))
                    .with_unresolved_requirement(&ProofObligation::verification_condition(guard)));
            }
            return Err(self.step_error("kernel rejected structural induction application"));
        }
        let added = (!self.facts().contains_top_level(&application.conclusion))
            .then(|| application.conclusion.clone())
            .into_iter()
            .collect::<Vec<_>>();
        let mut facts = instantiated;
        for fact in &added {
            facts = facts.with_kernel_checked_fact(fact.clone());
        }
        let complete = self.goal().is_some_and(|goal| facts.contains(goal));
        Ok(self.checked_fact_transition(
            self.state().locals().clone(),
            facts,
            complete,
            added.clone(),
            added,
        ))
    }

    // Preserve the rule/dispatcher frame boundary described above; instance
    // materialization is local to this rule.
    #[inline(never)]
    pub(super) fn apply_enumerate(&self) -> Result<KernelProofHandle, ClickError> {
        self.state.apply_enumerate().map_err(|error| match error {
            PropositionCloseError::NotProposition => {
                self.step_error("`enumerate` requires a proposition goal")
            }
            PropositionCloseError::ExpectedFiniteUniversal => {
                self.step_error("`enumerate` requires a universal goal with constant bounds")
            }
            PropositionCloseError::MissingFiniteInstance => self.step_error(
                "`enumerate` requires each in-range instance as an exact available fact",
            ),
            _ => unreachable!("kernel returned an unrelated enumerate error"),
        })
    }
}

fn trace_frontier(frontier: &ExecutionFrontier) -> String {
    if frontier.is_at_function_entry() {
        "function entry".into()
    } else if frontier.is_at_function_exit() {
        "function exit".into()
    } else if frontier.is_at_region_boundary() {
        "region boundary".into()
    } else {
        format!("C statement {}", frontier.next_statement_index + 1)
    }
}

fn trace_statement_head(statement: &ProgramStatement) -> String {
    if let ProgramStatement::Store { pointer, value }
    | ProgramStatement::TypedStore { pointer, value, .. } = statement
        && let ProgramExpression::Add(base, index) = pointer
    {
        return format!(
            "{}[{}] = {}",
            crate::surface::diagnostics::describe_program_expression(base),
            crate::surface::diagnostics::describe_program_expression(index),
            crate::surface::diagnostics::describe_program_expression(value),
        );
    }
    describe_statement_head(statement)
}

/// Prefer an exact parameter base for a trace. The general diagnostic range
/// printer accepts an offset from any parameter, which can turn a `visited`
/// view into `left[(v100002-v100000)..]` even though `visited` is available.
fn trace_resource_fact(
    fact: &ResourceFact,
    context: &ExecutionProofContext<'_>,
    reached: &ExecutionState,
) -> String {
    if let Some(range) = fact.memory_range() {
        for (parameter, argument) in context
            .parsed_function
            .parameters()
            .iter()
            .zip(context.arguments)
        {
            if let ProgramExpression::Value(ProgramValue::Pointer(base)) = argument
                && base.address() == range.base()
            {
                return crate::surface::proof_diagnostics::render::render_resource_fact_diagnostic(
                    fact,
                    ParameterBinding::new(
                        std::slice::from_ref(parameter),
                        std::slice::from_ref(argument),
                    ),
                );
            }
        }
    }
    // The reached state's locals name what the step introduced, a call's
    // result temporary as `<region>.result` among them.
    let mut labels = crate::surface::proof_diagnostics::render::MemoryStateLabels::with_state(
        context.parameter_binding(),
        reached,
    );
    let mut text =
        crate::surface::proof_diagnostics::render::render_resource_fact_spelled(fact, &mut labels);
    text.push_str(&labels.trace_legend());
    text
}

fn describe_known_goal(goal: &Proposition) -> &'static str {
    match goal {
        Proposition::And(..) => "a conjunction",
        Proposition::Or(..) => "a disjunction",
        Proposition::Implies(..) => "an implication",
        Proposition::Not(..) => "a negation",
        Proposition::ForAll { .. } => "a universal proposition",
        Proposition::Exists { .. } => "an existential proposition",
        Proposition::MemoryLoadable { .. } => "a memory-viewability fact",
        Proposition::ConditionIs(condition, _) => match condition.old_form() {
            OldConditionTerm::IntegerLessThan(..) => "an Integer less-than fact",
            OldConditionTerm::IntegerLessEqual(..) => "an Integer less-or-equal fact",
            OldConditionTerm::IntegerGreaterThan(..) => "an Integer greater-than fact",
            OldConditionTerm::IntegerGreaterEqual(..) => "an Integer greater-or-equal fact",
            OldConditionTerm::IntegerEqual(..) => "an Integer equality fact",
            OldConditionTerm::IntegerNotEqual(..) => "an Integer disequality fact",
            _ => "a condition fact",
        },
        Proposition::Equal(Term::Integer(_), Term::Integer(_)) => "an Integer equality fact",
        Proposition::Equal(..) => "an equality fact",
        _ => "a proposition fact",
    }
}

/// A step that adds a fact closes a proposition goal it added. A goal that was already available before the step stays open.
fn close_goal_from_added_fact(state: KernelProofHandle) -> KernelProofHandle {
    state.closed_if_goal_was_added().unwrap_or(state)
}

/// Recover one load's presentation from its accepted statement theorem.
/// Address evaluation is confined to the selected expression and supplies no
/// facts to checking. The produced value is read directly from the outcome.
fn trace_function_pointer_load(
    conclusion: &Proposition,
    assumptions: &crate::kernel::PureFactContext,
) -> Option<crate::surface::proof_trace::TraceLoad> {
    let Proposition::ProgramStatementVerifies {
        state,
        statement,
        outcome,
    } = conclusion
    else {
        return None;
    };
    let ProgramStatement::Assign {
        name,
        expression:
            ProgramExpression::TypedLoad {
                pointer,
                value_type: ProgramType::FunctionPointer(_),
                ..
            },
        ..
    } = statement.as_ref()
    else {
        return None;
    };
    let StatementOutcome::Normal(after) = outcome else {
        return None;
    };
    let value = after.scalar_local_value(name)?;
    let (address, _) = crate::kernel::program_evaluate_speprogram_expression_at_state(
        state,
        &crate::kernel::SpecExpression::ProgramExpression(pointer.as_ref().clone()),
        None,
        assumptions,
    )
    .ok()?;
    Some(crate::surface::proof_trace::TraceLoad {
        target: name.to_string(),
        value,
        address,
        memory: crate::kernel::intern_memory_ref(state.memory()),
    })
}

#[path = "../driver/steps.rs"]
mod driver;

/// How many dropped cached cells one traced step lists.
const TRACE_FORGOTTEN_CELL_LIMIT: usize = 4;

/// How many stopped read-history walks one traced step lists.
const TRACE_HISTORY_STOP_LIMIT: usize = 4;
