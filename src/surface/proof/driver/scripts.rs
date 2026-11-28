//! Proof script orchestration; explicit operations remain on Proof.
use super::*;
use crate::surface::proof::driver::ProofDriver;

use crate::kernel::proof::{
    PropositionIdentityKey, proposition_identity_key, proposition_with_canonical_binders,
    propositions_are_alpha_equal,
};
use std::collections::{HashMap, VecDeque};

#[derive(PartialEq, Eq, PartialOrd, Ord)]
enum ConjunctKey {
    Indexed(PropositionIdentityKey),
    Structural(Box<Proposition>),
}

impl ConjunctKey {
    fn of(proposition: &Proposition) -> Self {
        match proposition_identity_key(proposition) {
            Some(key) => Self::Indexed(key),
            None => Self::Structural(Box::new(proposition_with_canonical_binders(proposition))),
        }
    }
}

struct ConjunctArms<'proof, 'a, 'source> {
    parent: &'proof Proof<'a>,
    arms: &'source [ProofAllArm],
    written: HashMap<&'source SyntaxProposition, VecDeque<usize>>,
    lowered: Option<BTreeMap<ConjunctKey, VecDeque<(usize, Proposition)>>>,
    used: Vec<bool>,
    grouped: usize,
}

impl<'proof, 'a, 'source> ConjunctArms<'proof, 'a, 'source> {
    fn new(parent: &'proof Proof<'a>, arms: &'source [ProofAllArm]) -> Self {
        let mut written = HashMap::<_, VecDeque<_>>::new();
        let mut grouped = 0;
        for (index, arm) in arms.iter().enumerate() {
            crate::instrumentation::record_deterministic_work(1);
            written
                .entry(&arm.proposition)
                .or_default()
                .push_back(index);
            grouped += usize::from(matches!(arm.proposition, SyntaxProposition::And(..)));
        }
        Self {
            parent,
            arms,
            written,
            lowered: None,
            used: vec![false; arms.len()],
            grouped,
        }
    }

    fn take(
        &mut self,
        proof: &Proof<'a>,
        goal: &Proposition,
    ) -> Option<(usize, &'source ProofAllArm)> {
        let written = proof.surface_goal().and_then(|surface| {
            let candidates = self.written.get_mut(surface)?;
            while candidates.front().is_some_and(|&index| self.used[index]) {
                candidates.pop_front();
            }
            candidates.pop_front()
        });
        let index = written.or_else(|| self.take_lowered(goal))?;
        self.used[index] = true;
        let arm = &self.arms[index];
        self.grouped -= usize::from(matches!(arm.proposition, SyntaxProposition::And(..)));
        Some((index, arm))
    }

    fn take_lowered(&mut self, goal: &Proposition) -> Option<usize> {
        let grouped = matches!(goal, Proposition::And(..));
        if grouped && self.grouped == 0 {
            return None;
        }
        // All sibling obligations inherit the same bindings and assumptions.
        // Only labels that need structural comparison are lowered, once per
        // written arm against the scope shared by the children.
        let lowered = self.lowered.get_or_insert_with(|| {
            let mut lowered = BTreeMap::<_, VecDeque<_>>::new();
            for (index, arm) in self
                .arms
                .iter()
                .enumerate()
                .filter(|(index, _)| !self.used[*index])
            {
                crate::instrumentation::record_deterministic_work(1);
                if let Ok(label) = self.parent.lower_conjunct_label(&arm.proposition) {
                    lowered
                        .entry(ConjunctKey::of(&label))
                        .or_default()
                        .push_back((index, label));
                }
            }
            lowered
        });
        let candidates = lowered.get_mut(&ConjunctKey::of(goal))?;
        while candidates
            .front()
            .is_some_and(|(index, _)| self.used[*index])
        {
            candidates.pop_front();
        }
        // The identity indexes the labels in this explicit block. The
        // ordinary check also compares the non-memory storage of predicates.
        let matching = candidates.iter().position(|(index, label)| {
            !self.used[*index]
                && (!grouped || matches!(self.arms[*index].proposition, SyntaxProposition::And(..)))
                && propositions_are_alpha_equal(label, goal)
        })?;
        candidates.remove(matching).map(|(index, _)| index)
    }
}

impl<'p, 'a> ProofDriver<'p, Proof<'a>> {
    /// Checks source whose caller has already selected this Proof driver as
    /// the semantic authority. Explicit operation failures propagate instead
    /// of being converted into a compatibility miss; recursive scopes and
    /// branch arms inherit the same rule.
    pub(in crate::surface::proof) fn try_authoritative_linear_script(
        &self,
        tactics: &[ProofTactic],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        let driver_proof = self.proof;
        driver_proof
            .driver()
            .try_authoritative_linear_script_reporting(tactics, &mut None, None, false)
    }

    /// [`Self::try_authoritative_linear_script`], also reporting why the body
    /// declined. A caller that turns the decline into a user-facing error
    /// needs the written step to name, not only that some route said no.
    pub(in crate::surface::proof) fn try_authoritative_linear_script_reporting(
        &self,
        tactics: &[ProofTactic],
        declined: &mut Option<LinearScriptDecline>,
        unfinished: Option<&mut Option<Proof<'a>>>,
        implicit_tail: bool,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        let driver_proof = self.proof;
        // Address each tactic's diagnostics by its position in the block the
        // user wrote, so a failure inside one `have` body is distinguishable
        // from the same failure inside another.
        let sites = (0..tactics.len())
            .map(|index| driver_proof.site().at_block_position(index))
            .collect::<Vec<_>>();
        driver_proof.driver().try_addressed_linear_script(
            tactics,
            &sites,
            declined,
            unfinished,
            implicit_tail,
        )
    }

    /// Checks an explicit planner candidate without attributing its block
    /// positions to a written source body, then restores the caller's site.
    pub(in crate::surface::proof) fn try_generated_linear_script(
        &self,
        tactics: &[ProofTactic],
    ) -> Result<Option<Proof<'a>>, ClickError> {
        let driver_proof = self.proof;
        driver_proof
            .at_source_tactic(usize::MAX)
            .driver()
            .try_authoritative_linear_script(tactics)
            .map(|proof| proof.map(|proof| proof.at_site(driver_proof.site())))
    }

    /// The linear script runner. `sites[index]` is where `tactics[index]`
    /// was written. A proof `if` or `cases` arm is checked together with the
    /// tactics after it, so its script joins the arm's own tactics, addressed
    /// inside that arm, to the continuation, which keeps the addresses it has
    /// in the enclosing block: every written tactic reports its own source
    /// position however many arms check it.
    pub(in crate::surface::proof) fn try_addressed_linear_script(
        &self,
        tactics: &[ProofTactic],
        sites: &[ProofStepSite],
        declined: &mut Option<LinearScriptDecline>,
        unfinished: Option<&mut Option<Proof<'a>>>,
        implicit_tail: bool,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        let driver_proof = self.proof;
        driver_proof.driver().run_addressed_linear_script(
            tactics,
            sites,
            declined,
            unfinished,
            implicit_tail && !crate::surface::proof::proof_object::implicit_solve_disabled(),
        )
    }

    /// [`Self::try_authoritative_linear_script`], also keeping the proof a
    /// body left with its focused goal still open, so a caller refusing the
    /// body can name the goal it stopped at. Only a script that ran every
    /// written step (in its own block or in a proof `if`, `cases` or `both`
    /// arm) leaves one; a declined step leaves none.
    pub(in crate::surface::proof) fn try_authoritative_linear_script_leaving_open(
        &self,
        tactics: &[ProofTactic],
        unfinished: &mut Option<Proof<'a>>,
        implicit_tail: bool,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        let driver_proof = self.proof;
        driver_proof
            .driver()
            .try_authoritative_linear_script_reporting(
                tactics,
                &mut None,
                Some(unfinished),
                implicit_tail,
            )
    }

    /// Runs the arms of one `cases` to completion. The kernel splits a
    /// disjunction in two, so more than two arms split the leading arms'
    /// disjunction against the last arm and recurse into the leading branch;
    /// each arm still runs at the sites of its own source block.
    fn run_case_arms(
        &self,
        arms: &[CaseArmScript<'_>],
        mut unfinished: Option<&mut Option<Proof<'a>>>,
        implicit_tail: bool,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        let driver_proof = self.proof;
        let (last, leading) = arms.split_last().expect("`cases` has arms");
        let disjunction = leading.iter().skip(1).fold(
            leading
                .first()
                .expect("`cases` has at least two arms")
                .assumption
                .clone(),
            |disjunction, arm| {
                SyntaxProposition::Or(Box::new(disjunction), Box::new(arm.assumption.clone()))
            },
        );
        let disjunction =
            SyntaxProposition::Or(Box::new(disjunction), Box::new(last.assumption.clone()));
        let prepared = driver_proof
            .driver()
            .prove_cases_disjunction(&disjunction)?;
        let (split_proof, split, ids) = prepared.split_focused_cases(disjunction.clone())?;
        let marker = split_proof.checkpoint();
        let leading_branch = split_proof.focus_branch(ids[0])?;
        let leading_done = match leading {
            [only] => leading_branch.driver().run_addressed_linear_script(
                &only.tactics,
                &only.sites,
                &mut None,
                unfinished.as_deref_mut(),
                implicit_tail,
            )?,
            _ => leading_branch.driver().run_case_arms(
                leading,
                unfinished.as_deref_mut(),
                implicit_tail,
            )?,
        };
        let Some(leading_done) = leading_done else {
            return Ok(None);
        };
        let Some(all_done) = leading_done
            .restore_induction_scope_from(&split_proof)
            .focus_branch(ids[1])?
            .driver()
            .run_addressed_linear_script(
                &last.tactics,
                &last.sites,
                &mut None,
                unfinished,
                implicit_tail,
            )?
        else {
            return Ok(None);
        };
        all_done
            .join_focused_cases(&marker, split, ids, disjunction)
            .map(Some)
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::surface::proof) fn run_pure_match_group(
        &self,
        plan: &super::proof_object::PureMatchPlan,
        source: &ProofMatch,
        indices: &[usize],
        arm_tactics: &[Vec<ProofTactic>],
        arm_sites: &[Vec<ProofStepSite>],
        certificates: &mut Vec<ProofCertificate>,
        trace: &mut Option<crate::surface::proof_trace::TraceMatch>,
        mut unfinished: Option<&mut Option<Proof<'a>>>,
        implicit_tail: bool,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        let driver_proof = self.proof;
        if let [index] = indices {
            let (arm, constructor_equation) = driver_proof.enter_pure_match_case(plan, *index)?;
            let marker = arm.checkpoint();
            let written = source.arms[*index].tactics.len();
            let mut pending = None;
            let terminal = written == arm_tactics[*index].len();
            let closed = if written == 0 && !(terminal && implicit_tail) {
                Some(arm.clone())
            } else {
                arm.driver().run_addressed_linear_script(
                    &arm_tactics[*index][..written],
                    &arm_sites[*index][..written],
                    &mut None,
                    Some(&mut pending),
                    terminal && implicit_tail,
                )?
            };
            let Some(body_done) = closed.or(pending) else {
                return Ok(None);
            };
            let body_done = body_done.leave_pure_match_case(plan, *index)?;
            let done = if written < arm_tactics[*index].len() {
                let Some(done) = body_done.driver().run_addressed_linear_script(
                    &arm_tactics[*index][written..],
                    &arm_sites[*index][written..],
                    &mut None,
                    unfinished,
                    implicit_tail,
                )?
                else {
                    return Ok(None);
                };
                done
            } else if body_done.focused_discharged() {
                body_done
            } else {
                if let Some(unfinished) = unfinished {
                    *unfinished = Some(body_done);
                }
                return Ok(None);
            };
            certificates.push(done.certificate_since(&marker)?);
            if let Some(trace) = trace {
                let equation = constructor_equation
                    .as_ref()
                    .expect("traced match arm retains its constructor equation");
                trace.arms[*index] =
                    Some(done.pure_match_arm_trace(&arm, &marker, source, *index, equation));
            }
            return Ok(Some(done.leave_pure_match_case(plan, *index)?));
        }
        let middle = indices.len() / 2;
        let (split_proof, split, ids) = driver_proof.split_pure_match_group()?;
        let marker = split_proof.checkpoint();
        let Some(left_done) = split_proof
            .focus_branch(ids[0])?
            .driver()
            .run_pure_match_group(
                plan,
                source,
                &indices[..middle],
                arm_tactics,
                arm_sites,
                certificates,
                trace,
                unfinished.as_deref_mut(),
                implicit_tail,
            )?
        else {
            return Ok(None);
        };
        let Some(done) = left_done
            .restore_induction_scope_from(&split_proof)
            .focus_branch(ids[1])?
            .driver()
            .run_pure_match_group(
                plan,
                source,
                &indices[middle..],
                arm_tactics,
                arm_sites,
                certificates,
                trace,
                unfinished,
                implicit_tail,
            )?
        else {
            return Ok(None);
        };
        done.join_focused_both(&marker, split, ids).map(Some)
    }

    /// Keep the kernel's binary splits and joins in goal order. Source sites
    /// retain the written arm index even when its proof runs earlier or later.
    fn run_conjunct_proofs(
        &self,
        arms: &mut ConjunctArms<'_, 'a, '_>,
        site: &ProofStepSite,
        mut unfinished: Option<&mut Option<Proof<'a>>>,
        implicit_tail: bool,
        at_root: bool,
    ) -> Result<Option<(Proof<'a>, Option<Arc<SyntaxProposition>>)>, ClickError> {
        let proof = self.proof;
        let Some(goal) = proof.goal() else {
            return Err(proof.step_error("`all` requires a conjunction goal"));
        };
        if !at_root && let Some((index, arm)) = arms.take(proof, goal) {
            let sites = (0..arm.tactics.len())
                .map(|position| site.in_arm(index, "conjunct", position))
                .collect::<Vec<_>>();
            return Ok(proof
                .driver()
                .run_addressed_linear_script(
                    &arm.tactics,
                    &sites,
                    &mut None,
                    unfinished,
                    implicit_tail,
                )?
                .map(|done| (done, Some(Arc::new(arm.proposition.clone())))));
        }
        if !proof.has_conjunctive_goal() {
            return Err(proof.step_error(if at_root {
                "`all` requires a conjunction goal"
            } else {
                "`all` is missing an arm for this conjunct"
            }));
        }
        let (split_proof, split, ids) = proof.split_focused_both()?;
        let Some((left, left_label)) = split_proof
            .focus_branch(ids[0])?
            .driver()
            .run_conjunct_proofs(arms, site, unfinished.as_deref_mut(), implicit_tail, false)?
        else {
            return Ok(None);
        };
        let Some((right, right_label)) = left
            .restore_induction_scope_from(&split_proof)
            .focus_branch(ids[1])?
            .driver()
            .run_conjunct_proofs(arms, site, unfinished, implicit_tail, false)?
        else {
            return Ok(None);
        };
        let marker = split_proof
            .checkpoint()
            .with_conjunct_labels([left_label, right_label]);
        Ok(Some((right.join_focused_both(&marker, split, ids)?, None)))
    }

    pub(in crate::surface::proof) fn apply_scoped_intro(
        &self,
        binder: Option<&SurfaceBinder>,
        body: &[ProofTactic],
        implicit_tail: bool,
    ) -> Result<Proof<'a>, ClickError> {
        let parent = self.proof;
        let step = binder
            .cloned()
            .map_or(ProofStep::Intro, ProofStep::IntroBinder);
        let introduced = self.apply_scoped_intro_step(step)?;
        let range_opened = parent
            .opens_scoped_range(&introduced)
            .then(|| {
                introduced
                    .driver()
                    .apply_scoped_intro_step(ProofStep::Intro)
            })
            .transpose()?;
        let opened = range_opened.as_ref().unwrap_or(&introduced);
        let sites = (0..body.len())
            .map(|index| parent.site().in_arm(0, "intro", index))
            .collect::<Vec<_>>();
        let completed = opened
            .driver()
            .run_addressed_linear_script(body, &sites, &mut None, None, implicit_tail)?
            .ok_or_else(|| parent.step_error("the `intro` block must prove its opened goal"))?;
        parent.finish_scoped_intro(&introduced, opened, completed)
    }

    pub(in crate::surface::proof) fn apply_close(&self) -> Result<Proof<'a>, ClickError> {
        match self.apply_step(ProofStep::Known) {
            Ok(closed) => Ok(closed),
            Err(error)
                if error.verification_stopped()
                    || crate::surface::proof::implicit_solve_scope::checked_only() =>
            {
                Err(error.with_failed_tactic("close"))
            }
            Err(_) => {
                let _timing = TacticTiming::followup_search("close");
                let _origin = crate::surface::proof_trace::TraceOrigin::enter(Some("close"));
                let mut search = attempt::search_scope("close fallback");
                let (result, checks) =
                    crate::surface::proof_diagnostics::capture_check_observations(|| {
                        crate::kernel::search::ProofSearch::try_solve_closure(self.proof)
                    });
                match result {
                    Ok(Some(closed)) => {
                        search.succeed();
                        Ok(closed)
                    }
                    result => Err(result
                        .err()
                        .unwrap_or_else(|| self.proof.solve_failure())
                        .with_failed_tactic("close")
                        .with_check_observations(checks)
                        .with_search_failures(search.finish())),
                }
            }
        }
    }

    pub(in crate::surface::proof) fn run_addressed_linear_script(
        &self,
        tactics: &[ProofTactic],
        sites: &[ProofStepSite],
        declined: &mut Option<LinearScriptDecline>,
        mut unfinished: Option<&mut Option<Proof<'a>>>,
        implicit_tail: bool,
    ) -> Result<Option<Proof<'a>>, ClickError> {
        let driver_proof = self.proof;
        debug_assert_eq!(tactics.len(), sites.len());
        let solve = |proof: &Proof<'a>| {
            crate::surface::proof_diagnostics::capture_check_observations(|| {
                crate::kernel::search::ProofSearch::try_solve_closure(proof)
            })
        };
        let finish = |proof: Proof<'a>, unfinished: Option<&mut Option<Proof<'a>>>| {
            if proof.focused_discharged() {
                Ok(Some(proof))
            } else if implicit_tail {
                check_verification_deadline()?;
                let _timing =
                    TacticTiming::new(proof.claim_label(), 0, 0, &ProofTactic::ImplicitSolve, 0);
                let _origin =
                    crate::surface::proof_trace::TraceOrigin::enter_implicit("implicit tail");
                let mut search = attempt::search_scope("implicit script tail");
                let (result, checks) = solve(&proof);
                check_verification_deadline()
                    .map_err(|error| proof.attach_step_diagnostic(error))?;
                let error = match result {
                    Ok(Some(closed)) => {
                        search.succeed();
                        return Ok(Some(closed));
                    }
                    Ok(None) => proof.solve_failure(),
                    Err(error) => error,
                };
                Err(error
                    .with_check_observations(checks)
                    .with_search_failures(search.finish()))
            } else {
                if let Some(unfinished) = unfinished {
                    *unfinished = Some(proof);
                }
                Ok(None)
            }
        };
        let pure_source = matches!(driver_proof.context.as_ref(), ProofContext::Pure(_));
        if tactics.is_empty() && !implicit_tail {
            *declined = Some(LinearScriptDecline::Shape);
            return Ok(None);
        }
        let arm_sites = |index: usize, arm: usize, name: &'static str, written: usize| {
            (0..written)
                .map(|position| sites[index].in_arm(arm, name, position))
                .chain(sites[index + 1..].iter().cloned())
                .collect::<Vec<_>>()
        };

        let mut proof = driver_proof.clone();
        for (index, tactic) in tactics.iter().enumerate() {
            proof = proof.at_site(&sites[index]);
            let _timing = if pure_source {
                proof
                    .site()
                    .written_source_tactic_path()
                    .and_then(|path| TacticTiming::pure_source(proof.claim_label(), path, tactic))
            } else {
                None
            };
            let _origin = super::timing::trace_origin(tactic);
            let nested_capture = proof.begin_nested_tactic_capture();
            if proof.focused_discharged() {
                // A closer after a step that already discharged the goal (a
                // `transport` whose target is the goal, an exact theorem
                // conclusion, an `unfold` whose refreshed goal was already
                // an available fact) asserts a closed judgment: a harmless
                // no-op that emits no redundant certificate step. That is
                // `known`, a bare `solve`, and the checked bound closer,
                // in any position, so `unfold(f(x)); close();` means the
                // same whether or not the unfold alone closed the goal. Any
                // other suffix after closure is a declined shape, named with
                // the tactic that closed the goal.
                if matches!(
                    tactic,
                    ProofTactic::Known
                        | ProofTactic::Close
                        | ProofTactic::Solve
                        | ProofTactic::CloseBounds(_)
                ) {
                    // The harmless closer checks nothing: its expansion is
                    // empty.
                    if let Some(capture) = nested_capture {
                        capture.finish(&proof);
                    }
                    continue;
                }
                let closer = index
                    .checked_sub(1)
                    .and_then(|previous| tactics.get(previous))
                    .map_or("an earlier tactic".to_string(), |closer| {
                        format!("`{}`", tactic_name(closer))
                    });
                // `close() using` is refused here where a bare `close()`
                // is not, so it is named by its whole spelling.
                let name = match tactic {
                    ProofTactic::SolveUsing(_) => "close() using",
                    tactic => tactic_name(tactic),
                };
                return Err(proof.step_error(format!(
                    "`{name}` follows a goal-closing tactic: {closer} already closed this goal, so only `close()` may follow it",
                )));
            }
            // A step that adds a fact can close the goal before a written
            // suffix. Retain that completed step as a checked have, keeping
            // the outer goal open so every remaining explicit step is
            // checked; only a final step, or one followed by a harmless
            // closer, leaves the goal closed.
            let retain_application = matches!(
                tactic,
                ProofTactic::ApplyFact(_)
                    | ProofTactic::ApplyFactUsing { .. }
                    | ProofTactic::ApplyTheoremUsing { .. }
                    | ProofTactic::ApplyInduction { .. }
                    | ProofTactic::Instantiate { .. }
            ) && tactics.get(index + 1).is_some_and(|next| {
                !matches!(
                    next,
                    ProofTactic::Known | ProofTactic::Close | ProofTactic::Solve
                )
            });
            let retain_application = retain_application
                || (matches!(tactic, ProofTactic::ApplyTheorem(_))
                    && tactics.get(index + 1).is_some_and(|next| {
                        !matches!(
                            next,
                            ProofTactic::Known | ProofTactic::Close | ProofTactic::Solve
                        )
                    }));
            let before_application = retain_application.then(|| proof.clone());
            match tactic {
                ProofTactic::IntroBlock { binder, body } => {
                    proof =
                        proof
                            .driver()
                            .apply_scoped_intro(binder.as_ref(), body, implicit_tail)?;
                }
                ProofTactic::ApplyFact(fact) => {
                    proof = proof.driver().apply_fact_application(fact)?;
                }
                ProofTactic::ApplyTheorem(application) => {
                    proof = proof.driver().apply_theorem_application(application)?;
                }
                ProofTactic::ApplyInduction {
                    hypothesis,
                    arguments,
                } => {
                    proof = proof
                        .driver()
                        .apply_induction_application(hypothesis, arguments)?;
                }
                ProofTactic::Close => {
                    proof = proof.driver().apply_close().map_err(|error| {
                        if error.proof_refusal()
                            == Some(crate::surface::ProofRefusal::UnsuccessfulSearch)
                            && tactics[..index].iter().any(|previous| {
                                matches!(previous, ProofTactic::Witness(_) | ProofTactic::Choose(_))
                            })
                        {
                            error.with_context(
                                "checked `close` after witness/choose could not close the remaining witness obligations. Split conjunctions and discharge each definedness condition explicitly",
                            )
                        } else {
                            error
                        }
                    })?;
                }
                ProofTactic::Solve => {
                    let mut search = attempt::search_scope("written solve");
                    let (selected, checks) = solve(&proof);
                    let selected = match selected {
                        Ok(selected) => selected,
                        Err(error) => {
                            return Err(error
                                .with_check_observations(checks)
                                .with_search_failures(search.finish()));
                        }
                    };
                    let Some(closed) = selected else {
                        if tactics[..index].iter().any(|previous| {
                            matches!(previous, ProofTactic::Witness(_) | ProofTactic::Choose(_))
                        }) {
                            return Err(proof.step_error(
                                "checked `solve` after witness/choose could not close the remaining witness obligations; split conjunctions and discharge each definedness condition explicitly",
                            ).with_proof_refusal(crate::surface::ProofRefusal::UnsuccessfulSearch).with_search_failures(search.finish()));
                        }
                        return Err(proof
                            .solve_failure()
                            .with_check_observations(checks)
                            .with_search_failures(search.finish()));
                    };
                    search.succeed();
                    proof = closed;
                }
                ProofTactic::SolveUsing(solve) => {
                    let mut search = attempt::search_scope("written close using");
                    let (selected, checks) =
                        crate::surface::proof_diagnostics::capture_check_observations(|| {
                            crate::kernel::search::ProofSearch::try_restricted_solve_closure(
                                &(proof),
                                &solve.premises,
                            )
                        });
                    check_verification_deadline()?;
                    let Some(closed) = selected else {
                        if tactics[..index].iter().any(|previous| {
                            matches!(previous, ProofTactic::Witness(_) | ProofTactic::Choose(_))
                        }) {
                            return Err(proof.step_error(
                                "checked `close() using` after witness/choose could not close the remaining witness obligations; split conjunctions and discharge each definedness condition explicitly",
                            ).with_proof_refusal(crate::surface::ProofRefusal::UnsuccessfulSearch).with_search_failures(search.finish()));
                        }
                        // Preserve arithmetic's own refusal alongside theorem
                        // discovery: it says why the listed
                        // premises fall short, as `arithmetic() using`
                        // reported it.
                        let arithmetic = match proof
                            .driver()
                            .apply_step(ProofStep::ArithmeticUsing(solve.premises.clone()))
                        {
                            Err(error) => {
                                // The reason without its location prefix,
                                // which the report already gives.
                                let summary = error.raw_summary();
                                let reason = summary
                                    .find("` proof step tactic")
                                    .and_then(|at| summary[at..].find(": ").map(|end| at + end + 2))
                                    .map_or(summary, |start| &summary[start..]);
                                // A goal outside arithmetic's fragment has
                                // nothing to add about the premises.
                                if reason.starts_with("arithmetic requires a supported") {
                                    String::new()
                                } else {
                                    format!("; {reason}")
                                }
                            }
                            Ok(_) => String::new(),
                        };
                        check_verification_deadline()?;
                        return Err(proof.step_error(format!("`close() using` could not prove the current goal from only its listed premises{arithmetic}")).with_check_observations(checks).with_proof_refusal(crate::surface::ProofRefusal::UnsuccessfulSearch).with_search_failures(search.finish()));
                    };
                    search.succeed();
                    proof = closed;
                }
                ProofTactic::Have(have) => {
                    let scope = proof.driver().open_have(have.proposition.clone())?;
                    let source_proof = have.checking_proof();
                    let _origin = source_proof.uses_implicit_tail().then(|| {
                        crate::surface::proof_trace::TraceOrigin::enter_implicit("implicit solve")
                    });
                    let selected = match source_proof.as_ref() {
                        SourceProof::Tactic(SmartTactic::ImplicitTail) => {
                            let Some(selected) = scope.driver().try_solve_closure()? else {
                                // The omitted body runs `solve`: its
                                // miss is refused there, with the `have`'s
                                // goal, not declined to the enclosing claim.
                                let body = scope.body();
                                let solve = body.at_site(&body.site().at_block_position(0));
                                return Err(solve
                                    .step_error(format!(
                                        "`solve` could not prove `{}`",
                                        describe_click_proposition(&have.proposition)
                                    ))
                                    .with_proof_refusal(
                                        crate::surface::ProofRefusal::UnsuccessfulSearch,
                                    ));
                            };
                            Some(selected)
                        }
                        SourceProof::Default | SourceProof::Tactic(SmartTactic::Solve) => {
                            let selected = scope.driver().try_solve_closure()?;
                            if selected.is_none() {
                                *declined = Some(LinearScriptDecline::UnsuccessfulSearch(index));
                                return Ok(None);
                            }
                            selected
                        }
                        SourceProof::Script(body) => {
                            scope.driver().try_authoritative_linear_script_reporting(
                                body,
                                &mut None,
                                &mut None,
                                implicit_tail,
                            )?
                        }
                    };
                    let Some(selected) = selected else {
                        *declined = Some(LinearScriptDecline::Step(index));
                        return Ok(None);
                    };
                    proof = selected.join()?;
                }
                ProofTactic::If(proof_if) => {
                    let then_tactics =
                        script_arm_with_continuation(&proof_if.then_tactics, &tactics[index + 1..]);
                    let else_tactics =
                        script_arm_with_continuation(&proof_if.else_tactics, &tactics[index + 1..]);
                    let then_sites = arm_sites(index, 0, "then", proof_if.then_tactics.len());
                    let else_sites = arm_sites(index, 1, "else", proof_if.else_tactics.len());
                    let (split_proof, split, ids) =
                        proof.split_focused_if(proof_if.condition.clone())?;
                    let marker = split_proof.checkpoint();
                    let Some(then_done) = split_proof
                        .focus_branch(ids[0])?
                        .driver()
                        .run_addressed_linear_script(
                            &then_tactics,
                            &then_sites,
                            &mut None,
                            unfinished.as_deref_mut(),
                            implicit_tail,
                        )?
                    else {
                        *declined = Some(LinearScriptDecline::Step(index));
                        return Ok(None);
                    };
                    let Some(both_done) = then_done
                        .restore_induction_scope_from(&split_proof)
                        .focus_branch(ids[1])?
                        .driver()
                        .run_addressed_linear_script(
                            &else_tactics,
                            &else_sites,
                            &mut None,
                            unfinished.as_deref_mut(),
                            implicit_tail,
                        )?
                    else {
                        *declined = Some(LinearScriptDecline::Step(index));
                        return Ok(None);
                    };
                    proof = both_done
                        .join_focused_if(&marker, split, ids, proof_if.condition.clone())?
                        .at_site(&sites[index]);
                    // Both arms checked the tactics after the `if`; a trace
                    // to one of those follows the first arm.
                    proof
                        .note_trace_join_continuation_arm((index + 1 < tactics.len()).then_some(0));
                    return finish(proof, unfinished);
                }
                ProofTactic::All(all) => {
                    let mut arms = ConjunctArms::new(&proof, &all.arms);
                    let Some((done, _)) = proof.driver().run_conjunct_proofs(
                        &mut arms,
                        &sites[index],
                        unfinished.as_deref_mut(),
                        implicit_tail,
                        true,
                    )?
                    else {
                        *declined = Some(LinearScriptDecline::Step(index));
                        return Ok(None);
                    };
                    if let Some(extra) = arms.used.iter().position(|used| !used) {
                        return Err(proof.step_error(format!(
                            "`all` arm {} has no corresponding conjunct",
                            extra + 1
                        )));
                    }
                    proof = done.at_site(&sites[index]);
                }
                ProofTactic::Both(both) => {
                    // A `both` arm proves one conjunct and continues nothing.
                    let own_arm_sites = |arm: usize, name: &'static str, written: usize| {
                        (0..written)
                            .map(|position| sites[index].in_arm(arm, name, position))
                            .collect::<Vec<_>>()
                    };
                    let left_sites = own_arm_sites(0, "left", both.left_tactics.len());
                    let right_sites = own_arm_sites(1, "right", both.right_tactics.len());
                    let (split_proof, split, ids) = proof.split_focused_both()?;
                    let marker = split_proof.conjunction_checkpoint(ids)?;
                    let Some(left_done) = split_proof
                        .focus_branch(ids[0])?
                        .driver()
                        .run_addressed_linear_script(
                            &both.left_tactics,
                            &left_sites,
                            &mut None,
                            unfinished.as_deref_mut(),
                            implicit_tail,
                        )?
                    else {
                        *declined = Some(LinearScriptDecline::Step(index));
                        return Ok(None);
                    };
                    let Some(both_done) = left_done
                        .restore_induction_scope_from(&split_proof)
                        .focus_branch(ids[1])?
                        .driver()
                        .run_addressed_linear_script(
                            &both.right_tactics,
                            &right_sites,
                            &mut None,
                            unfinished.as_deref_mut(),
                            implicit_tail,
                        )?
                    else {
                        *declined = Some(LinearScriptDecline::Step(index));
                        return Ok(None);
                    };
                    proof = both_done
                        .join_focused_both(&marker, split, ids)?
                        .at_site(&sites[index]);
                }
                ProofTactic::Match(source) if pure_source => {
                    let (prepared, plan) = proof.prepare_pure_match(source)?;
                    let marker = prepared.checkpoint();
                    let bodies = source
                        .arms
                        .iter()
                        .map(|arm| {
                            script_arm_with_continuation(&arm.tactics, &tactics[index + 1..])
                                .into_owned()
                        })
                        .collect::<Vec<_>>();
                    let addressed = source
                        .arms
                        .iter()
                        .enumerate()
                        .map(|(arm, body)| arm_sites(index, arm, "case", body.tactics.len()))
                        .collect::<Vec<_>>();
                    let mut certificates = Vec::new();
                    let mut trace = proof.new_pure_match_trace(source);
                    let Some(done) = prepared.driver().run_pure_match_group(
                        &plan,
                        source,
                        &(0..source.arms.len()).collect::<Vec<_>>(),
                        &bodies,
                        &addressed,
                        &mut certificates,
                        &mut trace,
                        unfinished.as_deref_mut(),
                        implicit_tail,
                    )?
                    else {
                        *declined = Some(LinearScriptDecline::Step(index));
                        return Ok(None);
                    };
                    proof = done
                        .finish_execution_match(&marker, source, certificates, trace)?
                        .at_site(&sites[index]);
                    proof
                        .note_trace_join_continuation_arm((index + 1 < tactics.len()).then_some(0));
                    return finish(proof, unfinished);
                }
                ProofTactic::Cases(proof_cases) => {
                    // Each arm runs its own tactics and then the rest of the
                    // script, at the source sites of its own block.
                    let arm_names = if proof_cases.arms().len() == 2 {
                        ["left", "right"].as_slice()
                    } else {
                        ["case"].as_slice()
                    };
                    let arms = proof_cases
                        .arms()
                        .iter()
                        .enumerate()
                        .map(|(arm_index, arm)| CaseArmScript {
                            assumption: arm.assumption(),
                            tactics: script_arm_with_continuation(
                                arm.tactics(),
                                &tactics[index + 1..],
                            ),
                            sites: arm_sites(
                                index,
                                arm_index,
                                arm_names[arm_index.min(arm_names.len() - 1)],
                                arm.tactics().len(),
                            ),
                        })
                        .collect::<Vec<_>>();
                    let Some(done) = proof.driver().run_case_arms(
                        &arms,
                        unfinished.as_deref_mut(),
                        implicit_tail,
                    )?
                    else {
                        *declined = Some(LinearScriptDecline::Step(index));
                        return Ok(None);
                    };
                    proof = done.at_site(&sites[index]);
                    proof
                        .note_trace_join_continuation_arm((index + 1 < tactics.len()).then_some(0));
                    return finish(proof, unfinished);
                }
                tactic => {
                    if matches!(tactic, ProofTactic::Sorry) {
                        // Admitted only as a complete body (a `have` body
                        // reaching this runner, or a direct engine call with
                        // a single tactic). A bare `sorry` among other
                        // tactics would cover an unbounded suffix, so it is
                        // rejected to keep holes minimal.
                        if tactics.len() != 1 {
                            return Err(proof.step_error(
                                "`sorry` is only allowed as a complete `have` body or a complete contract proof body; it cannot cover a suffix of other tactics",
                            ));
                        }
                        if !crate::surface::verification::sorry_is_allowed() {
                            return Err(proof.step_error(
                                "`sorry` requires `click verify --allow-sorry`; it is a dev-only proof hole and never verifies in the gate",
                            ));
                        }
                        let label = proof
                            .surface_goal()
                            .map(crate::surface::diagnostics::describe_click_proposition)
                            .map(|goal| format!("have {goal}"))
                            .unwrap_or_else(|| "have (goal unavailable)".to_string());
                        crate::surface::verification::record_sorry_admission(label, String::new());
                        proof = proof.admit_focused_goal_for_sorry()?;
                        continue;
                    }
                    let step = SourceContext::PureGoal
                        .leaf_step(tactic)
                        .ok_or_else(|| proof.unsupported_operation_error(tactic_name(tactic)))?;
                    proof = proof.driver().apply_step(step)?;
                }
            }
            // A written step that checks the goal under another spelling of
            // the same order claim (`0 <= e` for the goal `e >= 0`) has
            // proved the goal. Close it with a recorded `known`, which
            // accepts that spelling, so the certificate re-runs on its own;
            // a planned step sequence never reaches this runner and keeps
            // the goal open after such a step.
            if matches!(
                tactic,
                ProofTactic::ApplyFact(_)
                    | ProofTactic::ApplyFactUsing { .. }
                    | ProofTactic::ApplyTheorem(_)
                    | ProofTactic::ApplyTheoremUsing { .. }
                    | ProofTactic::ApplyInduction { .. }
                    | ProofTactic::Instantiate { .. }
            ) && !proof.focused_discharged()
                && checked_fact_spells_the_goal(&proof)
            {
                proof = proof.driver().apply_step(ProofStep::Known)?;
            }
            if let Some(before) = before_application
                && proof.focused_discharged()
            {
                // An application guarantees every conclusion, including the
                // parts that were not needed for the current goal.
                let conclusions = match tactic {
                    ProofTactic::ApplyTheorem(application)
                    | ProofTactic::ApplyTheoremUsing { application, .. } => {
                        before.theorem_application_surface_conclusions(application)
                    }
                    ProofTactic::ApplyFact(fact) | ProofTactic::ApplyFactUsing { fact, .. } => {
                        vec![crate::surface::proof::driver::fact_application_parts(fact).1]
                    }
                    _ => Vec::new(),
                };
                proof = before.retain_completed_goal(&proof, &conclusions)?;
            }
            if let Some(capture) = nested_capture {
                capture.finish(&proof);
            }
        }

        finish(proof, unfinished)
    }
}

impl<'p, 'a> ProofDriver<'p, Proof<'a>> {
    /// Proves `conclusion` from exactly `premises` by Integer arithmetic,
    /// `arithmetic() using`, which expands to the explicit arithmetic
    /// certificate, and keeps it as a fact.
    pub(in crate::surface::proof) fn have_by_integer_arithmetic(
        &self,
        conclusion: SyntaxProposition,
        premises: Vec<SyntaxProposition>,
    ) -> Result<Proof<'a>, ClickError> {
        let driver_proof = self.proof;
        driver_proof
            .driver()
            .apply_step(super::wide_arithmetic::have(
                conclusion,
                vec![ProofStep::ArithmeticUsing(premises)],
            ))
    }

    /// Applies one uint32 lemma and closes the goal with its conclusion.
    pub(in crate::surface::proof) fn close_with_unsigned_lemma(
        &self,
        name: &str,
        arguments: Vec<SyntaxTerm>,
        premise: SyntaxProposition,
    ) -> Option<Proof<'a>> {
        let driver_proof = self.proof;
        let applied = driver_proof
            .driver()
            .apply_step(ProofStep::ApplyPlannedTheorem {
                application: TheoremApplication {
                    name: name.to_string(),
                    arguments,
                },
                premises: vec![premise],
            })
            .ok()?;
        // The lemma's conclusion is the goal, so applying it discharges the
        // goal where it is stated exactly; the focus then leaves it, though
        // sibling goals (other members of a loop bundle) may remain.
        if applied.is_complete() || applied.goal() != driver_proof.goal() {
            return Some(applied);
        }
        crate::kernel::search::ProofSearch::try_direct_logical_closure(&(applied))
            .ok()
            .flatten()
    }
}
