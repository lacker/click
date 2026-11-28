use super::*;
use crate::surface::proof::driver::OutcomeSplitFailure;

#[cfg(test)]
thread_local! {
    /// The deepest region depth the structural driver entered, for the
    /// depth-accounting regression tests.
    static DEEPEST_REGION_DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Why a checked driver declined a proof. A decline is not a refusal of any
/// claim: the caller tries the next driver, and when none checks the proof
/// the terminal diagnostic is chosen by the most specific reason returned.
/// The variants are ordered from least to most specific.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(in crate::surface::proof) enum Decline {
    /// The driver does not check this proof shape.
    Shape,
    /// The arm that continues past a split, a `branch` or a proof `if` whose
    /// other arm returned, ran out of tactics before the function exits, so
    /// the diagnostic says the path was left open.
    ShortOfExit,
    /// The proof nests execution regions past
    /// `MAX_CHECKED_EXECUTION_REGION_DEPTH`, so the diagnostic names that
    /// bound instead of calling the shape unimplemented.
    RegionDepth,
    /// A written call split was reached after execution finished.
    OutcomesAfterExit,
}

/// A driver's result: the checked value, a typed decline, or a terminal
/// error.
pub(in crate::surface::proof) type Driven<T> = Result<Result<T, Decline>, ClickError>;

/// Unwraps a [`Driven`] value inside a driver, returning its decline or error
/// to the caller unchanged.
macro_rules! driven {
    ($expression:expr) => {
        match $expression? {
            Ok(value) => value,
            Err(decline) => return Ok(Err(decline)),
        }
    };
}

/// Declines the current shape.
fn decline<T>() -> Driven<T> {
    Ok(Err(Decline::Shape))
}

/// Declines because a continuing arm stopped short of the function exit.
fn decline_short_of_exit<T>() -> Driven<T> {
    Ok(Err(Decline::ShortOfExit))
}

/// Declines because the proof nests regions past the checked bound.
fn decline_region_depth<T>() -> Driven<T> {
    Ok(Err(Decline::RegionDepth))
}

/// Whether a tactic only relates facts and resources at the frontier where it
/// stands, without running C. These tactics can establish falsehood before
/// an arm closes.
fn bridges_without_executing(tactic: &ProofTactic) -> bool {
    matches!(
        tactic,
        ProofTactic::Have(_)
            | ProofTactic::UnfoldResource(_)
            | ProofTactic::UnfoldWitnesses { .. }
            | ProofTactic::UnfoldProposition(_)
            | ProofTactic::UnfoldFunction(_)
            | ProofTactic::ObserveResource(_)
            | ProofTactic::Instantiate { .. }
            | ProofTactic::ApplyFact(_)
            | ProofTactic::ApplyFactUsing { .. }
            | ProofTactic::ObserveSubject(_)
            | ProofTactic::ApplyTheorem(_)
            | ProofTactic::ApplyTheoremUsing { .. }
            | ProofTactic::UserTactic(_)
    )
}

/// The refusal for an `if ... ensuring` whose arm cannot reach the join.
fn if_ensuring_arm_did_not_end() -> ClickError {
    ClickError::new(
        "an arm of this proof `if` did not end at a program point the other arm can rejoin: with `ensuring`, both arms must stop before function exit, at the same statement",
    ).with_failed_tactic("if").with_proof_refusal(ProofRefusal::Tactic)
}

/// The refusal for a proof `if` whose arms are both live and end apart.
/// What follows the `if` is checked once, so there must be one state to
/// check it from. When nothing is written after it, what follows is the
/// implicit tail that ends the proof, and the refusal says so.
fn proof_if_arms_do_not_rejoin(nothing_written_after: bool) -> ClickError {
    ClickError::new(if nothing_written_after {
        "the arms of this proof `if` do not rejoin: nothing is written after the `if`, but the implicit tail that ends the proof follows it and is checked once, so each arm must reach the function exit or end where the other does, in the same state. End each arm with `step_until(function.exit);`, or say what the arms agree on with `if P ensuring { ... } then { ... } else { ... }`"
    } else {
        "the arms of this proof `if` do not rejoin: with tactics written after the `if`, both arms must end at the same program point in the same state. Say what the arms agree on with `if P ensuring { ... } then { ... } else { ... }`, or move the tactics after the `if` into the arms"
    }).with_failed_tactic("if").with_proof_refusal(ProofRefusal::Tactic)
}

/// The refusal for a `cases` whose arms are live and end apart, worded as
/// [`proof_if_arms_do_not_rejoin`] is.
fn cases_arms_do_not_rejoin(nothing_written_after: bool) -> ClickError {
    ClickError::new(if nothing_written_after {
        "the arms of this `cases` do not rejoin: nothing is written after the `cases`, but the implicit tail that ends the proof follows it and is checked once, so each arm must reach the function exit or end where the others do, in the same state. End each arm with `step_until(function.exit);`"
    } else {
        "the arms of this `cases` do not rejoin: with tactics written after the `cases`, every arm must end at the same program point in the same state. Move the tactics after the `cases` into its arms"
    }).with_failed_tactic("cases").with_proof_refusal(ProofRefusal::Tactic)
}

/// The refusal for a proof `if` after execution whose condition is open on
/// some outcome path while tactics follow it: its arms do not rejoin, so
/// what follows would be checked once per arm.
fn post_execution_if_forks_the_proof() -> ClickError {
    ClickError::new(
        "the arms of this proof `if` after execution do not rejoin: its condition is not decided on every outcome path, so the tactics written after the `if` would be checked once per arm. Move those tactics into the arms",
    ).with_failed_tactic("if").with_proof_refusal(ProofRefusal::Tactic)
}

/// Whether nothing is written after a split: the script ends there, or only
/// the implicit closer follows it, which each forked path runs as its own.
fn ends_after_split(continuation: &InternalProofNode) -> bool {
    match continuation {
        InternalProofNode::Done => true,
        InternalProofNode::Linear {
            tactics,
            continuation,
        } => {
            matches!(tactics.as_slice(), [only] if matches!(only.tactic, ProofTactic::ImplicitSolve))
                && matches!(continuation.as_ref(), InternalProofNode::Done)
        }
        _ => false,
    }
}

/// A fact interface on an unchanged return state is a single proposition
/// proof by cases. Proving it leaves the continuation on the incoming path
/// and gives it only the interface facts, with the arm binders scoped away.
fn return_interface_facts(assertions: &[ProofAssertion]) -> SyntaxProposition {
    assertions
        .iter()
        .filter_map(|assertion| match assertion {
            ProofAssertion::Fact(fact) => Some(fact.clone()),
            ProofAssertion::Resource(_) => None,
        })
        .reduce(|left, right| SyntaxProposition::And(Box::new(left), Box::new(right)))
        .unwrap_or_else(|| crate::surface::bool_truth(crate::surface::bool_literal(true)))
}

fn return_interface_resource_check(assertions: &[ProofAssertion]) -> Option<PostExecutionTactic> {
    let resources: Vec<_> = assertions
        .iter()
        .filter(|assertion| matches!(assertion, ProofAssertion::Resource(_)))
        .cloned()
        .collect();
    (!resources.is_empty()).then(|| PostExecutionTactic::Ensuring(Arc::from(resources)))
}

fn push_deferred_return_interface(
    deferred: &mut Vec<DeferredPostExecutionTactic>,
    index: usize,
    source_index: usize,
    join: PostExecutionTactic,
    assertions: &[ProofAssertion],
    bindings: &DeferredValueBindings,
) {
    deferred.push(DeferredPostExecutionTactic {
        lexical_bindings: None,
        reads_deferred_binding: join.reads_deferred_binding(bindings),
        tactic_index: index,
        source_index,
        tactic: join,
    });
    if let Some(check) = return_interface_resource_check(assertions) {
        deferred.push(DeferredPostExecutionTactic {
            lexical_bindings: None,
            reads_deferred_binding: false,
            tactic_index: index,
            source_index: usize::MAX,
            tactic: check,
        });
    }
}

fn defer_return_interface_join<'a>(
    proof: &Proof<'a>,
    index: usize,
    source_index: usize,
    join: PostExecutionTactic,
    assertions: &[ProofAssertion],
    capture: Option<&mut ExpansionCapture>,
) -> Result<Proof<'a>, ClickError> {
    let proof = proof.defer_post_execution_source_tactic(index, source_index, join, capture)?;
    // Only proposition proofs ran in the arms. Every arm has the same
    // returned resource state, so check its interface once in the successor.
    if let Some(check) = return_interface_resource_check(assertions) {
        return proof.defer_post_execution_source_tactic(index, usize::MAX, check, None);
    }
    Ok(proof)
}

fn return_fact_interface_arm(body: &InternalProofNode) -> Option<Vec<ProofTactic>> {
    let steps = linear_execution_tactics(body)?;
    if steps.iter().any(|step| {
        !matches!(
            step.tactic,
            ProofTactic::Have(_)
                | ProofTactic::ApplyFact(_)
                | ProofTactic::ApplyTheorem(_)
                | ProofTactic::Close
                | ProofTactic::Known
        )
    }) {
        return None;
    }
    let mut body: Vec<_> = steps.iter().map(|step| step.tactic.clone()).collect();
    body.push(ProofTactic::Known);
    Some(body)
}

fn return_if_fact_join(
    condition: &SyntaxProposition,
    ensuring: &[ProofAssertion],
    then_branch: &InternalProofNode,
    else_branch: &InternalProofNode,
) -> Option<PostExecutionTactic> {
    let proposition = return_interface_facts(ensuring);
    let split = ProofTactic::If(ProofIf {
        condition: condition.clone(),
        ensuring: None,
        then_tactics: return_fact_interface_arm(then_branch)?,
        else_tactics: return_fact_interface_arm(else_branch)?,
    });
    Some(PostExecutionTactic::Have(ProofHave {
        proposition,
        proof: SourceProof::Script(vec![split]),
    }))
}

fn return_match_fact_join(
    source: &ProofMatch,
    arms: &[InternalProofNode],
) -> Option<PostExecutionTactic> {
    let proposition = return_interface_facts(source.ensuring.as_deref()?);
    let mut split = source.clone();
    split.ensuring = None;
    for (arm, body) in split.arms.iter_mut().zip(arms) {
        arm.tactics = return_fact_interface_arm(body)?;
    }
    Some(PostExecutionTactic::Have(ProofHave {
        proposition,
        proof: SourceProof::Script(vec![ProofTactic::Match(Arc::new(split))]),
    }))
}

/// Defers a proof `if` or `cases` reached at function exit onto the outcome
/// paths. Where its case is open on some path, the paths fork, one per arm;
/// a fork with tactics written after the split is refused, since they would
/// be checked once per arm.
#[allow(clippy::too_many_arguments)]
fn defer_post_execution_case_split<'a>(
    proof: Proof<'a>,
    index: usize,
    source_index: usize,
    condition: &SyntaxProposition,
    disjunction: bool,
    ensuring: Option<&[ProofAssertion]>,
    then_branch: &InternalProofNode,
    else_branch: &InternalProofNode,
    continuation: &InternalProofNode,
    expansion_capture: Option<&mut ExpansionCapture>,
) -> Driven<Proof<'a>> {
    let mut proof = proof;
    let bindings = &proof
        .execution()
        .expect("the case is deferred on a terminal frontier")
        .presentation
        .deferred_value_bindings;
    let then_tactics = driven!(Ok::<_, ClickError>(deferred_region_with_bindings(
        then_branch,
        bindings
    )));
    let else_tactics = driven!(Ok::<_, ClickError>(deferred_region_with_bindings(
        else_branch,
        bindings
    )));
    let nested = then_tactics
        .iter()
        .chain(else_tactics.iter())
        .any(|tactic| {
            matches!(
                tactic.tactic,
                PostExecutionTactic::If { .. } | PostExecutionTactic::Match { .. }
            )
        });
    let explicit_cursor = !disjunction
        && deferred_post_execution_if_is_explicit_path_cursor(
            condition,
            &then_tactics,
            &else_tactics,
        );
    let tactic = PostExecutionTactic::If {
        condition: condition.clone(),
        disjunction,
        execution_route: None,
        ensuring: DeferredPostExecutionTactic::interface_check(ensuring, index),
        then_tactics,
        else_tactics,
    };
    let deferred = DeferredPostExecutionTactic {
        lexical_bindings: None,
        reads_deferred_binding: tactic.reads_deferred_binding(bindings),
        tactic_index: index,
        source_index,
        tactic,
    };
    let needs_split = !deferred.reads_deferred_binding
        && (nested
            || !explicit_cursor
                && !proof.post_execution_if_is_path_decided(condition, disjunction)?);
    let before = outcome_path_count(&proof);
    let split = needs_split.then(|| proof.driver().split_outcome_paths(&deferred));
    let forks_before_continuation =
        |split: &Proof<'_>| outcome_path_count(split) > before && !ends_after_split(continuation);
    let needs_join = deferred.reads_deferred_binding
        || match &split {
            Some(Ok(split)) => forks_before_continuation(split),
            Some(Err(OutcomeSplitFailure::Partition(_))) => !disjunction,
            _ => false,
        };
    if needs_join
        && let Some(assertions) = ensuring
        && let Some(join) = return_if_fact_join(condition, assertions, then_branch, else_branch)
    {
        return Ok(Ok(defer_return_interface_join(
            &proof,
            index,
            source_index,
            join,
            assertions,
            expansion_capture,
        )?));
    }
    if let Some(split) = split {
        match split {
            Ok(split) if forks_before_continuation(&split) => {
                let error = if disjunction {
                    post_execution_cases_forks_the_proof()
                } else {
                    post_execution_if_forks_the_proof()
                };
                return Err(split
                    .at_source_tactic(source_index)
                    .attach_step_diagnostic(error));
            }
            Ok(split) => proof = split,
            Err(OutcomeSplitFailure::Obligation(error)) => return Err(error),
            Err(OutcomeSplitFailure::Partition(error)) if disjunction => return Err(error),
            Err(OutcomeSplitFailure::Partition(_)) => {
                check_verification_deadline()?;
                return decline();
            }
        }
    }
    Ok(Ok(proof.defer_post_execution_source_tactic(
        index,
        source_index,
        deferred.tactic,
        expansion_capture,
    )?))
}

/// A proof `match` at function exit is decided on each outcome path, as a
/// proof `if` or `cases` there is: each path takes only the arm its own
/// constructor case selects, and only a path with more than one live case
/// forks. It declines to the frontier match when the match is not
/// deferrable or a path's scrutinee has no checked partition.
#[allow(clippy::too_many_arguments)]
fn defer_post_execution_match<'a>(
    proof: Proof<'a>,
    index: usize,
    source_index: usize,
    proof_match: &Arc<ProofMatch>,
    arms: &[InternalProofNode],
    continuation: &InternalProofNode,
    expansion_capture: Option<&mut ExpansionCapture>,
) -> Driven<Proof<'a>> {
    let bindings = &proof
        .execution()
        .expect("the match is deferred on a terminal frontier")
        .presentation
        .deferred_value_bindings;
    let deferred = driven!(Ok::<_, ClickError>(deferred_post_execution_match(
        index,
        source_index,
        proof_match,
        arms,
        bindings,
    )));
    let before = outcome_path_count(&proof);
    let split = match proof.driver().split_outcome_paths(&deferred) {
        Ok(split) if outcome_path_count(&split) <= before || ends_after_split(continuation) => {
            split
        }
        Err(OutcomeSplitFailure::Obligation(error)) => return Err(error),
        other => {
            if let Some(assertions) = proof_match.ensuring.as_deref()
                && let Some(join) = return_match_fact_join(proof_match, arms)
            {
                return Ok(Ok(defer_return_interface_join(
                    &proof,
                    index,
                    source_index,
                    join,
                    assertions,
                    expansion_capture,
                )?));
            }
            match other {
                Ok(_) => return Err(post_execution_match_forks_the_proof()),
                Err(_) => {
                    check_verification_deadline()?;
                    return decline();
                }
            }
        }
    };
    Ok(Ok(split.defer_post_execution_source_tactic(
        index,
        source_index,
        deferred.tactic,
        expansion_capture,
    )?))
}

/// The refusal for a `cases` after execution whose disjuncts are open on
/// some outcome path while tactics follow it.
fn post_execution_cases_forks_the_proof() -> ClickError {
    ClickError::new(
        "the arms of this `cases` after execution do not rejoin: no disjunct is decided on some outcome path, so the tactics written after the `cases` would be checked once per arm. Move those tactics into the arms",
    ).with_failed_tactic("cases").with_proof_refusal(ProofRefusal::Tactic)
}

/// The refusal for a `match` after execution with more than one live arm
/// while tactics follow it.
fn post_execution_match_forks_the_proof() -> ClickError {
    ClickError::new(
        "the arms of this proof `match` after execution do not rejoin: each live arm is a separate outcome path, so the tactics written after the `match` would be checked once per arm. Move those tactics into the arms",
    ).with_failed_tactic("match").with_proof_refusal(ProofRefusal::Tactic)
}

/// The number of checked outcome paths at function exit.
fn outcome_path_count(proof: &Proof<'_>) -> usize {
    proof
        .execution()
        .and_then(|execution| execution.core.frontier.execution())
        .map_or(0, |checked| checked.paths().len())
}

/// `close_invariants()` is smart: it plans the back-edge bundle body. It has
/// no certificate step of its own, so the drivers that support it route it
/// through `apply_close_invariants_body`, which retains the checked body as a
/// `close_invariants() by` step. It stays outside the frontier's leaf admissions
/// so no driver can record a bare closure request as certificate evidence.
fn closes_loop_invariants(tactic: &ProofTactic) -> bool {
    matches!(
        tactic,
        ProofTactic::CloseInvariants | ProofTactic::CloseInvariantsBy(_)
    )
}

fn expanded_execution_arm_supported(steps: &[ProofStep]) -> bool {
    steps.is_empty()
        || (matches!(steps.first(), Some(ProofStep::Step))
            && matches!(steps.last(), Some(ProofStep::Step | ProofStep::If { .. })))
}

fn linear_execution_tactics(node: &InternalProofNode) -> Option<&[IndexedTactic]> {
    match node {
        InternalProofNode::Done => Some(&[]),
        InternalProofNode::Linear {
            tactics,
            continuation,
        } if matches!(continuation.as_ref(), InternalProofNode::Done) => Some(tactics),
        _ => None,
    }
}

pub(in crate::surface::proof) fn internal_proof_first_index(
    node: &InternalProofNode,
) -> Option<usize> {
    match node {
        InternalProofNode::Done => None,
        InternalProofNode::Linear {
            tactics,
            continuation,
        } => match tactics.first() {
            Some(indexed) => Some(indexed.index),
            None => internal_proof_first_index(continuation),
        },
        InternalProofNode::Open { index, .. }
        | InternalProofNode::Match { index, .. }
        | InternalProofNode::If { index, .. }
        | InternalProofNode::Cases { index, .. }
        | InternalProofNode::Branch { index, .. }
        | InternalProofNode::CallOutcomes { index, .. } => Some(*index),
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum CheckedExecutionRegionEnd {
    SharedContinuation,
    FunctionExit,
}

// The source interpreter applies the same bound below. The direct structural
// driver enforces it before recursive descent so nested explicit branches do
// not reserve an unbounded Rust stack either.
//
// Bound active recursive proof regions, excluding linear runs and sibling
// continuations, which the drivers walk iteratively. A completed first `if`
// case also leaves only a retained join record: its remaining else case runs
// in the same cursor. Written nesting therefore is not a recursion bound.
// Other arm, case, call-outcome, and open-body descents still charge a level,
// including a shared continuation run inside a continuing arm. Constructor
// family splits have their own independent bound below.
const MAX_CHECKED_EXECUTION_REGION_DEPTH: usize = 12;

/// The deepest active recursive region the checked drivers accept. Written
/// else nesting may be deeper because terminal cases run iteratively.
pub(in crate::surface::proof) const MAX_CHECKED_PROOF_REGION_RECURSION: usize =
    MAX_CHECKED_EXECUTION_REGION_DEPTH - 1;

/// How deep the binary frontier split that selects one live constructor arm
/// may recurse. The split halves the arm list, so this admits `2^12` arms —
/// far beyond any declared constructor family, and unrelated to how deeply
/// the proof's regions nest.
const MAX_CHECKED_EXECUTION_SPLIT_DEPTH: usize = 12;

fn checked_execution_arm_tactics_end(
    tactics: &[IndexedTactic],
    initial: CheckedExecutionRegionEnd,
) -> Option<CheckedExecutionRegionEnd> {
    let mut at_function_exit = initial == CheckedExecutionRegionEnd::FunctionExit;
    // A `step()` may execute a `return`; a post-execution tactic after one
    // classifies the arm as reaching function exit. The driver checks the
    // actual frontier.
    let mut may_exit = false;
    for indexed in tactics {
        if at_function_exit {
            flat_post_execution_tactic(&indexed.tactic)?;
            continue;
        }
        // A step written with its obligation proofs classifies as the step
        // it proves.
        let tactic = match &indexed.tactic {
            ProofTactic::StepProved { step, .. } => step.as_ref(),
            tactic => tactic,
        };
        if matches!(
            tactic,
            ProofTactic::SmartExecute | ProofTactic::ExecuteUntil(ExecutionPoint::FUNCTION_EXIT)
        ) {
            at_function_exit = true;
            continue;
        }
        // `step_until` to a statement stops before it, or at the exit a
        // `return` on the way reaches, so it classifies like a `step()`.
        if matches!(tactic, ProofTactic::ExecuteUntil(_)) {
            may_exit = true;
            continue;
        }
        // A `loop` summarizes the C loop at the frontier and lands on its exit
        // successor. When the loop is the last statement of the function body
        // that successor is function exit, so a `loop` classifies like a
        // `step()`: it may exit, and the driver checks the actual frontier.
        if matches!(
            tactic,
            ProofTactic::Step
                | ProofTactic::StepContract(_)
                | ProofTactic::StepBind(_)
                | ProofTactic::StepCall(_)
                | ProofTactic::Loop(_)
        ) {
            may_exit = true;
            continue;
        }
        if SourceContext::ExecutionFrontier.leaf_step(tactic).is_none()
            && !closes_loop_invariants(tactic)
            && !matches!(
                tactic,
                ProofTactic::ApplyFact(_)
                    | ProofTactic::ApplyTheorem(_)
                    | ProofTactic::Have(_)
                    | ProofTactic::LetSatisfy(_)
            )
        {
            if may_exit && flat_post_execution_tactic(&indexed.tactic).is_some() {
                at_function_exit = true;
                continue;
            }
            return None;
        }
    }
    Some(if at_function_exit {
        CheckedExecutionRegionEnd::FunctionExit
    } else {
        CheckedExecutionRegionEnd::SharedContinuation
    })
}

/// Classifies the supported execution-region grammar used inside a checked
/// branch arm. Linear prefixes and nested execution branches are accepted;
/// sibling branches share a frontier, while a call-outcomes pair may mix a
/// continuing normal arm with a terminal caught arm.
fn checked_execution_region_end(
    node: &InternalProofNode,
) -> Result<CheckedExecutionRegionEnd, Decline> {
    checked_execution_region_end_at(node, 0, CheckedExecutionRegionEnd::SharedContinuation)
}

/// Nested regions (`match` arms, `branch` and proof `if` cases, call
/// outcomes, a `with` body) are one level deeper. A node's continuation is
/// the rest of the region the node sits in, so it keeps `depth` and is walked
/// iteratively: a long run of sibling regions neither charges the nesting
/// bound nor reserves Rust stack.
fn checked_execution_region_end_at(
    node: &InternalProofNode,
    depth: usize,
    initial: CheckedExecutionRegionEnd,
) -> Result<CheckedExecutionRegionEnd, Decline> {
    if depth >= MAX_CHECKED_EXECUTION_REGION_DEPTH {
        return Err(Decline::RegionDepth);
    }
    let mut node = node;
    let mut initial = initial;
    loop {
        match node {
            InternalProofNode::Match {
                arms, continuation, ..
            } => {
                if arms.is_empty() || !matches!(continuation.as_ref(), InternalProofNode::Done) {
                    return Err(Decline::Shape);
                }
                for arm in arms {
                    if checked_execution_region_end_at(arm, depth + 1, initial)?
                        != CheckedExecutionRegionEnd::FunctionExit
                    {
                        return Err(Decline::Shape);
                    }
                }
                return Ok(CheckedExecutionRegionEnd::FunctionExit);
            }
            InternalProofNode::Done => return Ok(initial),
            InternalProofNode::CallOutcomes {
                returned_branch,
                threw_branch,
                continuation,
                ..
            } => {
                if initial == CheckedExecutionRegionEnd::FunctionExit {
                    return Err(Decline::OutcomesAfterExit);
                }
                let returned_end =
                    checked_execution_region_end_at(returned_branch, depth + 1, initial)?;
                let threw_end = checked_execution_region_end_at(threw_branch, depth + 1, initial)?;
                return (returned_end != threw_end
                    && matches!(continuation.as_ref(), InternalProofNode::Done))
                .then_some(CheckedExecutionRegionEnd::FunctionExit)
                .ok_or(Decline::Shape);
            }
            // A linear run continues the region it is in, and so does the
            // control node it ends at; only that node's arms nest.
            InternalProofNode::Linear {
                tactics,
                continuation,
            } => {
                initial =
                    checked_execution_arm_tactics_end(tactics, initial).ok_or(Decline::Shape)?;
                node = continuation;
            }
            InternalProofNode::Branch {
                then_branch,
                else_branch,
                continuation,
                ..
            } => {
                if initial == CheckedExecutionRegionEnd::FunctionExit {
                    return Err(Decline::Shape);
                }
                let then_end = checked_execution_region_end_at(then_branch, depth + 1, initial)?;
                let else_end = checked_execution_region_end_at(else_branch, depth + 1, initial)?;
                if then_end != else_end {
                    return Err(Decline::Shape);
                }
                initial = then_end;
                node = continuation;
            }
            InternalProofNode::Open {
                body, continuation, ..
            } => {
                initial = checked_execution_region_end_at(body, depth + 1, initial)?;
                node = continuation;
            }
            InternalProofNode::If {
                then_branch,
                else_branch,
                continuation,
                ..
            }
            | InternalProofNode::Cases {
                then_branch,
                else_branch,
                continuation,
                ..
            } => {
                let then_end = checked_execution_region_end_at(then_branch, depth + 1, initial)?;
                let else_end = checked_execution_region_end_at(else_branch, depth + 1, initial)?;
                // A proof `if` whose cases both reach the shared continuation
                // rejoins where they end, as a nested `branch` does.
                if matches!(node, InternalProofNode::If { .. })
                    && initial == CheckedExecutionRegionEnd::SharedContinuation
                    && then_end == CheckedExecutionRegionEnd::SharedContinuation
                    && else_end == CheckedExecutionRegionEnd::SharedContinuation
                {
                    node = continuation;
                    continue;
                }
                return (then_end == CheckedExecutionRegionEnd::FunctionExit
                    && else_end == CheckedExecutionRegionEnd::FunctionExit
                    && matches!(continuation.as_ref(), InternalProofNode::Done))
                .then_some(CheckedExecutionRegionEnd::FunctionExit)
                .ok_or(Decline::Shape);
            }
        }
    }
}

fn checked_execution_region_pair(
    then_branch: &InternalProofNode,
    else_branch: &InternalProofNode,
) -> Result<CheckedExecutionRegionEnd, Decline> {
    let then_end = checked_execution_region_end(then_branch)?;
    (checked_execution_region_end(else_branch)? == then_end)
        .then_some(then_end)
        .ok_or(Decline::Shape)
}

/// A `branch` whose arms end differently: one returns, the other reaches
/// the shared continuation. The driver runs the continuation inside the
/// continuing arm and joins both arms terminally.
fn checked_execution_region_pair_is_mixed(
    then_branch: &InternalProofNode,
    else_branch: &InternalProofNode,
) -> bool {
    matches!(
        (
            checked_execution_region_end(then_branch),
            checked_execution_region_end(else_branch),
        ),
        (Ok(then_end), Ok(else_end)) if then_end != else_end
    )
}

fn checked_execution_region_is_empty(node: &InternalProofNode) -> bool {
    match node {
        InternalProofNode::Done => true,
        InternalProofNode::Linear {
            tactics,
            continuation,
        } => tactics.is_empty() && checked_execution_region_is_empty(continuation),
        _ => false,
    }
}

fn checked_execution_region_contains_source(node: &InternalProofNode, source_index: usize) -> bool {
    checked_execution_region_contains_source_at(node, source_index, 0)
}

/// Records that a dropped execution region held the selected source tactic.
/// The work is bounded by the region the driver just skipped: it walks only
/// that arm, and only while a tactic is actually selected for this site.
fn note_dropped_execution_region(
    expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
    region: &InternalProofNode,
) {
    let Some(site) = proof_site else {
        return;
    };
    if let Some(capture) = expansion_capture.as_ref()
        && capture.site == *site
        && let Some(batch) = &capture.batch
    {
        let mut dropped = Vec::new();
        let mut pending = vec![region];
        while let Some(node) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            let mut mark = |start: usize, count: usize| {
                dropped.extend(
                    batch
                        .targets
                        .range(start..start.saturating_add(count))
                        .map(|(index, _)| *index),
                );
            };
            match node {
                InternalProofNode::Done => {}
                InternalProofNode::Linear {
                    tactics,
                    continuation,
                } => {
                    for indexed in tactics {
                        mark(
                            indexed.source_index,
                            source_tactic_count(std::slice::from_ref(&indexed.tactic)),
                        );
                    }
                    pending.push(continuation);
                }
                InternalProofNode::Match {
                    source_index,
                    arms,
                    continuation,
                    ..
                } => {
                    mark(*source_index, 1);
                    pending.extend(arms);
                    pending.push(continuation);
                }
                InternalProofNode::Open {
                    source_index,
                    body,
                    continuation,
                    ..
                } => {
                    mark(*source_index, 1);
                    pending.extend([body.as_ref(), continuation.as_ref()]);
                }
                InternalProofNode::Branch {
                    source_index,
                    then_branch: first,
                    else_branch: second,
                    continuation,
                    ..
                }
                | InternalProofNode::If {
                    source_index,
                    then_branch: first,
                    else_branch: second,
                    continuation,
                    ..
                }
                | InternalProofNode::Cases {
                    source_index,
                    then_branch: first,
                    else_branch: second,
                    continuation,
                    ..
                }
                | InternalProofNode::CallOutcomes {
                    source_index,
                    returned_branch: first,
                    threw_branch: second,
                    continuation,
                    ..
                } => {
                    mark(*source_index, 1);
                    pending.extend([first.as_ref(), second.as_ref(), continuation.as_ref()]);
                }
            }
        }
        if let Some(capture) = expansion_capture {
            for index in dropped {
                note_dropped_path_tactic_occurrence(capture.target_mut(index));
            }
        }
        return;
    }
    let Some(wanted) = selected_tactic_index_for_site(expansion_capture.as_deref(), site) else {
        return;
    };
    if checked_execution_region_contains_source(region, wanted) {
        note_dropped_path_tactic_occurrence(expansion_capture);
    }
}

/// Walks nested regions one level deeper and continuations at the same
/// level, iteratively, exactly as `checked_execution_region_end_at` does.
fn checked_execution_region_contains_source_at(
    node: &InternalProofNode,
    source_index: usize,
    depth: usize,
) -> bool {
    if depth >= MAX_CHECKED_EXECUTION_REGION_DEPTH {
        return false;
    }
    let nested = |region: &InternalProofNode| {
        checked_execution_region_contains_source_at(region, source_index, depth + 1)
    };
    let mut node = node;
    loop {
        node = match node {
            InternalProofNode::Done => return false,
            InternalProofNode::Match {
                source_index: own,
                arms,
                continuation,
                ..
            } => {
                if *own == source_index || arms.iter().any(&nested) {
                    return true;
                }
                continuation
            }
            InternalProofNode::Linear {
                tactics,
                continuation,
            } => {
                if tactics
                    .iter()
                    .any(|indexed| indexed_tactic_contains_source_index(indexed, source_index))
                {
                    return true;
                }
                continuation
            }
            InternalProofNode::Branch {
                source_index: own,
                then_branch: first,
                else_branch: second,
                continuation,
                ..
            }
            | InternalProofNode::CallOutcomes {
                source_index: own,
                returned_branch: first,
                threw_branch: second,
                continuation,
                ..
            }
            | InternalProofNode::If {
                source_index: own,
                then_branch: first,
                else_branch: second,
                continuation,
                ..
            }
            | InternalProofNode::Cases {
                source_index: own,
                then_branch: first,
                else_branch: second,
                continuation,
                ..
            } => {
                if *own == source_index || nested(first) || nested(second) {
                    return true;
                }
                continuation
            }
            InternalProofNode::Open {
                source_index: own,
                body,
                continuation,
                ..
            } => {
                if *own == source_index || nested(body) {
                    return true;
                }
                continuation
            }
        };
    }
}

/// Checks a written `step` with proofs of its open obligations: each body is
/// read by the source `have` driver, so it may use smart tactics, and the
/// step's certificate keeps what they expanded to.
pub(in crate::surface::proof) fn apply_source_step_proofs<'a>(
    proof: &Proof<'a>,
    step: &ProofTactic,
    step_proof: &StepProof,
    tactic_index: usize,
) -> Result<Proof<'a>, ClickError> {
    let Some(step) = SourceContext::ExecutionFrontier.leaf_step(step) else {
        return Err(proof.step_error("obligation proofs follow a `step` form"));
    };
    let solve = |proof: &Proof<'a>, have: &ProofHave| -> Result<Proof<'a>, ClickError> {
        let nested = proof.driver().open_source_have(have)?;
        let goal = nested.goal().cloned();
        let mut failed_check = None;
        let selected = solve_nested_have(nested, have, &mut failed_check)
            .map_err(|error| {
                source_have_error(proof, have, tactic_index, goal.as_ref(), Some(error), false)
            })?
            .ok_or_else(|| {
                source_have_error(
                    proof,
                    have,
                    tactic_index,
                    goal.as_ref(),
                    failed_check.take(),
                    true,
                )
            })?;
        selected.join()
    };
    match step_proof {
        StepProof::By(body) => proof.driver().apply_step_with_obligation_proofs(
            step,
            None,
            &mut |proof, proposition, _| {
                solve(
                    proof,
                    &ProofHave {
                        proposition,
                        proof: SourceProof::Script(body.clone()),
                    },
                )
            },
        ),
        StepProof::Requires(entries) => {
            let written = entries
                .iter()
                .map(|entry| (entry.label.clone(), entry.have.proposition.clone()))
                .collect::<Vec<_>>();
            proof.driver().apply_step_with_obligation_proofs(
                step,
                Some(&written),
                &mut |proof, _, index| {
                    solve(proof, &entries[index.expect("a `requires` entry")].have)
                },
            )
        }
    }
}

/// The written fact proved at an execution frontier.
fn frontier_have(tactic: &ProofTactic) -> Option<&ProofHave> {
    match tactic {
        ProofTactic::Have(have) => Some(have),
        _ => None,
    }
}

/// A written `apply`, in any context that admits it. It is a commitment,
/// not a speculative search: its refusal is the premise it was missing,
/// named with the `apply` as written, not a declined shape.
pub(in crate::surface::proof) fn apply_written_theorem<'a>(
    proof: &Proof<'a>,
    application: &TheoremApplication,
) -> Result<Proof<'a>, ClickError> {
    proof
        .driver()
        .apply_theorem_application(application)
        .map_err(|error| {
            if crate::instrumentation::deadline_exceeded() {
                return error;
            }
            let written = crate::surface::printing::format_partial_tactic_sequence(
                std::slice::from_ref(&ProofTactic::ApplyTheorem(application.clone())),
            );
            error.with_context(format!(
                "`{}` was refused",
                written.trim().trim_end_matches(';')
            ))
        })
}

fn flat_post_execution_tactic(tactic: &ProofTactic) -> Option<PostExecutionTactic> {
    if SourceContext::PostExecution.leaf_step(tactic).is_some() {
        return Some(PostExecutionTactic::Leaf(tactic.clone()));
    }
    match tactic {
        ProofTactic::StepProved { step, .. }
            if matches!(
                step.as_ref(),
                ProofTactic::FoldResource(_) | ProofTactic::UserTactic(_)
            ) =>
        {
            Some(PostExecutionTactic::ResourceStepProved(tactic.clone()))
        }
        ProofTactic::ApplyFact(fact) => Some(PostExecutionTactic::Have(ProofHave {
            proposition: crate::surface::proof::driver::fact_application_parts(fact).1,
            proof: SourceProof::Script(vec![ProofTactic::ApplyFact(fact.clone())]),
        })),
        ProofTactic::ApplyTheorem(application) => {
            Some(PostExecutionTactic::Apply(application.clone()))
        }
        ProofTactic::Have(have) => Some(PostExecutionTactic::Have(have.clone())),
        ProofTactic::IntroBlock { .. } | ProofTactic::Close => {
            Some(PostExecutionTactic::Leaf(tactic.clone()))
        }
        ProofTactic::Both(_) | ProofTactic::All(_) => {
            Some(PostExecutionTactic::Both(tactic.clone()))
        }
        ProofTactic::Solve => Some(PostExecutionTactic::Solve),
        ProofTactic::ImplicitSolve => Some(PostExecutionTactic::ImplicitSolve),
        ProofTactic::SolveUsing(solve) => Some(PostExecutionTactic::SolveUsing(solve.clone())),
        _ => None,
    }
}

fn deferred_post_execution_region(node: &InternalProofNode) -> Result<DeferredArm, Decline> {
    deferred_region_with_bindings(node, &DeferredValueBindings::default())
}

/// Converts a supported post-execution syntax region into cursor metadata.
/// This performs no proof transition and stores no semantic state; each leaf
/// operation is checked later against the focused outcome `Proof`. A region's
/// sequential nodes are walked in a loop; only written nesting recurses.
fn deferred_region_with_bindings(
    node: &InternalProofNode,
    bindings: &DeferredValueBindings,
) -> Result<DeferredArm, Decline> {
    let mut bindings = bindings.clone();
    let mut deferred = Vec::new();
    let mut node = node;
    loop {
        node = match node {
            InternalProofNode::Done => return Ok(Arc::new(deferred)),
            InternalProofNode::Linear {
                tactics,
                continuation,
            } => {
                for indexed in tactics {
                    let tactic =
                        flat_post_execution_tactic(&indexed.tactic).ok_or(Decline::Shape)?;
                    deferred.push(DeferredPostExecutionTactic {
                        lexical_bindings: None,
                        reads_deferred_binding: tactic.reads_deferred_binding(&bindings),
                        tactic_index: indexed.index,
                        source_index: indexed.source_index,
                        tactic,
                    });
                    bindings.record(&indexed.tactic);
                }
                continuation
            }
            InternalProofNode::If {
                index,
                source_index,
                condition,
                ensuring,
                then_branch,
                else_branch,
                continuation,
                ..
            } => {
                if let Some(assertions) = ensuring.as_deref()
                    && let Some(join) =
                        return_if_fact_join(condition, assertions, then_branch, else_branch)
                {
                    push_deferred_return_interface(
                        &mut deferred,
                        *index,
                        *source_index,
                        join,
                        assertions,
                        &bindings,
                    );
                    node = continuation;
                    continue;
                }
                let tactic = PostExecutionTactic::If {
                    condition: condition.clone(),
                    disjunction: false,
                    execution_route: None,
                    ensuring: DeferredPostExecutionTactic::interface_check(
                        ensuring.as_deref(),
                        *index,
                    ),
                    then_tactics: deferred_region_with_bindings(then_branch, &bindings)?,
                    else_tactics: deferred_region_with_bindings(else_branch, &bindings)?,
                };
                deferred.push(DeferredPostExecutionTactic {
                    lexical_bindings: None,
                    reads_deferred_binding: tactic.reads_deferred_binding(&bindings),
                    tactic_index: *index,
                    source_index: *source_index,
                    tactic,
                });
                continuation
            }
            InternalProofNode::CallOutcomes { .. } => return Err(Decline::OutcomesAfterExit),
            InternalProofNode::Cases {
                index,
                source_index,
                disjunction,
                then_branch,
                else_branch,
                continuation,
            } => {
                deferred.push(DeferredPostExecutionTactic {
                    lexical_bindings: None,
                    reads_deferred_binding: false,
                    tactic_index: *index,
                    source_index: *source_index,
                    tactic: PostExecutionTactic::If {
                        condition: disjunction.clone(),
                        disjunction: true,
                        execution_route: None,
                        ensuring: None,
                        then_tactics: deferred_region_with_bindings(then_branch, &bindings)?,
                        else_tactics: deferred_region_with_bindings(else_branch, &bindings)?,
                    },
                });
                continuation
            }
            InternalProofNode::Match {
                index,
                source_index,
                proof_match,
                arms,
                continuation,
            } => {
                if let Some(assertions) = proof_match.ensuring.as_deref()
                    && let Some(join) = return_match_fact_join(proof_match, arms)
                {
                    push_deferred_return_interface(
                        &mut deferred,
                        *index,
                        *source_index,
                        join,
                        assertions,
                        &bindings,
                    );
                    node = continuation;
                    continue;
                }
                deferred.push(deferred_post_execution_match(
                    *index,
                    *source_index,
                    proof_match,
                    arms,
                    &bindings,
                )?);
                continuation
            }
            InternalProofNode::Open {
                index,
                source_index,
                resource,
                body,
                continuation,
            } => {
                deferred.push(deferred_post_execution_open(
                    *index,
                    *source_index,
                    resource,
                    body,
                    &bindings,
                )?);
                continuation
            }
            InternalProofNode::Branch { .. } => return Err(Decline::Shape),
        };
    }
}

fn deferred_post_execution_open(
    index: usize,
    source_index: usize,
    resource: &ResourceClause,
    body: &InternalProofNode,
    bindings: &DeferredValueBindings,
) -> Result<DeferredPostExecutionTactic, Decline> {
    let close = DeferredPostExecutionTactic {
        lexical_bindings: None,
        reads_deferred_binding: false,
        tactic_index: index,
        source_index,
        tactic: PostExecutionTactic::CloseOpen {
            resource: resource.clone(),
            restoration: None,
            retain_deferred_body: false,
        },
    };
    Ok(DeferredPostExecutionTactic {
        lexical_bindings: None,
        reads_deferred_binding: false,
        tactic_index: index,
        source_index,
        tactic: PostExecutionTactic::Open {
            resource: Arc::new(resource.clone()),
            body: deferred_region_with_bindings(body, bindings)?,
            close: Arc::new(close),
        },
    })
}

fn post_execution_open(
    proof: &Proof<'_>,
    index: usize,
    source_index: usize,
    resource: &ResourceClause,
    body: &InternalProofNode,
) -> Result<PostExecutionTactic, ClickError> {
    let execution = proof
        .execution()
        .expect("a terminal frontier retains execution");
    deferred_post_execution_open(
        index,
        source_index,
        resource,
        body,
        &execution.presentation.deferred_value_bindings,
    )
    .map(|open| open.tactic)
    .map_err(|_| {
        proof
            .at_source_tactic(source_index)
            .step_error("unsupported proof structure inside a `with` block after function exit")
    })
}

/// A proof `match` after execution, deferred so that each outcome path
/// takes the arm its constructor case selects. A match with `ensuring`
/// rejoins at the frontier and stays with the frontier driver.
fn deferred_post_execution_match(
    tactic_index: usize,
    source_index: usize,
    proof_match: &Arc<ProofMatch>,
    arms: &[InternalProofNode],
    bindings: &DeferredValueBindings,
) -> Result<DeferredPostExecutionTactic, Decline> {
    if proof_match.ensuring.is_some() {
        return Err(Decline::Shape);
    }
    Ok(DeferredPostExecutionTactic {
        lexical_bindings: None,
        reads_deferred_binding: false,
        tactic_index,
        source_index,
        tactic: PostExecutionTactic::Match {
            source: Arc::clone(proof_match),
            arms: arms
                .iter()
                .map(|arm| deferred_region_with_bindings(arm, bindings))
                .collect::<Result<_, _>>()?,
        },
    })
}

fn deferred_post_execution_if_is_explicit_path_cursor(
    condition: &SyntaxProposition,
    then_tactics: &[DeferredPostExecutionTactic],
    else_tactics: &[DeferredPostExecutionTactic],
) -> bool {
    fn explicit_tree(tactics: &[DeferredPostExecutionTactic], depth: usize) -> bool {
        depth < MAX_CHECKED_EXECUTION_REGION_DEPTH
            && tactics.iter().all(|deferred| match &deferred.tactic {
                PostExecutionTactic::Solve
                | PostExecutionTactic::ImplicitSolve
                | PostExecutionTactic::Match { .. } => false,
                PostExecutionTactic::Open { body, .. } => explicit_tree(body, depth + 1),
                PostExecutionTactic::If {
                    condition,
                    then_tactics,
                    else_tactics,
                    ..
                } => {
                    proof_case_is_stable_program_point_condition(condition)
                        && explicit_tree(then_tactics, depth + 1)
                        && explicit_tree(else_tactics, depth + 1)
                }
                _ => true,
            })
    }
    proof_case_is_stable_program_point_condition(condition)
        && explicit_tree(then_tactics, 0)
        && explicit_tree(else_tactics, 0)
}

fn checked_structural_execution_branch_supported(
    then_branch: &InternalProofNode,
    else_branch: &InternalProofNode,
) -> Result<(), Decline> {
    match checked_execution_region_pair(then_branch, else_branch) {
        Ok(_) => Ok(()),
        Err(_) if checked_execution_region_pair_is_mixed(then_branch, else_branch) => Ok(()),
        Err(decline) => Err(decline),
    }
}

/// Applies one written tactic at an execution frontier that has not reached
/// the function exit. The linear continuation, a focused execution arm and a
/// loop's `maintain` body all run their frontier tactics through this one
/// function, so a tactic means the same thing in each; the contexts differ
/// only in which tactics they admit (`SourceContext::ExecutionFrontier`) and in what they do
/// at the function exit. `Ok(None)` declines the proof shape.
fn apply_frontier_source_tactic<'a>(
    proof: Proof<'a>,
    indexed: &IndexedTactic,
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
    owning_source_index: usize,
    timing_claim_label: Option<&str>,
) -> Driven<Proof<'a>> {
    // Each tactic is its own source operation: time it under its source site
    // so the profiler charges its work to the tactic rather than to shared
    // verifier work.
    let statement_index = proof.execution_frontier_index().unwrap_or_default();
    let _timing = timing_claim_label.and_then(|claim_label| {
        TacticTiming::new(
            claim_label,
            indexed.index,
            indexed.source_index,
            &indexed.tactic,
            statement_index,
        )
    });
    let _origin = crate::surface::proof::timing::trace_origin(&indexed.tactic);
    let checkpoint = proof.checkpoint();
    let next = if matches!(indexed.tactic, ProofTactic::CloseInvariants) {
        proof
            .driver()
            .apply_close_invariants_body(&[ProofTactic::Solve], None, true)?
    } else if let Some(step) = SourceContext::ExecutionFrontier.leaf_step(&indexed.tactic) {
        proof.driver().apply_step_at(step, indexed.source_index)?
    } else if let ProofTactic::StepProved {
        step,
        proof: step_proof,
    } = &indexed.tactic
    {
        apply_source_step_proofs(&proof, step, step_proof, indexed.index)?
    } else if let ProofTactic::CloseInvariantsBy(body) = &indexed.tactic {
        proof
            .driver()
            .apply_close_invariants_body(body, None, true)?
    } else if let ProofTactic::Choose(choice) = &indexed.tactic {
        proof
            .driver()
            .apply_step_at(ProofStep::Choose(choice.clone()), indexed.source_index)?
    } else if let ProofTactic::LetSatisfy(binding) = &indexed.tactic {
        proof
            .driver()
            .apply_step_at(ProofStep::LetSatisfy(binding.clone()), indexed.source_index)?
    } else if let ProofTactic::ApplyFact(fact) = &indexed.tactic {
        proof.driver().apply_fact_application(fact)?
    } else if let ProofTactic::ApplyTheorem(application) = &indexed.tactic {
        apply_written_theorem(&proof, application)?
    } else if let Some(have) = frontier_have(&indexed.tactic) {
        let nested = proof.driver().open_source_have(have)?;
        let goal = nested.goal().cloned();
        let mut failed_check = None;
        let selected = solve_nested_have(nested, have, &mut failed_check)
            .map_err(|error| {
                source_have_error(
                    &proof,
                    have,
                    indexed.index,
                    goal.as_ref(),
                    Some(error),
                    false,
                )
            })?
            .ok_or_else(|| {
                source_have_error(
                    &proof,
                    have,
                    indexed.index,
                    goal.as_ref(),
                    failed_check.take(),
                    true,
                )
            })?;
        selected.join()?
    } else if let ProofTactic::ExecuteUntil(point) = &indexed.tactic {
        match crate::kernel::search::ProofSearch::try_execute_until(&(proof), point)? {
            Some(executed) => executed,
            None => {
                // An arm of `branch` that does not return ends at the C
                // `if`'s shared continuation; the code after the `if` runs
                // after the arms join, so no target past it is in reach.
                let message = if proof.execution().is_some_and(|execution| {
                    execution.core.frontier.region == ExecutionRegionKind::BranchArm
                }) {
                    "`step_until` cannot step past the end of this `branch` arm: an arm that does not return stops at the C `if`'s shared continuation; write the steps after the `branch`, or split with a proof `if` before the C when each path needs its own work"
                } else {
                    "`step_until` found no checked step from this frontier"
                };
                return Err(proof.step_error(message));
            }
        }
    } else if matches!(indexed.tactic, ProofTactic::SmartExecute) {
        match crate::kernel::search::ProofSearch::try_execute_to_exit(&(proof))? {
            Some(executed) => executed,
            None => {
                // Terminal arms can succeed above. A continuing arm cannot
                // consume its parent's continuation to reach function exit.
                let message = if !proof.is_at_function_exit()
                    && proof.execution().is_some_and(|execution| {
                        execution.core.frontier.region == ExecutionRegionKind::BranchArm
                    }) {
                    "the implicit tail cannot reach function exit from a continuing branch arm; an arm of `branch` must stop at the shared continuation"
                } else {
                    "the implicit tail found no checked path from this frontier to function exit"
                };
                return Err(proof.step_error(message));
            }
        }
    } else if let ProofTactic::Loop(clause) = &indexed.tactic {
        // A frontier-local loop is one checked operation; its expansion
        // capture and surface record are handled inside the operation.
        proof.apply_frontier_local_loop(
            expansion_capture.as_deref_mut(),
            clause,
            indexed.index,
            indexed.source_index,
        )?
    } else {
        return decline();
    };
    // Observe the source tactic's limit before its timing scope ends, so a
    // completed checked operation cannot hand control to a later tactic after
    // exhausting its own budget. The stopped tactic has no accepted successor;
    // retain its checked predecessor just as an operation refusal does.
    check_verification_deadline().map_err(|error| proof.attach_step_diagnostic(error))?;
    // Generated certificates retain the source index of the smart operation
    // that produced them. Their nested steps are part of that operation's
    // already-recorded branch certificate, not independent expansions of the
    // same source occurrence.
    if indexed.source_index != owning_source_index
        && !matches!(indexed.tactic, ProofTactic::Loop(_))
        && let Some(site) = proof_site
        && capture_selects_source(expansion_capture.as_deref(), site, indexed.source_index)
    {
        let certificate = next.certificate_since(&checkpoint)?;
        record_proof_site_tactic_expansion(
            expansion_capture,
            site,
            indexed.source_index,
            &certificate.to_proof_tactics(),
        );
    }
    Ok(Ok(next))
}

/// With the implicit closer off, as an expanded proof is checked cold, the
/// implicit tail runs no C: a script that stops with C left is refused.
fn refuse_implicit_tail_when_disabled(proof: &Proof<'_>) -> Result<(), ClickError> {
    if crate::surface::proof::proof_object::implicit_solve_disabled() {
        return Err(proof.step_error(
            "the script stops with C left to run, and the implicit tail is off: write the remaining steps",
        ));
    }
    Ok(())
}

/// Advances the checked linear prefix following a structural branch. Every
/// accepted explicit or smart operation returns the next Proof directly; the
/// first unsupported tactic and its suffix remain untouched for the
/// compatibility driver. A smart miss rejects the whole candidate path, so
/// the caller can fall back from its unchanged root context.
fn advance_checked_linear_continuation<'a>(
    mut proof: Proof<'a>,
    continuation: &InternalProofNode,
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
    owning_source_index: usize,
    timing_claim_label: Option<&str>,
) -> Driven<(Proof<'a>, Vec<IndexedTactic>)> {
    let Some(tactics) = linear_execution_tactics(continuation) else {
        return decline();
    };
    for (offset, indexed) in tactics.iter().enumerate() {
        // A written `close();` at a live frontier first executes the C that
        // remains, as the implicit tail does, then closes the open goals at
        // function exit like the `solve` an omitted proof stands for.
        if matches!(indexed.tactic, ProofTactic::ImplicitSolve) && !proof.is_at_function_exit() {
            check_verification_deadline()?;
            proof = proof.start_source_tactic(indexed.source_index)?;
            refuse_implicit_tail_when_disabled(&proof)?;
            let execute = IndexedTactic {
                index: indexed.index,
                source_index: indexed.source_index,
                tactic: ProofTactic::SmartExecute,
            };
            proof = driven!(apply_frontier_source_tactic(
                proof,
                &execute,
                expansion_capture.as_deref_mut(),
                proof_site,
                owning_source_index,
                timing_claim_label,
            ));
            return Ok(Ok((proof, tactics[offset..].to_vec())));
        }
        if !SourceContext::ExecutionFrontier.admits(&indexed.tactic) {
            return Ok(Ok((proof, tactics[offset..].to_vec())));
        }
        check_verification_deadline()?;
        // Every source driver starts a tactic with an empty step delta.
        proof = proof.start_source_tactic(indexed.source_index)?;
        // Once the common execution has returned, proposition and resource
        // operations are interpreted once per concrete outcome. In
        // particular, `result` has no single value on this joined Proof.
        if proof.is_at_function_exit() {
            return Ok(Ok((proof, tactics[offset..].to_vec())));
        }
        let next = driven!(apply_frontier_source_tactic(
            proof,
            indexed,
            expansion_capture.as_deref_mut(),
            proof_site,
            owning_source_index,
            timing_claim_label,
        ));
        proof = next;
        // A checked function frame closes the execution-frontier portion of
        // this continuation. Later tactics are ordered outcome operations:
        // in particular, a `have` may name the path-local `result`, which has
        // no single lowering on the joined execution Proof. Return that suffix
        // to the post-execution driver instead of treating it as another
        // execution-frontier transition.
    }
    Ok(Ok((proof, Vec::new())))
}

/// Checks one flat function proof on a single persistent `Proof` lineage.
/// The source shape excludes structural proof branches, resource scopes, and
/// loop regions. Execution operations advance the frontier immediately;
/// result-aware suffix operations are retained only as source-order metadata
/// and are applied to the typed outcome goals during finalization. The exact
/// empty-frame transport segment owns its continuation transactionally, so
/// its smart statement steps may use the indexed selector without exporting a
/// partial descendant; other direct and compatibility callers retain the
/// narrower standalone-step policy.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface::proof) fn try_check_flat_function_proof<'a>(
    execution: &ExecutionProofState,
    pure_facts: &PureFactList,
    constants: &ExecutionProofConstants,
    program: &InternalProofNode,
    generated_by_source_index: Option<usize>,
    expansion_capture: Option<&mut ExpansionCapture>,
    function_block: &'a FunctionBlock,
    parsed_function: &'a crate::languages::interface::ImportedFunction,
    claim_label: &'a str,
    function_environment: &'a ExecutionEnvironment,
    spec_definitions: SpecDefinitions<'a>,
    resource_environment: &'a ResourceEnvironment,
    theorem_environment: &'a TheoremEnvironment,
    function: &'a ProgramFunction,
    arguments: &'a [ProgramExpression],
) -> Driven<Proof<'a>> {
    // A retained proof or a terminal error publishes what the driver
    // captured; only a decline (`Ok(None)`) leaves the cursor untouched.
    let mut staged = expansion_capture.as_deref().cloned();
    let result = try_check_flat_function_proof_inner(
        execution,
        pure_facts,
        constants,
        program,
        generated_by_source_index,
        &mut staged,
        function_block,
        parsed_function,
        claim_label,
        function_environment,
        spec_definitions,
        resource_environment,
        theorem_environment,
        function,
        arguments,
    );
    if !matches!(result, Ok(Err(_)))
        && let (Some(expansion_capture), Some(staged)) = (expansion_capture, staged)
    {
        *expansion_capture = staged;
    }
    result
}

#[allow(clippy::too_many_arguments)]
fn try_check_flat_function_proof_inner<'a>(
    execution: &ExecutionProofState,
    pure_facts: &PureFactList,
    constants: &ExecutionProofConstants,
    program: &InternalProofNode,
    generated_by_source_index: Option<usize>,
    staged_expansion_capture: &mut Option<ExpansionCapture>,
    function_block: &'a FunctionBlock,
    parsed_function: &'a crate::languages::interface::ImportedFunction,
    claim_label: &'a str,
    function_environment: &'a ExecutionEnvironment,
    spec_definitions: SpecDefinitions<'a>,
    resource_environment: &'a ResourceEnvironment,
    theorem_environment: &'a TheoremEnvironment,
    function: &'a ProgramFunction,
    arguments: &'a [ProgramExpression],
) -> Driven<Proof<'a>> {
    let Some(tactics) = linear_execution_tactics(program) else {
        return decline();
    };
    if tactics.is_empty() {
        return decline();
    }
    let root = Proof::for_execution_frontier(
        claim_label,
        tactics[0].index,
        execution.clone(),
        pure_facts.clone(),
        constants.clone(),
        function_block,
        function,
        parsed_function,
        arguments,
        function_environment,
        resource_environment,
        spec_definitions,
        theorem_environment,
    );
    let (mut proof, remaining) = driven!(advance_checked_linear_continuation(
        root,
        program,
        staged_expansion_capture.as_mut(),
        constants.proof_site.as_ref(),
        generated_by_source_index.unwrap_or(usize::MAX),
        Some(claim_label),
    ));
    check_verification_deadline()?;
    if !proof.is_at_function_exit() {
        if remaining.is_empty()
            && let Some(error) = proof.unfinished_callback_script_error()
        {
            return Err(error);
        }
        if let Some((indexed, reason)) = remaining.first().and_then(|indexed| {
            pre_exit_outcome_tactic_error(&proof, &indexed.tactic).map(|reason| (indexed, reason))
        }) {
            return Err(proof
                .at_source_tactic(indexed.source_index)
                .step_error(reason)
                .with_failed_tactic(tactic_name(&indexed.tactic)));
        }
        return decline();
    }
    for indexed in remaining {
        check_verification_deadline()?;
        let next = driven!(defer_post_exit_outcome_tactic(
            proof,
            &indexed,
            staged_expansion_capture.as_mut()
        ));
        proof = next;
    }
    Ok(Ok(proof))
}

/// Checks one function proof containing supported top-level resource scopes
/// and execution branches without exporting any checked structure back into
/// parallel semantic state. Linear prefixes, structural bodies and joins,
/// intervening continuations, the frame, and the outcome suffix remain one
/// persistent Proof lineage; a miss publishes neither semantic state nor
/// expansion metadata.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface::proof) fn try_check_structural_function_proof<'a>(
    execution: &ExecutionProofState,
    pure_facts: &PureFactList,
    constants: &ExecutionProofConstants,
    program: &InternalProofNode,
    generated_by_source_index: Option<usize>,
    expansion_capture: Option<&mut ExpansionCapture>,
    function_block: &'a FunctionBlock,
    parsed_function: &'a crate::languages::interface::ImportedFunction,
    claim_label: &'a str,
    function_environment: &'a ExecutionEnvironment,
    spec_definitions: SpecDefinitions<'a>,
    resource_environment: &'a ResourceEnvironment,
    theorem_environment: &'a TheoremEnvironment,
    function: &'a ProgramFunction,
    arguments: &'a [ProgramExpression],
) -> Driven<Proof<'a>> {
    // The linear driver owns these scripts. Running them here would execute
    // their entire prefix only to decline for lack of structural tactics,
    // forcing the caller to check the same execution again in the linear driver.
    if linear_execution_tactics(program).is_some() {
        return decline();
    }
    // A retained proof or a terminal error publishes what the driver
    // captured; only a decline (`Ok(None)`) leaves the cursor untouched.
    let mut staged = expansion_capture.as_deref().cloned();
    let result = try_check_structural_function_proof_inner(
        execution,
        pure_facts,
        constants,
        program,
        generated_by_source_index,
        &mut staged,
        function_block,
        parsed_function,
        claim_label,
        function_environment,
        spec_definitions,
        resource_environment,
        theorem_environment,
        function,
        arguments,
    );
    if !matches!(result, Ok(Err(_)))
        && let (Some(expansion_capture), Some(staged)) = (expansion_capture, staged)
    {
        *expansion_capture = staged;
    }
    result
}

/// A terminal closer after a proof-only prefix can refute its case at the
/// split's program point. Check the arm on its own frontier before running
/// the surviving sibling.
#[allow(clippy::too_many_arguments)]
fn try_advance_refuted_case_split<'a>(
    split: &Proof<'a>,
    record: &ExecutionProofCaseSplit<'a>,
    branches: [&InternalProofNode; 2],
    ensuring: Option<&[ProofAssertion]>,
    enclosing_record: Option<&ExecutionSplit<'a>>,
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
    owning_source_index: usize,
    depth: usize,
    ends_at_join: bool,
) -> Driven<Option<Proof<'a>>> {
    for (index, arm) in branches.iter().enumerate() {
        let Some((bridge, last)) = refuting_arm_prefix(arm) else {
            continue;
        };
        let scoped = split.focus_execution_if_arm(record, index == 0)?;
        let mut staged = expansion_capture.as_deref().cloned();
        let refuted = driven!(advance_refuting_bridge(
            scoped,
            bridge,
            staged.as_mut(),
            proof_site,
            owning_source_index,
        ));
        if !refuted.facts().holds_false() || refuted.is_at_function_exit() {
            continue;
        }
        let closed = close_refuted_arm(&refuted, last.source_index)?;
        let live = closed
            .focus_execution_if_arm(record, index != 0)?
            .retain_case_after_sibling_refutation(record, &refuted)?;
        if let (Some(capture), Some(staged)) = (expansion_capture.as_deref_mut(), staged) {
            *capture = staged;
        }
        let advanced = driven!(advance_focused_execution_region_with_branch_continuation(
            live,
            enclosing_record,
            branches[1 - index],
            expansion_capture,
            proof_site,
            owning_source_index,
            depth + 1,
            None,
            ends_at_join || ensuring.is_some(),
        ));
        return Ok(Ok(Some(advanced.join_after_case_refutation(
            record,
            ensuring.map(<[_]>::to_vec),
        )?)));
    }
    Ok(Ok(None))
}

/// Runs the two arms of a proof-level case split, a proof `if` or `cases`,
/// and joins them. What follows the
/// split is checked once: two live arms must rejoin, through `ensuring` or
/// because they end at one program point in one state, and a lone live arm
/// owns the continuation. Returns the joined proof and whether the
/// continuation was consumed inside an arm.
#[allow(clippy::too_many_arguments)]
fn advance_case_split_arms<'a>(
    split: Proof<'a>,
    record: &ExecutionProofCaseSplit<'a>,
    ensuring: &Option<Vec<ProofAssertion>>,
    then_branch: &InternalProofNode,
    else_branch: &InternalProofNode,
    continuation: &InternalProofNode,
    consumed_leading_steps: bool,
    enclosing_record: Option<&ExecutionSplit<'a>>,
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
    owning_source_index: usize,
    source_index: usize,
    depth: usize,
) -> Driven<(Proof<'a>, bool)> {
    let must_rejoin = ensuring.is_some();
    if !consumed_leading_steps {
        let refuted = driven!(try_advance_refuted_case_split(
            &split,
            record,
            [then_branch, else_branch],
            ensuring.as_deref(),
            enclosing_record,
            expansion_capture.as_deref_mut(),
            proof_site,
            owning_source_index,
            depth,
            !matches!(continuation, InternalProofNode::Done),
        ));
        if let Some(proof) = refuted {
            return Ok(Ok((proof, false)));
        }
    }
    if must_rejoin || !matches!(continuation, InternalProofNode::Done) {
        let mut advanced = split;
        let mut live = [false, false];
        for (take_then, branch) in [(true, then_branch), (false, else_branch)] {
            let focused = advanced.focus_execution_if_arm(record, take_then)?;
            let next = if consumed_leading_steps {
                advance_focused_execution_region_after_leading_tactic(
                    focused,
                    enclosing_record,
                    branch,
                    expansion_capture.as_deref_mut(),
                    proof_site,
                    owning_source_index,
                    depth + 1,
                )?
            } else {
                advance_focused_execution_region(
                    focused,
                    enclosing_record,
                    branch,
                    expansion_capture.as_deref_mut(),
                    proof_site,
                    owning_source_index,
                    depth + 1,
                )?
            };
            let next = match next {
                Ok(next) => next,
                Err(decline) => return Ok(Err(decline)),
            };
            live[usize::from(!take_then)] = !next.is_at_function_exit();
            advanced = next;
        }
        if live == [true, true] {
            let joined = match ensuring {
                Some(assertions) => {
                    advanced.join_focused_execution_if_interface(record, assertions.clone())?
                }
                None => advanced
                    .try_join_focused_execution_if(record)?
                    .ok_or_else(|| {
                        let error = if record.is_cases() {
                            cases_arms_do_not_rejoin(ends_after_split(continuation))
                        } else {
                            proof_if_arms_do_not_rejoin(ends_after_split(continuation))
                        };
                        advanced
                            .at_source_tactic(source_index)
                            .attach_step_diagnostic(error)
                    })?,
            };
            return Ok(Ok((joined, false)));
        }
        if must_rejoin {
            return Err(if_ensuring_arm_did_not_end());
        }
        let mut consumed_continuation = false;
        if live != [false, false] {
            // One arm is live. It is the else arm, still in
            // focus, or the then arm, focused again where it
            // stopped.
            let focused = if live[0] {
                advanced.focus_execution_if_arm(record, true)?
            } else {
                advanced
            };
            let continued = driven!(advance_focused_execution_region(
                focused,
                enclosing_record,
                continuation,
                expansion_capture.as_deref_mut(),
                proof_site,
                owning_source_index,
                depth + 1,
            ));
            if !continued.is_at_function_exit() {
                return decline_short_of_exit();
            }
            advanced = continued;
            consumed_continuation = true;
        }
        return Ok(Ok((
            advanced.join_focused_execution_if_terminal(record)?,
            consumed_continuation,
        )));
    }
    let mut advanced = split;
    let mut consumed_continuation = false;
    for (take_then, branch) in [(true, then_branch), (false, else_branch)] {
        let focused = advanced.focus_execution_if_arm(record, take_then)?;
        let next = if consumed_leading_steps {
            advance_focused_execution_region_after_leading_tactic(
                focused,
                enclosing_record,
                branch,
                expansion_capture.as_deref_mut(),
                proof_site,
                owning_source_index,
                depth + 1,
            )?
        } else {
            advance_focused_execution_region(
                focused,
                enclosing_record,
                branch,
                expansion_capture.as_deref_mut(),
                proof_site,
                owning_source_index,
                depth + 1,
            )?
        };
        let mut next = match next {
            Ok(next) => next,
            Err(decline) => return Ok(Err(decline)),
        };
        // A proof `if` is a case split: each case is the function
        // running linearly under one assumed polarity. A case
        // whose arm ends short of function exit keeps running
        // through the shared continuation to its own exit; the
        // cases never rejoin as one state.
        if !next.is_at_function_exit() && !matches!(continuation, InternalProofNode::Done) {
            let continued = driven!(advance_focused_execution_region(
                next,
                enclosing_record,
                continuation,
                expansion_capture.as_deref_mut(),
                proof_site,
                owning_source_index,
                depth + 1,
            ));
            next = continued;
            consumed_continuation = true;
        }
        if !next.is_at_function_exit() {
            return decline_short_of_exit();
        }
        advanced = next;
    }
    Ok(Ok((
        advanced.join_focused_execution_if_terminal(record)?,
        consumed_continuation,
    )))
}

#[allow(clippy::too_many_arguments)]
fn try_check_structural_function_proof_inner<'a>(
    execution: &ExecutionProofState,
    pure_facts: &PureFactList,
    constants: &ExecutionProofConstants,
    program: &InternalProofNode,
    generated_by_source_index: Option<usize>,
    staged_expansion_capture: &mut Option<ExpansionCapture>,
    function_block: &'a FunctionBlock,
    parsed_function: &'a crate::languages::interface::ImportedFunction,
    claim_label: &'a str,
    function_environment: &'a ExecutionEnvironment,
    spec_definitions: SpecDefinitions<'a>,
    resource_environment: &'a ResourceEnvironment,
    theorem_environment: &'a TheoremEnvironment,
    function: &'a ProgramFunction,
    arguments: &'a [ProgramExpression],
) -> Driven<Proof<'a>> {
    let proof_site = constants.proof_site.clone();
    let owning_source_index = generated_by_source_index.unwrap_or(usize::MAX);
    let mut proof = Proof::for_execution_frontier(
        claim_label,
        internal_proof_first_index(program).ok_or_else(|| {
            ClickError::new(format!("`{claim_label}` has no structural proof tactics"))
        })?,
        execution.clone(),
        pure_facts.clone(),
        constants.clone(),
        function_block,
        function,
        parsed_function,
        arguments,
        function_environment,
        resource_environment,
        spec_definitions,
        theorem_environment,
    );
    let mut current = program;
    let mut remaining = Vec::new();
    let mut saw_structure = false;
    loop {
        match current {
            InternalProofNode::Match {
                index,
                source_index,
                proof_match,
                arms,
                continuation,
                ..
            } => {
                if proof.is_at_function_exit()
                    && let Ok(deferred) = defer_post_execution_match(
                        proof.clone(),
                        *index,
                        *source_index,
                        proof_match,
                        arms,
                        continuation,
                        staged_expansion_capture.as_mut(),
                    )?
                {
                    proof = deferred;
                    saw_structure = true;
                    current = continuation;
                    continue;
                }
                proof = proof.with_execution_tactic_index(*index)?;
                let next = driven!(advance_execution_match(
                    proof,
                    proof_match,
                    *source_index,
                    arms,
                    continuation,
                    staged_expansion_capture.as_mut(),
                    proof_site.as_ref(),
                    owning_source_index,
                    0,
                ));
                proof = next;
                saw_structure = true;
                // A rejoined `match` leaves its continuation to run once.
                current = continuation;
            }
            InternalProofNode::Cases {
                index,
                source_index,
                disjunction,
                then_branch,
                else_branch,
                continuation,
            } => {
                if proof.is_at_function_exit() {
                    proof = driven!(defer_post_execution_case_split(
                        proof,
                        *index,
                        *source_index,
                        disjunction,
                        true,
                        None,
                        then_branch,
                        else_branch,
                        continuation,
                        staged_expansion_capture.as_mut(),
                    ));
                    saw_structure = true;
                    current = continuation;
                    continue;
                }
                proof = proof.with_execution_tactic_index(*index)?;
                if !matches!(continuation.as_ref(), InternalProofNode::Done) {
                    proof = proof.prepare_entry_interface()?;
                }
                proof = proof.driver().prove_cases_disjunction(disjunction)?;
                let (split, record) =
                    proof.split_focused_execution_disjunction(disjunction.clone())?;
                let (joined, consumed_continuation) = driven!(advance_case_split_arms(
                    split,
                    &record,
                    &None,
                    then_branch,
                    else_branch,
                    continuation,
                    false,
                    None,
                    staged_expansion_capture.as_mut(),
                    proof_site.as_ref(),
                    owning_source_index,
                    *source_index,
                    0,
                ));
                proof = joined;
                saw_structure = true;
                current = if consumed_continuation {
                    &DONE_PROOF
                } else {
                    continuation
                };
            }
            InternalProofNode::Done => break,
            InternalProofNode::Linear {
                tactics,
                continuation,
            } => {
                let linear = InternalProofNode::Linear {
                    tactics: tactics.clone(),
                    continuation: Box::new(InternalProofNode::Done),
                };
                let (advanced, unconsumed) = driven!(advance_checked_linear_continuation(
                    proof,
                    &linear,
                    staged_expansion_capture.as_mut(),
                    proof_site.as_ref(),
                    generated_by_source_index.unwrap_or(usize::MAX),
                    Some(claim_label),
                ));
                proof = advanced;
                if !unconsumed.is_empty() {
                    if matches!(continuation.as_ref(), InternalProofNode::Done) {
                        remaining = unconsumed;
                        break;
                    }
                    // Post-exit outcome tactics from this linear run precede
                    // more structure (a post-execution `if`). Defer them onto
                    // the exit Proof in order, then process the continuation.
                    for indexed in &unconsumed {
                        let next = driven!(defer_post_exit_outcome_tactic(
                            proof,
                            indexed,
                            staged_expansion_capture.as_mut(),
                        ));
                        proof = next;
                    }
                    saw_structure = true;
                }
                current = continuation;
            }
            InternalProofNode::Open {
                index,
                source_index,
                resource,
                body,
                continuation,
            } => {
                saw_structure = true;
                if proof.is_at_function_exit() {
                    let open = post_execution_open(&proof, *index, *source_index, resource, body)?;
                    proof = proof.defer_post_execution_source_tactic(
                        *index,
                        *source_index,
                        open,
                        staged_expansion_capture.as_mut(),
                    )?;
                    current = continuation;
                    continue;
                }
                proof = proof.with_execution_tactic_index(*index)?;
                let scope = proof.begin_open(resource.clone(), *source_index)?;
                let scope = driven!(advance_checked_open_scope(
                    scope,
                    body,
                    staged_expansion_capture.as_mut(),
                    proof_site.as_ref(),
                    owning_source_index,
                ));
                proof = scope.driver().complete_scope()?;
                current = continuation;
            }
            InternalProofNode::Branch {
                index,
                source_index,
                ensuring,
                then_branch,
                else_branch,
                continuation,
            } => {
                let selected_source_index = proof_site.as_ref().and_then(|site| {
                    selected_tactic_index_for_site(staged_expansion_capture.as_ref(), site)
                });
                let capture_in_continuation = selected_source_index.is_some_and(|wanted| {
                    internal_proof_contains_source_index(continuation, wanted)
                });
                let capture_in_nested_branch = selected_source_index.is_some_and(|wanted| {
                    checked_execution_region_contains_source(then_branch, wanted)
                        || checked_execution_region_contains_source(else_branch, wanted)
                });
                if !selected_source_index.is_none_or(|wanted| {
                    wanted <= *source_index || capture_in_continuation || capture_in_nested_branch
                }) {
                    return decline();
                }
                if let Err(decline) =
                    checked_structural_execution_branch_supported(then_branch, else_branch)
                {
                    return Ok(Err(decline));
                }
                let (advanced, _, certificate, consumed_continuation) =
                    driven!(try_advance_checked_execution_branch(
                        proof.at_source_tactic(*source_index),
                        *index,
                        ensuring,
                        then_branch,
                        else_branch,
                        continuation,
                        staged_expansion_capture.as_mut(),
                        proof_site.as_ref(),
                        owning_source_index,
                        0,
                    ));
                proof = advanced;
                saw_structure = true;
                if !capture_in_continuation
                    && !capture_in_nested_branch
                    && let Some(site) = proof_site.as_ref()
                {
                    record_proof_site_tactic_expansion(
                        staged_expansion_capture.as_mut(),
                        site,
                        *source_index,
                        &certificate
                            .expect("an expansion request retains the branch certificate")
                            .to_proof_tactics(),
                    );
                }
                current = if consumed_continuation {
                    &DONE_PROOF
                } else {
                    continuation
                };
            }
            InternalProofNode::CallOutcomes {
                index,
                payload_bindings,
                returned_branch,
                threw_branch,
                continuation,
                ..
            } => {
                if proof.is_at_function_exit() {
                    return Err(proof.with_execution_tactic_index(*index)?.step_error(
                        "`outcomes` requires a maybe-throwing call at the execution frontier",
                    ));
                }
                let owner = proof.clone();
                let proof_at_call = proof.with_execution_tactic_index(*index)?;
                let Some((split, record)) =
                    proof_at_call.split_focused_call_outcomes(payload_bindings.clone())?
                else {
                    return decline();
                };
                let mut advanced = split;
                for (take_returned, region) in [
                    (true, returned_branch.as_ref()),
                    (false, threw_branch.as_ref()),
                ] {
                    let focused =
                        advanced.focus_call_outcome_arm(&record, take_returned, &owner)?;
                    let next = driven!(advance_focused_execution_region(
                        focused,
                        Some(&record),
                        region,
                        staged_expansion_capture.as_mut(),
                        proof_site.as_ref(),
                        owning_source_index,
                        1,
                    ));
                    advanced = next.leave_call_outcome_arm(&owner);
                }
                if !advanced.is_at_function_exit() {
                    return decline();
                }
                proof = advanced
                    .join_focused_call_outcomes_terminal(&record)?
                    .restore_execution_tactic_attribution(&owner)?;
                saw_structure = true;
                current = continuation;
            }
            InternalProofNode::If {
                index,
                source_index,
                condition,
                ensuring,
                then_branch,
                else_branch,
                continuation,
                ..
            } => {
                if proof.is_at_function_exit() {
                    proof = driven!(defer_post_execution_case_split(
                        proof,
                        *index,
                        *source_index,
                        condition,
                        false,
                        ensuring.as_deref(),
                        then_branch,
                        else_branch,
                        continuation,
                        staged_expansion_capture.as_mut(),
                    ));
                    saw_structure = true;
                    current = continuation;
                    continue;
                }
                proof = proof
                    .with_execution_tactic_index(*index)?
                    // The split's trace and refusals name the `if` itself, so
                    // `--trace-to` a line in one arm finds that arm.
                    .at_source_tactic(*source_index);
                // Arms that rejoin before the first statement continue from
                // the bound entry state, as an interface join does.
                if ensuring.is_some() || !matches!(continuation.as_ref(), InternalProofNode::Done) {
                    proof = proof.prepare_entry_interface()?;
                }
                if expanded_execution_if_has_pruned_arm(then_branch, else_branch)
                    && expanded_execution_if_steps(then_branch, else_branch).is_none()
                    && proof.frontier_is_execution_branch(condition)?
                {
                    let owner = proof.clone();
                    let (split, record) = proof.split_focused_execution_branch()?;
                    if ensuring.is_none()
                        && matches!(continuation.as_ref(), InternalProofNode::Done)
                        && let Some(take_then) = record.sole_feasible_arm()
                    {
                        let arm = if take_then { then_branch } else { else_branch };
                        let (focused, remaining, arm_continuation) =
                            checked_expanded_execution_arm_prefix(
                                &split, &record, take_then, condition, arm,
                            )?;
                        if focused.is_at_region_boundary() {
                            let joined = focused
                                .join_focused_execution_split(&record, false, None)?
                                .restore_execution_tactic_attribution(&owner)?;
                            let next = driven!(advance_focused_execution_arm(
                                joined,
                                remaining,
                                staged_expansion_capture.as_mut(),
                                proof_site.as_ref(),
                                owning_source_index,
                            ));
                            proof = next;
                            saw_structure = true;
                            current = arm_continuation;
                            continue;
                        }
                    }
                    let arms = driven!(advance_checked_branch_arms(
                        split,
                        &record,
                        Some(condition),
                        ensuring,
                        then_branch,
                        else_branch,
                        continuation,
                        staged_expansion_capture.as_mut(),
                        proof_site.as_ref(),
                        owning_source_index,
                        0,
                    ));
                    proof = arms
                        .advanced
                        .join_focused_execution_split(&record, arms.empty, arms.join_interface)?
                        .restore_execution_tactic_attribution(&owner)?;
                    proof.note_trace_join_continuation_arm(arms.continuation_arm);
                    saw_structure = true;
                    current = if arms.consumed_continuation {
                        &DONE_PROOF
                    } else {
                        continuation
                    };
                    continue;
                }
                if let Some((then_steps, else_steps)) =
                    expanded_execution_if_steps(then_branch, else_branch)
                    && proof.frontier_is_execution_branch(condition)?
                {
                    proof = proof.driver().apply_expanded_execution_if(
                        condition,
                        &then_steps,
                        &else_steps,
                    )?;
                    saw_structure = true;
                    current = continuation;
                    continue;
                }
                let arm_steps = match (
                    execution_region_leading_tactic(then_branch),
                    execution_region_leading_tactic(else_branch),
                ) {
                    (Some(then_tactic), Some(else_tactic)) => match (
                        source_successor_if_arm_step(then_tactic),
                        source_successor_if_arm_step(else_tactic),
                    ) {
                        (Some(then_step), Some(else_step)) => Some([then_step, else_step]),
                        _ => None,
                    },
                    _ => None,
                };
                // An `ensuring` interface joins the arms where they end, so
                // their leading steps are not folded into the split.
                let arm_steps = arm_steps.filter(|_| ensuring.is_none());
                let product = if let Some(arm_steps) = arm_steps.as_ref() {
                    let exact = proof.driver().try_split_source_successor_if(
                        condition,
                        [
                            (arm_steps[0].0, arm_steps[0].1),
                            (arm_steps[1].0, arm_steps[1].1),
                        ],
                    )?;
                    if exact.is_some() {
                        record_source_successor_smart_expansions(
                            arm_steps,
                            staged_expansion_capture.as_mut(),
                            proof_site.as_ref(),
                            owning_source_index,
                        );
                    }
                    exact
                } else {
                    None
                };
                let consumed_leading_steps = product.is_some();
                let (split, record) = if let Some(split) = product {
                    split
                } else {
                    proof.split_focused_execution_if(condition.clone())?
                };
                // What follows a proof `if` is checked once. Each arm is run
                // once, without the continuation. Two arms that are both
                // still live must rejoin, through `ensuring` or because they
                // end at one program point in one state; if they cannot,
                // that is an error, not a reason to run the continuation
                // once per arm. When only one arm is live (the other reached
                // function exit), the continuation belongs to that arm.
                let (joined, consumed_continuation) = driven!(advance_case_split_arms(
                    split,
                    &record,
                    ensuring,
                    then_branch,
                    else_branch,
                    continuation,
                    consumed_leading_steps,
                    None,
                    staged_expansion_capture.as_mut(),
                    proof_site.as_ref(),
                    owning_source_index,
                    *source_index,
                    0,
                ));
                proof = joined;
                saw_structure = true;
                current = if consumed_continuation {
                    &DONE_PROOF
                } else {
                    continuation
                };
            }
        }
    }
    check_verification_deadline()?;
    if !proof.is_at_function_exit() {
        if remaining.is_empty()
            && let Some(error) = proof.unfinished_callback_script_error()
        {
            return Err(error);
        }
        if let Some((indexed, reason)) = remaining.first().and_then(|indexed| {
            pre_exit_outcome_tactic_error(&proof, &indexed.tactic).map(|reason| (indexed, reason))
        }) {
            return Err(proof
                .at_source_tactic(indexed.source_index)
                .step_error(reason)
                .with_failed_tactic(tactic_name(&indexed.tactic)));
        }
        return decline();
    }
    if !saw_structure {
        return decline();
    }
    for indexed in remaining {
        check_verification_deadline()?;
        let next = driven!(defer_post_exit_outcome_tactic(
            proof,
            &indexed,
            staged_expansion_capture.as_mut()
        ));
        proof = next;
    }
    Ok(Ok(proof))
}

/// Defers one ordered outcome operation, written after the checked
/// execution reached function exit, onto the exit `Proof`. Outcome tactics
/// are deferred by their post-execution kind. `Ok(None)` declines; `Err` is a
/// terminal diagnostic.
fn defer_post_exit_outcome_tactic<'a>(
    proof: Proof<'a>,
    indexed: &IndexedTactic,
    expansion_capture: Option<&mut ExpansionCapture>,
) -> Driven<Proof<'a>> {
    if let Some(reason) = post_exit_execution_tactic_error(&indexed.tactic) {
        return Err(proof
            .at_source_tactic(indexed.source_index)
            .step_error(reason)
            .with_failed_tactic(tactic_name(&indexed.tactic)));
    }
    let Some(post_tactic) = flat_post_execution_tactic(&indexed.tactic) else {
        return decline();
    };
    Ok(Ok(proof.defer_post_execution_source_tactic(
        indexed.index,
        indexed.source_index,
        post_tactic,
        expansion_capture,
    )?))
}

pub(in crate::surface::proof) fn source_have_error(
    proof: &Proof<'_>,
    have: &ProofHave,
    index: usize,
    goal: Option<&Proposition>,
    cause: Option<ClickError>,
    root_failure: bool,
) -> ClickError {
    // Search failures belong to the written solve goal, rather than the last
    // candidate's nested proof step. Resource exhaustion still takes priority.
    if matches!(
        have.checking_proof().as_ref(),
        SourceProof::Tactic(SmartTactic::ImplicitTail)
    ) {
        if let Err(error) = check_verification_deadline() {
            return error;
        }
        if cause
            .as_ref()
            .is_none_or(|error| error.kind() == crate::surface::ClickErrorKind::Proof)
        {
            if root_failure && let Some(error) = cause {
                return error.with_context(format!(
                    "`{}` tactic {index}: `solve` could not prove `{}`",
                    proof.claim_label(),
                    crate::surface::diagnostics::describe_click_proposition(&have.proposition)
                ));
            }
            // Keep the checked predecessor's diagnostic context, just as
            // the other source-have failures do. Search candidates are not
            // the environment in which this written goal failed.
            return proof.attach_step_diagnostic(
                ClickError::new(format!(
                    "`{}` tactic {index}: `solve` could not prove `{}`",
                    proof.claim_label(),
                    crate::surface::diagnostics::describe_click_proposition(&have.proposition)
                ))
                .with_proof_refusal(crate::surface::ProofRefusal::UnsuccessfulSearch),
            );
        }
    }
    if let Some(error) = cause {
        return proof.attach_step_diagnostic(error).with_context(format!(
            "`{}` tactic {index}: `have` failed for `{}`",
            proof.claim_label(),
            crate::surface::diagnostics::describe_click_proposition(&have.proposition)
        ));
    }
    let pointer_equality = matches!(&goal, Some(condition_source_0 @ Proposition::ConditionIs(
            _,
            true
        )) if matches!(condition_source_0.old_condition(), Some((OldConditionTerm::AddressEqual(_, _), _))));
    let detail = if pointer_equality {
        "missing pure fact: pointer equality is true".to_string()
    } else {
        // A nested goal that matches an available fact except for which
        // version it reads gets the one explanation for that.
        let premises = proof.facts().propositions().collect::<Vec<_>>();
        let mismatch = goal
            .and_then(|goal| {
                crate::surface::diagnostics::describe_proposition_version_mismatch(
                    goal,
                    &premises,
                    "the available fact was stated",
                    ParameterBinding::default(),
                )
            })
            .map(|mismatch| format!("\n  {mismatch}"))
            .unwrap_or_default();
        format!(
            "`have {}` did not close its checked nested goal{mismatch}",
            crate::surface::diagnostics::describe_click_proposition(&have.proposition)
        )
    };
    ClickError::new(format!(
        "`{}` tactic {index}: `have` failed: {detail}",
        proof.claim_label()
    ))
}

pub(in crate::surface::proof) fn solve_nested_have<'a>(
    nested: ProofScope<'a>,
    have: &ProofHave,
    failed_check: &mut Option<ClickError>,
) -> Result<Option<ProofScope<'a>>, ClickError> {
    use crate::surface::proof::smart_closures::LinearScriptDecline;
    let body = nested.body().clone();
    let source_proof = have.checking_proof();
    let _origin = source_proof
        .uses_implicit_tail()
        .then(|| crate::surface::proof_trace::TraceOrigin::enter_implicit("implicit solve"));
    let (selected, checks) = crate::surface::proof_diagnostics::capture_check_observations(
        || -> Result<_, ClickError> {
            Ok(match source_proof.as_ref() {
                SourceProof::Tactic(SmartTactic::ImplicitTail) => {
                    nested.driver().try_solve_closure()?
                }
                SourceProof::Default | SourceProof::Tactic(SmartTactic::Solve) => {
                    (nested).driver().try_solve_closure()?
                }
                SourceProof::Script(body) => {
                    // A refused written step is final. The tail runs only
                    // after the written body has reached an open goal.
                    let mut declined = None;
                    let mut unfinished = None;
                    let selected = nested.driver().try_authoritative_linear_script_reporting(
                        body,
                        &mut declined,
                        &mut unfinished,
                        true,
                    )?;
                    if selected.is_none() {
                        let detail = match declined {
                            Some(
                                LinearScriptDecline::Step(index)
                                | LinearScriptDecline::UnsuccessfulSearch(index),
                            ) => match body.get(index) {
                                Some(tactic) => format!(
                                    "step {} of its body, `{}`, declined",
                                    index + 1,
                                    tactic_name(tactic)
                                ),
                                None => format!("step {} of its body declined", index + 1),
                            },
                            Some(LinearScriptDecline::Shape) => {
                                "its body is not a shape the checked driver runs".to_string()
                            }
                            None => "its body ran to the end with the goal still open".to_string(),
                        };
                        let goal = crate::surface::diagnostics::describe_click_proposition(
                            &have.proposition,
                        );
                        check_verification_deadline()?;
                        // Preserve the body's checked prefix and remaining goal,
                        // rather than attaching the enclosing execution state.
                        return Err(unfinished
                            .as_ref()
                            .unwrap_or(nested.body())
                            .step_error(format!("`have {goal}` was not proved: {detail}"))
                            .with_proof_refusal(match declined {
                                None => crate::surface::ProofRefusal::IncompleteProof,
                                Some(LinearScriptDecline::UnsuccessfulSearch(_)) => {
                                    crate::surface::ProofRefusal::UnsuccessfulSearch
                                }
                                Some(_) => crate::surface::ProofRefusal::Tactic,
                            }));
                    }
                    selected
                }
            })
        },
    );
    let selected = selected.map_err(|error| error.with_check_observations(checks.clone()))?;
    // A surface `have` may lower to more than the currently focused
    // proposition goal (for example, a loadability assertion can carry an
    // additional resource obligation). The linear body above advances only
    // its focused goal, while joining requires the entire nested scope to be
    // complete. Treat that unsupported multi-goal shape as a transactional
    // miss so the enclosing checked driver can try another law or report the
    // unsupported shape.
    let selected = selected.filter(ProofScope::is_complete);
    if selected.is_none() {
        check_verification_deadline()?;
        *failed_check = Some(
            match source_proof.as_ref() {
                SourceProof::Script(_) => body
                    .step_error("the nested proof ended with an unproved obligation")
                    .with_proof_refusal(crate::surface::ProofRefusal::IncompleteProof),
                _ => body.solve_failure(),
            }
            .with_check_observations(checks),
        );
    }
    Ok(selected)
}

/// One smart statement step on a preservation-region descendant, with the
/// checked certificate delta pushed into the path's surface record. Shared
/// by the preservation driver and the automatic-preservation search. A
/// frontier the step declines (an undecided C `if`, a loop, a call's
/// outcomes) is refused with the bare step's own diagnostic.
pub(in crate::surface::proof) fn preservation_smart_step<'a>(
    proof: &Proof<'a>,
) -> Result<Proof<'a>, ClickError> {
    let _origin = crate::surface::proof_trace::TraceOrigin::enter_implicit("loop preservation");
    let mut retried_requirements = std::collections::BTreeSet::new();
    match crate::kernel::search::ProofSearch::try_smart_statement_step(
        proof,
        ProofStep::Step,
        &mut retried_requirements,
    )? {
        Some(stepped) => Ok(stepped),
        None => proof.driver().apply_step(ProofStep::Step),
    }
}

/// Whether a proof region is one straight run of tactics with no nested
/// split. Such an arm is cheap to run once more when its split turns out
/// not to rejoin.
fn region_is_straight_line(region: &InternalProofNode) -> bool {
    match region {
        InternalProofNode::Done => true,
        InternalProofNode::Linear { continuation, .. } => {
            matches!(continuation.as_ref(), InternalProofNode::Done)
        }
        _ => false,
    }
}

/// Whether anything is written after a split in a preservation region: in
/// its own continuation or in one still owed by an enclosing split.
fn preservation_split_has_continuation(
    continuation: &InternalProofNode,
    pending: &[&InternalProofNode],
) -> bool {
    !matches!(continuation, InternalProofNode::Done)
        || pending
            .iter()
            .any(|node| !matches!(node, InternalProofNode::Done))
}

/// An empty continuation that is not `Done`, which asks the function-region
/// drivers to rejoin a split's arms where they end instead of running each
/// to function exit.
fn rejoin_here() -> InternalProofNode {
    InternalProofNode::Linear {
        tactics: Vec::new(),
        continuation: Box::new(InternalProofNode::Done),
    }
}

thread_local! {
    /// The continuation nodes the preservation proof under way has entered
    /// from a finished arm, by address, each with the program points paths
    /// entered it at. See [`enter_preservation_continuation`].
    static PRESERVATION_CONTINUATIONS: std::cell::RefCell<
        Vec<(usize, crate::kernel::proof::ExecutionFrontier)>,
    > = const { std::cell::RefCell::new(Vec::new()) };
}

/// Records that a path which finished a split's arm is entering the tactics
/// written after the split at `frontier`, and returns whether it is the
/// first to enter them at that program point.
///
/// Paths that reach those tactics at different program points are different
/// paths of the C: one arm stepped to a `break` and another to the body's
/// end, say, and each has to be finished its own way. Two that reach them at
/// one program point are one path of the C split in two by the proof, which
/// is the case that would check the rest of the body twice. The record holds
/// one entry per path of the body, so the scan is over the body's own paths.
fn enter_preservation_continuation(
    node: &InternalProofNode,
    frontier: &crate::kernel::proof::ExecutionFrontier,
) -> bool {
    let node = std::ptr::from_ref(node) as usize;
    PRESERVATION_CONTINUATIONS.with(|entered| {
        let mut entered = entered.borrow_mut();
        if entered
            .iter()
            .any(|(other, at)| *other == node && at.at_same_program_point(frontier))
        {
            return false;
        }
        entered.push((node, frontier.clone()));
        true
    })
}

/// Runs one loop's preservation proof with its own record of the
/// continuations its paths enter, so a loop proved inside another loop's
/// body neither sees nor disturbs the outer record.
pub(in crate::surface::proof) fn with_preservation_continuation_record<R>(
    operation: impl FnOnce() -> R,
) -> R {
    let outer =
        PRESERVATION_CONTINUATIONS.with(|entered| std::mem::take(&mut *entered.borrow_mut()));
    let result = operation();
    PRESERVATION_CONTINUATIONS.with(|entered| *entered.borrow_mut() = outer);
    result
}

/// Drives one preservation program region on the typed boundary `Proof`.
/// `pending` is the stack of continuation nodes still owed to the current
/// path, innermost first. A proof-level split without `ensuring` keeps its
/// arms separate to the loop's typed boundary, where every leaf is collected
/// for the caller's per-path bundle, certificate, and effect processing.
/// That is allowed only while at most one of its arms goes on into the
/// tactics written after it: a second arm reaching them is refused, because
/// it would check the rest of the body once per arm. There is no
/// secondary interpreter: a tactic outside the checked operations is a
/// prompt failure naming the tactic.
#[allow(clippy::too_many_arguments)]
pub(in crate::surface::proof) fn advance_preservation_region<'a, 'node>(
    mut proof: Proof<'a>,
    mut node: &'node InternalProofNode,
    mut pending: &[&'node InternalProofNode],
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
    owning_source_index: usize,
    claim_label: &str,
    leaves: &mut Vec<Proof<'a>>,
    refuted_case_paths: &mut Vec<(ExecutionProofState, ProofCertificate)>,
    unfinished: &mut Vec<UnfinishedPreservationPath<'a>>,
    mut last_tactic: Option<(usize, &'static str)>,
) -> Result<Proof<'a>, ClickError> {
    // Sibling continuations stay in one preservation region. Walking them
    // here keeps the native stack bounded by actual proof nesting.
    loop {
        check_verification_deadline()?;
        if proof.is_at_function_exit() && !matches!(node, InternalProofNode::Done) {
            let tactics = deferred_post_execution_region(node).map_err(|reason| {
                if reason == Decline::OutcomesAfterExit {
                    proof.step_error(
                        "`outcomes` requires a maybe-throwing call at the execution frontier",
                    )
                } else {
                    proof.step_error("unsupported proof structure after a loop-body return")
                }
            })?;
            for deferred in Arc::unwrap_or_clone(tactics) {
                proof = proof.defer_post_execution_source_tactic(
                    deferred.tactic_index,
                    deferred.source_index,
                    deferred.tactic,
                    expansion_capture.as_deref_mut(),
                )?;
            }
            leaves.push(proof.clone());
            return Ok(proof);
        }
        return match node {
            InternalProofNode::Match {
                index,
                source_index,
                proof_match,
                arms,
                continuation,
                ..
            } => {
                proof = proof.with_execution_tactic_index(*index)?;
                // With an interface the arms rejoin inside the body, as the arms
                // of a `branch` do, and what follows the `match` is checked
                // once on the one path that leaves it.
                if proof_match.ensuring.is_some() {
                    let Ok(joined) = advance_execution_match(
                        proof,
                        proof_match,
                        *source_index,
                        arms,
                        continuation,
                        expansion_capture.as_deref_mut(),
                        proof_site,
                        owning_source_index,
                        0,
                    )?
                    else {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {index}: proof `match` did not rejoin as a checked preservation operation"
                        )));
                    };
                    proof = joined;
                    node = continuation;
                    last_tactic = Some((*index, "match"));
                    continue;
                }
                // Without an interface, straight-line arms that end at one
                // program point in one state still rejoin, as they do in a
                // function body. The attempt is transactional: arms that end
                // apart are run again below as separate paths, which costs
                // those arms once more and nothing nested, since they nest
                // nothing.
                if preservation_split_has_continuation(continuation, pending)
                    && arms.iter().all(region_is_straight_line)
                {
                    let saved_capture = expansion_capture.as_deref().cloned();
                    let attempt = advance_execution_match(
                        proof.clone(),
                        proof_match,
                        *source_index,
                        arms,
                        &rejoin_here(),
                        expansion_capture.as_deref_mut(),
                        proof_site,
                        owning_source_index,
                        0,
                    );
                    if let Ok(Ok(joined)) = attempt {
                        proof = joined;
                        node = continuation;
                        last_tactic = Some((*index, "match"));
                        continue;
                    }
                    if let (Some(capture), Some(saved)) =
                        (expansion_capture.as_deref_mut(), saved_capture)
                    {
                        *capture = saved;
                    }
                }
                let plan = proof.plan_execution_match(proof_match)?;
                // Otherwise every arm continues into the region's own
                // continuation as its own path, closes the invariants and
                // reaches the loop's boundary with its own resource state.
                let mut arm_pending: Vec<&InternalProofNode> =
                    Vec::with_capacity(pending.len() + 1);
                arm_pending.push(continuation.as_ref());
                arm_pending.extend_from_slice(pending);
                advance_preservation_match_group(
                    proof,
                    &plan,
                    arms,
                    &plan.live_cases(),
                    &arm_pending,
                    expansion_capture,
                    proof_site,
                    owning_source_index,
                    claim_label,
                    leaves,
                    refuted_case_paths,
                    unfinished,
                    0,
                    Some((*index, "match")),
                )
            }
            InternalProofNode::Done => {
                // A `return` completes this preservation path immediately.  The
                // syntactic continuation belongs only to paths that remained in
                // the loop body; attempting to drive it after function exit
                // misattributes the first continuation tactic as a post-return
                // operation and, more importantly, loses the terminal loop exit.
                let terminal_return = proof
                    .execution_view()
                    .is_ok_and(|view| view.frontier.is_at_function_exit());
                if terminal_return {
                    leaves.push(proof.clone());
                    return Ok(proof);
                }
                let Some((next, rest)) = pending.split_first() else {
                    if !proof.is_at_region_boundary() {
                        // One certified iteration is a path that reaches the
                        // body's end, a `continue`, or a `break`. A path that
                        // stops anywhere else has not been proved at all. A
                        // script still being written stops inside the body; it
                        // is set aside so the region's other paths still run
                        // and the finished ones still close their back edges,
                        // and the frontier it reached is reported after that
                        // (`describe_unfinished_preservation`). Anything else is
                        // a complete-but-wrong body.
                        if proof.execution_view().is_ok_and(|view| {
                            matches!(
                                view.frontier.position,
                                FrontierPosition::StatementEntry { .. }
                            )
                        }) {
                            // The script ran out before the body did: the rest
                            // of the body runs as the automatic closer runs a
                            // whole one, and each path it reaches closes its
                            // back edge like a written one. A rest that does not
                            // run reports the frontier the script reached.
                            match walk_loop_body(proof.clone()) {
                                Ok(completed) => leaves.extend(completed),
                                Err(error) => unfinished.push(UnfinishedPreservationPath {
                                    proof: proof.clone(),
                                    last_tactic,
                                    walk_failure: Some(error.raw_summary().to_string()),
                                }),
                            }
                            return Ok(proof);
                        }
                        return Err(ClickError::new(format!(
                            "`{claim_label}` must execute exactly one complete loop-body iteration, ending at the body's end, a `continue`, a `break`, or the loop's test when it is false"
                        )));
                    }
                    leaves.push(proof.clone());
                    return Ok(proof);
                };
                // The tactics after a split belong to one path. A second path
                // reaching them means two arms of that split, or of a split
                // nested in one of its arms, are both still live: running them
                // again would check the rest of the body once per arm.
                //
                // Tactics a smart tactic generated are not held to this. The
                // automatic closer walks each path of the C on its own and its
                // search has its own budget; its certificate writes each path's
                // tail inside the arm that reaches it, which is the shape this
                // rule asks a written proof for.
                let generated = execution_region_leading_tactic(next)
                    .is_some_and(|tactic| tactic.source_index == usize::MAX);
                if !matches!(next, InternalProofNode::Done)
                    && !generated
                    && proof
                        .execution_view()
                        .is_ok_and(|view| !enter_preservation_continuation(next, view.frontier))
                {
                    let after = execution_region_leading_tactic(next)
                        .map(|tactic| format!(" (tactic {})", tactic.index))
                        .unwrap_or_default();
                    return Err(ClickError::new(format!(
                        "`{claim_label}`: the tactics after a proof split in this loop body{after} are reached by more than one of its arms at the same program point, so they would be checked once per arm. Rejoin the arms where they end with `match value ensuring {{ ... }} {{ ... }}` or `if P ensuring {{ ... }} then {{ ... }} else {{ ... }}`, or move those tactics into each arm"
                    )).with_proof_refusal(ProofRefusal::Tactic));
                }
                node = next;
                pending = rest;
                continue;
            }
            InternalProofNode::Linear {
                tactics,
                continuation,
            } => {
                for indexed in tactics {
                    // A refuted path owes no invariant or measure and contributes
                    // no back edge or exit. Retain its terminal step for replay.
                    let refutation = match &indexed.tactic {
                        ProofTactic::Close if proof.facts().holds_false() => {
                            Some(ProofStep::CloseUnreachable)
                        }
                        ProofTactic::CloseUnreachable => Some(ProofStep::CloseUnreachable),
                        _ => None,
                    };
                    if let Some(step) = refutation {
                        let execution = proof.execution_view()?.execution.clone();
                        // A surviving sibling can depend on its case assumption.
                        // Keep the refuted arm's proof so expansion can replay the split.
                        let inside_case = !execution.presentation.case_assumptions.is_empty();
                        let proof = proof.start_source_tactic(indexed.source_index)?;
                        let proof = proof.driver().apply_step_at(step, indexed.source_index)?;
                        if inside_case {
                            refuted_case_paths.push((execution, proof.path_certificate()?));
                        }
                        return Ok(proof);
                    }
                    if proof.is_at_function_exit() {
                        if let Some(reason) = post_exit_execution_tactic_error(&indexed.tactic) {
                            return Err(proof
                                .at_source_tactic(indexed.source_index)
                                .step_error(reason));
                        }
                        let post_tactic =
                            flat_post_execution_tactic(&indexed.tactic).ok_or_else(|| {
                                proof.step_error("unsupported loop return closing tactic")
                            })?;
                        proof = proof.defer_post_execution_source_tactic(
                            indexed.index,
                            indexed.source_index,
                            post_tactic,
                            expansion_capture.as_deref_mut(),
                        )?;
                        continue;
                    }
                    let handled_by_linear_driver = !matches!(
                        indexed.tactic,
                        ProofTactic::Loop(_)
                            | ProofTactic::Close
                            | ProofTactic::Solve
                            | ProofTactic::Step
                    );
                    if handled_by_linear_driver {
                        let segment = InternalProofNode::Linear {
                            tactics: vec![indexed.clone()],
                            continuation: Box::new(InternalProofNode::Done),
                        };
                        let advanced = advance_checked_linear_continuation(
                            proof.clone(),
                            &segment,
                            expansion_capture.as_deref_mut(),
                            proof_site,
                            owning_source_index,
                            Some(claim_label),
                        )?;
                        let advanced = match advanced {
                            Ok((advanced, remaining)) if remaining.is_empty() => advanced,
                            declined => {
                                let diagnostic = ClickError::new(format!(
                                "`{claim_label}` tactic {}: `{}` did not verify as a checked preservation operation",
                                indexed.index,
                                tactic_name(&indexed.tactic)
                                )).with_failed_tactic(tactic_name(&indexed.tactic));
                                let diagnostic = match declined {
                                    Err(Decline::OutcomesAfterExit) => diagnostic
                                        .with_context("`outcomes` requires a maybe-throwing call at the execution frontier"),
                                    Err(Decline::ShortOfExit) => diagnostic
                                        .with_proof_refusal(ProofRefusal::IncompleteProof),
                                    Err(Decline::RegionDepth) => diagnostic
                                        .with_context(format!(
                                            "the checked execution region nesting limit is {MAX_CHECKED_EXECUTION_REGION_DEPTH}",
                                        ))
                                        .with_kind(ClickErrorKind::Unsupported),
                                    Ok(_) | Err(Decline::Shape) => {
                                        diagnostic.with_kind(ClickErrorKind::Internal)
                                    }
                                };
                                return Err(diagnostic);
                            }
                        };
                        proof = advanced;
                        if matches!(
                            indexed.tactic,
                            ProofTactic::CloseInvariants | ProofTactic::CloseInvariantsBy(_)
                        ) {
                            proof = proof
                                .record_invariant_closer(indexed.index, indexed.source_index)?;
                        }
                        last_tactic = Some((indexed.index, tactic_name(&indexed.tactic)));
                        continue;
                    }
                    match &indexed.tactic {
                        ProofTactic::Step => {
                            // The checked step is recorded, timed, and traced
                            // under this tactic's own index, not the last one
                            // the linear driver set.
                            proof = proof
                                .with_execution_tactic_index(indexed.index)?
                                .at_source_tactic(indexed.source_index);
                            let statement_index =
                                proof.execution_frontier_index().unwrap_or_default();
                            let _timing = TacticTiming::new(
                                claim_label,
                                indexed.index,
                                indexed.source_index,
                                &indexed.tactic,
                                statement_index,
                            );
                            let _origin =
                                crate::surface::proof::timing::trace_origin(&indexed.tactic);
                            let checkpoint = proof.checkpoint();
                            proof = proof.driver().apply_step(ProofStep::Step)?;
                            if indexed.source_index != owning_source_index
                                && let Some(site) = proof_site
                                && capture_selects_source(
                                    expansion_capture.as_deref(),
                                    site,
                                    indexed.source_index,
                                )
                            {
                                let certificate = proof.certificate_since(&checkpoint)?;
                                record_proof_site_tactic_expansion(
                                    expansion_capture.as_deref_mut(),
                                    site,
                                    indexed.source_index,
                                    &certificate.to_proof_tactics(),
                                );
                            }
                        }
                        ProofTactic::Loop(clause) => {
                            proof = proof.apply_frontier_local_loop(
                                expansion_capture.as_deref_mut(),
                                clause,
                                indexed.index,
                                indexed.source_index,
                            )?;
                        }
                        ProofTactic::Close => {
                            // At the back edge, first try the whole bundle as
                            // an explicit check. A miss can use the existing
                            // deferred region solver.
                            match proof.driver().apply_close_invariants_body(
                                &[ProofTactic::Known], None, false,
                            ) {
                                Ok(closed) => {
                                    proof = closed.record_invariant_closer(indexed.index, indexed.source_index)?;
                                }
                                Err(error) if error.verification_stopped()
                                    || crate::surface::proof::implicit_solve_scope::checked_only() =>
                                {
                                    return Err(error.with_failed_tactic("close"));
                                }
                                Err(_) => {
                                    proof = proof.defer_region_solve(indexed.index, indexed.source_index)?;
                                }
                            }
                        }
                        ProofTactic::Solve => {
                            // The region solve's semantic content is the bundle
                            // closer certified at the boundary; its capture
                            // completes with that closer.
                            proof =
                                proof.defer_region_solve(indexed.index, indexed.source_index)?;
                        }
                        tactic => {
                            return Err(ClickError::new(format!(
                                "`{claim_label}` tactic {}: `{}` is not a checked preservation operation",
                                indexed.index,
                                tactic_name(tactic)
                            )));
                        }
                    }
                    last_tactic = Some((indexed.index, tactic_name(&indexed.tactic)));
                }
                node = continuation;
                continue;
            }
            InternalProofNode::If {
                index,
                source_index,
                condition,
                ensuring,
                then_branch,
                else_branch,
                continuation,
            } => {
                proof = proof
                    .with_execution_tactic_index(*index)?
                    // The split's trace and refusals name the `if` itself, so
                    // `--trace-to` a line in one arm finds that arm.
                    .at_source_tactic(*source_index);
                // With an interface the cases rejoin inside the body, as the
                // arms of a `branch` do, and what follows the `if` is checked
                // once on the one path that leaves it.
                if ensuring.is_some() {
                    let alone = InternalProofNode::If {
                        index: *index,
                        source_index: *source_index,
                        condition: condition.clone(),
                        ensuring: ensuring.clone(),
                        then_branch: then_branch.clone(),
                        else_branch: else_branch.clone(),
                        continuation: Box::new(InternalProofNode::Done),
                    };
                    let Ok(joined) = advance_focused_execution_region(
                        proof,
                        None,
                        &alone,
                        expansion_capture.as_deref_mut(),
                        proof_site,
                        owning_source_index,
                        0,
                    )?
                    else {
                        return Err(ClickError::new(format!(
                            "`{claim_label}` tactic {index}: proof `if` did not rejoin as a checked preservation operation"
                        )));
                    };
                    proof = joined;
                    node = continuation;
                    last_tactic = Some((*index, "if"));
                    continue;
                }
                // An expanded C branch is the checked execution split it spells,
                // exactly as in a function body: a decided branch keeps its
                // infeasible arm empty, and reading that as a logical case split
                // would run the continuation on the refuted C arm.
                if let Some((then_steps, else_steps)) =
                    expanded_execution_if_steps(then_branch, else_branch)
                    && proof.frontier_is_execution_branch(condition)?
                {
                    let advanced = proof.driver().apply_expanded_execution_if(
                        condition,
                        &then_steps,
                        &else_steps,
                    )?;
                    proof = advanced;
                    node = continuation;
                    last_tactic = Some((*index, "if"));
                    continue;
                }
                // As for a `match`: straight-line arms that end in one state
                // rejoin without an interface.
                if preservation_split_has_continuation(continuation, pending)
                    && region_is_straight_line(then_branch)
                    && region_is_straight_line(else_branch)
                {
                    let saved_capture = expansion_capture.as_deref().cloned();
                    let alone = InternalProofNode::If {
                        index: *index,
                        source_index: *source_index,
                        condition: condition.clone(),
                        ensuring: None,
                        then_branch: then_branch.clone(),
                        else_branch: else_branch.clone(),
                        continuation: Box::new(rejoin_here()),
                    };
                    let attempt = advance_focused_execution_region(
                        proof.clone(),
                        None,
                        &alone,
                        expansion_capture.as_deref_mut(),
                        proof_site,
                        owning_source_index,
                        0,
                    );
                    if let Ok(Ok(joined)) = attempt {
                        proof = joined;
                        node = continuation;
                        last_tactic = Some((*index, "if"));
                        continue;
                    }
                    if let (Some(capture), Some(saved)) =
                        (expansion_capture.as_deref_mut(), saved_capture)
                    {
                        *capture = saved;
                    }
                }
                let (split, ids) = proof.split_preservation_case(condition, *index)?;
                let mut arm_pending: Vec<&InternalProofNode> =
                    Vec::with_capacity(pending.len() + 1);
                arm_pending.push(continuation.as_ref());
                arm_pending.extend_from_slice(pending);
                let mut advanced = split;
                for (value, arm) in [(true, then_branch), (false, else_branch)] {
                    let Some(id) = ids[usize::from(!value)] else {
                        continue;
                    };
                    let focused = advanced.focus_branch(id)?;
                    advanced = advance_preservation_region(
                        focused,
                        arm,
                        &arm_pending,
                        expansion_capture.as_deref_mut(),
                        proof_site,
                        owning_source_index,
                        claim_label,
                        leaves,
                        refuted_case_paths,
                        unfinished,
                        Some((*index, "if")),
                    )?;
                }
                Ok(advanced)
            }
            InternalProofNode::Cases {
                index,
                source_index,
                disjunction,
                then_branch,
                else_branch,
                continuation,
            } => {
                proof = proof.with_execution_tactic_index(*index)?;
                // A loop body's `cases` rejoins where its arms end, as a
                // straight-line proof `if` does there.
                let alone = InternalProofNode::Cases {
                    index: *index,
                    source_index: *source_index,
                    disjunction: disjunction.clone(),
                    then_branch: then_branch.clone(),
                    else_branch: else_branch.clone(),
                    continuation: Box::new(rejoin_here()),
                };
                let Ok(joined) = advance_focused_execution_region(
                    proof,
                    None,
                    &alone,
                    expansion_capture.as_deref_mut(),
                    proof_site,
                    owning_source_index,
                    0,
                )?
                else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {index}: the arms of this `cases` in a loop body do not rejoin; in a `maintain` proof each arm must end at the same program point in the same state"
                    )));
                };
                proof = joined;
                crate::surface::proof::note_preservation_cases_rejoined(*index);
                node = continuation;
                last_tactic = Some((*index, "cases"));
                continue;
            }
            InternalProofNode::Branch {
                index,
                source_index,
                ensuring,
                then_branch,
                else_branch,
                continuation,
                ..
            } => {
                proof = proof.with_execution_tactic_index(*index)?;
                let Ok((advanced, _, _, consumed_continuation)) =
                    try_advance_checked_execution_branch(
                        proof.at_source_tactic(*source_index),
                        *index,
                        ensuring,
                        then_branch,
                        else_branch,
                        continuation,
                        expansion_capture.as_deref_mut(),
                        proof_site,
                        owning_source_index,
                        0,
                    )?
                else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {index}: `branch` did not verify as a checked preservation operation"
                    )));
                };
                proof = advanced;
                node = if consumed_continuation {
                    &DONE_PROOF
                } else {
                    continuation
                };
                last_tactic = Some((*index, "branch"));
                continue;
            }
            InternalProofNode::CallOutcomes { .. } => Err(ClickError::new(
                "loop preservation proofs cannot split a call with `outcomes`",
            )),
            InternalProofNode::Open {
                index,
                source_index,
                resource,
                body,
                continuation,
            } => {
                proof = proof.with_execution_tactic_index(*index)?;
                let scope = proof.begin_open(resource.clone(), *source_index)?;
                let Ok(scope) = advance_checked_open_scope(
                    scope,
                    body,
                    expansion_capture.as_deref_mut(),
                    proof_site,
                    owning_source_index,
                )?
                else {
                    return Err(ClickError::new(format!(
                        "`{claim_label}` tactic {index}: `with` did not verify as a checked preservation operation"
                    )));
                };
                proof = scope.driver().complete_scope()?;
                node = continuation;
                last_tactic = Some((*index, "with"));
                continue;
            }
        };
    }
}

/// A `maintain` path that stopped inside the loop body because its script
/// ran out of tactics. The region keeps traversing its other paths after
/// meeting one, so a finished arm's back edge is still checked, and the
/// first of these is reported once those checks pass.
pub(in crate::surface::proof) struct UnfinishedPreservationPath<'a> {
    pub(in crate::surface::proof) proof: Proof<'a>,
    pub(in crate::surface::proof) last_tactic: Option<(usize, &'static str)>,
    /// Why the rest of the body did not run from where the script stopped.
    pub(in crate::surface::proof) walk_failure: Option<String>,
}

impl UnfinishedPreservationPath<'_> {
    /// The frontier report for this path, counting the paths in `leaves`
    /// as the ones already complete.
    pub(in crate::surface::proof) fn report(
        &self,
        claim_label: &str,
        leaves: &[Proof<'_>],
    ) -> ClickError {
        let error = match describe_unfinished_preservation(
            claim_label,
            &self.proof,
            leaves,
            self.last_tactic,
        ) {
            Some(frontier) => ClickError::new(match &self.walk_failure {
                Some(failure) => {
                    format!("{frontier}; the rest of the body did not run from there: {failure}")
                }
                None => frontier,
            }),
            None => ClickError::new(format!(
                "`{claim_label}` must execute exactly one complete loop-body iteration, ending at the body's end, a `continue`, a `break`, or the loop's test when it is false"
            )),
        };
        self.proof.attach_step_diagnostic(error)
    }
}

/// The report an unfinished `maintain` gets in place of the one-iteration
/// refusal: where in the loop body this path stopped, which tactic left it
/// there, what the body still holds ahead of it, and what the script's other
/// paths have already closed.
///
/// `None` means the path did not stop *inside* the body — it left through a
/// `return`, or ran past the body altogether — and the caller's refusal of a
/// complete-but-wrong iteration is the right diagnostic. A proof with no
/// execution frontier at all reports nothing here for the same reason: this is
/// a diagnostic, and it never replaces the caller's refusal with a complaint
/// of its own.
fn describe_unfinished_preservation(
    claim_label: &str,
    proof: &Proof<'_>,
    leaves: &[Proof<'_>],
    last_tactic: Option<(usize, &'static str)>,
) -> Option<String> {
    let view = proof.execution_view().ok()?;
    let FrontierPosition::StatementEntry { remaining } = &view.frontier.position else {
        return None;
    };
    let statement_index = view.frontier.next_statement_index;
    let head = match frontier_head_statement(remaining) {
        Some(statement) => format!("`{}`", describe_statement_head(statement)),
        // Only block ends are left: a `Skip` is a block the path has not
        // stepped out of, not a statement anyone wrote, and spelling it
        // `skip` in a diagnostic reads as an internal detail.
        None => "at the end of a block".to_string(),
    };
    let mut message = format!(
        "`{claim_label}` stopped inside the loop body: the frontier is at statement {statement_index}, {head}"
    );
    if let Some((index, name)) = last_tactic {
        message.push_str(&format!(", after tactic {index} `{name}`"));
    } else {
        message.push_str(", before any tactic ran");
    }
    let (breaks, continues) = remaining_body_exits(remaining);
    let mut ahead = vec!["the body's end".to_string()];
    if breaks > 0 {
        ahead.push(plural_exits(breaks, "break"));
    }
    if continues > 0 {
        ahead.push(plural_exits(continues, "continue"));
    }
    message.push_str(&format!(
        "; still ahead on this path: {}",
        join_list(&ahead)
    ));
    let mut closed = Vec::new();
    for (count, label) in [
        (
            count_leaves(leaves, LoopControlExit::BodyEnd),
            "the body's end",
        ),
        (count_leaves(leaves, LoopControlExit::Break), "a `break`"),
        (
            count_leaves(leaves, LoopControlExit::TestFalse),
            "the loop's test, false",
        ),
        (
            count_leaves(leaves, LoopControlExit::Continue),
            "a `continue`",
        ),
    ] {
        if count > 0 {
            closed.push(format!("{count} at {label}"));
        }
    }
    if closed.is_empty() {
        message.push_str(". No path of this `maintain` is complete yet");
    } else {
        message.push_str(&format!(". Already complete: {}", join_list(&closed)));
    }
    message.push_str(
        ". Every path a `maintain` opens must end at the body's end, a `continue`, a `break`, or the loop's test when it is false",
    );
    Some(message)
}

/// The next statement the path would actually execute: the leading `Skip`s a
/// block end leaves in the remaining program are not statements the author
/// wrote, so they are skipped. `None` when nothing but block ends remains.
fn frontier_head_statement(statement: &ProgramStatement) -> Option<&ProgramStatement> {
    match statement {
        ProgramStatement::Skip => None,
        ProgramStatement::Seq(statements) => statements
            .iter()
            .find_map(|statement| frontier_head_statement(statement)),
        other => Some(other),
    }
}

/// How many of the collected leaves left the body the given way.
fn count_leaves(leaves: &[Proof<'_>], control: LoopControlExit) -> usize {
    leaves
        .iter()
        .filter(|leaf| {
            leaf.execution_view()
                .is_ok_and(|view| view.frontier.loop_control == control)
        })
        .count()
}

/// The `break`s and `continue`s the rest of the body still contains, counting
/// only those that belong to this loop: a nested loop or `switch` owns its
/// own, so this does not descend into one.
fn remaining_body_exits(statement: &ProgramStatement) -> (usize, usize) {
    match statement {
        ProgramStatement::Break => (1, 0),
        ProgramStatement::Continue => (0, 1),
        ProgramStatement::Seq(statements) => {
            statements
                .iter()
                .fold((0, 0), |(breaks, continues), statement| {
                    let (statement_breaks, statement_continues) = remaining_body_exits(statement);
                    (breaks + statement_breaks, continues + statement_continues)
                })
        }
        ProgramStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            let (then_breaks, then_continues) = remaining_body_exits(then_branch);
            let (else_breaks, else_continues) = remaining_body_exits(else_branch);
            (then_breaks + else_breaks, then_continues + else_continues)
        }
        _ => (0, 0),
    }
}

/// `1 `break`` or `2 `break`s`, for a diagnostic list.
fn plural_exits(count: usize, keyword: &str) -> String {
    if count == 1 {
        format!("1 `{keyword}`")
    } else {
        format!("{count} `{keyword}`s")
    }
}

/// `a`, `a and b`, `a, b, and c`.
fn join_list(items: &[String]) -> String {
    match items {
        [] => String::new(),
        [only] => only.clone(),
        [first, second] => format!("{first} and {second}"),
        [rest @ .., last] => format!("{}, and {last}", rest.join(", ")),
    }
}

/// Runs one group of a preservation `match`'s live constructor arms, halving
/// the group with the same frontier split the entry-time driver uses until a
/// single arm remains.
///
/// Nothing joins: each arm's path reaches the loop's typed boundary as its own
/// leaf, keeping the resource state that arm folded before the back edge. The
/// certificate is reassembled from those leaves by path-aligned merging, which
/// rebuilds this `match` from the arm case each leaf recorded.
#[allow(clippy::too_many_arguments)]
fn advance_preservation_match_group<'a>(
    proof: Proof<'a>,
    plan: &super::super::proof_object::ExecutionMatchPlan,
    arms: &[InternalProofNode],
    live: &[usize],
    pending: &[&InternalProofNode],
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
    owning_source_index: usize,
    claim_label: &str,
    leaves: &mut Vec<Proof<'a>>,
    refuted_case_paths: &mut Vec<(ExecutionProofState, ProofCertificate)>,
    unfinished: &mut Vec<UnfinishedPreservationPath<'a>>,
    split_depth: usize,
    last_tactic: Option<(usize, &'static str)>,
) -> Result<Proof<'a>, ClickError> {
    if split_depth >= MAX_CHECKED_EXECUTION_SPLIT_DEPTH {
        return Err(ClickError::new(format!(
            "`{claim_label}`: proof `match` splits deeper than the checked split bound of {MAX_CHECKED_EXECUTION_SPLIT_DEPTH}"
        )));
    }
    let [index] = live else {
        let (left, right) = live.split_at(live.len() / 2);
        if left.is_empty() {
            return Err(ClickError::new(format!(
                "`{claim_label}`: proof `match` needs at least one live constructor arm"
            )));
        }
        let (mut proof, record) = proof.split_execution_match_group(plan.condition(left))?;
        for (take_left, group) in [(true, left), (false, right)] {
            let focused = proof.focus_execution_if_arm(&record, take_left)?;
            proof = advance_preservation_match_group(
                focused,
                plan,
                arms,
                group,
                pending,
                expansion_capture.as_deref_mut(),
                proof_site,
                owning_source_index,
                claim_label,
                leaves,
                refuted_case_paths,
                unfinished,
                split_depth + 1,
                last_tactic,
            )?;
        }
        return Ok(proof);
    };
    let index = *index;
    let proof = proof.enter_execution_match_arm(plan, index)?;
    // An arm with no tactics reaches the region's end at once. Say so in a
    // frontier report, rather than "after tactic N `match`", which reads as
    // if the `match` itself were the last thing that ran.
    let last_tactic = if matches!(arms[index], InternalProofNode::Done) {
        last_tactic.map(|(tactic_index, _)| (tactic_index, "match, inside an arm with no tactics"))
    } else {
        last_tactic
    };
    advance_preservation_region(
        proof,
        &arms[index],
        pending,
        expansion_capture,
        proof_site,
        owning_source_index,
        claim_label,
        leaves,
        refuted_case_paths,
        unfinished,
        last_tactic,
    )
}

/// Advances one sibling arm of an in-`Proof` execution split through its
/// linear source tactics, on a proof focused at that arm's recorded goal.
/// Every operation is the ordinary focused `Proof` form; the bounded arm
/// frontier itself refuses source steps past the arm's typed region
/// boundary, so a source `branch` arm must stop at its shared
/// continuation. Only expanded and smart step layers may continue past a
/// boundary, through their own split records.
fn advance_focused_execution_arm<'a>(
    mut proof: Proof<'a>,
    tactics: &[IndexedTactic],
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
    owning_source_index: usize,
) -> Driven<Proof<'a>> {
    for indexed in tactics {
        proof = proof.at_source_tactic(indexed.source_index);
        // The implicit closer at a live frontier first runs the C that
        // remains, as in a linear continuation, then closes at exit.
        if matches!(indexed.tactic, ProofTactic::ImplicitSolve) && !proof.is_at_function_exit() {
            refuse_implicit_tail_when_disabled(&proof)?;
            let execute = IndexedTactic {
                index: indexed.index,
                source_index: indexed.source_index,
                tactic: ProofTactic::SmartExecute,
            };
            let claim_label = proof.claim_label().to_string();
            proof = driven!(apply_frontier_source_tactic(
                proof,
                &execute,
                expansion_capture.as_deref_mut(),
                proof_site,
                owning_source_index,
                Some(&claim_label),
            ));
        }
        if proof.is_at_function_exit() {
            if let Some(reason) = post_exit_execution_tactic_error(&indexed.tactic) {
                return Err(proof
                    .at_source_tactic(indexed.source_index)
                    .step_error(reason)
                    .with_failed_tactic(tactic_name(&indexed.tactic)));
            }
            let Some(post_tactic) = flat_post_execution_tactic(&indexed.tactic) else {
                return decline();
            };
            proof = proof.defer_post_execution_source_tactic(
                indexed.index,
                indexed.source_index,
                post_tactic,
                expansion_capture.as_deref_mut(),
            )?;
            continue;
        }
        if !SourceContext::ExecutionFrontier.admits(&indexed.tactic) {
            if matches!(indexed.tactic, ProofTactic::Close | ProofTactic::Solve) {
                let name = tactic_name(&indexed.tactic);
                return Err(proof
                    .at_source_tactic(indexed.source_index)
                    .step_error(closer_before_exit_reason(&proof, name))
                    .with_failed_tactic(name));
            }
            return decline();
        }
        let claim_label = proof.claim_label().to_string();
        let next = driven!(apply_frontier_source_tactic(
            proof,
            indexed,
            expansion_capture.as_deref_mut(),
            proof_site,
            owning_source_index,
            Some(&claim_label),
        ));
        proof = next;
    }
    Ok(Ok(proof))
}

/// Checks the proof prefix of a match arm that ends by refuting itself.
/// Unlike [`advance_focused_execution_arm`], it never defers a tactic to the
/// post-execution phase at function exit: the refuted arm has no outcome
/// path for a deferred tactic to run on. Each prefix tactic is checked in
/// the arm's own state without executing C.
fn advance_refuting_bridge<'a>(
    mut proof: Proof<'a>,
    tactics: &[IndexedTactic],
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
    owning_source_index: usize,
) -> Driven<Proof<'a>> {
    if !tactics.is_empty() && proof.is_at_function_exit() {
        (proof, ()) = proof.edit_execution_presentation(|presentation| {
            presentation.refuting_exit_match_arm = true;
        })?;
    }
    for indexed in tactics {
        proof = proof.at_source_tactic(indexed.source_index);
        let claim_label = proof.claim_label().to_string();
        proof = driven!(apply_frontier_source_tactic(
            proof,
            indexed,
            expansion_capture.as_deref_mut(),
            proof_site,
            owning_source_index,
            Some(&claim_label),
        ));
    }
    Ok(Ok(proof))
}

fn execution_region_leading_tactic(region: &InternalProofNode) -> Option<&IndexedTactic> {
    let InternalProofNode::Linear { tactics, .. } = region else {
        return None;
    };
    tactics.first()
}

fn source_successor_if_arm_step(indexed: &IndexedTactic) -> Option<(usize, usize, bool)> {
    match &indexed.tactic {
        ProofTactic::Step => Some((indexed.index, indexed.source_index, true)),
        _ => None,
    }
}

fn record_source_successor_smart_expansions(
    arm_steps: &[(usize, usize, bool); 2],
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
    owning_source_index: usize,
) {
    let Some(site) = proof_site else {
        return;
    };
    for (_, source_index, smart) in arm_steps {
        if *smart
            && *source_index != owning_source_index
            && capture_selects_source(expansion_capture.as_deref(), site, *source_index)
        {
            record_proof_site_tactic_expansion(
                expansion_capture.as_deref_mut(),
                site,
                *source_index,
                &[ProofTactic::Step],
            );
        }
    }
}

/// Advances a structural source region after its first linear tactic was
/// already consumed by the operation that created the focused Proof arms.
/// The untouched continuation is borrowed directly, so this cursor retains
/// no semantic state and does not clone the proof tree.
fn advance_focused_execution_region_after_leading_tactic<'a>(
    proof: Proof<'a>,
    enclosing_record: Option<&ExecutionSplit<'a>>,
    region: &InternalProofNode,
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
    owning_source_index: usize,
    depth: usize,
) -> Driven<Proof<'a>> {
    let InternalProofNode::Linear {
        tactics,
        continuation,
    } = region
    else {
        return decline();
    };
    let Some(_) = tactics.first() else {
        return decline();
    };
    let proof = driven!(advance_focused_execution_arm(
        proof,
        &tactics[1..],
        expansion_capture.as_deref_mut(),
        proof_site,
        owning_source_index,
    ));
    // The rest of the arm continues the arm's own region: `depth` already
    // charges this arm, so the continuation is not a level of its own.
    advance_focused_execution_region(
        proof,
        enclosing_record,
        continuation,
        expansion_capture,
        proof_site,
        owning_source_index,
        depth,
    )
}

/// Advances the supported structural grammar of one checked execution arm.
/// Nested branches recurse through the same typed split/arm/join helper; the
/// enclosing split record remains only the checked stop boundary for linear
/// source steps.
fn advance_execution_match<'a>(
    proof: Proof<'a>,
    source: &Arc<ProofMatch>,
    source_index: usize,
    arms: &[InternalProofNode],
    continuation: &InternalProofNode,
    expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
    owning_source_index: usize,
    depth: usize,
) -> Driven<Proof<'a>> {
    let proof = proof.prepare_execution_match(source.ensuring.is_some(), source_index)?;
    advance_prepared_execution_match(
        proof,
        source,
        arms,
        continuation,
        expansion_capture,
        proof_site,
        owning_source_index,
        depth,
    )
}

fn close_refuted_arm<'a>(proof: &Proof<'a>, source_index: usize) -> Result<Proof<'a>, ClickError> {
    proof
        .driver()
        .apply_step_at(ProofStep::CloseUnreachable, source_index)
}

fn refuting_arm_prefix(arm: &InternalProofNode) -> Option<(&[IndexedTactic], &IndexedTactic)> {
    let InternalProofNode::Linear {
        tactics,
        continuation,
    } = arm
    else {
        return None;
    };
    let (last, prefix) = tactics.split_last()?;
    (matches!(
        last.tactic,
        ProofTactic::Close | ProofTactic::CloseUnreachable
    ) && matches!(continuation.as_ref(), InternalProofNode::Done)
        && prefix
            .iter()
            .all(|indexed| bridges_without_executing(&indexed.tactic)))
    .then_some((prefix, last))
}

/// Checks the existing model-match rule from its exact prepared marker.
/// Both ordinary execution and resource scopes use this same driver.
fn advance_prepared_execution_match<'a>(
    proof: Proof<'a>,
    source: &Arc<ProofMatch>,
    arms: &[InternalProofNode],
    continuation: &InternalProofNode,
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
    owning_source_index: usize,
    depth: usize,
) -> Driven<Proof<'a>> {
    // With a continuation the live arms must rejoin; otherwise each arm
    // completes the function proof on its own.
    let rejoins = source.ensuring.is_some() || !matches!(continuation, InternalProofNode::Done);
    let marker = proof.checkpoint();
    let mut plan = proof.plan_execution_match(source)?;
    // A terminal closer can exclude a constructor before executing C.
    // Run the arm's proof prefix so it can establish the refutation in
    // the arm's own state. Publish its capture only if the arm is excluded.
    for (index, arm) in arms.iter().enumerate() {
        if plan.excluded_certificate(index).is_some() {
            continue;
        }
        let Some((bridge, last)) = refuting_arm_prefix(arm) else {
            continue;
        };
        let probe = matches!(last.tactic, ProofTactic::Close)
            && proof.is_at_function_exit()
            && !plan.arm_holds_false(index);
        if probe && bridge.is_empty() {
            continue;
        }
        let scoped = proof.enter_execution_match_arm(&plan, index)?;
        let entered = scoped.checkpoint();
        // The bridge records into a copy of the expansion capture: a bridge
        // that fails leaves the arm to the live driver below, which runs the
        // same tactics again and must find the capture as it was.
        let mut bridge_capture = expansion_capture.as_deref().cloned();
        let advanced = advance_refuting_bridge(
            scoped,
            bridge,
            bridge_capture.as_mut(),
            proof_site,
            owning_source_index,
        );
        // At function exit a live arm can depend on the outcome. If its
        // frontier bridge fails, keep it for the normal outcome driver.
        let advanced = if probe {
            attempt::candidate_outcome(advanced)?
        } else {
            Some(advanced?)
        };
        let Some(Ok(scoped)) = advanced else {
            continue;
        };
        let scoped = scoped.at_source_tactic(last.source_index);
        let Some(partition) = scoped.execution_match_arm_unreachable(&plan, index) else {
            continue;
        };
        if let (Some(capture), Some(bridged)) = (expansion_capture.as_deref_mut(), bridge_capture) {
            *capture = bridged;
        }
        let closed = close_refuted_arm(&scoped, last.source_index)?;
        closed.finish_execution_match_arm_exclusion(&mut plan, index, &entered, partition)?;
        if last.source_index != owning_source_index
            && let Some(site) = proof_site
            && capture_selects_source(expansion_capture.as_deref(), site, last.source_index)
        {
            record_proof_site_tactic_expansion(
                expansion_capture.as_deref_mut(),
                site,
                last.source_index,
                &[ProofTactic::CloseUnreachable],
            );
        }
    }
    if plan.live_cases().is_empty() {
        return Err(ClickError::new(
            "proof match with every constructor excluded is not yet supported",
        ));
    }
    // A checked refutation covers its dead constructor without a C outcome,
    // so only the live arms are executed and joined. Certificates are placed by
    // constructor index, not by the order the live arms are visited.
    let mut certificates: Vec<Option<ProofCertificate>> = (0..arms.len())
        .map(|index| plan.excluded_certificate(index).cloned())
        .collect();
    let live = plan.live_cases();
    // After execution each live arm is a separate outcome path, so tactics
    // written after the `match` would be checked once per arm, as after a
    // proof `if` or `cases` that forks.
    if proof.is_at_function_exit()
        && live.len() > 1
        && source.ensuring.is_none()
        && !ends_after_split(continuation)
    {
        return Err(post_execution_match_forks_the_proof());
    }
    let proof = driven!(advance_execution_match_group(
        proof,
        &plan,
        arms,
        &live,
        &mut certificates,
        expansion_capture,
        proof_site,
        owning_source_index,
        depth,
        0,
        rejoins,
        source.ensuring.as_deref(),
    ));
    let Some(certificates) = certificates.into_iter().collect::<Option<Vec<_>>>() else {
        return Err(ClickError::new(
            "proof `match` left a constructor without a checked arm certificate",
        ));
    };
    let proof = proof.finish_execution_match(&marker, source, certificates, plan.take_trace())?;
    if plan.has_sole_live_case()
        && let Some(assertions) = source.ensuring.as_deref()
    {
        return Ok(Ok(proof.check_sole_arm_interface(assertions)?));
    }
    Ok(Ok(proof))
}

/// Executes one group of live constructor arms, splitting the frontier in half
/// until a single arm remains. Every live arm costs one entry, its own region,
/// and at most one enclosing split, so an N-constructor match costs its N arms.
fn advance_execution_match_group<'a>(
    proof: Proof<'a>,
    plan: &super::super::proof_object::ExecutionMatchPlan,
    arms: &[InternalProofNode],
    live: &[usize],
    certificates: &mut [Option<ProofCertificate>],
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
    owning_source_index: usize,
    depth: usize,
    split_depth: usize,
    rejoins: bool,
    ensuring: Option<&[ProofAssertion]>,
) -> Driven<Proof<'a>> {
    if depth >= MAX_CHECKED_EXECUTION_REGION_DEPTH {
        return decline_region_depth();
    }
    if split_depth >= MAX_CHECKED_EXECUTION_SPLIT_DEPTH {
        return decline();
    }
    let [index] = live else {
        let (left, right) = live.split_at(live.len() / 2);
        if left.is_empty() {
            return Err(ClickError::new(
                "proof `match` needs at least one live constructor arm",
            ));
        }
        let (mut proof, record) = proof.split_execution_match_group(plan.condition(left))?;
        let mut completed = [false, false];
        for (side, (take_left, group)) in [(true, left), (false, right)].into_iter().enumerate() {
            let focused = proof.focus_execution_if_arm(&record, take_left)?;
            let next = driven!(advance_execution_match_group(
                focused,
                plan,
                arms,
                group,
                certificates,
                expansion_capture.as_deref_mut(),
                proof_site,
                owning_source_index,
                depth,
                split_depth + 1,
                rejoins,
                ensuring,
            ));
            completed[side] = next.is_at_function_exit();
            proof = next;
        }
        if completed == [true, true] && ensuring.is_none() {
            return Ok(Ok(proof.join_focused_execution_if_terminal(&record)?));
        }
        // With an interface, each split of the constructor family rejoins
        // through it: the halves of a wider `match` are joined pairwise, and
        // a half that was itself joined already holds the interface's state.
        if let Some(assertions) = ensuring {
            if completed != [false, false] {
                return Err(ClickError::new(
                    "an arm of this proof `match` reached function exit, so its `ensuring` interface has nothing to rejoin",
                ));
            }
            return Ok(Ok(proof.join_focused_execution_if_interface(
                &record,
                assertions.to_vec(),
            )?));
        }
        let Some(joined) = proof.try_join_focused_execution_if(&record)? else {
            return Err(ClickError::new(
                "the arms of this proof `match` do not rejoin: with tactics written after the `match`, every live arm must end at the same program point in the same state",
            ).with_proof_refusal(ProofRefusal::Tactic).with_failed_tactic("match"));
        };
        return Ok(Ok(joined));
    };
    let index = *index;
    let proof = proof.enter_execution_match_arm(plan, index)?;
    let marker = proof.checkpoint();
    let proof = driven!(advance_focused_execution_region(
        proof,
        None,
        &arms[index],
        expansion_capture,
        proof_site,
        owning_source_index,
        depth + 1,
    ));
    if !rejoins && !proof.is_at_function_exit() {
        return Err(ClickError::new(
            "each proof `match` arm must reach function exit",
        ));
    }
    certificates[index] = Some(proof.execution_match_arm_certificate(&marker)?);
    proof.record_execution_match_arm_trace(plan, index, &marker);
    // An arm that finished the function leaves its binders to the closers
    // written after the `match`, which close its path.
    if proof.is_at_function_exit() {
        return Ok(Ok(proof.leave_terminal_execution_match_arm(plan)?));
    }
    Ok(Ok(proof.leave_execution_match_arm(plan)?))
}

fn advance_focused_execution_region<'a>(
    proof: Proof<'a>,
    enclosing_record: Option<&ExecutionSplit<'a>>,
    region: &InternalProofNode,
    expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
    owning_source_index: usize,
    depth: usize,
) -> Driven<Proof<'a>> {
    advance_focused_execution_region_with_branch_continuation(
        proof,
        enclosing_record,
        region,
        expansion_capture,
        proof_site,
        owning_source_index,
        depth,
        None,
        false,
    )
}

/// Discharges every retained terminal-case join through its original Proof
/// lineage. No case can escape without reaching exit and checking its join.
fn join_terminal_execution_cases<'a>(
    mut proof: Proof<'a>,
    cases: &mut Vec<(
        super::super::proof_object::ExecutionProofCaseSplit<'a>,
        Proof<'a>,
    )>,
) -> Driven<Proof<'a>> {
    while let Some((record, owner)) = cases.pop() {
        if !proof.is_at_function_exit() {
            return decline_short_of_exit();
        }
        proof = proof
            .join_focused_execution_if_terminal(&record)?
            .restore_execution_tactic_attribution(&owner)?;
    }
    Ok(Ok(proof))
}

/// A mixed call-outcome join needs the enclosing branch's source continuation
/// while its normal sibling is still open. The split record already owns the
/// checked frontier transition; this parameter only identifies the proof
/// region to run after that transition.
///
/// `depth` is the nesting depth of the region this cursor is in. Descending
/// into an arm, a `then`/`else` case, or a call outcome opens a region one
/// level deeper. A node's continuation is the rest of the region the node
/// sits in, so it runs at the same depth; this loop walks it iteratively, so
/// a long run of sibling regions reserves no Rust stack. The only recursion is
/// into a nested region (charged a level) or into the rest of the proof run
/// inside a continuing arm (charged at that arm's level). Once a first case
/// has exited, its remaining else case is walked here with a retained join
/// record, so a sequence of early returns does not grow the Rust stack.
fn advance_focused_execution_region_with_branch_continuation<'a>(
    mut proof: Proof<'a>,
    enclosing_record: Option<&ExecutionSplit<'a>>,
    region: &InternalProofNode,
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
    owning_source_index: usize,
    depth: usize,
    branch_continuation: Option<&InternalProofNode>,
    ends_at_join: bool,
) -> Driven<Proof<'a>> {
    #[cfg(test)]
    DEEPEST_REGION_DEPTH.with(|deepest| deepest.set(deepest.get().max(depth)));
    if depth >= MAX_CHECKED_EXECUTION_REGION_DEPTH {
        return decline_region_depth();
    }
    let mut region = region;
    let mut branch_continuation = branch_continuation;
    let mut terminal_cases: Vec<(
        super::super::proof_object::ExecutionProofCaseSplit<'a>,
        Proof<'a>,
    )> = Vec::new();
    'regions: loop {
        match region {
            InternalProofNode::Match {
                index,
                source_index,
                proof_match,
                arms,
                continuation,
                ..
            } => {
                // Like every other structure in this region, the match is
                // attributed to its own tactic only while it runs. Its
                // result continues the enclosing region (an enclosing
                // branch arm, case, or outcome), so it carries the owner's
                // exact diagnostic context back out: the enclosing join and
                // certificate checkpoint compare that context by identity.
                if proof.is_at_function_exit()
                    && let Ok(deferred) = defer_post_execution_match(
                        proof.clone(),
                        *index,
                        *source_index,
                        proof_match,
                        arms,
                        continuation,
                        expansion_capture.as_deref_mut(),
                    )?
                {
                    proof = deferred;
                    region = continuation;
                    branch_continuation = None;
                    continue;
                }
                let owner = proof.clone();
                let at_match = proof.with_execution_tactic_index(*index)?;
                let matched = driven!(advance_execution_match(
                    at_match,
                    proof_match,
                    *source_index,
                    arms,
                    continuation,
                    expansion_capture.as_deref_mut(),
                    proof_site,
                    owning_source_index,
                    depth,
                ));
                // A rejoined `match` leaves its continuation to run once.
                proof = matched.restore_execution_tactic_attribution(&owner)?;
                region = continuation;
                branch_continuation = None;
            }
            InternalProofNode::Done => {
                return join_terminal_execution_cases(proof, &mut terminal_cases);
            }
            InternalProofNode::Linear {
                tactics,
                continuation,
            } => {
                let advanced = driven!(advance_focused_execution_arm(
                    proof,
                    tactics,
                    expansion_capture.as_deref_mut(),
                    proof_site,
                    owning_source_index,
                ));
                // The linear run continues this region, and so does the
                // control node it ends at: only that node's arms nest. The
                // enclosing branch's continuation is still the one a mixed
                // call-outcome join inside this region runs.
                proof = advanced;
                region = continuation;
            }
            InternalProofNode::Branch {
                index,
                source_index,
                ensuring,
                then_branch,
                else_branch,
                continuation,
            } => {
                let owner = proof.clone();
                let (nested, _, certificate, consumed_continuation) =
                    driven!(try_advance_checked_execution_branch(
                        proof.at_source_tactic(*source_index),
                        *index,
                        ensuring,
                        then_branch,
                        else_branch,
                        continuation,
                        expansion_capture.as_deref_mut(),
                        proof_site,
                        owning_source_index,
                        depth,
                    ));
                proof = nested.restore_execution_tactic_attribution(&owner)?;
                if let Some(site) = proof_site
                    && capture_selects_source(expansion_capture.as_deref(), site, *source_index)
                {
                    record_proof_site_tactic_expansion(
                        expansion_capture.as_deref_mut(),
                        site,
                        *source_index,
                        &certificate
                            .expect("an expansion request retains the nested branch certificate")
                            .to_proof_tactics(),
                    );
                }
                if consumed_continuation {
                    return join_terminal_execution_cases(proof, &mut terminal_cases);
                }
                region = continuation;
                branch_continuation = None;
            }
            InternalProofNode::Open {
                index,
                source_index,
                resource,
                body,
                continuation,
            } => {
                if proof.is_at_function_exit() {
                    let open = post_execution_open(&proof, *index, *source_index, resource, body)?;
                    proof = proof.defer_post_execution_source_tactic(
                        *index,
                        *source_index,
                        open,
                        expansion_capture.as_deref_mut(),
                    )?;
                    region = continuation;
                    branch_continuation = None;
                    continue;
                }
                let owner = proof.clone();
                let opened = proof.with_execution_tactic_index(*index)?;
                let scope = opened.begin_open(resource.clone(), *source_index)?;
                let scope = driven!(advance_checked_open_scope(
                    scope,
                    body,
                    expansion_capture.as_deref_mut(),
                    proof_site,
                    owning_source_index,
                ));
                proof = scope
                    .driver()
                    .complete_scope()?
                    .restore_execution_tactic_attribution(&owner)?;
                region = continuation;
                branch_continuation = None;
            }
            InternalProofNode::CallOutcomes {
                index,
                payload_bindings,
                returned_branch,
                threw_branch,
                continuation,
                ..
            } => {
                if proof.is_at_function_exit() {
                    return Err(proof.with_execution_tactic_index(*index)?.step_error(
                        "`outcomes` requires a maybe-throwing call at the execution frontier",
                    ));
                }
                let owner = proof.clone();
                let at_outcomes = proof.with_execution_tactic_index(*index)?;
                let Some((split, record)) =
                    at_outcomes.split_focused_call_outcomes(payload_bindings.clone())?
                else {
                    return decline();
                };
                let mut advanced = split;
                for (take_returned, region) in [
                    (true, returned_branch.as_ref()),
                    (false, threw_branch.as_ref()),
                ] {
                    let focused =
                        advanced.focus_call_outcome_arm(&record, take_returned, &owner)?;
                    let next = driven!(advance_focused_execution_region(
                        focused,
                        Some(&record),
                        region,
                        expansion_capture.as_deref_mut(),
                        proof_site,
                        owning_source_index,
                        depth + 1,
                    ));
                    advanced = next.leave_call_outcome_arm(&owner);
                }
                let returned_exit = advanced.arm_at_function_exit(&record, true);
                let threw_exit = advanced.arm_at_function_exit(&record, false);
                let mixed = returned_exit != threw_exit;
                if mixed {
                    let (Some(enclosing_record), Some(branch_continuation)) =
                        (enclosing_record, branch_continuation)
                    else {
                        return decline();
                    };
                    if !matches!(continuation.as_ref(), InternalProofNode::Done) {
                        return decline();
                    }
                    let continuing = advanced.focus_split_arm(&record, !returned_exit)?;
                    if !continuing.is_at_region_boundary() {
                        return decline();
                    }
                    let continuing =
                        continuing.continue_arm_into_parent_frontier(enclosing_record)?;
                    // The enclosing branch's continuation runs inside the
                    // continuing outcome, so it is charged at that
                    // outcome's level: this is a genuine nested descent.
                    let continued = driven!(advance_focused_execution_region(
                        continuing,
                        Some(enclosing_record),
                        branch_continuation,
                        expansion_capture.as_deref_mut(),
                        proof_site,
                        owning_source_index,
                        depth + 1,
                    ));
                    advanced = continued;
                }
                if !advanced.is_at_function_exit() {
                    return decline();
                }
                let joined = advanced.join_focused_call_outcomes_terminal(&record)?;
                proof = joined.restore_execution_tactic_attribution(&owner)?;
                if mixed {
                    return join_terminal_execution_cases(proof, &mut terminal_cases);
                }
                region = continuation;
                branch_continuation = None;
            }
            InternalProofNode::Cases {
                index,
                source_index,
                disjunction,
                then_branch,
                else_branch,
                continuation,
            } => {
                if proof.is_at_function_exit() {
                    proof = driven!(defer_post_execution_case_split(
                        proof,
                        *index,
                        *source_index,
                        disjunction,
                        true,
                        None,
                        then_branch,
                        else_branch,
                        continuation,
                        expansion_capture.as_deref_mut(),
                    ));
                    region = continuation;
                    branch_continuation = None;
                    continue;
                }
                let owner = proof.clone();
                let mut proof_at_cases = proof.with_execution_tactic_index(*index)?;
                if !matches!(continuation.as_ref(), InternalProofNode::Done) {
                    proof_at_cases = proof_at_cases.prepare_entry_interface()?;
                }
                proof_at_cases = proof_at_cases
                    .driver()
                    .prove_cases_disjunction(disjunction)?;
                let (split, record) =
                    proof_at_cases.split_focused_execution_disjunction(disjunction.clone())?;
                let (joined, consumed_continuation) = driven!(advance_case_split_arms(
                    split,
                    &record,
                    &None,
                    then_branch,
                    else_branch,
                    continuation,
                    false,
                    enclosing_record,
                    expansion_capture.as_deref_mut(),
                    proof_site,
                    owning_source_index,
                    *source_index,
                    depth,
                ));
                proof = joined.restore_execution_tactic_attribution(&owner)?;
                if consumed_continuation {
                    return join_terminal_execution_cases(proof, &mut terminal_cases);
                }
                region = continuation;
                branch_continuation = None;
                continue;
            }
            InternalProofNode::If {
                index,
                source_index,
                condition,
                ensuring,
                then_branch,
                else_branch,
                continuation,
                ..
            } => {
                if proof.is_at_function_exit() {
                    proof = driven!(defer_post_execution_case_split(
                        proof,
                        *index,
                        *source_index,
                        condition,
                        false,
                        ensuring.as_deref(),
                        then_branch,
                        else_branch,
                        continuation,
                        expansion_capture.as_deref_mut(),
                    ));
                    region = continuation;
                    branch_continuation = None;
                    continue;
                }
                let owner = proof.clone();
                let proof_at_if = proof
                    .with_execution_tactic_index(*index)?
                    // The split's trace and refusals name the `if` itself, so
                    // `--trace-to` a line in one arm finds that arm.
                    .at_source_tactic(*source_index);
                if expanded_execution_if_has_pruned_arm(then_branch, else_branch)
                    && expanded_execution_if_steps(then_branch, else_branch).is_none()
                    && proof_at_if.frontier_is_execution_branch(condition)?
                {
                    let (split, record) = proof_at_if.split_focused_execution_branch()?;
                    if ensuring.is_none()
                        && matches!(continuation.as_ref(), InternalProofNode::Done)
                        && let Some(take_then) = record.sole_feasible_arm()
                    {
                        let arm = if take_then { then_branch } else { else_branch };
                        let (focused, remaining, arm_continuation) =
                            checked_expanded_execution_arm_prefix(
                                &split, &record, take_then, condition, arm,
                            )?;
                        if focused.is_at_region_boundary() {
                            let joined = focused
                                .join_focused_execution_split(&record, false, None)?
                                .restore_execution_tactic_attribution(&owner)?;
                            let next = driven!(advance_focused_execution_arm(
                                joined,
                                remaining,
                                expansion_capture.as_deref_mut(),
                                proof_site,
                                owning_source_index,
                            ));
                            proof = next;
                            region = arm_continuation;
                            continue;
                        }
                    }
                    let arms = driven!(advance_checked_branch_arms(
                        split,
                        &record,
                        Some(condition),
                        ensuring,
                        then_branch,
                        else_branch,
                        continuation,
                        expansion_capture.as_deref_mut(),
                        proof_site,
                        owning_source_index,
                        depth,
                    ));
                    proof = arms
                        .advanced
                        .join_focused_execution_split(&record, arms.empty, arms.join_interface)?
                        .restore_execution_tactic_attribution(&owner)?;
                    proof.note_trace_join_continuation_arm(arms.continuation_arm);
                    region = if arms.consumed_continuation {
                        &DONE_PROOF
                    } else {
                        continuation
                    };
                    branch_continuation = None;
                    continue;
                }
                if let Some((then_steps, else_steps)) =
                    expanded_execution_if_steps(then_branch, else_branch)
                    && proof_at_if.frontier_is_execution_branch(condition)?
                {
                    proof = proof_at_if
                        .driver()
                        .apply_expanded_execution_if(condition, &then_steps, &else_steps)?
                        .restore_execution_tactic_attribution(&owner)?;
                    region = continuation;
                    branch_continuation = None;
                    continue;
                }
                let arm_steps = match (
                    execution_region_leading_tactic(then_branch),
                    execution_region_leading_tactic(else_branch),
                ) {
                    (Some(then_tactic), Some(else_tactic)) => match (
                        source_successor_if_arm_step(then_tactic),
                        source_successor_if_arm_step(else_tactic),
                    ) {
                        (Some(then_step), Some(else_step)) => Some([then_step, else_step]),
                        _ => None,
                    },
                    _ => None,
                };
                // An `ensuring` interface joins the arms where they end, so
                // their leading steps are not folded into the split.
                let arm_steps = arm_steps.filter(|_| ensuring.is_none());
                let product = if let Some(arm_steps) = arm_steps.as_ref() {
                    let product = proof_at_if.driver().try_split_source_successor_if(
                        condition,
                        [
                            (arm_steps[0].0, arm_steps[0].1),
                            (arm_steps[1].0, arm_steps[1].1),
                        ],
                    )?;
                    if product.is_some() {
                        record_source_successor_smart_expansions(
                            arm_steps,
                            expansion_capture.as_deref_mut(),
                            proof_site,
                            owning_source_index,
                        );
                    }
                    product
                } else {
                    None
                };
                let consumed_leading_steps = product.is_some();
                let (split, record) = if let Some(split) = product {
                    split
                } else {
                    proof_at_if.split_focused_execution_if(condition.clone())?
                };
                // As at the top level: each arm runs once, two live arms
                // must rejoin, and a lone live arm owns the continuation. A
                // proof `if` that ends a region ending at a join, such as a
                // `branch` arm, rejoins where its cases end: the region's
                // end is that join, not the function exit.
                let must_rejoin = ensuring.is_some();
                if !consumed_leading_steps {
                    let refuted = driven!(try_advance_refuted_case_split(
                        &split,
                        &record,
                        [then_branch, else_branch],
                        ensuring.as_deref(),
                        enclosing_record,
                        expansion_capture.as_deref_mut(),
                        proof_site,
                        owning_source_index,
                        depth,
                        ends_at_join || !matches!(continuation.as_ref(), InternalProofNode::Done),
                    ));
                    if let Some(joined) = refuted {
                        proof = joined.restore_execution_tactic_attribution(&owner)?;
                        region = continuation;
                        branch_continuation = None;
                        continue;
                    }
                }
                if must_rejoin
                    || ends_at_join
                    || !matches!(continuation.as_ref(), InternalProofNode::Done)
                {
                    let mut advanced = split;
                    let mut live = [false, false];
                    for (take_then, branch) in
                        [(true, then_branch.as_ref()), (false, else_branch.as_ref())]
                    {
                        let focused = advanced.focus_execution_if_arm(&record, take_then)?;
                        let next = if consumed_leading_steps {
                            advance_focused_execution_region_after_leading_tactic(
                                focused,
                                enclosing_record,
                                branch,
                                expansion_capture.as_deref_mut(),
                                proof_site,
                                owning_source_index,
                                depth + 1,
                            )?
                        } else {
                            advance_focused_execution_region_with_branch_continuation(
                                focused,
                                enclosing_record,
                                branch,
                                expansion_capture.as_deref_mut(),
                                proof_site,
                                owning_source_index,
                                depth + 1,
                                None,
                                true,
                            )?
                        };
                        let next = match next {
                            Ok(next) => next,
                            Err(decline) => return Ok(Err(decline)),
                        };
                        live[usize::from(!take_then)] = !next.is_at_function_exit();
                        advanced = next;
                    }
                    if live == [true, true] {
                        let joined = match ensuring {
                            Some(assertions) => advanced
                                .join_focused_execution_if_interface(&record, assertions.clone())?,
                            None => advanced
                                .try_join_focused_execution_if(&record)?
                                .ok_or_else(|| {
                                    proof_if_arms_do_not_rejoin(
                                        !ends_at_join && ends_after_split(continuation),
                                    )
                                })?,
                        };
                        proof = joined.restore_execution_tactic_attribution(&owner)?;
                        region = continuation;
                        branch_continuation = None;
                        continue;
                    }
                    if must_rejoin {
                        return Err(if_ensuring_arm_did_not_end());
                    }
                    if live != [false, false] {
                        // The other case reached function exit, so the lone
                        // live case owns the continuation. As for a completed
                        // first case above, retain only the checked join
                        // record and run the continuation in this cursor: a
                        // run of sequential early returns written one after
                        // another does not nest regions.
                        proof = if live[0] {
                            advanced.focus_execution_if_arm(&record, true)?
                        } else {
                            advanced
                        };
                        terminal_cases.push((record, owner));
                        region = continuation;
                        branch_continuation = None;
                        continue;
                    }
                    proof = advanced
                        .join_focused_execution_if_terminal(&record)?
                        .restore_execution_tactic_attribution(&owner)?;
                    region = continuation;
                    branch_continuation = None;
                    continue;
                }
                let mut advanced = split;
                let mut consumed_continuation = false;
                for (take_then, branch) in
                    [(true, then_branch.as_ref()), (false, else_branch.as_ref())]
                {
                    let focused = advanced.focus_execution_if_arm(&record, take_then)?;
                    let next = if consumed_leading_steps {
                        advance_focused_execution_region_after_leading_tactic(
                            focused,
                            enclosing_record,
                            branch,
                            expansion_capture.as_deref_mut(),
                            proof_site,
                            owning_source_index,
                            depth + 1,
                        )?
                    } else {
                        advance_focused_execution_region(
                            focused,
                            enclosing_record,
                            branch,
                            expansion_capture.as_deref_mut(),
                            proof_site,
                            owning_source_index,
                            depth + 1,
                        )?
                    };
                    let mut next = match next {
                        Ok(next) => next,
                        Err(decline) => return Ok(Err(decline)),
                    };
                    if take_then
                        && next.is_at_function_exit()
                        && ensuring.is_none()
                        && matches!(continuation.as_ref(), InternalProofNode::Done)
                    {
                        // A completed first case needs only its checked join
                        // record. Run the remaining case in this cursor, then
                        // join all terminal cases in reverse order at Done.
                        proof = next.focus_execution_if_arm(&record, false)?;
                        region = else_branch;
                        if consumed_leading_steps {
                            let InternalProofNode::Linear {
                                tactics,
                                continuation,
                            } = region
                            else {
                                return decline();
                            };
                            let advanced = driven!(advance_focused_execution_arm(
                                proof,
                                &tactics[1..],
                                expansion_capture.as_deref_mut(),
                                proof_site,
                                owning_source_index,
                            ));
                            proof = advanced;
                            region = continuation;
                        }
                        terminal_cases.push((record, owner));
                        branch_continuation = None;
                        continue 'regions;
                    }
                    // Case split, as at the top level: a case whose arm ends
                    // short of function exit runs the shared continuation to
                    // its own exit. That continuation runs inside the case,
                    // so it is charged at the case's level.
                    if !next.is_at_function_exit()
                        && !matches!(continuation.as_ref(), InternalProofNode::Done)
                    {
                        let continued = driven!(advance_focused_execution_region(
                            next,
                            enclosing_record,
                            continuation,
                            expansion_capture.as_deref_mut(),
                            proof_site,
                            owning_source_index,
                            depth + 1,
                        ));
                        next = continued;
                        consumed_continuation = true;
                    }
                    if !next.is_at_function_exit() {
                        return decline_short_of_exit();
                    }
                    advanced = next;
                }
                proof = advanced
                    .join_focused_execution_if_terminal(&record)?
                    .restore_execution_tactic_attribution(&owner)?;
                if consumed_continuation {
                    return join_terminal_execution_cases(proof, &mut terminal_cases);
                }
                region = continuation;
                branch_continuation = None;
            }
        }
    }
}

/// Applies one supported two-arm execution branch entirely through the typed
/// Proof split/join API. Callers may choose different source-driving
/// boundaries, but branch entry, arm advancement, interface checking, and the
/// semantic join have one implementation.
/// The fourth result reports that the branch's continuation was consumed:
/// one arm returned and the other ran the continuation to function exit
/// inside the arm, so the caller must not run the continuation again.
fn try_advance_checked_execution_branch<'a>(
    proof: Proof<'a>,
    tactic_index: usize,
    ensuring: &Option<Vec<ProofAssertion>>,
    then_branch: &InternalProofNode,
    else_branch: &InternalProofNode,
    continuation: &InternalProofNode,
    expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
    owning_source_index: usize,
    depth: usize,
) -> Driven<(Proof<'a>, bool, Option<ProofCertificate>, bool)> {
    if depth >= MAX_CHECKED_EXECUTION_REGION_DEPTH {
        return decline_region_depth();
    }
    let at_branch = proof.with_execution_tactic_index(tactic_index)?;
    let checkpoint = at_branch.checkpoint();
    let (split, record) = at_branch.split_focused_execution_branch()?;
    let has_sole_feasible_arm = record.sole_feasible_arm().is_some();
    let arms = driven!(advance_checked_branch_arms(
        split,
        &record,
        None,
        ensuring,
        then_branch,
        else_branch,
        continuation,
        expansion_capture,
        proof_site,
        owning_source_index,
        depth,
    ));
    // The arms share one proof and may leave it attributed to a nested
    // structure's tactic. Restore the branch's own attribution after the
    // join, as the neighbouring `if` and call-outcome joins do, so the
    // certificate checkpoint and the caller see the branch's exact context.
    let joined =
        arms.advanced
            .join_focused_execution_split(&record, arms.empty, arms.join_interface)?;
    joined.note_trace_join_continuation_arm(arms.continuation_arm);
    let joined = joined.restore_execution_tactic_attribution(&at_branch)?;
    let certificate = proof_site
        .is_some()
        .then(|| joined.certificate_since(&checkpoint))
        .transpose()?;
    Ok(Ok((
        joined,
        has_sole_feasible_arm,
        certificate,
        arms.consumed_continuation,
    )))
}

/// The result of advancing a branch's two arms, ready for the caller to join
/// on its own target (`Proof` or `ProofScope`).
struct AdvancedBranchArms<'a> {
    advanced: Proof<'a>,
    consumed_continuation: bool,
    continuation_arm: Option<usize>,
    empty: bool,
    join_interface: Option<Vec<ProofAssertion>>,
}

/// The single branch arm-advancing law, shared by the `Proof` branch driver
/// and the open-scope branch handler: it advances both feasible arms, runs
/// the shared continuation inside a continuing arm when the arms end
/// differently (checking any `ensuring` interface there), and reports whether
/// the continuation was consumed. The caller splits and joins on its own
/// target; only the arm interiors, which are always `Proof`s, live here.
#[allow(clippy::too_many_arguments)]
fn advance_checked_branch_arms<'a>(
    split: Proof<'a>,
    record: &ExecutionSplit<'a>,
    expanded_condition: Option<&SyntaxProposition>,
    ensuring: &Option<Vec<ProofAssertion>>,
    then_branch: &InternalProofNode,
    else_branch: &InternalProofNode,
    continuation: &InternalProofNode,
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
    owning_source_index: usize,
    depth: usize,
) -> Driven<AdvancedBranchArms<'a>> {
    if ensuring
        .as_ref()
        .is_some_and(|_| !record.supports_interface_branch())
    {
        return decline();
    }
    let has_sole_feasible_arm = record.sole_feasible_arm().is_some();
    let mut advanced = split;
    for (take_then, region) in [(true, then_branch), (false, else_branch)] {
        if record.arm_id(take_then).is_none() {
            // The kernel proved this C path infeasible, so the arm's tactics
            // never run. A selected smart tactic written there contributes no
            // checked operation to any retained certificate; tell expansion
            // so it answers with the empty rewrite instead of reporting the
            // occurrence as missing.
            note_dropped_execution_region(expansion_capture.as_deref_mut(), proof_site, region);
            continue;
        }
        let next = if let Some(condition) = expanded_condition {
            let (focused, remaining, arm_continuation) = checked_expanded_execution_arm_prefix(
                &advanced, record, take_then, condition, region,
            )?;
            let after_linear = driven!(advance_focused_execution_arm(
                focused,
                remaining,
                expansion_capture.as_deref_mut(),
                proof_site,
                owning_source_index,
            ));
            advance_focused_execution_region_with_branch_continuation(
                after_linear,
                Some(record),
                arm_continuation,
                expansion_capture.as_deref_mut(),
                proof_site,
                owning_source_index,
                depth + 1,
                Some(continuation),
                true,
            )?
        } else {
            advance_focused_execution_region_with_branch_continuation(
                advanced.focus_split_arm(record, take_then)?,
                Some(record),
                region,
                expansion_capture.as_deref_mut(),
                proof_site,
                owning_source_index,
                depth + 1,
                Some(continuation),
                true,
            )?
        };
        let next = match next {
            Ok(next) => next,
            Err(decline) => return Ok(Err(decline)),
        };
        advanced = next;
    }
    // A `branch` joins its arms at the `if`'s continuation. An arm that left
    // the loop through `break`, or jumped to the back edge through
    // `continue`, is not there to be joined: its path ends at the loop rule,
    // not at the statement after the `if`. Joining the arms anyway would
    // export one successor for two paths that go to different places, so the
    // rule refuses and names the spelling that keeps them apart.
    for (name, take_then) in [("then", true), ("else", false)] {
        let control = advanced.arm_loop_control(record, take_then);
        if control != LoopControlExit::BodyEnd {
            let keyword = if control == LoopControlExit::TestFalse {
                "path leaves the loop at its test"
            } else if control.is_exit() {
                "`break` leaves the loop"
            } else {
                "`continue` reaches the loop's back edge"
            };
            return Err(ClickError::new(format!(
                "the {name} `branch` arm's {keyword}, so the arms have no common successor to join; write this case as a proof `if` on the C condition, whose arms each reach the loop rule on their own"
            )).with_proof_refusal(ProofRefusal::Tactic).with_failed_tactic("branch"));
        }
    }
    let mut consumed_continuation = false;
    let mut continuation_arm = None;
    if !has_sole_feasible_arm {
        let then_exit = advanced.arm_at_function_exit(record, true);
        let else_exit = advanced.arm_at_function_exit(record, false);
        if then_exit != else_exit {
            // One arm returned. The other continues past its boundary into
            // the shared continuation, which it runs to function exit; the
            // two arms then join terminally. An `ensuring` interface is
            // checked on the continuing arm at its boundary; the retained
            // state is the arm's own, which is stronger than the interface.
            let continuing = advanced.focus_split_arm(record, !then_exit)?;
            if let Some(assertions) = ensuring
                && !continuing.interface_facts_established(assertions)?
            {
                return decline();
            }
            let continuing = continuing.continue_arm_into_parent_frontier(record)?;
            let next = driven!(advance_focused_execution_region(
                continuing,
                Some(record),
                continuation,
                expansion_capture,
                proof_site,
                owning_source_index,
                depth + 1,
            ));
            if !next.is_at_function_exit() {
                return decline_short_of_exit();
            }
            advanced = next;
            consumed_continuation = true;
            continuation_arm = Some(usize::from(then_exit));
        }
    }
    let empty = checked_execution_region_is_empty(then_branch)
        && checked_execution_region_is_empty(else_branch);
    let join_interface = if consumed_continuation {
        None
    } else {
        ensuring.clone()
    };
    Ok(Ok(AdvancedBranchArms {
        advanced,
        consumed_continuation,
        continuation_arm,
        empty,
        join_interface,
    }))
}

/// The simple execution steps an expanded arm spells: its simple tactics,
/// and a nested proof `if` whose arms each spell simple steps that advance
/// execution (a case split inside the arm, or a nested C branch). Anything
/// else, including an `if` after the path has exited, is left to the
/// structural driver.
fn arm_execution_steps(node: &InternalProofNode, depth: usize) -> Option<Vec<ProofStep>> {
    if depth >= MAX_CHECKED_EXECUTION_REGION_DEPTH {
        return None;
    }
    let mut steps = Vec::new();
    let mut node = node;
    loop {
        match node {
            InternalProofNode::Done => return Some(steps),
            InternalProofNode::Linear {
                tactics,
                continuation,
            } => {
                for indexed in tactics {
                    steps.push(SourceContext::ExecutionFrontier.leaf_step(&indexed.tactic)?);
                }
                node = continuation;
            }
            InternalProofNode::If {
                condition,
                then_branch,
                else_branch,
                continuation,
                ..
            } => {
                let then_steps = arm_execution_steps(then_branch, depth + 1)?;
                let else_steps = arm_execution_steps(else_branch, depth + 1)?;
                if !steps_advance_execution(&then_steps) || !steps_advance_execution(&else_steps) {
                    return None;
                }
                steps.push(ProofStep::If {
                    condition: condition.clone(),
                    ensuring: None,
                    then_proof: Box::new(ProofCertificate::from_steps(then_steps).ok()?),
                    else_proof: Box::new(ProofCertificate::from_steps(else_steps).ok()?),
                });
                node = continuation;
            }
            _ => return None,
        }
    }
}

fn steps_advance_execution(steps: &[ProofStep]) -> bool {
    steps.iter().any(|step| match step {
        ProofStep::Step => true,
        ProofStep::If {
            then_proof,
            else_proof,
            ..
        } => {
            steps_advance_execution(then_proof.steps())
                && steps_advance_execution(else_proof.steps())
        }
        _ => false,
    })
}

/// An omitted arm is the source form retained by a checked, decided C
/// branch. Two live source cases keep the ordinary iterative proof-if driver.
fn expanded_execution_if_has_pruned_arm(
    then_branch: &InternalProofNode,
    else_branch: &InternalProofNode,
) -> bool {
    (checked_execution_region_is_empty(then_branch)
        || checked_execution_region_is_empty(else_branch))
        && [then_branch, else_branch].iter().any(|arm| {
            execution_region_leading_tactic(arm)
                .is_some_and(|indexed| matches!(indexed.tactic, ProofTactic::Step))
        })
}

/// Borrow the written body after the exact entry operations already checked
/// by the C split. The split remains the sole authority for selecting an arm.
fn checked_expanded_execution_arm_prefix<'a, 'r>(
    proof: &Proof<'a>,
    record: &ExecutionSplit<'a>,
    take_then: bool,
    condition: &SyntaxProposition,
    region: &'r InternalProofNode,
) -> Result<(Proof<'a>, &'r [IndexedTactic], &'r InternalProofNode), ClickError> {
    let expected =
        proof.checked_expanded_execution_arm_entry_steps(record, take_then, Some(condition))?;
    let InternalProofNode::Linear {
        tactics,
        continuation,
    } = region
    else {
        return Err(
            proof.step_error("expanded execution arm is missing its checked branch-entry steps")
        );
    };
    if tactics.len() < expected.len()
        || !tactics[..expected.len()]
            .iter()
            .all(|indexed| matches!(indexed.tactic, ProofTactic::Step))
    {
        return Err(
            proof.step_error("expanded execution arm is missing its checked branch-entry steps")
        );
    }
    Ok((
        proof.focus_split_arm(record, take_then)?,
        &tactics[expected.len()..],
        continuation,
    ))
}

fn expanded_execution_if_steps(
    then_branch: &InternalProofNode,
    else_branch: &InternalProofNode,
) -> Option<(Vec<ProofStep>, Vec<ProofStep>)> {
    let then_steps = arm_execution_steps(then_branch, 0)?;
    let else_steps = arm_execution_steps(else_branch, 0)?;
    (expanded_execution_arm_supported(&then_steps)
        && expanded_execution_arm_supported(&else_steps)
        && !(then_steps.is_empty() && else_steps.is_empty()))
    .then_some((then_steps, else_steps))
}
/// Advances a linear resource scope one checked node at a time. A nested
/// `have` is joined back through the scope API, so its selected theorem steps
/// and its published proposition are retained by the same immutable proof.
fn advance_linear_open_scope<'a>(
    mut scope: ProofScope<'a>,
    tactics: &[IndexedTactic],
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
    owning_source_index: usize,
) -> Driven<ProofScope<'a>> {
    for indexed in tactics {
        // A back-edge closure plans and retains an invariant-body proof, which
        // this linear resource scope has no way to open. Decline rather than
        // record a bare closure request the certificate cannot spell.
        if closes_loop_invariants(&indexed.tactic) {
            return decline();
        }
        // After execution reached function exit inside the scope, an ordered
        // outcome operation (`solve`, `fold`, a `have` naming `result`, ...)
        // is deferred on the scope body and follows the scope's join.
        //
        // A `have` written here is such an operation: only the outcome binds
        // `result`, so lowering it at the scope's frontier would produce no
        // path at all for the very proposition a smart tactic's expansion
        // renders. The flat driver already defers a post-exit `have`; the
        // scope driver defers the same tactic through its own body.
        if scope.is_at_function_exit()
            && let Some(post_tactic) = flat_post_execution_tactic(&indexed.tactic)
        {
            scope = scope.defer_post_execution_source_tactic(
                indexed.index,
                indexed.source_index,
                post_tactic,
                expansion_capture.as_deref_mut(),
            )?;
            continue;
        }
        if let Some(step) = SourceContext::ExecutionFrontier.leaf_step(&indexed.tactic) {
            scope = scope.driver().apply_step(step)?;
            continue;
        }
        if matches!(indexed.tactic, ProofTactic::StepProved { .. }) {
            let body = scope.body().with_execution_tactic_index(indexed.index)?;
            let stepped = driven!(apply_frontier_source_tactic(
                body,
                indexed,
                expansion_capture.as_deref_mut(),
                proof_site,
                owning_source_index,
                Some(scope.body().claim_label()),
            ));
            scope = scope.join_nested_result(stepped)?;
            continue;
        }
        if let ProofTactic::ApplyFact(fact) = &indexed.tactic {
            let checkpoint = scope.checkpoint();
            let Some(applied) = scope.driver().apply_fact_application(fact)? else {
                return decline();
            };
            scope = applied;
            if indexed.source_index != owning_source_index
                && let Some(site) = proof_site
            {
                let certificate = scope.certificate_since(&checkpoint)?;
                record_proof_site_tactic_expansion(
                    expansion_capture.as_deref_mut(),
                    site,
                    indexed.source_index,
                    &certificate.to_proof_tactics(),
                );
            }
            continue;
        }
        if let ProofTactic::ApplyTheorem(application) = &indexed.tactic {
            let checkpoint = scope.checkpoint();
            let Some(applied) = scope.driver().apply_theorem_application(application)? else {
                return decline();
            };
            scope = applied;
            if indexed.source_index != owning_source_index
                && let Some(site) = proof_site
            {
                let certificate = scope.certificate_since(&checkpoint)?;
                record_proof_site_tactic_expansion(
                    expansion_capture.as_deref_mut(),
                    site,
                    indexed.source_index,
                    &certificate.to_proof_tactics(),
                );
            }
            continue;
        }
        if matches!(indexed.tactic, ProofTactic::SmartExecute) {
            let checkpoint = scope.checkpoint();
            let Some(executed) = (scope).driver().try_execute_to_exit()? else {
                return decline();
            };
            scope = executed;
            if indexed.source_index != owning_source_index
                && let Some(site) = proof_site
            {
                let certificate = scope.certificate_since(&checkpoint)?;
                record_proof_site_tactic_expansion(
                    expansion_capture.as_deref_mut(),
                    site,
                    indexed.source_index,
                    &certificate.to_proof_tactics(),
                );
            }
            continue;
        }
        if let ProofTactic::ExecuteUntil(point) = &indexed.tactic {
            let checkpoint = scope.checkpoint();
            let Some(executed) = (scope).driver().try_execute_until(point)? else {
                return decline();
            };
            scope = executed;
            if indexed.source_index != owning_source_index
                && let Some(site) = proof_site
            {
                let certificate = scope.certificate_since(&checkpoint)?;
                record_proof_site_tactic_expansion(
                    expansion_capture.as_deref_mut(),
                    site,
                    indexed.source_index,
                    &certificate.to_proof_tactics(),
                );
            }
            continue;
        }
        let ProofTactic::Have(have) = &indexed.tactic else {
            return decline();
        };
        // A `have` with a smart body is a selectable source site like the
        // operations above, so its checked steps are retained for expansion
        // here too; without this the site verifies and then reports that the
        // proof has no such source tactic.
        let checkpoint = scope.checkpoint();
        let nested = scope.driver().open_source_have(have)?;
        let mut failed_check = None;
        let selected = solve_nested_have(nested, have, &mut failed_check)?;
        let Some(selected) = selected else {
            let fact = crate::surface::diagnostics::describe_click_proposition(&have.proposition);
            return Err(failed_check
                .map(|error| error.with_context(format!("Requires {fact}")))
                .unwrap_or_else(|| ClickError::new(format!("Requires {fact}"))));
        };
        scope = scope.join_nested(selected)?;
        if indexed.source_index != owning_source_index
            && let Some(site) = proof_site
        {
            let certificate = scope.certificate_since(&checkpoint)?;
            record_proof_site_tactic_expansion(
                expansion_capture.as_deref_mut(),
                site,
                indexed.source_index,
                &certificate.to_proof_tactics(),
            );
        }
    }
    Ok(Ok(scope))
}

fn advance_checked_open_scope<'a>(
    scope: ProofScope<'a>,
    body: &InternalProofNode,
    mut expansion_capture: Option<&mut ExpansionCapture>,
    proof_site: Option<&ProofSite>,
    owning_source_index: usize,
) -> Driven<ProofScope<'a>> {
    if matches!(body, InternalProofNode::Done) {
        return Ok(Ok(scope));
    }
    if let Some(tactics) = linear_execution_tactics(body) {
        return advance_linear_open_scope(
            scope,
            tactics,
            expansion_capture,
            proof_site,
            owning_source_index,
        );
    }
    if let InternalProofNode::Linear {
        tactics,
        continuation,
    } = body
    {
        let scope = driven!(advance_linear_open_scope(
            scope,
            tactics,
            expansion_capture.as_deref_mut(),
            proof_site,
            owning_source_index,
        ));
        return advance_checked_open_scope(
            scope,
            continuation,
            expansion_capture,
            proof_site,
            owning_source_index,
        );
    }
    if let InternalProofNode::Match {
        index,
        source_index,
        proof_match,
        arms,
        continuation,
        ..
    } = body
    {
        let scope = scope.with_execution_tactic_index(*index)?;
        let scope = driven!(scope.try_execution_match(
            proof_match.ensuring.is_some(),
            *source_index,
            |proof| {
                advance_prepared_execution_match(
                    proof,
                    proof_match,
                    arms,
                    continuation,
                    expansion_capture.as_deref_mut(),
                    proof_site,
                    owning_source_index,
                    0,
                )
            }
        ));
        return advance_checked_open_scope(
            scope,
            continuation,
            expansion_capture,
            proof_site,
            owning_source_index,
        );
    }
    if let InternalProofNode::Open {
        index,
        source_index,
        resource,
        body: nested_body,
        continuation,
    } = body
    {
        if scope.is_at_function_exit() {
            let open =
                post_execution_open(scope.body(), *index, *source_index, resource, nested_body)?;
            let scope = scope.defer_post_execution_source_tactic(
                *index,
                *source_index,
                open,
                expansion_capture.as_deref_mut(),
            )?;
            return advance_checked_open_scope(
                scope,
                continuation,
                expansion_capture,
                proof_site,
                owning_source_index,
            );
        }
        let scope = scope.with_execution_tactic_index(*index)?;
        let nested = scope.begin_open(resource.clone(), *source_index)?;
        let nested = driven!(advance_checked_open_scope(
            nested,
            nested_body,
            expansion_capture.as_deref_mut(),
            proof_site,
            owning_source_index,
        ));
        let scope = scope.driver().complete_nested_scope(nested)?;
        return advance_checked_open_scope(
            scope,
            continuation,
            expansion_capture,
            proof_site,
            owning_source_index,
        );
    }
    if let InternalProofNode::If {
        condition,
        then_branch,
        else_branch,
        continuation,
        ..
    } = body
        && let Some((then_steps, else_steps)) =
            expanded_execution_if_steps(then_branch, else_branch)
        && scope.frontier_is_execution_branch(condition)?
    {
        let scope =
            scope
                .driver()
                .apply_expanded_execution_if(condition, &then_steps, &else_steps)?;
        return advance_checked_open_scope(
            scope,
            continuation,
            expansion_capture,
            proof_site,
            owning_source_index,
        );
    }
    if let InternalProofNode::If {
        index,
        condition,
        then_branch,
        else_branch,
        continuation,
        ..
    } = body
    {
        // A proof `if` inside a resource scope is the same case split as
        // outside one: each case runs its arm and then the shared
        // continuation to its own function exit, and the cases join
        // terminally as the scope's next node.
        let scope = scope.with_execution_tactic_index(*index)?;
        let (split, record) = scope.split_execution_if(condition.clone())?;
        let mut advanced = split;
        let mut consumed_continuation = false;
        for (take_then, branch) in [(true, then_branch.as_ref()), (false, else_branch.as_ref())] {
            let focused = advanced.focus_execution_if_arm(&record, take_then)?;
            let mut next = driven!(advance_focused_execution_region(
                focused,
                None,
                branch,
                expansion_capture.as_deref_mut(),
                proof_site,
                owning_source_index,
                1,
            ));
            if !next.is_at_function_exit()
                && !matches!(continuation.as_ref(), InternalProofNode::Done)
            {
                let continued = driven!(advance_focused_execution_region(
                    next,
                    None,
                    continuation,
                    expansion_capture.as_deref_mut(),
                    proof_site,
                    owning_source_index,
                    1,
                ));
                next = continued;
                consumed_continuation = true;
            }
            if !next.is_at_function_exit() {
                return decline_short_of_exit();
            }
            advanced = next;
        }
        let scope = scope.join_execution_if_terminal(&advanced, &record)?;
        return advance_checked_open_scope(
            scope,
            if consumed_continuation {
                &DONE_PROOF
            } else {
                continuation
            },
            expansion_capture,
            proof_site,
            owning_source_index,
        );
    }
    let InternalProofNode::Branch {
        ensuring,
        then_branch,
        else_branch,
        continuation,
        ..
    } = body
    else {
        return decline();
    };
    let (split, record) = scope.split_execution_branch()?;
    let arms = driven!(advance_checked_branch_arms(
        split,
        &record,
        None,
        ensuring,
        then_branch,
        else_branch,
        continuation,
        expansion_capture.as_deref_mut(),
        proof_site,
        owning_source_index,
        0,
    ));
    let scope =
        scope.join_execution_split(&arms.advanced, &record, arms.empty, arms.join_interface)?;
    scope.note_trace_join_continuation_arm(arms.continuation_arm);
    advance_checked_open_scope(
        scope,
        if arms.consumed_continuation {
            &DONE_PROOF
        } else {
            continuation
        },
        expansion_capture,
        proof_site,
        owning_source_index,
    )
}

/// Introduces one arm's case assumption: `Ok(Some(fact))` is the kernel fact
/// the arm adds (`Ok(Some(None))` when the arm adds none yet), and `Ok(None)`
/// says the arm is infeasible because `available` holds the fact's exact
/// negation.
///
/// The condition is lowered against `available`'s own indexed context, and
/// the negation is looked up by its spellings, so a split costs its condition
/// and not the proof facts that precede it.
pub(in crate::surface::proof) fn introduce_proof_case_assumption(
    execution: &mut ExecutionProofState,
    proof_context: &ExecutionProofContext<'_>,
    available: &PureFactStore,
    structured_branch_history: bool,
    condition: &SyntaxProposition,
    lowering_condition: &SyntaxProposition,
    value: bool,
) -> Result<Option<Option<Proposition>>, ClickError> {
    let tactic_index = proof_context.tactic_index;
    let parameters = proof_context.parsed_function.parameters();
    let arguments = proof_context.arguments;
    let predicate_environment = proof_context.spec_definitions.predicates;
    let click_function_environment = proof_context.spec_definitions.functions;
    let claim_label = proof_context.claim_label;

    if execution.core.frontier.is_at_function_exit()
        && structured_branch_history
        && proof_case_is_stable_program_point_condition(condition)
    {
        // A source-qualified condition can still be lowered without choosing
        // one return outcome. Use it immediately when possible so a logical
        // certificate nested under an already selected C path does not
        // manufacture its contradictory sibling at function exit. Conditions
        // involving `result` or the post-state retain the deferred per-outcome
        // handling below.
        if let Ok(proposition) = lower_fixed_state_proposition(
            lowering_condition,
            available,
            ParameterBinding::new(parameters, arguments),
            FixedStateFrame::new(
                proof_context.old_reference_state(&execution.core.frontier, &execution.core.state),
                &execution.core.state,
                None,
                &execution.presentation.recorded_states,
            ),
            SpecDefinitions::new(predicate_environment, click_function_environment),
        ) {
            let surface_fact = if value {
                condition.clone()
            } else {
                negate_click_proposition(condition)
            };
            let kernel_fact = if value {
                proposition
            } else {
                match proposition {
                    Proposition::ConditionIs(condition, value) => {
                        Proposition::condition_is(condition, !value)
                    }
                    Proposition::Not(body) => *body,
                    proposition => Proposition::Not(Box::new(proposition)),
                }
            };
            if holds_exact_negation(available, &kernel_fact) {
                return Ok(None);
            }
            execution
                .presentation
                .surface_propositions
                .record_lowering(&surface_fact, &kernel_fact)?;
            execution
                .presentation
                .case_assumptions
                .push(CaseAssumption {
                    tactic_index,
                    condition: condition.clone(),
                    value,
                    fact: Some(kernel_fact.clone()),
                    match_arm: None,
                });
            return Ok(Some(Some(kernel_fact)));
        }
    }
    if execution.core.frontier.is_at_function_exit() {
        execution
            .presentation
            .case_assumptions
            .push(CaseAssumption {
                tactic_index,
                condition: condition.clone(),
                value,
                fact: None,
                match_arm: None,
            });
        return Ok(Some(None));
    }
    let proposition = lower_fixed_state_proposition(
        lowering_condition,
        available,
        ParameterBinding::new(parameters, arguments),
        FixedStateFrame::new(
            proof_context.old_reference_state(&execution.core.frontier, &execution.core.state),
            &execution.core.state,
            None,
            &execution.presentation.recorded_states,
        ),
        SpecDefinitions::new(predicate_environment, click_function_environment),
    )
    .map_err(|message| {
        ClickError::new(format!(
            "`{claim_label}` tactic {tactic_index}: could not lower `if` condition: {message}"
        ))
    })?;
    let surface_fact = if value {
        condition.clone()
    } else {
        negate_click_proposition(condition)
    };
    let kernel_fact = if value {
        proposition
    } else {
        match proposition {
            Proposition::ConditionIs(condition, value) => {
                Proposition::condition_is(condition, !value)
            }
            Proposition::Not(body) => *body,
            proposition => Proposition::Not(Box::new(proposition)),
        }
    };
    if holds_exact_negation(available, &kernel_fact) {
        return Ok(None);
    }
    execution
        .presentation
        .surface_propositions
        .record_lowering(&surface_fact, &kernel_fact)?;
    execution
        .presentation
        .case_assumptions
        .push(CaseAssumption {
            tactic_index,
            condition: condition.clone(),
            value,
            fact: Some(kernel_fact.clone()),
            match_arm: None,
        });
    Ok(Some(Some(kernel_fact)))
}

/// Whether `available` holds a fact that `propositions_are_exact_negations`
/// pairs with `fact`, read from the exact index by the spellings that relation
/// accepts rather than by comparing every fact.
fn holds_exact_negation(available: &PureFactStore, fact: &Proposition) -> bool {
    let negated = Proposition::Not(Box::new(fact.clone()));
    let mut spellings = vec![negated];
    match fact {
        Proposition::ConditionIs(condition, value) => {
            spellings.push(Proposition::condition_is(condition.clone(), !value));
        }
        Proposition::Not(body) => {
            spellings.push(body.as_ref().clone());
        }
        _ => {}
    }
    spellings.iter().any(|spelling| {
        crate::instrumentation::record_deterministic_work(1);
        available.contains(spelling) && propositions_are_exact_negations(spelling, fact)
    })
}

fn proof_case_is_stable_program_point_condition(proposition: &SyntaxProposition) -> bool {
    let expression_is_stable =
        |expression: &SyntaxTerm| matches!(expression, SyntaxTerm::At { .. } | SyntaxTerm::Old(_));
    fn stable(
        proposition: &SyntaxProposition,
        expression_is_stable: &impl Fn(&SyntaxTerm) -> bool,
    ) -> bool {
        match proposition {
            SyntaxProposition::Value(expression) => expression_is_stable(expression),
            SyntaxProposition::Comparison { left, right, .. } => {
                expression_is_stable(left) && expression_is_stable(right)
            }
            SyntaxProposition::FloatClassification { expression, .. } => {
                expression_is_stable(expression)
            }
            SyntaxProposition::Defined { expression }
            | SyntaxProposition::IsA {
                pointer: expression,
                ..
            } => expression_is_stable(expression),
            SyntaxProposition::At { .. } => true,
            SyntaxProposition::And(left, right)
            | SyntaxProposition::Or(left, right)
            | SyntaxProposition::Implies(left, right) => {
                stable(left, expression_is_stable) && stable(right, expression_is_stable)
            }
            SyntaxProposition::Not(body) => stable(body, expression_is_stable),
            SyntaxProposition::Separate { .. }
            | SyntaxProposition::ResourceViewable { .. }
            | SyntaxProposition::Contains { .. }
            | SyntaxProposition::Loadable { .. }
            | SyntaxProposition::ForAll { .. }
            | SyntaxProposition::Exists { .. }
            | SyntaxProposition::RangeAll { .. }
            | SyntaxProposition::RangeAny { .. }
            | SyntaxProposition::PredicateCall { .. } => false,
        }
    }
    stable(proposition, &expression_is_stable)
}

fn add_proof_branch_context(error: ClickError, branch: &str) -> ClickError {
    error.with_prefix(format!("in {branch}:\n"))
}

pub(in crate::surface::proof) fn add_proof_branch_path(
    mut error: ClickError,
    branch_path: &PersistentSequence<String>,
) -> ClickError {
    for branch in branch_path.iter().rev() {
        error = add_proof_branch_context(error, branch);
    }
    error
}

/// Why a closer cannot run at an execution frontier that has not reached the
/// function exit: what still lies ahead, and the two ways to get there.
fn closer_before_exit_reason(proof: &Proof<'_>, name: &str) -> String {
    format!(
        "`{name}` closes the outcome claims at function exit and does not execute: {}. Step to the exit first with `step_until(function.exit)` or `step()` (the end of the body is one step), or omit the proof, whose implicit tail runs the C and closes the claims.",
        frontier_ahead_of_exit(proof)
    )
}

/// Where a live frontier stands, for a refusal of a tactic that needs the
/// function exit.
fn frontier_ahead_of_exit(proof: &Proof<'_>) -> String {
    proof
        .execution_view()
        .ok()
        .and_then(|view| match &view.frontier.position {
            FrontierPosition::StatementEntry { remaining } => {
                Some(match frontier_head_statement(remaining) {
                    Some(statement) => format!(
                        "the frontier is at statement {}, `{}`",
                        view.frontier.next_statement_index,
                        describe_statement_head(statement)
                    ),
                    None => {
                        "the frontier is at the end of a block, one step before the function exit"
                            .to_string()
                    }
                })
            }
            _ => None,
        })
        .unwrap_or_else(|| "execution has not reached the function exit".to_string())
}

/// The diagnostic for an execution tactic written after execution already
/// reached function exit: the tactic has no statement to run.
const INDUCT_EXECUTION_REFUSAL: &str =
    "`induct` requires a pure theorem. Prove the property as a pure theorem and apply it here.";

fn post_exit_execution_tactic_error(tactic: &ProofTactic) -> Option<String> {
    let name = match tactic {
        ProofTactic::Induct { .. } => return Some(INDUCT_EXECUTION_REFUSAL.to_owned()),
        ProofTactic::Step => "step()".to_string(),
        ProofTactic::StepContract(name) => format!("step({name})"),
        ProofTactic::StepBind(name) => format!("let {{ result: {name} }} = step()"),
        ProofTactic::StepCall(transport) => transport.to_string(),
        ProofTactic::SmartExecute => "the implicit tail".to_string(),
        ProofTactic::ExecuteUntil(point) => format!(
            "step_until({})",
            crate::surface::diagnostics::describe_execution_point(point)
        ),
        // These act on the frontier's memory and program points, which a
        // function outcome no longer has.
        ProofTactic::Iterated(tactic) => {
            return Some(format!(
                "`{}` must run before execution reaches function exit; move it before the `step_until(function.exit)` or last `step()` that reaches the exit",
                crate::surface::printing::describe_iterated_tactic(tactic)
            ));
        }
        ProofTactic::ObserveResource(resource)
            if !matches!(
                resource,
                ResourceClause::ViewMemory(_) | ResourceClause::OwnMemory(_)
            ) =>
        {
            return Some(format!(
                "`observe({})` must run before execution reaches function exit; move it before the `step_until(function.exit)` or last `step()` that reaches the exit",
                crate::surface::printing::format_resource_target(resource)
            ));
        }
        ProofTactic::Mark(name) => {
            return Some(format!(
                "`mark {name};` must name a program point before function exit; move it before the `step_until(function.exit)` or last `step()` that reaches the exit"
            ));
        }
        _ => return None,
    };
    Some(format!(
        "`{name}` cannot run after execution already reached function exit"
    ))
}

/// The diagnostic for a function-exit tactic written before execution
/// reached function exit.
/// A closer gets the same diagnostic here as in an execution arm.
fn pre_exit_outcome_tactic_error(proof: &Proof<'_>, tactic: &ProofTactic) -> Option<String> {
    let name = match tactic {
        ProofTactic::Induct { .. } => return Some(INDUCT_EXECUTION_REFUSAL.to_owned()),
        ProofTactic::Witness(_) => "witness",
        ProofTactic::Choose(_) => "choose",
        ProofTactic::Close | ProofTactic::Solve => {
            return Some(closer_before_exit_reason(proof, tactic_name(tactic)));
        }
        // Any other tactic that only works on the outcome claims, such as a
        // closer: execution has to reach function exit before it has a goal.
        _ if flat_post_execution_tactic(tactic).is_some() => {
            return Some(format!(
                "`{}` works on the outcome claims at function exit and does not execute: {}. Step to the exit first with `step_until(function.exit)` or `step()` (the end of the body is one step), or end the script there, so that its implicit tail runs the C and closes the claims.",
                tactic_name(tactic),
                frontier_ahead_of_exit(proof)
            ));
        }
        _ => return None,
    };
    Some(format!(
        "`{name}` requires execution to reach function exit first; write `step_until(function.exit);` before it"
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// C that allocates `count` cells, returning `-1` after freeing the
    /// earlier ones when an allocation fails, and `18` after freeing them all.
    fn null_checked_allocation_chain(count: usize) -> String {
        let mut source =
            "void *malloc(unsigned long size);\nvoid free(void *ptr);\n\nint f(void) {\n"
                .to_string();
        for index in 0..count {
            source.push_str(&format!(
                "    int *p{index} = malloc(sizeof(int));\n    if (p{index} == 0) {{\n"
            ));
            for earlier in 0..index {
                source.push_str(&format!("        free(p{earlier});\n"));
            }
            source.push_str("        return -1;\n    }\n");
        }
        for index in 0..count {
            source.push_str(&format!("    free(p{index});\n"));
        }
        source.push_str("    return 18;\n}\n");
        source
    }

    /// The explicit proof `click expand` writes for that chain: one proof
    /// `if` per null check, each nested in the previous one's `else` arm, so
    /// the proof nests exactly `count` regions.
    fn nested_null_check_proof(count: usize) -> String {
        fn steps(out: &mut String, indent: usize, count: usize) {
            for _ in 0..count {
                out.push_str(&format!("{:indent$}step();\n", ""));
            }
        }
        let mut proof = String::from(
            "verifying \"chain.c\";\n\nint f() {\n    ensures result == 18 or result == -1;\n} by {\n",
        );
        steps(&mut proof, 4, 2);
        let mut statement = 2;
        for index in 0..count {
            let indent = 4 * (index + 1);
            proof.push_str(&format!(
                "{:indent$}if at(region({statement}).entry, p{index}) == at(region({statement}).entry, 0) {{\n",
                ""
            ));
            steps(&mut proof, indent + 4, index + 2);
            proof.push_str(&format!(
                "{:w$}close();\n{:indent$}}} else {{\n",
                "",
                "",
                w = indent + 4
            ));
            if index + 1 < count {
                steps(&mut proof, indent + 4, 4);
            } else {
                steps(&mut proof, indent + 4, count + 3);
                proof.push_str(&format!("{:w$}close();\n", "", w = indent + 4));
            }
            statement += index + 5;
        }
        for index in (0..count).rev() {
            proof.push_str(&format!("{:w$}}}\n", "", w = 4 * (index + 1)));
        }
        proof.push_str("}\n");
        proof
    }

    /// Completed null-check cases retain join records, not recursive frames.
    #[test]
    #[cfg(not(feature = "fast-gate"))]
    #[ignore = "nightly: 1.1s in the parallel gate"]
    fn terminal_proof_if_cases_do_not_charge_recursive_depth() {
        for count in [1, 4, 12] {
            let c_source = null_checked_allocation_chain(count);
            let proof = nested_null_check_proof(count);
            DEEPEST_REGION_DEPTH.with(|deepest| deepest.set(0));
            crate::surface::verify_c_sources(&proof, &[("chain.c", &c_source)])
                .unwrap_or_else(|error| panic!("{count} cases: {}", error.message()));
            let deepest = DEEPEST_REGION_DEPTH.with(std::cell::Cell::get);
            assert!(
                deepest < MAX_CHECKED_EXECUTION_REGION_DEPTH,
                "{count}: {deepest}"
            );
        }
    }

    fn linear(tactics: usize, continuation: InternalProofNode) -> InternalProofNode {
        InternalProofNode::Linear {
            tactics: (0..tactics)
                .map(|index| IndexedTactic {
                    index,
                    source_index: index,
                    tactic: ProofTactic::Step,
                })
                .collect(),
            continuation: Box::new(continuation),
        }
    }

    fn branch(source_index: usize, continuation: InternalProofNode) -> InternalProofNode {
        InternalProofNode::Branch {
            index: source_index,
            source_index,
            ensuring: None,
            then_branch: Box::new(linear(1, InternalProofNode::Done)),
            else_branch: Box::new(linear(1, InternalProofNode::Done)),
            continuation: Box::new(continuation),
        }
    }

    fn proof_if(
        then_branch: InternalProofNode,
        else_branch: InternalProofNode,
    ) -> InternalProofNode {
        InternalProofNode::If {
            index: 0,
            source_index: 0,
            condition: SyntaxProposition::Comparison {
                left: SyntaxTerm::IntegerLiteral("1".into()),
                operator: ComparisonOperator::Equal,
                right: SyntaxTerm::IntegerLiteral("0".into()),
            },
            ensuring: None,
            then_branch: Box::new(then_branch),
            else_branch: Box::new(else_branch),
            continuation: Box::new(InternalProofNode::Done),
        }
    }

    /// A proof `if` whose cases both end short of the function exit, as in a
    /// `branch` arm, reaches the shared continuation: its cases rejoin there.
    #[test]
    fn a_proof_if_whose_cases_continue_reaches_the_shared_continuation() {
        let region = linear(
            1,
            proof_if(
                linear(1, InternalProofNode::Done),
                linear(1, InternalProofNode::Done),
            ),
        );
        assert!(
            checked_execution_region_end(&region)
                == Ok(CheckedExecutionRegionEnd::SharedContinuation)
        );
    }

    /// The structural predicates walk a continuation at its region's depth:
    /// a run of sibling `branch`es far longer than the nesting bound is one
    /// level, and a source tactic at its end is still found.
    #[test]
    fn sibling_regions_do_not_charge_the_nesting_bound() {
        let count = 4 * MAX_CHECKED_EXECUTION_REGION_DEPTH;
        let mut region = InternalProofNode::Done;
        for source_index in (1000..1000 + count).rev() {
            region = linear(1, branch(source_index, region));
        }
        assert!(
            checked_execution_region_end(&region)
                == Ok(CheckedExecutionRegionEnd::SharedContinuation)
        );
        assert!(checked_execution_region_contains_source(
            &region,
            1000 + count - 1
        ));
    }
}
