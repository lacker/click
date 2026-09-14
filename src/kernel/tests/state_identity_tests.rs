use super::*;
use crate::kernel::loans::LoanLedger;
use std::cmp::Ordering;
use std::collections::HashSet;

fn ledger_with_participants() -> (
    LoanLedger,
    crate::kernel::loans::LoanParticipantId,
    crate::kernel::loans::LoanParticipantId,
) {
    let ledger = LoanLedger::new();
    let owner = ledger.fresh_participant().expect("owner identity");
    let reader = ledger.fresh_participant().expect("reader identity");
    (ledger, owner, reader)
}

fn token_with_support(name: &str) -> (CResourceFact, ResourceOccurrenceId) {
    let fact = CResourceFact::own_token(name.to_string(), Vec::new());
    let support = ResourceContext::new()
        .unchecked_with_fact(fact.clone())
        .unique_owned_occurrence_for_fact(&fact)
        .expect("token backing")
        .0;
    (fact, support)
}

#[test]
fn empty_states_remain_canonically_equal() {
    assert_eq!(CState::new(), CState::default());
}

#[test]
fn cloned_state_shares_the_loan_ledger_root() {
    let (ledger, _, _) = ledger_with_participants();
    let state = CState::new().with_loan_ledger(Some(ledger));
    let clone = state.clone();

    assert!(state.shares_nonlocal_storage_with(&clone));
    assert!(
        state
            .loan_ledger()
            .expect("state has ledger")
            .shares_storage_with(clone.loan_ledger().expect("clone has ledger"))
    );
}

#[test]
fn divergent_holders_make_equal_ledger_states_differ() {
    let (ledger, owner, reader) = ledger_with_participants();
    let owner_state = CState::new()
        .with_loan_ledger(Some(ledger.clone()))
        .with_loan_participant(Some(owner));
    let reader_state = CState::new()
        .with_loan_ledger(Some(ledger))
        .with_loan_participant(Some(reader));

    assert_ne!(owner_state, reader_state);
    assert_ne!(owner_state.cmp(&reader_state), Ordering::Equal);
    assert!(!owner_state.shares_nonlocal_storage_with(&reader_state));
}

#[test]
fn statement_outcome_reconstruction_preserves_holder_identity() {
    let (ledger, owner, _) = ledger_with_participants();
    let state = CState::new()
        .with_local("x", int32(0))
        .with_loan_ledger(Some(ledger))
        .with_loan_participant(Some(owner));
    let paths = execute_c_statement_paths(
        &state,
        &c_assign("x", c_int32_literal(1)),
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("assignment should execute");
    let [
        CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(next_state),
            ..
        },
    ] = paths.as_slice()
    else {
        panic!("assignment should have one normal outcome");
    };

    assert_eq!(next_state.loan_participant(), Some(owner));
    assert!(
        state
            .loan_ledger()
            .expect("state has ledger")
            .shares_storage_with(next_state.loan_ledger().expect("outcome has ledger"))
    );
}

#[test]
fn divergent_ledger_successors_make_state_identities_differ() {
    let (ledger, owner, reader) = ledger_with_participants();
    let (first_fact, first_support) = token_with_support("first");
    let (second_fact, second_support) = token_with_support("second");
    let first = ledger
        .lend(owner, reader, first_support, first_fact)
        .expect("first loan");
    let second = ledger
        .lend(owner, reader, second_support, second_fact)
        .expect("second loan");
    let first = ledger.apply(&first.transition).expect("first successor");
    let second = ledger.apply(&second.transition).expect("second successor");
    let first_state = CState::new().with_loan_ledger(Some(first));
    let second_state = CState::new().with_loan_ledger(Some(second));

    assert_ne!(first_state, second_state);
    assert_ne!(first_state.cmp(&second_state), Ordering::Equal);
    let states = [first_state, second_state]
        .into_iter()
        .collect::<HashSet<_>>();
    assert_eq!(states.len(), 2);
}

#[test]
fn abstract_join_rejects_divergent_loan_roots_without_scanning_ledgers() {
    let (ledger, owner, reader) = ledger_with_participants();
    let (first_fact, first_support) = token_with_support("first");
    let (second_fact, second_support) = token_with_support("second");
    let first = ledger
        .lend(owner, reader, first_support, first_fact)
        .expect("first loan");
    let second = ledger
        .lend(owner, reader, second_support, second_fact)
        .expect("second loan");
    let first_state = CState::new().with_loan_ledger(Some(
        ledger.apply(&first.transition).expect("first successor"),
    ));
    let second_state = CState::new().with_loan_ledger(Some(
        ledger.apply(&second.transition).expect("second successor"),
    ));

    let error = abstract_c_state_for_join(&first_state, &std::collections::BTreeMap::new())
        .expect("single-state join retains its root");
    assert_eq!(error.loan_ledger(), first_state.loan_ledger());
    let error = abstract_c_state_for_join_across(
        &first_state,
        &[&first_state, &second_state],
        &std::collections::BTreeMap::new(),
    )
    .expect_err("divergent loan roots must not be silently selected");
    assert!(error.contains("stable-view loan state"));
}

/// R22: one arm returns its access and recovers the owner, the other keeps
/// its share. These are alternative states, not pieces to add together, so
/// the join refuses rather than handing the continuation unconditional
/// ownership. Both arms holding the same recovered ledger join normally.
#[test]
fn abstract_join_rejects_a_loan_ended_on_only_one_arm() {
    let (ledger, owner, reader) = ledger_with_participants();
    let (fact, support) = token_with_support("lent");
    let opening = ledger.lend(owner, reader, support, fact).expect("loan");
    let lent = ledger.apply(&opening.transition).expect("lent successor");
    let transfer = lent
        .transfer(opening.root_share, reader, owner)
        .expect("the reader returns its share");
    let returned = lent.apply(&transfer).expect("returned successor");
    let end = returned
        .end(opening.scope, owner)
        .expect("the owner closes");
    let ended = returned.apply(&end).expect("ended successor");
    let (recover, _, _) = ended
        .recover(opening.loan, owner)
        .expect("the owner recovers");
    let recovered = ended.apply(&recover).expect("recovered successor");

    let kept = CState::new().with_loan_ledger(Some(lent.clone()));
    let closed = CState::new().with_loan_ledger(Some(recovered.clone()));
    let error = abstract_c_state_for_join_across(
        &closed,
        &[&closed, &kept],
        &std::collections::BTreeMap::new(),
    )
    .expect_err("a loan ended on one arm only must not join into ownership");
    assert!(error.contains("stable-view loan state"), "{error}");
    let error = abstract_c_state_for_join_across(
        &kept,
        &[&kept, &closed],
        &std::collections::BTreeMap::new(),
    )
    .expect_err("arm order does not matter");
    assert!(error.contains("stable-view loan state"), "{error}");

    let closed_too = CState::new().with_loan_ledger(Some(recovered.clone()));
    let joined = abstract_c_state_for_join_across(
        &closed,
        &[&closed, &closed_too],
        &std::collections::BTreeMap::new(),
    )
    .expect("both arms recovered the same way");
    assert_eq!(joined.loan_ledger(), closed.loan_ledger());
}

/// One arm state holding a checked view of `name`, rooted in a fresh loan
/// taken from `ledger`. The state keeps `ledger` itself, so two arms built
/// this way differ only in their occurrence bindings.
fn arm_with_view_binding(
    ledger: &LoanLedger,
    owner: crate::kernel::loans::LoanParticipantId,
    reader: crate::kernel::loans::LoanParticipantId,
    name: &str,
) -> (CState, crate::kernel::loans::LoanViewBinding) {
    let (support_fact, _) = token_with_support(&format!("{name}_support"));
    let viewed = CResourceFact::view_token(format!("{name}_view"), Vec::new());
    let resources =
        ResourceContext::new().unchecked_with_facts([support_fact.clone(), viewed.clone()]);
    let support = resources.owned_occurrences_for_fact(&support_fact)[0];
    let occurrence = resources.occurrences_for_fact(&viewed)[0];
    let opening = ledger
        .lend(owner, reader, support, support_fact)
        .expect("the arm's view is backed by a fresh loan");
    let binding = crate::kernel::loans::LoanViewBinding {
        loan: opening.loan,
        scope: opening.scope,
        share: opening.root_share,
        support,
        viewed,
        hold: None,
    };
    let state = CState::new()
        .with_loan_ledger(Some(ledger.clone()))
        .with_loan_participant(Some(reader))
        .with_resource_context_and_loan_dependencies(resources, [(occurrence, binding.clone())]);
    (state, binding)
}

#[test]
fn abstract_join_keeps_one_shared_view_root_and_drops_its_occurrence_sidecar() {
    let (ledger, owner, reader) = ledger_with_participants();
    let (arm, binding) = arm_with_view_binding(&ledger, owner, reader, "shared");
    let sibling = arm.clone();

    let abstraction = abstract_c_state_for_interface_join_across(
        &arm,
        &[&arm, &sibling],
        &std::collections::BTreeMap::new(),
    )
    .expect("arms holding the same root have one deterministic abstraction");

    // The root survives the join; the bookkeeping of the discarded resource
    // context does not, so the abstraction agrees with every other path that
    // reaches an empty context through `with_resource_context`.
    assert_eq!(abstraction.loan_ledger(), arm.loan_ledger());
    assert_eq!(abstraction.loan_participant(), Some(reader));
    assert!(abstraction.resources().facts().is_empty());
    assert_eq!(abstraction.loan_view_bindings().iter().count(), 0);
    assert_eq!(
        abstraction,
        abstraction
            .clone()
            .with_resource_context(ResourceContext::new())
    );
    assert!(
        arm.loan_view_bindings()
            .iter()
            .any(|(_, held)| held == &binding)
    );
}

#[test]
fn abstract_join_rejects_a_changed_view_root_on_one_ledger() {
    let (ledger, owner, reader) = ledger_with_participants();
    let (arm, _) = arm_with_view_binding(&ledger, owner, reader, "left");
    let (sibling, _) = arm_with_view_binding(&ledger, owner, reader, "right");

    // Same ledger root and same holder: only the checked occurrence binding
    // moved, and a join must not pick one arm's authority for the successor.
    assert_eq!(arm.loan_ledger(), sibling.loan_ledger());
    let error = abstract_c_state_for_interface_join_across(
        &arm,
        &[&arm, &sibling],
        &std::collections::BTreeMap::new(),
    )
    .expect_err("a changed view root must not be silently selected");
    assert!(error.contains("stable-view occurrence bindings"));
}

#[test]
fn abstract_join_rejects_an_arm_that_dropped_its_view_root() {
    let (ledger, owner, reader) = ledger_with_participants();
    let (arm, _) = arm_with_view_binding(&ledger, owner, reader, "kept");
    let dropped = CState::new()
        .with_loan_ledger(Some(ledger))
        .with_loan_participant(Some(reader))
        // The same visible facts, but no recorded dependency on the loan that
        // authorized reading them.
        .with_resource_context(
            ResourceContext::new().unchecked_with_facts(arm.resources().facts().iter().cloned()),
        );

    assert_eq!(dropped.loan_view_bindings().iter().count(), 0);
    let error = abstract_c_state_for_interface_join_across(
        &arm,
        &[&arm, &dropped],
        &std::collections::BTreeMap::new(),
    )
    .expect_err("an arm that dropped its root must not inherit the other arm's");
    assert!(error.contains("stable-view occurrence bindings"));
}

#[test]
fn abstract_join_rejects_divergent_holders_on_one_ledger_root() {
    let (ledger, owner, reader) = ledger_with_participants();
    let owner_state = CState::new()
        .with_loan_ledger(Some(ledger.clone()))
        .with_loan_participant(Some(owner));
    let reader_state = CState::new()
        .with_loan_ledger(Some(ledger))
        .with_loan_participant(Some(reader));

    let error = abstract_c_state_for_join_across(
        &owner_state,
        &[&owner_state, &reader_state],
        &std::collections::BTreeMap::new(),
    )
    .expect_err("divergent holders must not be silently selected");
    assert!(error.contains("stable-view loan participant"));
}

#[test]
fn loop_backedge_rejects_divergent_holders_on_one_ledger_root() {
    let (ledger, owner, reader) = ledger_with_participants();
    let top_state = CState::new()
        .with_loan_ledger(Some(ledger.clone()))
        .with_loan_participant(Some(owner));
    let next_state = CState::new()
        .with_loan_ledger(Some(ledger))
        .with_loan_participant(Some(reader));

    let error = c_loop_state_components_match_at_back_edge(
        &top_state,
        &next_state,
        &PureFactContext::new(),
        &[],
    )
    .expect_err("divergent holders must not cross a loop backedge");
    assert!(error.contains("stable-view loan participant"));
}
