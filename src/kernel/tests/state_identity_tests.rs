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
