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
    let (ledger, owner) = ledger.fresh_participant().expect("owner identity");
    let (ledger, reader) = ledger.fresh_participant().expect("reader identity");
    (ledger, owner, reader)
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
fn divergent_ledger_successors_make_state_identities_differ() {
    let (ledger, owner, reader) = ledger_with_participants();
    let first = ledger
        .lend(
            owner,
            reader,
            CResourceFact::own_token("first".to_string(), Vec::new()),
        )
        .expect("first loan");
    let second = ledger
        .lend(
            owner,
            reader,
            CResourceFact::own_token("second".to_string(), Vec::new()),
        )
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
    let first = ledger
        .lend(
            owner,
            reader,
            CResourceFact::own_token("first".to_string(), Vec::new()),
        )
        .expect("first loan");
    let second = ledger
        .lend(
            owner,
            reader,
            CResourceFact::own_token("second".to_string(), Vec::new()),
        )
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
