use super::*;
use crate::kernel::{Memory, Pointer, PointerOffsetTerm};

fn view(index: usize, end: u32) -> CheckedResourceFact {
    CheckedResourceFact {
        fact: ResourceFact::view_memory(MemoryRange::new(
            Pointer {
                block: format!("local:loan-{index}").into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            0.into(),
            end.into(),
        )),
        role: ResourceTransferRole::Borrow,
        state_source: ResourceStateSource::Entry,
        clause_position: None,
        section_index: None,
        selected_mutex_source: None,
    }
}

fn plan() -> StableViewTransferPlan {
    let ledger = LoanLedger::new();
    plan_stable_view_transfer(
        &ResourceContext::new(),
        &[],
        &PureFactContext::new(),
        &ledger,
        ledger.fresh_participant().unwrap(),
        ledger.fresh_participant().unwrap(),
    )
    .unwrap()
}

#[test]
fn local_views_preserve_aliases_check_bounds_and_mint_no_owned_escrow() {
    let memory = Memory::new().with_block(
        view(0, 2).fact.memory_range().unwrap().base().block.clone(),
        8,
    );
    let assumptions = PureFactContext::new();
    let mut plan = plan();
    plan.lend_local_views(&memory, &[view(0, 2), view(0, 1), view(0, 2)], &assumptions)
        .unwrap();
    assert!(plan.ledger.invariant_holds());
    assert_eq!(plan.stable_views.len(), 2);
    assert!(plan.escrowed_owners.is_empty());
    assert!(plan.caller_resources_after_requirements.is_empty());
    let entry = plan.ledger.clone();
    assert_eq!(plan.recheck_entry(plan.caller_ledger()).unwrap(), entry);
    let recovery = plan
        .recover_stable_views(&assumptions, &BTreeMap::new(), &[])
        .unwrap();
    assert!(recovery.resources.is_empty());
    assert!(recovery.recovered_escrows.is_empty());
    assert!(recovery.terminal_ledger.invariant_holds());
    let mut outside = self::plan();
    assert!(
        outside
            .lend_local_views(&memory, &[view(0, 3)], &assumptions)
            .is_err()
    );
    let ended = memory.without_local_block(&view(0, 2).fact.memory_range().unwrap().base().block);
    assert!(
        outside
            .lend_local_views(&ended, &[view(0, 1)], &assumptions)
            .is_err()
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/loans/local_storage_tests.rs");
}
