# lib: 7 #[ignore] expansion-era tests

Status: open
Claimed: worktree-agent-a876e0cedfd5fc405 2026-07-30

Scope: 7 `#[ignore]` lib tests from the expansion era. Retest against
current master (the 2026-07-30 certifier/expansion work moved a lot);
un-ignore what passes, diagnose what doesn't into this file:
- expands_nested_branch_tactic_by_source_location
- expansion_preserves_unfolded_resource_and_predicate_fact_spellings
- execute_rest_return_certificate_omits_unused_ambient_facts
- execute_step_expands_call_assign_fact_from_internal_snapshot
- verifies_opaque_predicate_from_requirement
- verifies_old_memory_loop_invariant
- expands_grouped_immutable_read_with_multiple_claim_successors

Repro: cargo nextest run --lib -- --ignored (or run each by name).

Done when: each test is green-and-unignored or has a one-paragraph
diagnosis here naming its family (store-provenance members move to
store-provenance-family.md).
