# Contract retire leaves the blanket zeroed reading in place

P1. A consumed allocation claim must not leave status knowledge behind that
the contract admits was destroyed.

## Invariant

"Reads as zero where unwritten" is a claim about an allocation's contents.
`retire_contract_heap_allocation_claim`
(`src/kernel/primitives/memory_state.rs:1863`) removes the live claim, the
uninitialized status and the zeroed-prefix entry for the retired base, but
not the blanket `zeroed_allocations` entry. A callee whose contract does not
decide allocation continuity admits a deallocating implementation, so after
the retire the caller may hold a load through the same pointer that the
callee freed, and the surviving blanket status answers that load as concrete
`0` instead of declining it.

Machine-confirmed: a calloc'd allocation retired through
A calloc'd allocation retired through`
`retire_contract_heap_allocation_claim` keeps answering
`is_zeroed_heap_address(...)=true`, and the zeroed fast path in the load
resolver (`src/kernel/eval/memory_loads.rs`, `is_zeroed_heap_address`
 answering before unknown-resolution) turns it into a concrete value. The
free path (`free_heap_block`) removes the same entry; the asymmetry is the
defect.

## Scenario

```c
/* caller: p = calloc(4); call f(p); ... read p[0]; */
```
where `f(p)` consumes the contract's input allocation without deciding
continuity (`AllocationContinuity::Undecided`,
`src/kernel/functions.rs` `apply_verified_heap_allocation_delta`, retire arm
around line 9051). The callee's declared write set may exclude the
allocation (freeing is not a memory write), so the call havoc's
`forget_zeroed_allocations_written_by` does not drop the status either.

## Intended regression

A kernel-level test mirroring
`src/kernel/tests/heap_tests.rs`
`retire_investigation_zeroed_status_survives_contract_retire` (committed on
the `claude/soundness-hunt-phase2` investigation branch): after
`retire_contract_heap_allocation_claim` on a calloc-shaped allocation,
`is_zeroed_heap_address` must answer `false`, and a load through the retired
pointer must not resolve to `0` when the memory history does not establish
continuity.

## Acceptance

- [ ] `retire_contract_heap_allocation_claim` removes (or otherwise
      invalidates) the blanket zeroed status of the retired allocation, under
      every proven-equal spelling of the base, and the change records a
      derivation edge the effect checker can see.
- [ ] The zeroed regression passes at the deciding rule, and
      `scripts/check.sh` is green.
