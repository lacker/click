# Certification outcome equality ignores the heap statuses

P1. A deciding comparison compares everything the state's read behavior
depends on; heap statuses (zeroed / uninitialized / initialized prefix)
change what a load answers, so an equality that skips them is unsound in
the false-acceptance direction.

## What was found

`c_memories_definitionally_equal`
(`src/kernel/api/contract_certification/contract_claims.rs:505-545`)
compares blocks, ended-local tombstones and the cell/union overlays
(alias-aware), and compares **no field of `heap`**. Its caller at line 175
(`c_function_outcomes_program_state_definitionally_equal`, the deciding
check that two return states are the same certified state) therefore
accepts two return states whose `CHeapMemory` statuses disagree — e.g. one
shows an allocation `zeroed` and the other `uninitialized` for the same
live allocation, or their `initialized_cells` bookkeeping differs for bytes
that are not materialized as cells.

The asymmetry inside the same file proves the omission is the defect: the
effect-side wrapper `c_effect_memories_definitionally_equal` (line 1740)
explicitly adds `left.heap == right.heap` to the same comparator chain,
and the deciding caller for outcomes does not.

Machine-confirmed:
`hunt_investigation_outcome_equality_ignores_heap_statuses` (`src/kernel/api/contract_certification/contract_claims.rs`
investigation module) — two memories differing only in
`zeroed_allocations` vs `uninitialized_allocations` for the same live
allocation are declared definitionally equal.

## Intended regression

The investigation test converted to a true regression: the comparator must
compare the heap statuses (alias-awareness for equal-spellings is a follow-
up reviewed by the same fix; the minimal requirement is "two states with
different heap statuses are refused as definitionally equal").

## Acceptance

- [ ] `c_memories_definitionally_equal` refuses states whose `heap` differs
      (regression green); the effect wrapper and the outcome comparator use
      one shared deciding rule.
- [ ] `scripts/check.sh` green.
