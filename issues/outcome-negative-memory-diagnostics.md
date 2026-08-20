# Preserve stale-memory and mutation failures without outcome fallbacks

## Violated invariant

When a postcondition is false because a store, loop, alias, or hidden branch
invalidated a memory fact, the checked outcome proof should reject it directly
from explicit effect and snapshot evidence. The legacy closer must not remain
as a negative-path oracle after all successful memory transitions move onto
`Proof`.

## Current reproductions

The 2026-08-19 census includes:

- `mdtests/fill3_bad_memory_postcondition.md`
- `mdtests/fill_tail_rejects_tail_segment_unchanged.md`
- `mdtests/forall_array_segment_rejects_overwritten_cell.md`
- `mdtests/loop_rejects_stale_address_escaped_local.md`
- `mdtests/loop_rejects_stale_pre_loop_store.md`
- `mdtests/pointer_params_may_alias_without_separate.md`
- `mdtests/proof_branch_hides_arm_facts.md`
- `mdtests/write_second_old_rejects_overwritten_cell.md`

## Intended regression

- Build a per-file fallback manifest and pin each existing failure substring.
- The proof-object candidate may inspect only the focused target's indexed
  snapshot/effect dependencies; a miss must stay bounded as unrelated memory
  facts grow.
- Regressions distinguish an unavailable stale source from an available source
  whose certified effects cannot reach the target.

## Acceptance criteria

- Every listed fixture retains its expected semantic failure without either
  outcome fallback span.
- The direct rejection neither launders a stale fact through ambient
  assumptions nor drops an infeasible sibling path.
- Diagnostics remain concise and source-facing.
- Deterministic scaling regressions and `scripts/check.sh` pass.

