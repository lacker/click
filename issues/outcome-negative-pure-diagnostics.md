# Preserve pure and type failure diagnostics without outcome fallbacks

## Violated invariant

Expected-failure fixtures must reach their authoritative checked rejection
without invoking the legacy outcome closer merely to rediscover or format the
failure. Removing the compatibility path is incomplete while negative pure,
arithmetic, or type cases depend on it for their current diagnostic.

## Current reproductions

The 2026-08-19 census places these representative failures in this class:

- `mdtests/c_multiplication.md`
- `mdtests/c_nonzero_integer_rejected_as_pointer.md`
- `mdtests/contract_let_type_mismatch.md`
- `mdtests/max_bad_ensure.md`
- grouped ordering/top-level tactic failures whose claim is
  `identity.ensures_0` or `identity.contract`

Some timing labels are reused across fixtures, so the implementation slice
must first pin a per-file census rather than treating the label as identity.

## Intended regression

- Each fixture keeps its current `fail:` substring while counters assert that
  neither outcome fallback path ran.
- A direct proof-object miss returns a structured, bounded rejection naming
  the focused goal or invalid operation; it does not manufacture a partial
  proof or fall through to legacy planning.
- Positive siblings with the same claim spelling remain green.

## Acceptance criteria

- Every fixture in the classified manifest fails for the same semantic reason
  and with its pinned diagnostic substring.
- Neither compatibility construction nor legacy exit planning runs.
- No diagnostic includes a huge internal state dump.
- `scripts/check.sh` passes.

