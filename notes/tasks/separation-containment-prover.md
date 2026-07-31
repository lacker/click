# Deterministic separation containment for the memory-resolution prover

Status: open — THE critical path for the regression burn-down
Claimed:

## Why this one item gates four members

Two independent fix attempts (see store-provenance-family.md: "the
d78b49b restoration is real but cannot land", and the field_derived
experiment matrix) both terminated at the same wall. The store-time
cell-retention prover and the certificate framing prover are the
bounded `*_for_memory_resolution` family, deterministic by design —
the later certified-store provenance work (61f824c, 3125d16) depends
on that determinism, so the general ambient prover cannot come back
(measured: restoring it fixes owner_buffer 9.8s-fail -> 0.16s-pass and
collapses field_derived's callee >300s -> 9.7s, but breaks
expanded_read_step_keeps_named_range_separation_premises and regresses
owned-string 2.6s -> 348s).

What the bounded prover cannot conclude today: **a constant-offset
struct-field cell (e.g. owner->len at owner+0) is outside a
value-dependent range (e.g. (data+len)[0..2] or
owner[(load(...) - v)..(...)])** even when a recorded
`separate(memory(owner[0..4]), memory((owner->data)[0..owner->cap]))`
fact states exactly that — because the containment step needs
offset-equality across divergent nested snapshot spellings, which is
the chicken-and-egg with retention itself.

Members gated: owner_buffer_field_dependent (fold body fact),
bubble_pass3 (operand placement), field_derived (BOTH its blockers:
callee grouped-simp framing across `data[index+1] = 0`, and
caller-side footprint placement of data+0 vs (data+len)[0..2]),
likely vector_fill (identical grouped-simp message, unmoved by every
other lever). Plus the perf collapse (field_derived callee certifies
in 9.7 s instead of timing out) comes free.

## Recorded direction (from both agents' measurements)

Extend `pointers_proven_disjoint_by_explicit_range_for_memory_resolution`
(already consults CResourceSeparate facts) so its containment step
covers constant-offset-field vs value-dependent-range:
`bitvector_index_in_range_shallow` already has exact-order-path
transitivity; the missing piece is offset equality across nested
snapshot spellings resolved from EXACT facts only (no ambient
non-exact condition reasoning — determinism is the constraint, and
03a7f63's recursion bounds must stay).

## Dead ends already measured — do not re-attempt

- Restoring `pointers_proven_distinct` in
  `CMemory::without_possible_aliasing_cells` (breaks determinism
  consumers, above).
- Union of both provers at the retention site; 10x and 50x fuel; both
  d78b49b load-side disjunct restorations; pre-3a924ff theorem-prefix
  premises; premise-recording fixes (the missing pieces are prover
  conclusions, not recordable premises).

## Acceptance

`CLICK_RUN_QUARANTINED=1 MDTEST_FILTER=<m>` for owner_buffer (expect
pass ~0.2 s), bubble_pass3, field_derived, vector_fill; the sibling
lib test `expanded_read_step_keeps_named_range_separation_premises`
and example owned-string must NOT regress; all three gates green both
with and without `CLICK_DISABLE_MEMORY_DAG=1`. Guard and depth-gate
any new recursive arm (conventions.md).
