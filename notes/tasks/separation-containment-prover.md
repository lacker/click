# Deterministic separation containment for the memory-resolution prover

Status: prover-family extension DONE (2026-07-31); remaining member
blockers measured to be in certificate surface-spelling, not here
Claimed:

## Why this one item gates four members

Two independent fix attempts (see ../regression-history.md: "the
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

## Findings 2026-07-31 (worktree-agent-a76baad67a09d1b37)

Two increments landed on branch `worktree-agent-a76baad67a09d1b37`;
both are EXACT-only and structural, no ambient reasoning touched.

1. **c5db22a — exact-equality endpoint pinning.** Probes showed
   owner_buffer's store-pointer spelling and the `separate(...)`
   fact's range-base spelling are byte-for-byte IDENTICAL (879-char
   terms compared equal) — no snapshot divergence at all in this
   member. The only gap: `bitvector_index_in_range_shallow` could not
   place index 0 in `[0..owner->len]` although the exact fact
   `owner->len == 1` was in `condition_facts` (no exact arm consults
   equality facts). Fix: resolve index/start/end through at most ONE
   recorded exact `Bitvector32Equal` fact to constants (success-only,
   falls through otherwise). owner_buffer 4.4s-fail -> 0.06s-PASS.
2. **e8f4b91 — affine inequality.** bubble_pass3's dropped retention
   cell was the trivial pair `base + v*4` vs `base + (v+1)*4`:
   `decide_bitvector_equality_shallow` had no arithmetic arm, and the
   order-path needs facts it does not have. `x + c != x` whenever
   `c % 2^32 != 0`, unconditionally — added that arm (structural,
   fact-free). All 20 bubble_pass3 retention queries now conclude;
   fail time 7.2s -> 0.47s.

**bubble_pass3's remaining blocker is NOT in the prover family**: with
retention complete, the planned `simp` context ForAll premise IS
found among available facts (kernel-identical, `fact == required`),
but `checked_surface_fact_at_outcome` fails with "no checked Click
spelling for post-execution fact ForAll{...}" —
`synthesize_surface_proposition` cannot spell the ForAll's
snapshot-qualified loads (snapshot with blocks {havoc:1000002,
local:j, local:tmp}, no cells) at any retained program point. That is
certificate-lowering/spelling work (proof.rs ~7600-7770), a different
subsystem from this task's prover extension.

Guard status after both increments: lib
`expanded_read_step_keeps_named_range_separation_premises` 2.6s pass;
owned-string unchanged failure signature (owned_string_push tactic 7
loadable gap, pre-existing at HEAD baseline 2.95s; 2.85s with fixes).

## Final acceptance results (2026-07-31, branch worktree-agent-a76baad67a09d1b37)

- **owner_buffer_field_dependent: PASS 0.06s** (expected ~0.2s), both
  with and without `CLICK_DISABLE_MEMORY_DAG=1`. DE-QUARANTINED
  (fb2b7a2).
- **bubble_pass3: moved.** 7.2s fail -> 0.47s fail (0.52s DAG-off);
  retention fully concludes (20/20 queries). New frontier documented
  in its quarantine reason (f465b8c): `synthesize_surface_proposition`
  has no Click spelling for the loop-exit ForAll's
  loop-havoc-snapshot loads (proof.rs ~7758). NOT prover work.
- **field_derived: moved.** Was >300s (hit the 5m limit) with the
  callee's grouped simp unable to derive at all
  (`minimal_proposition_derivation == None`); now fails in 238s at the
  same site (`buffer_push.contract` path 0 tactic 7, ensures_1..4)
  with the message class "expressible path facts do not replay the
  postcondition derivation" — the same surface-spelling layer as
  vector_fill.
- **vector_fill: retested, unchanged** (41.5s, same grouped-simp
  message) — but newly diagnosed: with `CLICK_DERIVE_DUMP_DIR` set,
  NO dump is written, proving `minimal_proposition_derivation`
  SUCCEEDS on its goal; the failure is premise
  spelling/self-check inside proof.rs ~13380-13530, not the bounded
  prover.
- Gates: `cargo nextest run --lib --bins` 529/529,
  `cargo test --test mdtests`, `cargo test --test examples` — all
  green, both default and `CLICK_DISABLE_MEMORY_DAG=1`.

**Where the remaining members' fix lives:** all three still-failing
members (bubble_pass3, vector_fill, field_derived) now fail in ONE
subsystem — certificate lowering's surface spelling of premises whose
loads are spelled against snapshots no retained program point carries
(`checked_surface_fact_at_outcome` /
`synthesize_surface_proposition`, src/lang/click/proof.rs). The
separation-containment prover itself concludes everything these
members ask of it. Next agent should attack the spelling layer, not
this prover.

## Dead ends added this session

- None new in the prover family. Note for the spelling layer: the
  ForAll premise IS found kernel-identical among available facts in
  bubble_pass3 (`fact == required` is true); candidate selection is
  not the problem, spelling synthesis is.

## Acceptance

`CLICK_RUN_QUARANTINED=1 MDTEST_FILTER=<m>` for owner_buffer (expect
pass ~0.2 s), bubble_pass3, field_derived, vector_fill; the sibling
lib test `expanded_read_step_keeps_named_range_separation_premises`
and example owned-string must NOT regress; all three gates green both
with and without `CLICK_DISABLE_MEMORY_DAG=1`. Guard and depth-gate
any new recursive arm (conventions.md).
