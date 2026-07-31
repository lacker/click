# Regression record (reference, not a task)

The bisect verdicts, diagnoses, and experiment matrices for the
quarantined-member regressions. The WORK ITEMS live in notes/tasks/:
separation-containment-prover.md (gates owner_buffer, bubble_pass3,
field_derived, likely vector_fill), owned-string-loadable.md,
owned-vector-forward-fix.md. This file is the shared evidence base.

**These used to work.** Every member was added green (2026-06-18 to
07-16) and broke during the 2026-07-25..28 strict-certificate wave
("enforce strict smart tactic certificates", "remove smart have
transport fallback", "Make expanded proofs canonical Surface Click"),
then was quarantined 07-29/30 already failing on master. They are
regressions from this project raising its own acceptance bar — for four
of them the prover still closes the claims and only the certificate
machinery cannot express the result. Owner ruling: fix them as part of
this project, as long as the fix stays straightforward; if one turns
out to need new surface semantics, bring it back to the owner instead
of brute-forcing.

**Attack per member: fix forward from the current diagnosis** (owner
call 2026-07-31; the bisect-first phase is over — completed verdicts
below). Each has a bounded window (its add
commit → 2026-07-29). Bisect to the exact breaking commit before
working the diagnosis; "certificate machinery gap" becomes "this commit
removed/required X". Add commits: bubble_pass3 78218b6, vector_fill
a28eb1c, field_derived d0f54fe, owner_buffer a3d00d3, owned-string
d2be685, owned-vector 45e7aea.

As of 2026-07-31 (arc stages 1–5 landed), every member fails on
something that is *not* a load-equality question — do not chase these
into the arc; each diagnosis below was measured.

## Cleared (for the record)

- lib `verifies_old_memory_loop_invariant` — passes, un-ignored (arc
  stage 2a: `old(...)` now names function entry).
- mdtest `fill_tail_keeps_first.md` — de-quarantined (same fix).

## d78b49b restoration attempt (2026-07-31, worktree-agent-a5b7c1d4b897bfcad)

Worked the two d78b49b members. Verdict: **the diagnosed one-line
restoration is real but cannot land** — it collides with the landed
provenance machinery. Everything below was measured, not inferred.

**The mechanism is one hunk, not two.** Of d78b49b's two cell-retention
changes in `src/kernel/primitives.rs`, only the store-side one matters:
`CMemory::without_possible_aliasing_cells` switched from the general
`pointers_proven_distinct` to the bounded
`pointers_proven_distinct_for_memory_resolution` when deciding which
cells survive a store. The load-side `without_proven_distinct_cells`
disjunct deletion is irrelevant (restoring it alone fixes nothing,
breaks nothing). Restoring the store-side prover:

- at d78b49b: bubble_pass3 passes (13.5 s), owner_buffer still fails
  (its failure at that commit had a second ingredient that later
  commits resolved);
- at HEAD: owner_buffer **passes in 0.16 s** (from 9.8 s fail);
  bubble_pass3 still fails — bisected (with restoration applied at
  every step) to `03a7f63` "Bound memory-resolution and resource-prover
  recursion", whose depth/fuel bounds cut the reasoning the restored
  prover needs on bubble_pass3's nested spellings;
- at HEAD it **breaks lib test
  `expanded_read_step_keeps_named_range_separation_premises`**
  (10 s pass -> 9 s fail), and at d78b49b it sends the same test into
  its historical >60 s timeout (it was quarantined-for-cost before the
  refactor; the trimmed retention is what made it fast and green).

**Why the collision is structural, not incidental.** The expanded
(all-simple) replay of that lib test fails whenever the struct-field
cells survive the value-dependent store `owner->data[index] = 0` —
even when the certificate itself was generated under the same
retention semantics, and even with 10x fuel budgets. The general
prover's verdicts depend on ambient non-exact condition facts, which
differ between smart-proof execution and pinned certificate replay, so
post-store snapshot shapes diverge exactly where the certified-store
provenance matching (61f824c, 3125d16) needs them stable. The refactor
did not delete the disjunct by accident; determinism of store-time
retention is what its certificate matching stands on.

**The real fix (design work, not this task):** make the
memory-resolution prover complete enough for the family's class —
constant-offset field cell vs value-dependent store covered by an
explicit `separate(...)` fact. The machinery exists
(`pointers_proven_disjoint_by_explicit_range_for_memory_resolution`
already consults CResourceSeparate facts; `bitvector_index_in_range_shallow`
has exact-order-path transitivity) but fails on these because
containment needs offset-equality across divergent nested snapshot
spellings — a chicken-and-egg with retention itself — and because
03a7f63's bounds cap the recursion. Deterministic (exact-fact-only)
extension of that containment is the direction; general-prover
restoration is a dead end.

Family movement at HEAD + store-side restoration (for the record):
owner_buffer PASS 0.16 s; bubble_pass3 FAIL (unchanged ForAll simp
premise); vector_fill FAIL (unchanged grouped-simp message, 48 s ->
77 s); owned-string example FAIL 348 s (from 2.6 s) with **exactly the
lib test's failure signature** (`owned_string_pop` ensures 0/3/4/5) —
owned-string, and that lib test, are the same collision. The general
prover's cost on provenance-era spellings is also prohibitive,
consistent with the lib test's pre-refactor 60 s quarantine.
field_derived / owned-vector / two_pass not re-measured (no fix lands,
and owned-vector has a concurrent bisect agent on it).

## field_derived fix attempt (2026-07-31, worktree-agent-a0e5edf87e3e25ee7)

Verdict: **no straightforward fix lands — field_derived is a member of
the d78b49b structural collision above, plus a second deterministic
frame gap.** Everything below was measured at HEAD (62d17ab) unless
noted; all experiment code was env-gated and stripped.

**Hunk isolation at 3a924ff** (isolated clone, both hunks tested
independently): hunk 2 (trivial-return premise-free certificates) is
the sole breaker; hunk 1 exonerated (also independently reverted next
day by c002ea5). At 3a924ff the mechanism is: with a premise-free
`step` recorded for the caller's `return ignored;`, the ambient smart
`simp` for `buffer_push_preserves_first.ensures_1`
(`data[0] == old(data[0])`) fails with "simplified proposition was not
true" — the recorded-premise flow is authoritative for the claim
context even during the original verification.

**At HEAD the lever no longer works; two independent blockers:**

1. **Callee blocker.** `buffer_push.contract` path 0 tactic 7 (grouped
   `simp`) now fails first, on ensures_1..4:
   `minimal_proposition_derivation == None` over the full certified
   context (35 facts) — the deterministic derive cannot frame
   `owner->len` / `owner->cap` / `owner->data` loads across the
   value-dependent metadata store `owner->data[index+1] = 0` under the
   provenance-era bounded retention. Restoring the pre-d78b49b
   store-side retention (`pointers_proven_distinct` in
   `CMemory::without_possible_aliasing_cells` — the same restoration
   the section above proved cannot land) certifies the whole callee and
   collapses runtime from >300 s (hits the 5 m limit today) to ~10 s.
   The 200→300 s growth is the callee grinding the bounded prover.
2. **Caller blocker (survives the retention restoration).** With the
   callee fixed, `buffer_push_preserves_first.ensures_1` fails in the
   *ambient smart simp itself* — same signature as 3a924ff. Measured
   non-causes: restoring pre-3a924ff theorem-prefix `exact_premises` in
   the `CertifiedStatementReplay` arm (descendant: 7e96bce
   `consults_conditions`) changes nothing; 50x memory-resolution +
   resource-prover fuel changes nothing. Context dump
   (`CLICK_DERIVE_DUMP_DIR`) shows every frame *input* present
   (`1 <= len`, `len+1 < cap`, `data == owner->data`,
   `separate(memory(owner[0..4]), memory(data[0..cap]))`,
   `CMemoryEffectSummary` for the call) and no data[0]-preservation
   fact; the prover cannot place `data + 0` outside the call footprint
   `(data+len)[0..2]` because the footprint offsets are spelled with
   nested snapshot loads — the same "offset-equality across divergent
   nested snapshot spellings" chicken-and-egg named in the d78b49b
   section.

So the fix for field_derived is the same design item as owned-string /
the lib test: deterministic (exact-fact-only) containment for
constant-offset cells vs value-dependent stores/footprints, able to
resolve offsets across nested snapshot spellings. A premise-recording
fix (the caution's preferred direction) does not reach either blocker:
the missing facts are not recordable premises, they are conclusions the
deterministic provers cannot yet reach.

Family movement measured this session: vector_fill FAIL 42 s at HEAD
baseline (was ~48 s), FAIL 42 s with the retention restoration, same
grouped-simp message — no movement. field_derived stays quarantined
with its current reason (correctness, not cost-only: it does not pass
under any tested configuration).

## Bisect results (2026-07-31, three of six complete)

- **owner_buffer_field_dependent AND bubble_pass3 -> `d78b49b`** ("WIP:
  snapshot of in-progress store-provenance refactor from main
  checkout", 07-29, 911+/398-). Two mechanisms named: the
  replay-context premise filter drops `separate(...)` facts it deems
  reconstructible from projected resources (owner_buffer's missing
  exact body fact), and the `CMemory` store cell-retention filter lost
  its `pointers_proven_distinct` disjunct so post-store snapshots keep
  divergent cell spellings (bubble_pass3's unplaceable operands). The
  07-25..28 strict-certificate wave is EXONERATED for both members —
  every sampled commit through 07-28 passes them.
- **field_derived -> `3a924ff`** ("Keep trivial return certificates
  premise-free", 07-27). Hunk isolation done (2026-07-31, see the
  field_derived section below): **hunk 2 is the breaker** — the
  trivial-return `exact_premises = Vec::new()` in
  `record_surface_replay_tactic` (the caller's `return ignored;`).
  Reverting it alone at 3a924ff passes in ~12 s. Hunk 1 (the
  `prove_pure_proposition_at_point(Some(goal))` replay switch) is
  exonerated: reverting it alone still fails, and c002ea5 (same day)
  already reverted it back to `prove_have_at_point` — HEAD still has
  that shape. Fails in ~13 s at the breaking commit; the ~200 s fail
  time accreted later.
- **owned-vector -> `9ea6739`** ("remove replay bookkeeping tactics",
  07-19 — BEFORE the certificate wave; the 07-24 baseline already
  fails). Engine-only: deleted RecordExecutionPoint /
  ResetOpaqueCallCounter bookkeeping tactics and reworked replay;
  first failure is `vector_pipeline.contract` tactic 2 `execute_rest`
  missing prerequisite. Two later, separate events layered on top: a
  fail->hang at `919e084` ("make fact transport premises explicit",
  07-24), and today's distinct failure site (`vector_replace_if`
  tactic 8) introduced by post-break edits to an already-failing
  example. Also: PASS time exploded 1 s -> ~190 s between 07-15 and
  07-19 before any breakage — an unattributed perf regression worth
  its own look once the example verifies again.
- **vector_fill, owned-string: bisects CANCELLED (owner call,
  2026-07-31) — fix forward instead.** The first four bisects paid for
  themselves by refuting the certificate-wave theory and naming exact
  mechanisms, but these two add little: vector_fill shares
  field_derived's failure class (grouped-simp certification), so the
  field_derived fix answers it; owned-string's frontier diagnosis
  (missing `loadable(data[len])` permission plumbing) is already
  actionable without knowing which commit introduced it.

## Remaining members, 2026-07-31 frontiers

- **mdtest `bubble_sort3_two_pass_sorted.md`** — **passes** at 137 s vs
  the 30 s limit; quarantined on cost. 65 s of it is a slow SIMPLE
  invariant-closer replay: an engine bug, tracked in
  `invariant-closer-replay-cost.md`, not here.
- **mdtest `bubble_pass3_max_suffix.md`** (~12 s) — certificate
  lowering: the planned `simp` context premise (the loop-exit invariant
  `ForAll`) is not an available *source* fact. Looks like arc work and
  is not: its two loads sit in the **same snapshot**, differing only in
  the index term. The two-pass version of the same program does not hit
  it.
- **mdtest `composite_resource_vector_fill_loop_snapshot.md`** (~42 s)
  and **mdtest `field_derived_precise_effect_after_metadata_write.md`**
  (>300 s as of 07-31; was ~198 s, 487 s before arc stage 4) — same
  failure class: grouped `simp` cannot certify its complete claim
  transition (vector_fill at `contract` path 0 tactic 2 for
  `ensures_2`; field_derived diagnosed in full above — two blockers,
  both in the d78b49b collision; it also carries a 29 s simple `fold`,
  tracked in `invariant-closer-replay-cost.md`).
- **mdtest `composite_resource_owner_buffer_field_dependent.md`**
  (~6 s) — "execution proof for `set_owned_first.ensures_0` changed
  more than the certified ghost-resource representation".
- **example `owned-vector`** (~13 s) — `vector_replace_if.contract`
  tactic 8 `have` cannot find `Implies(replace == 0, new == old)`. A
  propositional gap over plain variables; the goal contains no memory
  at all.
- **example `owned-string`** (~2.6 s) — the `terminated_at` smart-have
  unfold cannot discharge `loadable(data[len])`: a permission-plumbing
  question, not an equality one. (Earlier attempt recorded: feeding
  `replay.effect_facts` into planning did not help — stores are
  execution facts, not effect summaries; reverted.)

## Related, not quarantined

`mdtests/proof_advance_pointer_local.md` carries an explicit
`have at(statement(1).exit, selected) == ...` because certificate
generation cannot synthesize a point-qualified spelling for a local
pointer (the `advance` abstracts it into a fresh symbolic block; no
recorded program-point state binds the local to the abstracted value —
teaching `synthesize_surface_pointer` to look up pointer-valued locals
was measured not to help). When generation can find that spelling,
delete the `have` and confirm.

## Repro

```
CLICK_RUN_QUARANTINED=1 MDTEST_FILTER=<name> cargo test --test mdtests
CLICK_EXAMPLE=owned-vector cargo test --test examples
./target/debug/click-verify examples/owned-string/owned_string.click
```

Bound field_derived with `MDTEST_TIME_LIMIT` and keep it out of loops
(~200 s to fail); bubble_sort3 takes ~137 s to pass.

Done when: all members above de-quarantine / pass, and
`proof_advance_pointer_local`'s explicit `have` deletes cleanly.
