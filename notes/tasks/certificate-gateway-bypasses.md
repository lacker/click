# Certificate-gateway bypasses (from the one-gateway audit)

Status: claimed — redesign accepted, migration in progress.
Strict-gate worklist is at 2 failing mdtests (was 24), both parked on the
store-provenance / named-memory-states representation work; see the last
migration-log section.
Claimed: worktree-agent-a18665869a3d1251b, 2026-07-30

The 2026-07-30 audit (see one-gateway-check.md for the full evidence)
found that the settled invariant

  "a smart success must replay through a surface-expressible
   certificate before acceptance"

holds for every mid-execution smart tactic but NOT for at-function-exit
tactics in per-claim proofs. Three bypasses, all reachable from an
ordinary `by { ... simp; }` or `by simp;`:

- **BYPASS-A** (proof.rs ~10704 + ~10820): `closed_claims[i] = true` is
  set on the ambient `check_function_claim_by_simp` success BEFORE the
  certificate is built. A certificate build OR REPLAY failure only
  records `surface_closer_blockers[i]`, which is consumed at ~11152
  solely to make click-expand refuse. Verification returns Ok. This
  includes the "smart `simp` certificate failed replay" case — i.e.
  literally accept-anyway-on-replay-failure.
- **BYPASS-A'** (~10835): with a pending `witness`/`choose`, no
  certificate is attempted at all; the claim still closes.
- **BYPASS-B** (~10164): a post-execution `have` whose script is not
  `[unfold*, simp]` runs `prove_have_at_point` with no lowering and
  records the raw script. The mid-execution `have` (~16862) DOES gate
  this; the asymmetry is the bug.

Measured incidence (env-gated counters, all in PASSING tests):
lib/bins 278 gateway events / 5 bypass hits in 4 tests; mdtests 599
events / 345 certified / 39 bypass hits across 21 claims; examples 105
events / 0 bypasses (that corpus is entirely grouped/auto paths).

## ANSWERED 2026-07-30 (evening): invariant hole, on the current corpus

Measured: under `CLICK_STRICT_EXIT_GATE=1`, 24 mdtests fail (16
certificate-lower/replay, 3 existential-lowering, 5 smart-shaped
post-execution `have`). Joining those against `opaque_contract_supported`:
**all 37 involved functions are opaque-supported**, so every bypassed
claim is independently certified by kernel contract certification. No
currently-accepted proof rests on the ambient closer alone. Caveat: that
is a corpus fact, not a theorem — a non-opaque function with a bypassing
exit claim would be surface-only, which is why the gate still gets
flipped.

Owner accepted the redesign (2026-07-30): one acceptance judgment
(closure = replay of simple tactics, closure carries its certificate),
exit drain becomes plan -> lower -> replay -> accept, grouped/ungrouped
lose the trust asymmetry, expansion prints what verification holds.
Migration: strict flag (DONE, `CLICK_STRICT_EXIT_GATE`) -> fix lowering
gaps against the 24-test worklist -> flip default -> delete blockers.

The original open question, for the record:

Is this an INVARIANT hole or a SOUNDNESS hole? The bypassed claims are
not unchecked — the ambient closer runs kernel checks — but nobody has
verified that the ambient path is as strong as certificate replay. That
determines urgency:
- if the ambient check is equally strong, this is a documentation/
  design-invariant problem and the fix is sequencing work;
- if it is weaker anywhere, BYPASS-A is a trust-chain hole and jumps
  the queue.

## Sequencing constraint

Flipping the ungrouped gate to a hard error would fail the 21 listed
mdtest claims until the underlying lowering gaps are fixed (dominant
causes: `unfold(...)`-active goals, predicate-valued postconditions,
"surface goal lowered to a different kernel proposition"). So the order
has to be: (1) decide invariant-vs-soundness, (2) fix the lowering
gaps, (3) flip the gate. Step 3 changes what gets accepted, so it is a
semantics decision.

Not verified by the audit: adversarial reachability (no crafted .click
repro yet), whether kernel-side paths bypass proof.rs entirely, and
whether click-expand's refusal is user-visible on the 21 claims.


## Migration log

- DONE 2026-07-30: `CLICK_STRICT_EXIT_GATE` added (three bypass sites
  become verification failures; fully simple `have` scripts stay
  accepted as their own certificates). Baseline: 24 failing mdtests.
- DONE: exit-claim goals re-lower under the drain's local unfold set
  (the certificate replay clone never received it). 24 -> 22; the
  entire "surface goal lowered to a different kernel proposition"
  category (10) is gone.
- DONE: replay's derive/calculate check now supplies ambient effect
  facts (CMemoryMutatesOnly / CMemoryEffectSummary) alongside the
  listed premises, closing the asymmetry with generation, which
  deliberately filters those unspellable facts out of premise lists.
  No corpus test flips on this alone, but the prior state made the
  generation-side filter unsound against the replay judgment.

## Next cluster (start here): predicate-valued goals, 9 tests

The dominant remaining failure: claim certificates of the shape
`have same_first(p, old(p)) by { ... }` whose target is an opaque
`Proposition::Predicate` over two memory snapshots. Generation proves
it via `plan_simp_certificate` -> `ExactPropositionDerivation` and
validates with `derivation.replay(premises)`; replay validates with
`derive_simp_*` from the listed premises (check_atomic_derivation_goal,
proof.rs ~230), which cannot prove an opaque Predicate. The two
judgments disagree; per the accepted design, generation must emit what
the REPLAY judgment accepts.

The fix shape: when the goal is/contains an opaque Predicate, emit
`unfold(<name>)` prefix tactics and lower the UNFOLDED goal (the
comparison plumbing for unfolded goals already exists and works — see
the fix above). Insertion point: `lower_outcome_simp_tactic`
(proof.rs ~12190) or its caller `certify_outcome_simp_have`. Then
re-measure; the remaining categories after this cluster are
3 expressible-path-facts, 2 premise-not-available, 3 existential
lowering, 5 smart-shaped post-execution `have`.

Worklist (failing under CLICK_STRICT_EXIT_GATE=1): bubble_sort3_loop_
permutation, byte_slice_range_predicates, byte_slice_stdlib,
click_array_refs, click_proposition_logic, compare_swap2_permutation,
compare_swap2_sorted_predicate, contract_let_where, cstr_stdlib,
grouped_function_post_execution_have, loop_explicit_initialize_and_
preserve, loop_sorted_range_invariant, loop_stdlib_permutation_
invariant, permission_call_split_rejoin, proof_advance_pointer_local,
pure_click_functions, pure_have_rejects_advance (expected-error text
drift only), resource_summary_splits_write_range, sort3_permutation,
sort3_permutation_predicate, witness_and_choose, theorem_apply_in_
function_proof.


## Migration log, continued (late evening)

- DONE: unfold-emission in exit-claim certificates
  (`lower_outcome_simp_proof` is now a dispatcher over
  `lower_outcome_simp_proof_direct`): (a) an opaque predicate in the
  kernel goal is unfolded best-effort and the certificate proves the
  body; (b) when the drain's unfold set is active, its unfolds are
  prefixed to the emitted have script so replay lowers the surface
  goal and premises to the same spellings the tactics certify.
  Strict-gate corpus: 22 -> 14 (eight fixed, none broken).

Remaining 14 by category: 4 expressible-path-facts, 2
premise-not-available, 3 existential lowering, 5 smart-shaped
post-execution `have` (list in notes; `pure_have_rejects_advance` is
expected-error text drift only).

Diagnosed but not fixed — the next iteration starts here:
`click_array_refs` (`identity_two_arrays.unfolded_requirement`) fails
in the expressible-path-facts generator (proof.rs ~12774) at the
SELF-CHECK stage: premises spell as
[loadable(p[0..1]), loadable(q[0..1]), same_first(p, q)] but
check_atomic_derivation_goal rejects. Open question: which arm pushed
the opaque predicate premise and what kernel fact the derivation
actually consumed — instrument kernel_premises at the self-check
before theorizing. A speculative arm accepting unfold-spelled premises
was implemented and REVERTED (no measured effect; recorded here so it
is not re-attempted blind).

Then: the 3 existential cases (concatenate witness/choose with the
simp certificate — the pieces are all simple tactics), the 5
smart-have shapes (route through the same have-certificate path the
mid-execution arm uses), then flip the default and do the ClosedClaim
restructure per the accepted design.


## Migration log, continued (2026-07-30, worktree-agent-a18665869a3d1251b)

Strict-gate corpus: **14 -> 2**, none broken, three default gates green
at every commit (`cargo nextest run --lib --bins` 497,
`cargo test --test mdtests`, `cargo test --test examples`).

The corrected root cause for the whole "expressible path facts" and
"premise not available" family: **`surface_certificate_facts` is
snapshotted from `path_requirements` at the top of the post-execution
drain, before any deferred tactic runs.** But a claim's certificate is
`[recorded post tactics ..., closer tactics ...]`, so when the closer
replays, the recorded tactics have already run. Generation was planning
against strictly less than the replay judgment holds.

The previous iteration's guess ("fails at the SELF-CHECK stage") was
WRONG and cost time — the probe showed `minimal_proposition_derivation`
found no derivation at all, because the enabling fact was simply absent
from the context. Measure the context before theorizing about the check.

- DONE: exit-claim certificate generation gets the drain's post-tactic
  facts. (a) The drain's `unfold(p)` is applied to the certificate facts
  at the ungrouped `certify_outcome_simp` call site — deliberately NOT
  globally, because the grouped path does not emit the `unfold(...)`
  prefix and would then plan against facts replay lacks. (b)
  post-execution `apply` now records the theorem conclusions it derived
  by replaying its own `ApplyTheoremUsing` certificate (helper
  `record_certificate_facts_from_replay`; `FrameRegion` was the
  precedent). 14 -> 11: click_array_refs, sorted_pair_unfold_requirement,
  theorem_apply_in_function_proof.
- DONE: BYPASS-A' (existential closers) has a certificate. `witness` and
  `choose` are simple tactics and a `have` proof runs both
  (`prove_pure_proposition_case_at_point`), so the closer lowers to
  `have <claim goal> by { unfold*; <existence tactics>; <closer> }` +
  `assumption`. Using the claim's OWN surface goal as the have's
  proposition avoids synthesizing a surface spelling for the
  witness-instantiated body. 11 -> 9 (contract_let_where, cstr_stdlib),
  then 4 -> 2 after two follow-ups below.
- DONE: BYPASS-B is gated on certificate expressibility, not shape. The
  old strict test was a flat scan requiring every tactic to be
  `TacticClass::Simple`, which misclassified any *structured* script (a
  nested `have`, an `if`) as smart even when every leaf was simple.
  Replaced by `TacticCertificate::from_proof_tactics`, the settled
  judgment, which descends into nested bodies. Replay now runs BEFORE the
  gate so a script rejected on its own terms still reports that — this is
  what `pure_have_rejects_advance` asserts; it was never text drift, the
  gate was firing ahead of the pure-proof check. Added
  `lower_smart_simp_suffix_have` for `[<expressible prefix>, simp]`, the
  shape an existential `have` takes. 9 -> 4: click_proposition_logic,
  permission_call_split_rejoin, resource_summary_splits_write_range,
  pure_have_rejects_advance, grouped_function_post_execution_have.
- DONE: two follow-ups closed the existential category. (a) The replayed
  goal was compared to the claim goal by strict equality, so a goal
  spelled with `unfold(...)` active never matched the folded predicate
  the have proves; reconcile the spellings the way
  `certify_outcome_simp_have` already does. (b) A witness-instantiated
  goal needs premises, and has no surface spelling to write a `calculate`
  against — but it does not need one:
  `prove_pure_proposition_case_at_point` takes the CURRENT goal as the
  target when a derivation's surface proposition is identical to the
  enclosing have's (proof.rs, `if derive.proposition == *proposition`).
  So a `calculate` spelled with the have's own goal discharges the
  instantiated body; premises are the spellable ambient facts, greedily
  reduced to what replay still accepts. 4 -> 2
  (byte_slice_range_predicates, witness_and_choose).

Every candidate emitted by the new arms is accepted only when
`prove_have_at_point` — the replay judgment itself — proves it AND yields
the claim's kernel goal. No replay-side check was loosened.

### Remaining 2 — PARKED on the representation work, do not retry blind

Both are "planned `simp` context premise is not an available source
fact" (proof.rs ~12496), i.e. the planner selected a premise that
`checked_surface_fact_at_outcome` cannot spell.

- `loop_sorted_range_invariant.still_sorted`: the premise is an opaque
  `Proposition::Predicate { name: "sorted_range", arguments: [CMemory,
  CValue(Pointer), CValue(0), CValue(3)] }`. There is no recorded
  lowering (the source says `sorted(p, 3)`; `sorted_range(p, 0, 3)` only
  ever appears inside the definition body), and
  `synthesize_surface_proposition` (proof.rs ~11752) has NO
  `Proposition::Predicate` arm at all. Adding one needs the predicate
  definition to know which parameters are array refs (an array-ref
  parameter contributes a (memory, pointer) pair to `Vec<Term>`) and a
  way to NAME the memory-snapshot argument. Here the snapshot happens to
  be the empty/current one, but loop-carry and `old(...)` premises are
  not — that is the named-memory-states work.
- `advance_selected_pointer.ensures_0`: the premise is
  `selected == left or selected == right` over a local pointer with a
  symbolic block, established by an `advance` region join. No surface
  name for `selected` exists at function exit; it is only spellable as
  `at(statement(1).exit, ...)`, which is the store-provenance work.

DEAD END, measured and reverted: making the plan branch's
"premise is not an available source fact" non-fatal (fall through to the
expressible-path-facts strategy, which CAN synthesize `at(point, ...)`
spellings) did NOT fix either test AND made
`loop_sorted_range_invariant` run >300 s instead of 0.2 s. That `?`
short-circuit is load-bearing for performance — do not remove it without
bounding the fallback search.

### Next steps

1. The representation work above, then these two tests.
2. Flip `CLICK_STRICT_EXIT_GATE` to the default and delete
   `surface_closer_blockers`.
3. The ClosedClaim restructure per the accepted design.

Quality follow-up (not a gate): `collect_surface_predicate_calls`
(proof.rs) and `collect_load_pointers` (kernel/api.rs) are dead and warn
on every build; they predate this work.
