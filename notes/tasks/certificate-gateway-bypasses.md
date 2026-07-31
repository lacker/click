# Certificate-gateway bypasses (from the one-gateway audit)

Status: claimed — redesign accepted, migration in progress
Claimed: claude/nervous-ptolemy-90e738, 2026-07-30
Claimed:

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
