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
