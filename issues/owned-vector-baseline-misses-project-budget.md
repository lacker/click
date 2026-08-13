# Owned-vector baseline misses the project budget

The unchanged `examples/owned-vector` proof is not a stable member of the
30-second example gate. It has passed alone, but repeated ordinary runs have
failed at different smart sites, including:

- `vector_grow.contract`: a bare `step` at statement 12 crossed its two-second
  smart-tactic budget; and
- `vector_pipeline.contract`: a `have` was still searching when the project
  deadline expired.

Making one `vector_grow` premise explicit only moved the next run to the later
project-level failure. Do not tune the shared heuristics or raise either
budget. Treat these as proof decomposition work: profile a verified run, then
replace broad smart sites with small smart goals or explicit simple premises
in independently understandable chunks. Keep all C sources unchanged.

The project remains directly runnable with `CLICK_EXAMPLE=owned-vector`; it is
quarantined from the default example gate until repeated ordinary runs fit the
existing deadline.

As of 2026-08-11, before any budget pressure appears, the run fails promptly
at a certificate-lowering gap: a smart site proves `1 <= x + 1` from `x >= 0`
(a folded-constant increment lower bound), and Click has no explicit simple
certificate for that spelling. Two sibling gaps (`x < c1` from `x <= c2`, and
`x + 1 <= c1` from `x <= c2`) were closed by the constant-bound weakening
planners in `surface_certificates.rs`; the folded-constant `lower + 1`
orientation of `int32_increment_preserves_order` still needs a planner before
the budget question is reachable again.

## Acceptance criteria

- `CLICK_EXAMPLE=owned-vector cargo test --test examples -- --nocapture`
  passes repeatedly under the production 30-second project limit.
- No individual smart tactic crosses its existing class budget.
- Any explicit replacement states the real premises of the C statement; it
  does not reuse a fact after a call that invalidated it.
- No C source, proof obligation, heuristic, or budget is weakened to make the
  example pass.

## Update (2026-08-12): source proof succeeds, hard gate still fails

The source proof now constructs successfully under the production budgets
after the `vector_grow` call prerequisites and broad `vector_push` closure
were made explicit. A missing simple arithmetic certificate was also added
for `left <= right` plus `left != right` implying `left < right`. The public
`click verify` command is intentionally not green, because its mandatory
whole-claim expansion gate catches the replay failure below.

Profiling/expansion remains blocked by a distinct tooling failure. With event
collection enabled, or when expanding the `step` at line 378, the whole-claim
certificate generated for `allocated_vector_push` later contains a
`step() using` premise for a snapshot-local int32 equality that ordinary replay
does not have exactly. The expansion hard gate correctly rejects it. Preserve
this full sidecar as the regression: `click expand
examples/owned-vector/vector.click:378:13` must produce a proof that verifies,
and `click profile --time-limit 3m examples/owned-vector/vector.click` must be
a complete correctness run before the quarantine is removed.

Dropping that redundant-looking equality is not a valid local fix. A diagnostic
experiment then reaches the preceding generated plain `step`, where replay can
no longer decide the C condition `grown == 0` even though planning split on its
SSA value. The missing artifact is therefore a replayable transport from the
opaque call result through the C local store to the later branch load. Fix this
at the call/store execution-certificate boundary; do not special-case the
vector proof or silently omit the premise.

A fresh incomplete structured profile took 34.813s on its completed frontier.
It reported 145 smart source sites (87 dynamic attempts), with
`allocated_vector_push.contract` at 10.764s and `vector_grow` at 9.103s.
Independent kernel certification totaled 3.297s and whole-contract replay
2.155s. The largest completed deterministic tactics were an
`allocated_vector_push` unfold at 1.982s and frames at 724ms/571ms. These are
diagnostic-only until the whole-claim replay failure above is fixed; they must
not be used to justify expansion or unquarantining.
