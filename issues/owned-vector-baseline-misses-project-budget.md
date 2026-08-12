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
