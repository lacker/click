# split-buffer perf: last two SLOW audit findings

Status: open
Claimed: worktree-agent-aa455ca39fbbaf91c 2026-07-30

Scope: get the full `click-audit --keep-going examples` run to zero
SLOW findings by cutting owned_split_buffer_pipeline's ~7.7 s unit
verification (~3.6 s of it is kernel contract execution).

Context (2026-07-30): after the constant-normalization prefilter and
expanding both pipelines' execute_rest, the full audit is 314 s with 98
sites passing and exactly two SLOW findings, both bound by this unit:
- owned_split_buffer.click:235:5 (have) — 18.3 s; first site of its
  claim, so it also pays the once-per-claim cold reverify (~10.3 s).
- owned_split_buffer.click:427:5 (simp) — 13.5 s; its own expansion
  costs ~5.9 s.

Phase split for the unit (CLICK_TIMINGS on a targeted verify):
contract execution 3.6 s, claims 0.8 s, tactics ~0.7 s, get_left
execution 0.76 s, remainder environment building. The lever is the
3.6 s `prove_c_function_contract_execution_paths_with_environment` run
(symbolic execution with call rules over the 6-call body) — profile it
with `sample` or finer CLICK_TIMINGS before touching anything.

Repro:
  CLICK_TIMINGS=1 ./target/debug/click-verify \
    examples/owned-split-buffer/owned_split_buffer.click:200:5
  ./target/debug/click-audit examples   # fails fast at the first SLOW site

Done when: full `click-audit --keep-going examples` reports 0 site
failures (the 2 session failures for owned-string/owned-vector are a
different task) and all three gates stay green.
