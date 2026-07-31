# Enforce tactic time budgets in the regular test pass

Status: landed 2026-07-31 (master 7eb5860); one owner decision pending
Claimed:

No separate profile sweep: the mdtest and examples harnesses already
run every child with `CLICK_TIMINGS=1` and capture the per-tactic
timing stream (added 2026-07-31 for timeout attribution) — today it is
only consulted on timeout and discarded otherwise. Instead, after each
isolated child exits, the parent scans the timing lines it already has
and fails that test if any tactic broke its budget, naming the tactic,
its class, and its time.

Budgets (conventions.md, owner ruling 2026-07-31):

- SIMPLE tactic over 500 ms — fail (engine bug).
- SMART tactic over 2 s — fail (expand it).
- Certification phases held to the simple standard.

Design points settled with the owner (2026-07-31):

- Applies to the regular `cargo test --test mdtests` / `--test examples`
  passes; no fourth gate. `click-profile` stays the human diagnostic.
- Expect-fail tests enforce too: budgets apply to every tactic that
  *finished*, regardless of the file's verdict (slow failure is a
  finding).
- Children run in parallel so timings are load-noisy; the budgets have
  58–130x headroom over the known violations, so enforce at face value.
  If it ever flakes, raise the threshold — do not serialize the suite.
- Quarantined tests are skipped by default and thus not enforced; when
  one de-quarantines it picks up enforcement automatically.

Implementation notes: the timing-line parser lives in `src/cli.rs`
(`last_unfinished_tactic`, `without_timing_lines` — extend, don't
duplicate). Timing lines carry class (`class simple|smart|control`) and
seconds on the finish line.

Done when: a test with an over-budget tactic fails with a message
naming it, the full green corpus still passes, and a deliberate
slow-tactic fixture proves the check fires.

## Landed, and what the gate immediately found (2026-07-31)

Enforcement lives in `run_isolated` (src/cli.rs, `tactic_budget_violations`),
exclusive-time accounting, `CLICK_DISABLE_TACTIC_BUDGETS=1` bypass.
click-expand gained mdtest mode (`file.md:line:col`, md coordinates,
whole-markdown output) because rule 6 was otherwise unsatisfiable for
mdtests.

First sweep found 7 violating tests in the green corpus; 5 fixed by
expansion (loop_sorted_range_invariant 14.9 s smart simp,
fill_n_segment_invariant, bubble_sort3_loop_permutation,
owned-segmented-buffer, owned_buffer_len_cap_data). Expanding
bubble_sort3_loop_permutation's bounded_execute also removed a 3-4 s
exclusive CONTROL violation (certified_alternatives) — container cost
that vanished when its child was expanded.

**Owner decision pending — pure case splits.** sort3_sorted and
bubble_sort3_loop_sorted (both quarantined) have smart simps whose
entire content is a case split: the accepted certificate is an `if`
tree with EMPTY branches (each leaf goal closes via the ordinary
path-end check — kernel replay accepts this). The surface parser
refuses an `if` branch with no tactics, so the expansion is
unspellable. `assumption();` as a leaf filler was tried and fails
replay ("did not match any current proposition goal" — leaves have no
open goal). Options: allow empty `if` branches in proof scripts
(grammar relaxation; checker semantics already exist), or add an
explicit no-op/case-split marker tactic. Both are Surface Click
changes = owner's call.
