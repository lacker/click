# Enforce tactic time budgets in the regular test pass

Status: open (build next)
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
