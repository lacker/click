# Profiler coverage — the two holes in the profiling story

Claimed: worktree-agent-afe95e523b42125d8 (2026-07-31)

## Why

The repo's settled invariant is that a slow *smart* tactic is an
expansion candidate and a slow *simple* tactic is an engine bug. To
apply it to the two slowest corpus members we have to be able to ask
"which is it?" — and today we cannot:

1. **Instrumentation hole.** The class-tagged `click timing: tactic ...`
   lines account for only ~3.7 s of `bubble_sort3_two_pass_sorted`'s
   ~137 s and ~19 s of
   `field_derived_precise_effect_after_metadata_write`'s ~198 s. The
   loop-invariant bundle path — the initialize phase, the preserve
   phase, and the invariant-closer replay — emits no tactic lines at
   all, so ~95 % of the runtime is unattributed.
2. **Tooling hole.** `click-profile` takes example *projects*
   (directories of `.c` + `.click`). Both slow tests are mdtests, so
   the profiler cannot be pointed at either of them.

## Scope

1. Emit class-tagged tactic timings for the invariant-bundle work, in
   the existing `click timing: tactic ...` format, with the class taken
   from the code (`source_tactic_class` / `ProofTactic::class()`), not
   guessed.
2. Teach `click-profile` to accept a `.md` mdtest (and a directory of
   them), reusing the mdtest extraction rather than duplicating it.
3. Report the real SIMPLE / SMART / CONTROL / certification split for
   both slow tests.

## Status

- [ ] Instrumentation
- [ ] mdtest mode
- [ ] Numbers

## Findings

(measurements land here)
