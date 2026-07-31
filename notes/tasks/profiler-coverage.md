# Profiler coverage — the two holes in the profiling story

Claimed: (released 2026-07-31; worked on branch
worktree-agent-afe95e523b42125d8, not merged to master)

## Why

The repo's settled invariant is that a slow *smart* tactic is an
expansion candidate and a slow *simple* tactic is an engine bug. To
apply it to the two slowest corpus members we had to be able to ask
"which is it?" — and could not:

1. **Instrumentation hole.** The loop-invariant bundle path emitted no
   class-tagged timings for its dominant cost, so most of each slow
   run was unattributed.
2. **Tooling hole.** `click-profile` took example *projects*
   (directories of `.c` + `.click`). Both slow tests are mdtests, so
   the profiler could not be pointed at either of them.

## Status

- [x] Instrumentation (3adb135)
- [x] mdtest mode + time accounting (fa00eab, d56dd01, 787bde2)
- [x] Numbers

## What was actually uninstrumented

The diagnosis differed from the initial guess, and the difference is
the whole answer. The *planning* side of the invariant closer was
already timed — that is the `simp` line at ~65 s. What carried no
timing at all was the **replay** side:

`ProofTactic::CloseInvariants` does nothing during replay but set
`region_invariants_closed`. The kernel re-derivation that gives it
meaning — `c_loop_invariants_hold_at_back_edge_using` — runs in
`verify_one_loop_preservation_proof` *after* the whole certificate has
replayed, outside any tactic's timing span. So the bundle was
re-derived twice per path and only the first was ever attributed.

Fix: `TacticReplayState` records where the `close_invariants` step sat
(`invariant_closer_step`), and the caller times its own work against
that tactic's identity. The class comes from
`source_tactic_class(&ProofTactic::CloseInvariants)` — the code, not a
guess — which is `simple`.

Two more gaps in the initialize phase: `verify_loop_initialization_pure_proof`
never reaches `replay_linear_tactics`, so neither its per-invariant
planning nor its per-step certificate replay was timed. Both now emit
the same `click timing: tactic` format. The planner is named
`plan_invariant_entry` and classified by the `by` clause it discharges.

No new *line kinds* were introduced — everything reuses the existing
tactic format, so `IGNORED_TIMING_KINDS` needed no new entries for it.

## The numbers (serial runs, dev profile, 2026-07-31)

### bubble_sort3_two_pass_sorted — 139.4 s, passes

| bucket | time | share |
|---|---|---|
| SIMPLE | 68.9 s | 49.4 % |
| SMART | 70.1 s | 50.3 % |
| CONTROL | 0 | 0.0 % |
| CERTIFICATION | 0.28 s | 0.2 % |
| UNATTRIBUTED | 0.06 s | 0.0 % |

Two steps are the whole run, and they are the same work done twice:

- `loop(1).preserve` `simp` — **65.7 s SMART** (the planner searching
  for the back-edge certificate)
- `loop(1).preserve` `close_invariants` — **65.1 s SIMPLE** (replaying
  the certificate that search produced)

`loop(0)` is the same shape at ~3.3 s each.

**Verdict: half smart, half a slow-simple engine bug.** The SIMPLE half
is 130x over the 500 ms simple budget. Per the settled invariant this
is *not* expandable: expanding the enclosing `simp` only emits the
certificate whose `close_invariants` replay is the other 65 s. The
engine path to fix is `c_loop_invariants_hold_at_back_edge_using`,
which matches the earlier finding that bubble_sort3's cost is fact
scanning (540k comparisons) rather than snapshot comparison.

### field_derived_precise_effect_after_metadata_write — 210.3 s measured, fails

This mdtest **fails** verification (it is quarantined as broken, not
merely slow), so no `function` total line is emitted and the split is
over measured tactic time. Wall clock was 214 s, so the measured time
is essentially the whole run.

| bucket | time | share |
|---|---|---|
| SMART | 181.4 s | 86.3 % |
| SIMPLE | 28.9 s | 13.7 % |
| CONTROL | 0 | 0.0 % |
| CERTIFICATION | 0 | 0.0 % |
| UNATTRIBUTED | 0 | 0.0 % |

The steps, all in the grouped `buffer_push.contract` proof:

- `simp` at `:84:5` — **162.6 s SMART** (the trailing grouped simp)
- `fold` at `:82:5` — **28.9 s SIMPLE**
- `have` at `:76:5` / `:75:5` / `:74:5` — 14.2 s / 2.7 s / 1.8 s SMART

**Verdict: overwhelmingly smart — expand-it territory, with one real
simple offender.** The 162.6 s `simp` is proof search that never
succeeds; the run ends with "grouped `simp` could not certify its
complete claim transition". Its cost is a *failure* cost, so expanding
it is not available until the underlying derivation works
(named-memory-states arc). The 28.9 s `fold` is a genuine slow-simple
engine bug, 58x over budget, and is actionable independently.

Certification is not the story in either test: 0.2 % of bubble_sort3
and zero of field_derived, which never reaches the kernel phase.

## Dead ends and things worth knowing

- **The 3.7 s / 19 s figures in the original framing did not
  reproduce.** On this commit the pre-fix stream already accounted for
  69.5 s of bubble_sort3's 141.5 s (the planner-side `simp`). The hole
  was real but was ~50 %, not ~95 %.
- **Auto-planned loop phases emit source indices that do not exist.**
  `verify_one_loop_preservation_proof` builds its program with
  `build_internal_proof`, so `source_index` is positional over the
  *generated* tactic vector. bubble_sort3's `preserve by { unfold(...); }`
  has one source tactic but the stream reports `source 7` and
  `source 10`. `c0_tactic_source_position` rejects those, which made
  the old profiler's hard error fatal on exactly the proofs worth
  profiling. The profiler now degrades to "no source location" and
  lists them. Making those indices honest is a separate task.
- **Measure serially.** Running both profiles concurrently inflated
  bubble_sort3 from 139 s to 153 s and field_derived from 210 s to
  231 s. The class *ratios* were stable to within a percentage point;
  the absolutes were not. Every number above is from a serial run.
- Both slow runs are ~2.5 min and ~3.5 min. Run them backgrounded.
- `field_derived`'s 210 s matches the 198.3 s recorded in
  `named-memory-states-arc.md` stage 4 (dev profile, different
  machine load), so the instrumentation did not change the cost.

## Repro

```sh
cargo run --quiet --bin click-profile -- --time-limit 10m --threshold 500ms \
  mdtests/bubble_sort3_two_pass_sorted.md
cargo run --quiet --bin click-profile -- --time-limit 10m --threshold 500ms \
  mdtests/field_derived_precise_effect_after_metadata_write.md
```

## Follow-ups this opens

1. `c_loop_invariants_hold_at_back_edge_using` is a 65 s simple replay
   in bubble_sort3. That is the engine bug the invariant says to fix
   before expanding anything around it. It is also *exactly* the work
   the smart planner already did one call earlier — the two halves of
   the run are the same derivation twice — so caching the planner's
   result for the replay is worth investigating before optimizing the
   derivation itself.
2. `fold` is a 29 s simple step in field_derived — a second, smaller
   engine bug on an independent path.
3. Auto-planned loop-phase certificates should report source indices
   the surface proof actually has, so their steps get locations.
