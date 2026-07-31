# Plan — status board

Last updated: 2026-07-31. Read `conventions.md` before working; each
task lives in its own file under `tasks/`. Claim a task by setting the
`Claimed:` line in its file.

## The project: fixing the performance tools (owner, 2026-07-31)

Three tools work together so Click users can speed up code, diagnose
slowness, and detect performance bugs in Click itself: `click-profile`,
`click-expand`, `click-audit`. Desired state:

1. The tests work and are fast.
2. Every tactic is classed smart or simple (the verifier decides).
3. Simple tactics are fast — always.
4. `click-profile` reports any slow tactic (projects AND mdtests).
5. A slow SIMPLE tactic is an error in Click, and the profiler says so.
6. A slow SMART tactic is expanded by `click-expand` into simple ones.
7. Profile-then-expand accounts for ALL slowness; there is no other
   source. Corollaries, from measured cases:
   - Expansion REDUCES slowness to simple-tactic slowness (a certificate
     whose replay is slow = an engine bug per rule 5, not a resting
     state — bubble_sort3 is the type case).
   - Smart search must be bounded: a FAILING tactic must fail fast, and
     slow failure is a profiler finding (field_derived's 162 s simp).
   - Non-tactic machinery (certification, environment building) is held
     to the simple standard, and the profiler's UNATTRIBUTED bucket must
     stay ~0; nonzero unattributed time is a tooling bug.
8. `click-audit` checks expansion works across whole projects; its
   purpose is detecting bugs in Click itself.

Language-design decisions are explicitly punted to a later group
(`language-proposals.md`).

## Board

| Task file (tasks/) | Status | One-line scope |
|---|---|---|
| split-buffer-perf.md | done | Audit at 0 SLOW: constant test hoisted above the equality search; transport equality memoized |
| one-gateway-check.md | done | Audit done: mid-execution gated by replay_smart_plan; 3 bypasses in the ungrouped post-execution drain (39 corpus hits) — see file for follow-up tasks |
| cli-consolidation.md | done | Helpers single-sourced in src/cli.rs; click-verify DIR mode + docs; click timing: drift is now a loud error or a counted warning |
| proof-panics.md | done | 78 sites classified; 7 converted, 71 invariant-true; the design review's cited example is a false positive |
| while-invariant-rule.md | done | Fenced: rule is `#[cfg(test)] pub(super)`, no callers; a sound fix needs `CLoopInvariantCheck`, not a flat `Vec<Proposition>` |
| docs-vocabulary-pass.md | done | Inventory + synonyms documented; audit docs match the binary (worktree-agent-ae547bd447d583266) |
| parser-ergonomics.md | done | Both stale: `a->b->c` verifies (new mdtest), else already optional; 22 no-op else paddings removed; doubly-indirect `owns` parked as C5 |
| lib-ignored-expansion-tests.md | done | Premise policy fixed: 5 of 7 un-ignored. Certificates now carry consumed conditions + non-reconstructible permissions. Found a latent `condition_polarity_equivalent` None==None bug, filed separately |
| certificate-gateway-bypasses.md | done | Gate flipped and then made structural: closing an exit claim needs a ClosedClaim whose certificate constructor is private to the one function that replays. strict_exit_gate(), surface_closer_blockers and three more parallel arrays deleted; grouped/ungrouped share one discharge function |
| store-provenance-family.md | parked | owned-string, owned-vector, 6 mdtests — blocked on the canonical-memory arc |
| named-memory-states-arc.md | open | The canonical-memory representation change: memory states named in a derivation DAG instead of embedded as values. Staged behind `CLICK_DISABLE_MEMORY_DAG`; unparks store-provenance-family. Stages 1, 2, 2a landed — `old(...)` now names function entry instead of resolving positionally, un-ignoring `verifies_old_memory_loop_invariant` and de-quarantining `fill_tail_keeps_first`. Stage 3 landed: the closer now refutes vacuous alias guards from recorded separation and splits a goal at its final index under an assumed bound. `bubble_sort3_two_pass_sorted` passes but at 137 s, so it stays quarantined on cost. Stages 4–5 landed: a DAG-guided cell lookup resolves a load along derivation edges and relates sibling snapshots through a common ancestor, cutting `field_derived` from 487 s to 198 s (flag A/B confirms the arc, not stage 3). `bubble_sort3` is unmoved — its cost is fact scanning, not snapshot comparison, and only 6 of 540k comparisons there are load-vs-load. Two snapshot-equality scans retired (92 lines); two more attempted and reverted with diagnoses. No de-quarantines; every remaining member's frontier is off load equality |
| profiler-coverage.md | done | Both holes closed. The invariant closer's *replay* side (`c_loop_invariants_hold_at_back_edge_using`, run by the caller after `close_invariants` sets its flag) was untimed; so were both halves of the initialize phase. `click-profile <path.md>` now profiles mdtests, quarantined ones included, and reports an exclusive SIMPLE/SMART/CONTROL/certification split with an unattributed remainder. Answers: bubble_sort3 139.4 s = 49.4% simple / 50.3% smart / 0.0% unattributed — half of it a 65 s `close_invariants` replay, 130x over the simple budget, an engine bug not an expansion candidate. field_derived 210.3 s = 86.3% smart / 13.7% simple — a 162.6 s failing grouped `simp` plus a 28.9 s `fold` engine bug |
| condition-polarity-none-equivalence.md | done | Predicate sound (both sides need a canonical order form) + proof-backed snapshot bridge at four sites. input-cursor/owned-split-buffer sidecars regenerated (their premises were false); owned-segmented-buffer needed the transport source+target bridges. All four gates green |
| repo-hygiene.md | done | Executed with owner approval; worktree-claude verified (all 3 fixes on master via rebase-copy cd90c80) and deleted |

## Reference docs

- `conventions.md` — gates, multi-agent workflow, decision boundaries,
  working rules, settled invariants, tooling flags. Read first.
- `canonical-memory.md` — the named-memory-states arc (the intended fix
  for the store-provenance family). Larger than short-term; owner-gated.
- `design-review.md` — the ranked 2026-07 review (historical reference;
  actionable residue is in tasks/).
- `language-proposals.md` — surface-language proposals (parked; any of
  these is a Surface Click semantics change and needs the owner).

## Done criteria for the current arc

The profile/expand/audit ladder is done when the full audit reports
zero site failures on the green corpus (only split-buffer-perf.md
remains) and the profile stays clean (currently: no SIMPLE >500 ms, no
SMART >2 s in any verifying project).
