# Plan — status board

Last updated: 2026-07-31. Read `conventions.md` before working; each
task lives in its own file under `tasks/`. Claim a task by setting the
`Claimed:` line in its file. Finished task files are deleted, not
archived — their record is `git log -- notes/`.

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

## Board — open work

One file in `tasks/` = one work item, exactly (owner rule, 2026-07-31).
Reference material lives in `notes/` root, never in `tasks/`.

| Task file (tasks/) | Status | One-line scope |
|---|---|---|
| certificate-spelling-gap.md | open (critical path) | Successor: the prover landed (owner_buffer FIXED, de-quarantined 0.06 s); all three remaining members provably fail in certificate lowering's surface spelling of snapshot-orphaned premises |
| loadable-bridging-cost.md | open (small) | The scoped DAG bridging that closed the loadable gap is hot: owned-string now takes 5m26s to reach its next frontier. Profile before extending; memo is generation-invalidated by load-caching stores |
| owned-vector-forward-fix.md | open (queued) | Propositional `Implies` gap at vector_replace_if tactic 8; retest after the critical path lands |
| field-derived-fold-cost.md | open (small) | 29 s SIMPLE fold; re-profile after the critical path lands |

## Reference docs

- `conventions.md` — gates, multi-agent workflow, decision boundaries,
  working rules, settled invariants, tooling flags. Read first.
- `regression-history.md` — bisect verdicts, diagnoses, and experiment
  matrices behind the open regression tasks.
- `memory-dag.md` — the landed named-memory-states arc: invariants,
  wins, dead ends, and the punted fourth-edge-kind increment.
- `canonical-memory.md` — original design brief for that arc.
- `language-proposals.md` — surface-language proposals (parked; any of
  these is a Surface Click semantics change and needs the owner).

## Done criteria for the current arc

The performance-tools project is done when: `click-audit` reports zero
site failures on the green corpus (achieved 2026-07-31: 100 sites, 0
failures, 144 s); `click-profile` stays clean — no SIMPLE over 500 ms,
no SMART over 2 s, UNATTRIBUTED ~0 — on every verifying project and
mdtest (violated today by exactly the two engine bugs above); and no
quarantine-for-cost entries remain.
