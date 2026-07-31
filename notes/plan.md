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

Finish order (owner, 2026-07-31): budget enforcement first, then the
regression burn-down, then the two engine bugs. Punted: language
proposals, and the arc's fourth-edge-kind increment unless a regression
fix needs it.

| Task file (tasks/) | Status | One-line scope |
|---|---|---|
| mdtest-budget-enforcement.md | landed | Budgets enforced in the regular passes; 5 corpus sites expanded green; empty `if` branches now legal (owner 2026-07-31). Residue: pure-case-split expansions are unfaithful (per-path merge bug) — 2 tests quarantined, same family as the certificate-lowering regressions |
| separation-containment-prover.md | open (critical path) | The one design item gating owner_buffer, bubble_pass3, field_derived and likely vector_fill: deterministic exact-fact containment for constant-offset cells vs value-dependent ranges. Both fix agents terminated at this wall; direction and dead ends recorded |
| store-provenance-family.md | open | Corpus record: bisect verdicts for four members, forward-fix for the rest. owned-string is independently actionable (loadable permission plumbing) |
| slow-simple-engine-bugs.md | open | Rule 5's two known violations: the 65 s invariant-closer replay (fixing it de-quarantines bubble_sort3) and field_derived's 29 s `fold`. Lead: the replay repeats the planner's own derivation — cache it |
| expansion-aggregate-object-spelling.md | open (small) | The last lib `#[ignore]`: unfold decomposes `object(owner)` separation and expansion loses the aggregate spelling. Printing/re-folding, not soundness |
| named-memory-states-arc.md | paused | Stages 1–5 landed (field_derived 487→198 s; two members cleared). The fourth-edge-kind increment is punted unless a regression fix needs it |

## Reference docs

- `conventions.md` — gates, multi-agent workflow, decision boundaries,
  working rules, settled invariants, tooling flags. Read first.
- `canonical-memory.md` — design brief for the named-memory-states arc.
- `language-proposals.md` — surface-language proposals (parked; any of
  these is a Surface Click semantics change and needs the owner).

## Done criteria for the current arc

The performance-tools project is done when: `click-audit` reports zero
site failures on the green corpus (achieved 2026-07-31: 100 sites, 0
failures, 144 s); `click-profile` stays clean — no SIMPLE over 500 ms,
no SMART over 2 s, UNATTRIBUTED ~0 — on every verifying project and
mdtest (violated today by exactly the two engine bugs above); and no
quarantine-for-cost entries remain.
