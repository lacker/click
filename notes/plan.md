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

| Task file (tasks/) | Status | One-line scope |
|---|---|---|
| slow-simple-engine-bugs.md | open | Rule 5's two known violations: the 65 s invariant-closer replay (fixing it de-quarantines bubble_sort3) and field_derived's 29 s `fold`. Lead: the replay repeats the planner's own derivation — cache it |
| named-memory-states-arc.md | open | Memory states named in a derivation DAG. Stages 1–5 landed (field_derived 487→198 s; `old` names function entry; two corpus members cleared). Next increment: a fourth edge kind (block allocation) — measured lead |
| store-provenance-family.md | open | The acceptance corpus, with current per-member frontiers. All remaining members now fail *downstream* of load equality: certificate lowering, grouped-simp certification, ghost-resource representation, one propositional gap, one permission gap |
| expansion-aggregate-object-spelling.md | open (small) | The last lib `#[ignore]`: unfold decomposes `object(owner)` separation and expansion loses the aggregate spelling. Printing/re-folding, not soundness |

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
