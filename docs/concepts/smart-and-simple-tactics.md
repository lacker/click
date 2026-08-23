# Smart and simple tactics

Simple and smart tactics differ in who chooses the proof steps.

A simple tactic names a bounded operation: apply this theorem with these
premises, unfold this definition, execute this statement, or split this goal.
The verifier checks the requested transition directly. Work may scale with the
explicit input and affected proof-state delta, but it must not perform hidden
project-wide search.

A smart tactic is a planner. It examines the proof state and tries candidate
checked operations on persistent alternatives under deterministic work
budgets. `auto`, `simp`, and other tactics classified as smart can fail to find
an existing proof. That is bounded incompleteness, not evidence that the claim
is false.

Smart search remains outside the trust boundary:

- search can advance proof state only through checked simple or structural
  operations;
- a reported success must be a completed checked proof state;
- expansion must extract an equivalent sequence of surface-level simple
  tactics and verify the rewritten source;
- a missed or exhausted budget must produce a bounded, actionable failure.

Use a small smart tactic when it closes a local, routine gap. Prefer explicit
simple tactics when proof intent or performance matters. Split a difficult
goal before asking search to explore more possibilities. Don't raise limits or
reshape the verified C merely to accommodate the search heuristic.

See [Tactics](../reference/tactics/index.md) for classification and [Proof-
failure triage](proof-failure-triage.md) for the boundary between an ordinary
search miss and a tooling defect.
