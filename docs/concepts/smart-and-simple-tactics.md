# Smart and simple tactics

Simple and smart tactics differ in who chooses the proof steps and where the
cost of that choice is paid.

A simple tactic requests one deterministic checked operation: apply this
theorem with these premises, unfold this definition, execute this statement, or
split this goal. The verifier checks that transition directly, without
heuristic planning, premise selection, alternative-rule search, or speculative
proof branching. The operation may consult the current proof context through
indexed lookups; `step()`, for example, checks one C transition with the whole
indexed fact and resource context available.

Simple checking must also be fast and output-sensitive. Work may scale with the
tactic's explicit input, the affected program operation, indexed access to the
current proof context, and the proof-state delta it produces. It must not scan,
compare, or copy unrelated ambient state. A slow simple tactic is a verifier
performance defect, not a candidate for further expansion.

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

Expansion is therefore both an audit boundary and a performance operation. It
replaces avoidable planning and search with direct checking of the selected
operations. The rewritten proof still pays for parsing its explicit text and
for the unavoidable semantic work of each transition, so a tiny smart tactic
need not become measurably faster. A smart hotspot should, however, lose
approximately all cost that can conveniently be removed by making its choices
explicit; a materially slow simple leaf remains an engine bug.

Use a small smart tactic when it closes a local, routine gap. Prefer explicit
simple tactics when proof intent or performance matters. Split a difficult
goal before asking search to explore more possibilities. Don't raise limits or
reshape the verified C merely to accommodate the search heuristic.

See [Tactics](../reference/tactics/index.md) for classification and [Proof-
failure triage](proof-failure-triage.md) for the boundary between an ordinary
search miss and a tooling defect.
