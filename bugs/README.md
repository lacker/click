# Verifier bugs

A bug is a reproduced defect in behavior Click already claims to support.
Humans and agents file bugs here without asking; only an explicit user request
authorizes new roadmap entries in `issues/`.

Examples include accepting a false claim, rejecting a documented valid proof
operation, crashes or hangs, violated work budgets, disagreement between proof
tools, and inaccurate, misleading, or unbounded diagnostics. Use the
[proof-failure triage guide](../docs/concepts/proof-failure-triage.md) to classify
the failure. Missing features and new design directions belong to the roadmap,
not here; report ambiguous cases to the user rather than bypassing issue policy.

Reproduce the defect before filing. A one-off observation or a suspicion from
reading code should be reported to the user as such. File one kebab-case `.md`
per independent bug, stating:

- the violated invariant;
- a small reproduction and intended regression that preserve the relevant
  original source pattern; and
- concrete acceptance criteria.

Directly under the title, state `Soundness: <label>.` with a one-paragraph
argument, using the labels defined in
[`issues/README.md`](../issues/README.md). A bug that lets a false claim
verify is `unsound`. Put `Priority: P1.` above its Soundness paragraph: it
blocks launch.

Write enough for a fresh contributor to act without the originating chat.
Tell the user what was filed. Delete the file when its fix, regression coverage,
and relevant documentation land.

The files in this directory are the backlog. This README does not maintain a
separate bug list.
