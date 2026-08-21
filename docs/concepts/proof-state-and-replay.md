# Proof state and replay

A Click proof doesn't manipulate only a list of logical formulas. Its state
also represents where symbolic C execution has reached and which memory and
resource claims remain available.

At a proof site, the state can contain:

- goals that remain to be closed;
- pure facts and assumptions;
- one or more symbolic execution paths at a frontier;
- path conditions and generated definedness obligations;
- memory snapshots, resource views, and permissions;
- named marks and structural context for branches or loops.

A tactic requests a state transition. A simple tactic makes that request
explicit enough for the checker to validate directly. A smart tactic searches
for several such transitions and emits a certificate. Replay reconstructs the
same initial state and validates each certificate step in order. It rejects a
step if its selected fact, program point, resource, path, or goal isn't
available.

This model explains why a search message isn't a proof. Search can rank
candidates, abandon paths, or hit a budget. Only the replayed transitions
become accepted evidence. It also explains expansion: expansion prints the
simple surface tactics represented by a replayable certificate, not a trace of
every failed search attempt.

## What a step carries

Advancing the frontier across a statement changes which facts are still
about the current state. The rule is fixed and cheap:

- A fact that mentions no memory is unaffected by the step and stays
  available as it is.
- A fact that mentions memory (a load term or a load variable) crosses the
  step only if the step's frame check shows the loaded cell is outside the
  statement's declared effect. `step() using { ... }` lists exactly the
  facts the step attempts to carry; `execute()` attempts every available
  fact, and its expansion writes the list it found. Each attempt is one
  bounded, deterministic check against the effect: distinct blocks, offset
  arithmetic, constant ranges, and a direct lookup of ownership (two owned
  resources are disjoint, including memory owned through a resource's
  footprint). The check does not search.
- A fact the step could not carry is not lost, but it remains a fact about
  the pre-step snapshot. Relating it to the current state afterwards takes
  an explicit `transport`, which may do more reasoning because the
  certificate asks for it.
- Comparing two terms never does frame reasoning. Two load variables for
  one cell on either side of an effect are equal only because a step or a
  `transport` carried the fact across.

The point of the rule is cost and honesty together: a step's work is
proportional to the facts it is told to carry, and every frame proof a
certificate depends on is a transition the certificate names.

Proof branches create path-specific states. A join is valid only after the
required facts and resources can be reconciled across all relevant branches.
Loop invariants play a similar role across an unbounded number of iterations:
the proof checks initialization, preservation, and the exit consequence rather
than unrolling the loop indefinitely.

See [Tactics](../reference/tactics/index.md) for individual transitions and
[Loops and invariants](loops-and-invariants.md) for structural obligations.
