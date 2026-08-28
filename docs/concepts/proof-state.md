# Proof state and checked transitions

A Click proof doesn't manipulate only a list of logical formulas. Its state
also represents where symbolic C execution has reached and which memory and
resource claims remain available.

At a proof site, the state can contain:

- goals that remain to be closed;
- pure facts and assumptions;
- one or more symbolic execution paths at a frontier;
- path conditions and generated definedness obligations;
- memory snapshots and resource facts, including derived views;
- named marks and structural context for branches or loops.

A tactic requests a state transition. A simple tactic identifies the operation
and its inputs explicitly enough for Click to check directly. A smart tactic
searches by trying the same checked operations on persistent descendants of
the current state. Search may rank candidates, abandon paths, or hit a budget;
it succeeds only by producing a completed checked state.

Internally, Click represents this persistent state and its checked transition
history with a proof object. Cheap structural sharing lets a smart tactic try
alternatives without copying the complete state. The proof object is an
implementation model, not a separate artifact that proof authors manipulate.

Expansion can extract the surface-expressible operations attributed to a smart
proof site and render them as an explicit proof. Click then verifies the
rewritten source through the ordinary verification entry point. The extracted
proof is sometimes called a *certificate* in implementation discussions, but
ordinary verification doesn't require users to create or manage certificates.

## What a step carries

Advancing the frontier across a statement changes which facts are still
about the current state. The rule is fixed and cheap:

- A fact that mentions no memory is unaffected by the step and stays
  available as it is.
- A fact that mentions memory (a load term or a load variable) stays true
  across the step when the kernel, executing the statement with the whole
  proof context visible, proves the loaded cell is outside the statement's
  effect: the cell keeps its name, so the fact is literally unchanged. Nothing
  is carried by list; `execute()` is the repetition of `step()`. That
  disjointness is one bounded, deterministic check against the effect:
  distinct blocks, offset arithmetic, constant ranges, and a direct lookup of
  ownership (two owned resources are disjoint, including memory owned through
  a resource's footprint). The check does not search.
- A fact about a cell the context cannot prove untouched is not lost, but it
  remains a fact about the pre-step snapshot. Relating it to the current state afterwards takes
  an explicit `transport`, which may do more reasoning because that operation
  names the relationship to establish.
- Comparing two terms never does frame reasoning. Two load variables for
  one cell on either side of an effect are equal only because a step or a
  `transport` carried the fact across.

The point of the rule is cost and honesty together: a step's work is
proportional to the facts it is told to carry, and every frame proof on which
an explicit proof depends appears as a named transition.

Proof branches create path-specific states. A join is valid only after the
required facts and resources can be reconciled across all relevant branches.
Loop invariants play a similar role across an unbounded number of iterations:
the proof checks initialization, preservation, and the exit consequence rather
than unrolling the loop indefinitely.

See [Tactics](../reference/tactics/index.md) for individual transitions and
[Loops and invariants](loops-and-invariants.md) for structural obligations.
