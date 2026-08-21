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

Proof branches create path-specific states. A join is valid only after the
required facts and resources can be reconciled across all relevant branches.
Loop invariants play a similar role across an unbounded number of iterations:
the proof checks initialization, preservation, and the exit consequence rather
than unrolling the loop indefinitely.

See [Tactics](../reference/tactics/index.md) for individual transitions and
[Loops and invariants](loops-and-invariants.md) for structural obligations.
