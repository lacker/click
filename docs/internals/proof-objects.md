# Proof objects

Click's internal `Proof` object is the persistent checked representation of an
evolving proof. It lets explicit tactics and smart search share one semantic
transition boundary while retaining enough provenance to explain or expand the
result.

## Persistent proof state

`Proof` owns an immutable `ProofState`, a provenance `ProofNode`, shared proof
context, and one focused goal. Applying a checked operation returns a successor
that shares unchanged structure with its ancestor. A smart tactic can therefore
branch, inspect alternatives, and abandon candidates without cloning the
complete logical or execution state.

Goals carry the facts, resources, and symbolic execution state relevant to one
judgment. Typed scope, split, and join helpers preserve branch and loop
structure. A focus is only a cursor into the owned goal structure; it isn't a
second semantic state.

## Source proof and expansion types

`SourceProof` distinguishes an omitted proof, a smart proof request, and an
explicit tactic block. Parsed tactic statements become `ProofTactic` values.
Each tactic has a `TacticClass` used by checking, instrumentation, profiling,
and expansion.

`Proof` provenance retains the surface-expressible operation that produced each
checked successor. `ProofCertificate` is the current structured serialization
of those operations as `SimpleProofStep` values, including nested scopes and
branches. It can be rendered back to surface tactics for expansion. The
serialization carries no semantic authority of its own and need not exist
during ordinary verification in the intended architecture.

## Replay state inside a proof

`ExecutionProofState` owns every semantic path fact: the `CState`, the
execution frontier (program point, region, region start state, continuations),
the program-point states recorded on the path, the surface spellings the path
has lowered, case assumptions, execution facts, frontier-local loop clauses and
rules, function-entry prerequisites and derivations, planned statement
transitions, the freshness counters, the loop-effect goal and region flags,
branch provenance, deferred post-execution tactics, and the path's unfolded
predicates. Its `TacticReplayState` holds only cursors: the certificate
builder and expansion-capture state, all scheduled for retirement in phase 3.
It lives only as the execution snapshot of a `Proof` goal: the checked drivers
advance a `Proof`, and every source or generated proof tree is checked that
way. The earlier interpreter that advanced this context as a parallel engine
is gone; the remaining duplication of facts and `CState` between the snapshot
and the `Proof` is tracked for removal in `issues/replay-smell.md`.

Lowering and point proofs read execution data through `ExecutionView`, a
borrowed view of the frontier, recorded program-point states, surface
spellings, execution facts, and the `old(...)` reference state. It is built from
typed fields only (`ExecutionProofState::view`, or `ExecutionView::new` for a
planner's scratch state); nothing in it borrows the replay bag.

A surviving source or expansion cursor may own syntax position, focus,
attribution, and diagnostics. It must not own facts, resources, `CState`, an
execution frontier, or authority to construct a successor.

## Smart planning

Planning modules inspect `Proof`, rank candidate operations, and explore
persistent descendants within deterministic budgets. They use the same checked
simple and structural operations as explicit tactics. A candidate is not
accepted merely because the planner labels it successful; success is a
completed checked descendant.

A checked `simp` derivation is added only for a common, bounded,
replayable shape: it must emit simple steps the kernel checks one at a
time and a certificate can replay. That the search-based `simp` decision
procedure could decide a goal is not a criterion; it is a diagnostic, not
an authority.

For expansion, the completed proof's provenance is filtered to the selected
source site and rendered as an explicit Surface Click proof. The complete
rewritten source is then parsed and verified through the ordinary entry point.
That check validates provenance extraction, surface synthesis, rendering,
parsing, lowering, and source interpretation without preserving a second
semantic proof engine.

## Kernel derivations

Kernel structures in `src/kernel/primitives/proof_objects.rs` represent
primitive semantic evidence and obligations. They are separate from the
surface expansion: surface proof steps encode user-reviewable operations,
while kernel derivations justify the underlying proposition, execution,
memory, or resource transition. `Theorem` is authority for an established
proposition; `PropositionDerivation` retains the checked reasoning tree; other
typed evidence records execution and memory transitions.

The target invariants are:

- explicit and smart tactics advance one `Proof` through checked operations;
- smart success is a completed checked descendant, not an unchecked plan;
- selectors resolve against the focused state where their operation applies;
- proof checking doesn't depend on failed-search history;
- expansion extracts exact attributed provenance and emits verifiable Surface
  Click;
- persistent proof-state sharing must not permit mutation of an earlier state;
- instrumentation can observe work but cannot change the validity decision.

Until the compatibility migration finishes, the parallel replay types above
are an explicit exception to the first invariant. Don't add new semantic fields
or operations to them.

The former chronological proof-object design log is preserved at
`design/proof-object-api.md`; this page describes the current architecture.
