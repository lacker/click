# Eliminate double execution

## Current state

Click normally executes C statements once, through checked proof-object
operations, and retains the resulting kernel-issued transition evidence. At
function exit the kernel can seal that retained trace into the checked function
execution used by claim and contract certification. Existing zero-rerun
regressions cover straight-line proofs, explicit C branches, proof-level case
partitions, shared continuations, verified and concretely executed loops,
post-execution resource folds, nested resource scopes, counted resources, and
`branch ensuring` interfaces.

Two fallback mechanisms still execute a function body independently after its
proof-directed execution:

1. In `finish_ordered_proof`, claim finishing uses retained proof evidence for
   supported shapes but selects `cached_independent_execution` for three
   explicit shapes:
   - an outcome proof with an unfolded predicate;
   - a quantified resource fold or close after C execution; and
   - a counted entry whose output resources are closed implicitly rather than
     by an explicit checked `frame()`.
2. At the opaque-contract boundary, final certification reuses an exact,
   resource-rebased, or exhaustive entry-partition checked artifact when it
   can. If none matches, it silently falls back to fresh symbolic execution of
   the function body.

Consequently, one proof can still perform its proof-directed statement
execution, an independent claim execution, and another contract-finalization
execution. The independent-execution cache reduces repeated work but preserves
the wrong architecture. It can also produce the characteristic failure in
which proof construction succeeds but a later execution cannot reproduce it.

The proof object already retains statement theorems, checked branch structure,
proof-case partitions, resource representation transitions, and function-entry
resource materialization. Do not redesign those completed parts merely to
remove the remaining fallbacks.

The arena example verifies through nested `arena_region` and `arena_metadata`
scopes, but its sidecar does not yet contain the intended explicit
`arena_write` contract. That contract remains the end-to-end resource-shaped
acceptance case.

## Violated invariant

A completed checked proof object is the execution evidence for the function it
proved. Ordinary verification must not secretly execute the same C body again
to decide whether that proof was valid.

Every proof-object operation must check its explicit premises and return a new
valid proof object. At function exit, sealing composes those already-checked
operations. It may validate lineage, source order, exhaustive branch coverage,
and exact state compatibility; it must not reconstruct the proof by executing C
again or by re-proving accumulated facts from an ambient context.

If a checked operation lacks information required by later composition, retain
the smallest output-sized identity or state delta when that operation succeeds.
Reject a mismatched transition at the operation or join that creates it. Do not
hide the mismatch behind independent execution.

## Kernel and tactic boundary

The proof object itself is the checked authority. Do not introduce a parallel
fact-derivation or certification representation that must later be aligned with
the proof object. In particular, removing double execution does not call for a
`CheckedFactDerivation`-style database of facts to be proved a second time.

Smart tactics may search or plan and then emit explicit simple proof steps.
Simple steps and final sealing must remain deterministic and fast. Their kernel
checks may use narrow decision procedures appropriate to the explicit rule,
but they must not recover a missing premise through general ambient
disjunction splitting, unrelated theorem search, or recursive reconstruction
of the proof context.

Per-path state should have one canonical checked representation. Avoid parallel
vectors of facts, conditions, snapshots, and evidence whose correctness
depends on positional alignment. Persistent sharing and output-sized deltas are
appropriate; cloning or rescanning accumulated path history per operation is
not.

## Remaining implementation slices

Work from current `master` and remove one fallback shape at a time. Each slice
must be independently green and must delete the guard or fallback it replaces.
Do not accumulate a second implementation alongside the old one.

### 1. Pin each remaining claim fallback

Add or identify a focused regression for each of the three guarded shapes in
`finish_ordered_proof`. Reset the checked whole-function execution counter,
verify the proof, and assert that claim finishing performs zero whole-body
executions. Before changing representations, confirm the exact checked
transition or state delta that the existing proof object lacks.

### 2. Remove the claim fallbacks individually

For each guarded shape:

1. Make the proof-object operation that already checks the unfold, resource
   transition, or implicit closure retain the minimum information needed to
   seal its successor.
2. Have sealing consume that checked successor directly.
3. Delete that shape's fallback guard immediately.
4. Add a negative test showing that forged, stale, or mismatched state is
   rejected without executing the body.
5. Run the focused regression and the existing zero-rerun suite before moving
   to the next shape.

An implicit counted-resource close should use the same kernel-checked state
transition as its explicit equivalent; it should not be justified by rerunning
the function. Outcome predicate unfolding similarly needs a checked
proof-object successor, not an ambient fact derivation reconstructed during
sealing.

### 3. Remove opaque-contract fallback execution

Once claim finishing always supplies a checked execution artifact, classify
the remaining reasons exact, resource-rebased, or entry-partition reuse can
fail. Repair composition at the operation that loses the necessary identity.
If a supplied artifact is incompatible, final certification must report that
incompatibility rather than execute the body.

Delete the `(None, None, None)` body-execution fallback and then remove the
independent-execution cache. Retain the execution counter as regression
instrumentation if it remains useful for proving that ordinary verification
performs no hidden body execution.

### 4. Add the arena acceptance contract

Add the intended `arena_write` contract to `examples/arena/arena.click`, keeping
the existing C unchanged and its mutable footprint narrow. Its nested resource
scopes must verify with zero independent whole-body executions.

## Not in scope

The following are intentional independent checks, not double execution in this
sense:

- `click expand` verifies the rewritten source artifact it emits;
- `click audit` cold-verifies original and rewritten artifacts;
- expansion regressions independently verify serialized proof text; and
- an opaque function call applies its installed rule without executing the
  callee body.

This issue does not require new surface syntax, changed C semantics, rewritten
C, a general proof-object redesign, or removal of search from smart tactics.

## Acceptance criteria

- `finish_ordered_proof` contains no independent whole-function execution or
  independent-execution cache.
- Opaque-contract certification never executes a supplied proof's function
  body when artifact reuse fails; it reports a local evidence error.
- A completed proof seals its existing checked proof-object state directly;
  finalization does not re-prove accumulated facts.
- Simple checks added or used by this migration, and final sealing, perform no
  ambient case search and remain approximately linear, up to logarithmic
  indexes and output-sized deltas, in selected C, Click, proof state, and
  certificate size.
- Focused zero-rerun and negative tests cover every removed fallback shape.
- The explicit `arena_write` contract verifies without changing its C source,
  weakening resource semantics, or adding proof-only C structure.
- Documentation describes proof-directed execution as the sole ordinary
  verification model while preserving the intentional independent checks
  listed above.
- `scripts/check.sh` passes.
