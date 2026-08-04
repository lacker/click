# Add optional termination certificates for C functions

## Priority and dependency

This is a later capability, not a prerequisite for recursive C verification.
Implement it only after partial-correctness contracts and recursive C
components are sound and documented.

## Problem

Some callers need more than “if the function returns.” They may need to prove
that code after a call is reachable, establish total correctness of an
algorithm, or rule out an accidentally infinite loop. Today Click has no
separate way to state or prove that stronger claim.

Making termination mandatory would reject event loops and other legitimate C.
Silently treating ordinary `ensures` as termination would repeat the kernel
conflation fixed by the partial-correctness work.

## Desired design

Explicit `decreases` declarations should supply the ranking arguments for a
termination certificate. Use them at the boundary whose cycle they justify:

- a function-level `decreases` clause ranks calls within its recursive
  call-graph component; and
- a loop-region `decreases` clause ranks that loop's back edges.

Their absence leaves the corresponding construct partially correct. To certify
that a whole function terminates, Click must prove every reachable loop and
recursive cycle well-founded and must call only functions that are themselves
known to terminate.

Start with one nonnegative integer measure. At each relevant edge, establish:

- the next measure is defined, nonnegative, and strictly smaller than the
  current measure; and
- all paths either return or reach such a decreasing edge.

A base path with no back edge or recursive call need not prove an otherwise
unused incoming measure nonnegative. The proof obligation belongs to the
descending edge, matching the pure-function rule.

For mutually recursive functions, compare the callee's instantiated measure
with the caller's current measure. For loops, compare the next-iteration value
with the current loop-head value. A loop variant may refer to locals in scope at
that loop; a function recursion measure uses function-entry contract values.
Multiple nested cycles may eventually need tuples, but the first implementation
should reject unsupported shapes explicitly rather than infer termination from
a heuristic.

The resulting kernel object must be distinct from body-safety and partial
contract evidence. A total-correctness rule may be constructed only from both
partial correctness and termination evidence. Ordinary opaque-call application
must not start depending on the stronger object.

Do not use `terminates` as an unproved assertion. If convenient, it may later be
a readable theorem consequence of a checked `decreases` clause.

## Focused mdtests

- `c_decreases_recursive.md`: a direct countdown recursion proves termination.
- `c_decreases_loop.md`: a bounded loop proves termination with a loop variant.
- `c_decreases_rejects_same_measure.md`: a recursive self-call at the same
  measure remains partially verifiable but cannot receive a termination
  certificate.
- `c_decreases_rejects_bad_loop_path.md`: one nondecreasing back edge rejects
  total correctness.
- `c_decreases_mutual_recursion.md`: a mutually recursive component shares a
  valid decreasing discipline.
- `c_partial_without_decreases.md`: the same partial recursive function remains
  accepted when no termination claim is requested.
- `c_termination_allows_reachability.md`: a caller can use certified termination
  where a reachability-sensitive proof actually requires it.

## Non-goals

- Proving that an infinite service is productive.
- Fairness of a scheduler or external input source.
- Temporal “eventually” properties.
- Automatically guessing ranking functions.

Those are not termination-by-decrease problems and should not be smuggled into
this feature.

## Acceptance criteria

- C partial correctness remains the default.
- `decreases` produces a separate, kernel-checked termination certificate.
- Direct recursion, mutual recursion, and loops have focused positive and
  negative coverage for the supported measure shape.
- Callers use termination evidence only when they explicitly need a
  reachability/total-correctness fact.
- Documentation clearly distinguishes termination from safety and
  productivity.
