# Authorize invariant-bearing population bodies across opaque calls

The base population-body fix makes an unconditional, nonrecursive composite
whose body contains only resources available to C execution after an opaque
call produces its first unit. A scoped `open` uses that already-active body in
place and closing the scope neither duplicates nor consumes it.

Bodies with pure facts, conditional bodies, and recursive bodies remain more
subtle. Their active representation can depend on a memory snapshot or a path
choice. Naively installing and refreshing those bodies caused existing owned
vector and owned box proofs to acquire overlapping stale memory ranges. They
must not be treated as a larger version of the stable ownership-only case.

## Regression

Have an opaque call consume `object(obj)` and produce `wrapper(obj)`, where the
wrapper owns the object and states a pure fact about it. The caller opens the
wrapper, performs a store that re-establishes the fact, closes it, and passes
the wrapper to another opaque call. Proof replay and independent whole-function
certification must agree without changing the C.

Add corresponding guarded and recursive cases only if they share the same
principled representation; otherwise split them into focused follow-up issues.

## Acceptance criteria

- The population body has one authoritative owned representation, not a folded
  unit plus a second linear copy.
- A mutable call refreshes snapshot-sensitive body resources and facts at its
  post-state before a later C access or contract transfer uses them.
- `open` exposes an already-active body without duplicating it, and close
  preserves exactly that body after checking its facts.
- Existing mixed-snapshot owned-vector and owned-box regressions remain green.
- A negative test still rejects access without the wrapper or raw body.
