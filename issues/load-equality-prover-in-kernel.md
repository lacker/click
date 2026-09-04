# Move the global load-equality prover out of the kernel

`PureFactContext::memory_loads_proven_equal`
(`src/kernel/assumptions/condition_reasoning/memory_conditions.rs`) decides
whether two loads of one cell taken at different memory snapshots denote
the same value. Its cheap legs are checks: fact transport, resolving a load
to a recorded value, the memory DAG's recorded edges, and a direct
snapshot match. Its last leg, `c_memory_load_is_unchanged`, is a prover: it
reconstructs the cell's write history from the effect summaries and
mutates-only facts in scope and frames the loaded pointer across each
intervening effect. Fact matching modulo snapshots
(`conditions_equal_modulo_proven_snapshots`, used by
`proves_condition_exact_or_snapshot` and the decision procedure's fact
scans) calls the decision for every pair of loads a fact and the goal
align, and the framed-load prover's own decisions scan facts again, so the
decision re-enters itself with a branching factor of the number of facts.

The recursion is cut by `MEMORY_LOAD_EQUALITY_DEPTH_LIMIT = 2`
(`src/kernel/assumptions.rs`), which the slice 7 census found met
345,653 times over the examples and 315,061 over the mdtests, marking the
enclosing decisions truncated so the memo layers cannot cache them. It is
the one bound in `issues/simplify-kernel.md` that no counter-free
replacement inside the kernel removes, because it does not bound a walk
over a well-founded structure; it caps a search. Measured on owned-vector
(2026-09-03, `click profile`, chunk E of slice 7 as the baseline):

| variant | wall | framed-load walks |
|---|---|---|
| depth of two | 7.5 s | 611 |
| cycle check on the pair | 32 s | 4,733 |
| cycle check and a memo per pair | 28 s | 4,732 |
| nested queries skip the prover | 9.5 s | 138 |

The memo does nothing because the pairs are distinct, which is what a
search produces; the last variant is the depth limit under another name.

## Violated invariant

The kernel checks; it does not search. A kernel decision is decided by
rules whose work is bounded by the inputs they name, and search belongs to
the surface's smart tactics, whose results are certificates the kernel
then checks. Global load equality across snapshots should be decided from
recorded evidence only: exact facts, DAG edges crossed by cheap predicates,
and a snapshot-equality fact a tactic established and recorded. Matching a
fact against a goal modulo snapshots should then be a canonicalization by
recorded evidence followed by a lookup, with no recursion.

## Intended regression

A proof whose goal mentions a load at a snapshot after a verified call and
whose fact was recorded at the snapshot before it, where the call's effect
summary frames the loaded pointer, should still verify, and it should do so
through a recorded snapshot-equality fact rather than a proof the kernel
runs at match time. A scaling regression should show that matching a goal
against N such facts costs work near-linear in N, with the framed-load
prover never invoked from fact matching. The perpetual-service and
owned-vector examples exercise this path most (their framed-load walk
counts above); they must verify unchanged.

## Acceptance criteria

- A census records, per claim, which loads the framed-load prover decided
  that no cheaper leg could, and what fact the surface would have to record
  in its place.
- A surface tactic (transport, frame, or a completion of the call step)
  records the snapshot-equality fact the kernel needs, as a checkable
  certificate.
- `memory_loads_proven_equal` decides from recorded evidence only; the
  framed-load reconstruction is deleted from the kernel or moved behind a
  surface certificate, and `MEMORY_LOAD_EQUALITY_DEPTH_LIMIT` is deleted
  with no counter, depth, or tier in its place.
- The scaling regression above lands, both harnesses pass, and the
  `click profile` work units of perpetual-service and owned-vector do not
  rise.
- `issues/simplify-kernel.md` no longer lists the load-equality depth as a
  remaining bound.
