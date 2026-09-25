# Branching graph DFS: checked success-path reachability

The already-verified `examples/modeled-binary-tree/` search is recursive and
branches over both children, but it traverses a disjoint, acyclic tree. It does
not cover a graph with cycles or shared successors. This is the smallest graph
step beyond the pointer-chasing `search` in `issues/dfs.md`: two read-only
successor arrays and one mutable visited array. The C below is the intended
algorithm, not a verifier-specific rewrite. Preserve it as the regression.

```c
int32 dfs(int32 *left, int32 *right, int32 *visited,
          int32 n, int32 cur, int32 to) {
    if (visited[cur] != 0) return 0;
    if (cur == to) return 1;
    visited[cur] = 1;
    if (dfs(left, right, visited, n, left[cur], to)) return 1;
    return dfs(left, right, visited, n, right[cur], to);
}
```

Termination and memory safety for bounded successor indices, with `decreases
unmarked(visited, 0, n)`, are checked in `mdtests/branching_graph_dfs.md`.
A nonzero return now also implies that `to` is in bounds, was unmarked at
entry, and is reachable from `cur` by a finite left/right path in the entry
graph. Full failure-path completeness remains a later claim: it must account
for nodes visited by the left call before the right call starts.

The checked contract owns `visited[0..n]`, views both successor arrays through
a `bounded_successors` resource carrying their bounds, and keeps each array
separate from `visited`. Its inductive postcondition says the unmarked count
cannot increase. The local marking store drops the count by one using
`unmarked_point_update`; the first recursive call's postcondition composes
with that strict drop, so the right call still descends. The contract now also
preserves every previously marked cell. This per-cell summary composes across both recursive calls and proves that a target still
unmarked at a recursive call's entry was unmarked at the outer entry. A
nonincreasing count alone would not establish that fact.

The termination proof needed one verifier repair: a recursive ranking obligation already
discharged by an exact established fact must not remain pending when the
stable-view return check runs. The kernel now drops only those exactly
discharged ranking obligations, never one justified by another pending
obligation. The mdtest checks the unchanged C through both recursive calls
and all early returns. The success-path proof now preserves a finite path
witness through each recursive result and relates it to the entry graph.

The older `issues/dfs.md` note that a loop guard cannot read through any
folded resource is not a general current limitation: for example,
`mdtests/composite_resource_vector_fill_loop_snapshot.md` checks a loop guard
reading `owner->len` from a folded owned composite. A special recursive or
matched-resource refusal would need its own current reduction before changing
the verifier. This graph example uses flat arrays, so that route is not its
first blocker.

## Reachability attempt (2026-09-23; lowering fixed 2026-09-25)

The original attempt reached the left recursive-success branch. The call
produced the required path existential, but its historical surface spelling
inserted a read-validity guard inside the existential and could not cite it.

Ordinary memory reads now lower as total logical terms. Both the unconditional
and nonzero-conditional call-guarantee citations verify in
`mdtests/call_existential_evaluated_load_guard.md` and
`mdtests/conditional_call_existential_historical_read.md`, including opening the
witness with `let satisfy`. Explicit `defined(...)` claims carry validity
separately, and C argument evaluation still checks the actual read.

## Checked composition (2026-09-25)

`mdtests/branching_graph_dfs.md` now checks every return path of the unchanged
C under the stronger contract. Direct success constructs `Path::Here`.
Left and right success open the corresponding call's historical existential,
prepend `Path::Left(rest)` or `Path::Right(rest)`, and apply `walk_frame` to
move the endpoint equality to the original graph snapshot. The standalone
lemma is checked in `mdtests/branching_graph_path_witness.md`; its induction
uses successor bounds and cell equality only within `0..n`, never equality
of whole memory snapshots or implicit read-validity claims.

The right branch crosses both the marking store and the left call. Explicit
per-cell transport supplies the two graph-equality premises. Symbolic
zero-based range membership now accepts exact index bounds with checked byte
extent, and final contract certification recognizes an already proved
algebraic existential through the typed alpha-identity index. The focused
regressions are `mdtests/graph_view_survives_marked_summary_call.md` and
`mdtests/conditional_algebraic_witness_contract.md`. Expansion also retains the
empty binder map required by a let-bound scalar call; a source-backed test
checks expansion and reverification of the historical witness fixture.

## Next design decision

Failure does not imply ordinary graph unreachability with arbitrary initial
marks: a previsited intermediate node can hide an otherwise reachable target.
Before implementing completeness, choose an all-unmarked initial condition
for the public theorem or define reachability through initially unmarked
nodes. Either route needs a recursive exploration summary that composes when
the left call marks nodes subsequently encountered by the right call.
Automatic fold read-range inference remains a separate, unapproved design;
it is not required for the success theorem now checked here.
