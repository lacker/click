# Branching graph DFS: checked reachability and completeness

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
graph. With every entry cell unmarked, a zero return proves that no finite
left/right path reaches the target.

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
lemma is checked in `mdtests/branching_graph_paths.click`; its induction
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

## Checked failure completeness (2026-09-25)

The public theorem uses an all-unmarked entry condition. The recursive contract
allows arbitrary initial marks and adds three summaries: the target cell is
unchanged; a failed call leaves its root marked; and every newly marked node
has both successors marked. Previously marked nodes remain marked as before.

The failed outer call composes these summaries by splitting nodes into the
root, nodes newly marked by the left call, and nodes newly marked by the right
call. Monotonic marking carries the left call's closed successors across the
right call. This accounts for shared nodes and cycles without changing C.

`closed_marks_exclude_target` proves by structural induction that a path from a
marked node cannot leave a successor-closed marked set excluding the target.
`exhausted_zero_entry` constructs that set from the failure summary and the
all-zero entry array. Both are checked independently in
`mdtests/branching_graph_paths.click` and used in the complete C proof.
The zero-entry condition is essential: a previsited intermediate node can
block exploration of a reachable target.

The verifier changes supporting the public contract are small: reported post-return
`have` introductions accept algebraic universal binders, and certification
uses the typed alpha-identity index for established implications containing
quantifiers. Explicit assumption checking also compares quantified guards by
that typed identity. Expansion keeps quantifier braces inside a `have`
proposition until its `by` body. The focused
`mdtests/conditional_algebraic_universal_contract.md` and its source-backed
expand/reverify regression cover these paths.
Kernel tests reject dropping the guard, changing the endpoint, graph snapshot,
or binder sort, and check lookup work across increasing unrelated fact counts.
`mdtests/conditional_call_indexed_result_fact.md` checks explicit framing of a
historical graph read used as another read's index.

The remaining work is proof ergonomics, catalogued in `issues/dfs.md`.
Automatic fold read-range inference remains a separate, unapproved design;
it is not required for either correctness theorem.
