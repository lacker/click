# Branching graph DFS: the next proof frontier

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
A successful return should next imply that `to` was unmarked at the entry of
the call and is reachable
from `cur` by a finite left/right path in the entry graph. Full failure-path
completeness is a later claim: it must account for nodes visited by the left
call before the right call starts.

The checked contract owns `visited[0..n]`, views both successor arrays through
a `bounded_successors` resource carrying their bounds, and keeps each array
separate from `visited`. Its inductive postcondition says the unmarked count
cannot increase. The local marking store drops the count by one using
`unmarked_point_update`; the first recursive call's postcondition composes
with that strict drop, so the right call still descends. A stronger per-cell
monotonicity summary and its checked lemmas remain available in
`mdtests/unmarked_count_lemmas.md` if the reachability proof needs them.

The proof needed one verifier repair: a recursive ranking obligation already
discharged by an exact established fact must not remain pending when the
stable-view return check runs. The kernel now drops only those exactly
discharged ranking obligations, never one justified by another pending
obligation. The mdtest checks the unchanged C through both recursive calls
and all early returns. The next implementation step is success-path
reachability, preserving a finite path witness through the recursive result
and relating it to the entry graph.

The older `issues/dfs.md` note that a loop guard cannot read through any
folded resource is not a general current limitation: for example,
`mdtests/composite_resource_vector_fill_loop_snapshot.md` checks a loop guard
reading `owner->len` from a folded owned composite. A special recursive or
matched-resource refusal would need its own current reduction before changing
the verifier. This graph example uses flat arrays, so that route is not its
first blocker.

## Reachability attempt (2026-09-23)

Adding `ensures result != 0 implies exists (path: Path) {
walk(left, right, cur, path) == to }` to the unchanged DFS reaches the first
recursive-success branch. The direct `cur == to` return proves the claim with
`Path::Here`. For the left call, `let left_result = step(dfs(..., left[cur],
to), {});` and the following C branch establish `left_result != 0`, and the
trace shows that the callee produced the reachability guarantee. However, the
trace reports that the two call-produced checked facts have no exact
caller-side Click spelling. A current-state `left[cur]` is not the argument
evaluated before the call. Spelling it `at(before_left_call, left[cur])` puts a
historical `viewable(left[cur])` guard *inside* the existential. `assumption`,
`extract`, and `let (rest: Path) satisfy { ... };` then all reject that stated
existential as unavailable. The right recursive branch has not been reached.

This is the same call-site evaluated-load existential gap isolated by
`mdtests/call_existential_evaluated_load_guard.md`, not a need to change the C
or invent a path witness. The needed general proof rule is to use a checked
call-produced existential together with a binder-independent, already-proved
historical viewability fact, so the caller can open the witness in surface
Click. Keep the negative minimal regression until that rule has a checked
positive test; then resume the DFS claim from the left-success branch.
