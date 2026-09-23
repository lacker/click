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

The first target is termination and memory safety for bounded successor
indices, with `decreases unmarked(visited, 0, n)`. A successful return should
then imply that `to` was unmarked at the entry of the call and is reachable
from `cur` by a finite left/right path in the entry graph. Full failure-path
completeness is a later claim: it must account for nodes visited by the left
call before the right call starts.

The contract should own `visited[0..n]`, view `left[0..n]` and `right[0..n]`,
state bounds for both successor arrays, and state that each successor array is
separate from `visited` so marking cannot change the graph. The useful
inductive summary is that the call never changes a nonzero visited cell back
to zero. `unmarked_monotone` in `mdtests/unmarked_count_lemmas.md` proves that
this per-cell summary makes the count nonincreasing, including across the left
call. The local marking store drops the count by one using the already-checked
`unmarked_point_update`; the checked
`unmarked_after_first_call_decreases` theorem composes that decrease with the
left call's monotonicity. Thus the right call, even after an arbitrary left
search, still has a measure strictly below this call's entry measure. This is
the distinctive proof obligation absent from a one-successor walk or a
resource-ranked tree search.

An exploratory sidecar with the bounded-array requirements and
`decreases unmarked(visited, 0, n)` reached the first recursive call in 0.08 s.
Bare `execute()` failed promptly on the expected nonnegative-measure premise;
it did not expose a verifier timeout, broken certificate, or folded-resource
read refusal. The full graph proof has not been claimed or added to the gate.
The next implementation step is to state and prove the monotone visited
postcondition and the point-update decrease, then verify both recursive calls
and the early returns against the unchanged C.

The older `issues/dfs.md` note that a loop guard cannot read through any
folded resource is not a general current limitation: for example,
`mdtests/composite_resource_vector_fill_loop_snapshot.md` checks a loop guard
reading `owner->len` from a folded owned composite. A special recursive or
matched-resource refusal would need its own current reduction before changing
the verifier. This graph example uses flat arrays, so that route is not its
first blocker.
