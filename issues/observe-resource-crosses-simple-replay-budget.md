# `observe` resource replay crosses the simple-tactic budget

Direct verification of `examples/binary-tree` reproducibly fails before the
proof under development runs:

```text
tactic `observe` in `tree_sum_root_and_children.contract` exceeded its 500ms
simple real-time limit (statement 0, source tactic 2)
```

Two consecutive direct `click verify examples/binary-tree` runs failed at the
same site. `observe` is a simple tactic, so this is a deterministic replay
performance bug, not a reason to raise the limit, warm a cache, reshape the
example, or change a smart heuristic.

Reduce the case from the existing `tree_sum_root_and_children` proof while
preserving its recursive composite-resource shape. Attribute the work inside
the resource lookup/observation path and remove any search whose result should
have been selected while planning the surrounding smart proof.

Initial attribution found the hot path. `apply_composite_observation_law`
checks whether every owned body resource is already exposed. For this viewed
tree, the first missing owned memory fact falls through
`ResourceContext::satisfies_fact` into whole-context normalization even though
the context contains no owned memory capable of satisfying it.

A Boolean-preserving early return for that impossible case made the third
`observe` fast, but exposed a correctness coupling in `tree_rotate_left`:
ghost-resource certification then reported structurally different missing and
extra `views tree(...)` facts. The failed entailment/normalization scan is
recording implicit equality provenance that later resource representation
currently depends on. Do not keep the early return in isolation. The focused
fix must make a failed resource query observationally pure (or retain the
actually required equality as explicit evidence) before skipping impossible
ownership normalization.

## Acceptance criteria

- A focused regression exercises the same nested `tree(node)` observation.
- `observe(tree(...))` checks one explicitly named resource occurrence with
  deterministic work proportional to that resource body's relevant clauses.
- Removing an irrelevant failed ownership query does not change later ghost
  resource identity; a regression covers the `tree_rotate_left` representation
  check as well as the slow three-node observation.
- The regression and `examples/binary-tree` remain comfortably below the
  500ms simple ceiling on an uncached direct run.
- No tactic budget is raised and the C, resource declaration, and proof claim
  are unchanged.
- `click profile examples/binary-tree` reports no slow simple tactic.
