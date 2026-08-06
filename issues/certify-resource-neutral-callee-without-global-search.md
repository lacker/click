# Certify a resource-neutral callee without global proof search

## Problem

Replacing the owned-vector example's proof-specialized `vector_push_first`
clone with one resource-neutral `vector_push` exposed a certification
bottleneck after the ordinary proof became fast.

The principled contract factors the append algorithm through a
`vector_storage(owner)` resource. A caller with allocation authority unfolds
`allocated_vector(owner)`, lends `vector_storage(owner)` to `vector_push`, and
folds the allocation-owning resource again afterward. The surface proof and
smart `frame()` can check this transition without changing the C.

Kernel contract certification does not yet handle the same composition at an
acceptable cost. Profiling the resulting `allocated_vector_push` reached the
30-second project deadline in certification. About 18 seconds were attributed
to certification of its first postcondition, after which diagnostics reported
that an execution path's required resource context could not be evaluated.
The focused in-process example run continued past 90 seconds and was stopped;
its process tree exited cleanly.

This is a tooling blocker, not permission to restore a specialized C clone,
raise a timeout, or keep an expanded proof that avoids the call shape.

## Reduced semantic shape

The regression should contain:

1. an allocation-owning composite resource that contains metadata, backing
   storage, and allocation authority;
2. a resource-neutral storage view over the same metadata and backing range;
3. one ordinary C callee that owns the storage view and mutates one in-capacity
   element; and
4. one C caller that owns the allocation-bearing resource, temporarily lends
   the storage view to the callee, and regains the original resource.

The caller should have a small disjunctive result postcondition so the
regression also distinguishes resource preparation from unrelated proposition
search. Keep the C bodies unchanged while reducing the Click declarations.

## Likely work

Trace contract certification separately through:

- preparation and expansion of each execution path's entry and return
  resources;
- modular-call resource consumption and production;
- construction of the assumptions used for each contract claim; and
- postcondition lowering and proof.

Cache or reuse prepared resource contexts when the kernel is recomputing the
same path data. Prefer exact resource decomposition and the facts carried by
the selected call rule before building an ambient assumptions index over the
entire memory-snapshot history. Any cached result must remain subordinate to
the kernel's ordinary resource-validity and claim checks.

## Acceptance criteria

- The reduced resource-neutral-callee regression certifies within the normal
  certification and project budgets.
- `click profile` attributes no certification claim or path above its
  normalized threshold.
- `click expand` emits a replayable certificate for every smart site in the
  reduced caller, and `click audit` agrees.
- The allocation authority is neither accepted by the storage-only callee nor
  lost when the caller regains its enclosing resource.
- No C wrapper, cloned implementation, arbitrary search cap, raised timeout,
  or proof-only C operation is introduced.
- The general vector-push issue can resume and pass the default suite after
  this blocker is removed.
