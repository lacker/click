# Prove C termination by recursive-resource descent

## Dependency

Do this after the recursive zero-list example and its ordinary composition
audit. The example should first demonstrate that partial recursive contracts
work without this feature.

## Problem

Click can certify C recursion ranked by an `int32` parameter that is passed as
`measure - K`. That handles countdowns and artificial fuel, but not the normal
termination argument for a list or tree traversal:

1. the function starts with a finite inductive resource such as `list(node)`;
2. one unfold or observation exposes `list(node->next)`; and
3. the recursive call receives that strict contained child.

The ordinary C contract remains valid under partial correctness. This feature
must add only the separate evidence that the traversal returns.

## Semantic basis

A guarded direct-recursive composite resource is an inductive, least-fixed-point
object. A witness for its recursive child is a proper subtree of the witness
for its parent, so witness height is a natural-number rank even though source C
does not store a length.

The rank is proof structure, not pointer structure. These are not sufficient
termination arguments by themselves:

- the recursive argument is spelled `node->next`;
- the child pointer differs from the parent pointer;
- a fact with the same resource name is available at the call; or
- the proof folded a new resource shortly before the call.

In particular, pointer inequality admits cycles, and an independently available
resource has no certified ancestry from the function's measure.

## Recommended surface declaration

Keep numeric measures unchanged and make the different judgment explicit:

```click
int32 zero_list_sum(struct node* node) {
    views zero_list(node);
    immutable;
    decreases resource zero_list(node);
    ensures result == 0;
}
```

`decreases resource` is preferable for the first slice to bare
`decreases zero_list(node)`: a bare call expression is already the shape of a
pure Click function application, while a resource measure is not an integer
expression. The parser must resolve the declaration to an exact required
composite resource instance at function entry.

If implementation experience finds a cleaner unambiguous spelling, update the
language-design documentation before changing it. Do not infer structural
termination merely because a function happens to require a recursive resource.

## Kernel design

The current runtime `CResource::Composite` fact records a name and arguments,
not an inductive height or parent identity. Therefore termination checking
cannot soundly compare two resource facts by value alone. Add an unforgeable
descent boundary.

Unlike the current numeric checker, this cannot be established by scanning
`source_body` call expressions alone. The structural checker must consume an
exact certified resource-transition trace, or a minimized certificate replayed
against that trace, because the proof establishes which resource satisfied each
call requirement.

A useful shape is:

1. Exact contract certification identifies the declared entry measure fact.
2. A kernel-checked unfold or observation of that exact fact may produce a
   `CRecursiveResourceProjection` linking the parent instance to each direct
   self-recursive `contains` child exposed by the selected conditional body.
3. Projection evidence retains lineage through exact argument equalities and
   C-local spellings, but not through arbitrary folding or same-name lookup.
4. Each component-internal recursive call records which required callee
   resource was satisfied by a projection descendant of the caller's entry
   measure.
5. The termination checker accepts the edge only if the projection chain has
   at least one strict recursive `contains` step. It then constructs the
   existing separate `CVerifiedFunctionTerminationRule`.

The surface proof and termination plan are untrusted descriptions. The kernel
must recheck the exact composite definition, active guard, parent resource,
child occurrence, call arguments, and callee requirement against the exact
partially verified function rule. A crate caller must not be able to construct
projection or termination evidence directly.

Projection evidence is resource provenance, not an ambient pure proposition.
Consuming a resource transfers or ends its lineage; folding creates a new
parent witness from the children it consumes. A branch join, call havoc, or
memory mutation must not retain a stale projection merely because the resource
arguments still compare equal.

Owned lineage is linear. Viewed lineage may be duplicated, but every projected
view still denotes a strict child of the finite parent witness; duplication
does not create an infinite descending chain. The first useful slice must
support measures named by either an exact owned requirement or an exact viewed
requirement. If viewed provenance needs a separate implementation chunk, split
and document that dependency before claiming this issue complete; do not
weaken the ancestry check.

## First supported slice

- One structural measure per function.
- A guarded, directly self-recursive composite resource already accepted by
  the resource validator.
- An exact `owns` or `views` requirement matching the declared entry measure.
- Directly recursive C functions first. Mutual function recursion can wait
  even when every member carries a compatible resource, because the lineage
  must cross several contract interfaces.
- The callee measure is a strict projected descendant of the caller entry
  measure on every reached recursive edge.
- Base paths with no recursive edge owe no descent proof.
- Every reachable loop still needs its own numeric loop `decreases` evidence,
  and every out-of-component callee must already have termination evidence.
- Recursive calls inside loops remain rejected until a deliberate
  lexicographic/product ranking design exists.
- Numeric and structural function measures are alternatives in the first
  slice, not an implicit tuple.

Do not use recursive-resource auto-expansion to discover a rank. The proof must
select the resource layer explicitly, and certification must retain that exact
selection.

## Soundness cases to test

Positive mdtests and examples:

- a read-only zero-list traversal descends through `zero_list(node->next)`;
- an owned traversal consumes a parent, recursively processes the child,
  receives it back, and folds the parent;
- a binary-tree traversal chooses either direct child on each recursive edge;
- the same partial contract still verifies when the structural declaration is
  removed.

Negative mdtests and kernel tests:

- a self-call with the original parent resource is not decreasing;
- `node->next != node` without a resource projection is not decreasing;
- a same-named resource folded independently at the call site is not accepted
  as a child;
- a child from an unrelated parent is not accepted;
- an inactive conditional body produces no child projection;
- a fabricated or mismatched surface termination plan cannot create a kernel
  termination rule;
- one nondecreasing edge rejects termination for the whole recursive function;
  and
- partial verification remains available after termination rejection when the
  `decreases resource` request is removed.

## Documentation

Update the language reference, kernel guide, permissions guide, and recursive
example README. Explain that:

- recursive resources are inductive and finite, not coinductive heap claims;
- the hidden rank belongs to the certified resource witness, not a pointer;
- partial correctness remains the ordinary C contract meaning;
- structural `decreases` constructs separate termination evidence; and
- this is termination, not productivity, fairness, or a trace property.

## Non-goals

- Guessing structural measures from function bodies.
- Proving termination from pointer acyclicity alone.
- Coinductive or cyclic resources.
- Mutual recursive resource definitions, which remain invalid.
- Mutual C recursion, mixed numeric/structural tuples, lexicographic measures,
  or recursive calls inside loops in the first slice.
- Making ordinary opaque calls depend on termination evidence.
- Pure Click theorem induction.

## Acceptance criteria

- A recursive list/tree traversal receives a separate kernel-checked
  termination rule from strict resource descent.
- The read-only zero-list traversal can use its viewed child lineage rather
  than adding artificial ownership transfer or numeric fuel.
- No public or surface API can assert parent-child lineage without kernel
  replay against the exact resource definition and proof state.
- Same-resource, pointer-inequality, unrelated-resource, and fabricated-plan
  negative tests fail locally and clearly.
- Removing the structural declaration restores ordinary partial verification.
- Numeric `decreases` behavior and existing perpetual-service behavior are
  unchanged.
- Documentation never describes resource facts alone as carrying a runtime
  size that the current kernel representation does not contain.
