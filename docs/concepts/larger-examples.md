# Larger example projects

Small proof patterns live in `mdtests/`. Larger verification examples live in
`examples/`.

An example project should look like a tiny library verification effort: ordinary
C files, sidecar specs, and local documentation explaining the proof boundary.

## Current examples

The current project fixtures are:

### Heap object

```text
examples/heap-object/
```

This fixture follows one fixed-size `struct item` through allocation failure,
successful initialization, folding into a nullable owning resource, read-only
borrowing, modular ownership transfer, and destruction. It is the reference
example for the distinction between complete memory access and exclusive
allocation authority.

### Input cursor

```text
examples/input-cursor/
```

This fixture defines a viewed `readable_input(data, len)` resource and an
`input_cursor(owner)` resource that owns cursor metadata while viewing the
nested input resource. Two cursor resources can therefore share one input and
advance independently. The example exercises explicit observation through
both composite layers and modular calls with precise metadata effects.

### JSON-C reference count

```text
examples/jsonc-refcount/
```

It contains json-c-shaped operations over a one-field object:

- `json_object_get_ref_count`
- `json_object_set_ref_count`
- `json_object_inc_ref_count`

This fixture's proof scope is intentionally narrow:

- one `int32` field in the json-c-shaped struct,
- pointer-to-struct parameters,
- `->` field loads and stores for that first field,
- `views obj->ref_count` for field reads,
- `owns obj->ref_count` for field writes.

This gives Click a realistic preallocated shape alongside the separate
heap-object fixture.

### Detachable buffer

```text
examples/detachable-buffer/
```

This fixture separates one attached composite resource into independently
owned metadata and backing-storage resources, uses the detached backing through
an owner-independent helper, and then recombines both pieces. Attachedness is a
proof state rather than a runtime flag. The example exercises ownership moving
out of and back into a field-dependent composite resource through opaque call
summaries, without requiring allocation or deallocation.

### Borrowed slice

```text
examples/borrowed-slice/
```

This fixture temporarily splits a complete buffer into one resource holding
the metadata and outer ranges, plus an independently owned, nonempty middle
slice. A helper mutates the slice without access to its owner, after which a
return operation recombines the prefix, slice, and suffix into the original
buffer resource.
The explicit backing pointer and length arguments preserve the allocation's
identity while its ownership is divided across opaque calls.

### Ring buffer

```text
examples/ring-buffer/
```

This fixture models a fixed-capacity ring in linear and wrapped logical states.
Both outer states contain the same nested full-backing resource; wrapping
changes metadata and stored content, not ownership of the allocation. The
backing therefore stays encapsulated behind a natural owner-only resource and
API. The example covers construction, a linear-to-wrapped push, a viewed read
through both composite layers, a wrapped-to-linear pop, and a modular round
trip.

### Preallocated linked list

```text
examples/linked-list/
```

This fixture defines a guarded recursive `list(node)` resource. Null is the
empty list; a nonnull node owns its value and next fields and contains a folded
resource for its tail. The project verifies empty construction by returning
C's null pointer constant, head access, preallocated push and pop ownership
transfers, and a multi-call round trip. Each proof unfolds at most one node.
Allocation, deallocation, traversal loops, shared tails, and cyclic lists
remain outside the example.

### Allocated linked list

```text
examples/allocated-linked-list/
```

This fixture extends the recursive list with one allocation authority per
nonnull node. It verifies a prepend operation that returns the original tail
on allocation failure, borrowed head access, a one-node drop that returns the
live tail, and a recursive postorder destructor. The destructor accepts null,
consumes the full list, recursively transfers the direct child resource, and
then frees the parent; its structural resource measure proves termination even
though the witness is deallocated during the traversal. A modular pipeline
combines two independent allocation attempts with borrow, drop, and complete
cleanup.

### Binary tree

```text
examples/binary-tree/
```

This fixture branches the same guarded-recursion model into two child trees. A
nonnull node owns its value, left, and right fields and contains folded
resources for both children. It verifies empty and root construction, a viewed
root read, child swapping, and a modular leaf pipeline whose two independently
returned null children act as empty resource identities. Its recursive walk
visits both nonnull children sequentially, checking that the first opaque call
preserves the sibling resource and parent fields needed afterward. Allocation,
deallocation, mutating traversal, balancing, sharing, and cycles remain outside
the example.

### Modeled binary tree

```text
examples/modeled-binary-tree/
```

This fixture is the same C shape with an exact model attached. `HeapTree`
records each node's address, payload, and both submodels, and the matched
resource `tree_at(p)` owns different cells in each arm, so the model decides
what the resource holds. A second resource, `ctx_at(child)`, holds everything
the tree has *except* one focused subtree, and the pure `plug` rebuilds the
whole model from the two. Every function in its C file is verified: the
initializer, both rotations against exact model transformations with in-order
preservation, the recursive search against a membership function, and the two
iterative walks against the context. It is the reference example for a model
that is derived from owned memory rather than asserted beside it, and the next
section walks through its loop proof.

### Red-black tree model

```text
examples/rbtree-model/
```

This fixture is pure: no C file and no `verifying` line. It is the Linux rbtree
model — `RbTree` with each node's identity, parent, color, and both submodels
— with the in-order list, membership, black height, the red-black and
almost-red-black predicates, parent/child consistency, and the theorems that
rotation, recolor, leaf insertion, and both erase splices preserve them. The
zipper half adds `plug`, a context-level red-black predicate `ctx_rb` from
which `is_rb_root` of the whole plug follows, its insert-fixup weakening
`ctx_almost_rb_insert`, and each fixup case restated as one step of the fixup
loop. The proofs about verbatim Linux C that use this model live in the `rb_*`
mdtests; this project is the library they cite.

### Recursive zero list

```text
examples/recursive-zero-list/
```

This fixture gives every nonnull node the invariant `node->value == 0`, then
uses a viewed recursive resource to verify an opaque self-call on the tail. Its
ordinary contract proves that a returning call yields zero, while `decreases
resource` separately certifies return by descent through the contained tail. A
second fuel-bounded traversal proves termination with a numeric measure. A
small pipeline constructs two nodes from caller-owned fields, folds the list,
and composes both traversal contracts.

### Owned vector

```text
examples/owned-vector/
```

This fixture defines `empty_vector(owner)` and `nonempty_vector(owner)`
composite resources over vector metadata and a dependent backing array. It
verifies raw memory adoption, viewed length and indexed reads, indexed
mutation, empty-to-nonempty and nonempty-to-empty state transitions, and a
multi-step pipeline.

The pipeline uses verified opaque call summaries for all operations, including
calls that consume and produce memory-backed composite resources. The project
uses one grouped execution proof per function so effects, produced resources,
and pure postconditions are checked from one chronological proof state.

### Perpetual service

```text
examples/perpetual-service/
```

This fixture owns protocol metadata and a separate backing cell as one
composite `service(owner)` resource. A verified opaque step toggles between two
legal states and returns the folded resource. `service_run` repeats that call
inside a constant-true loop, proving safety and invariant preservation for
every finite prefix without inventing a return frontier. Its README draws the
boundary explicitly: Click proves neither scheduler fairness nor productive
external I/O traces.

### Owned string

```text
examples/owned-string/
```

This fixture defines an `owned_string(owner)` composite resource over string
metadata and a field-dependent backing array. In addition to length and
capacity bounds, the resource carries a `terminated_at(data, len)` predicate
that records the trailing zero terminator. Its mutators change the logical end
of the string while re-establishing that memory invariant, and their precise
effects let modular callers prove that earlier characters are preserved.

The example covers initialization, indexed reads and writes, push, pop, clear,
and a multi-call pipeline. It is the main larger fixture for the interaction
between a folded composite resource and a content invariant over owned memory.

### Owned split buffer

```text
examples/owned-split-buffer/
```

This fixture packages metadata and two adjacent sibling ranges as one
`owned_split_buffer(owner)` composite resource. Its setters mutate the left and
right partitions independently. Its boundary operation changes only metadata
while transferring one cell from the right resource to the left resource, so
folding must recombine and repartition ownership without changing backing
memory. A modular pipeline then reads that transferred cell through the newly
expanded left partition.

### Owned segmented buffer

```text
examples/owned-segmented-buffer/
```

This fixture defines one `owned_segmented_buffer(owner)` composite resource
over four metadata fields and the two backing ranges they select. Each setter
transfers exactly the cell it writes: it views the metadata and owns a single
element of one segment, so the other segment and the rest of its own are
framed by ownership with no effect clause. The swap changes only metadata and
refolds the same two ranges in the opposite order. A modular pipeline composes
initialization, both segment mutations, and a first-segment read.

## A modeled loop, end to end

`tree_leftmost` in
[`examples/modeled-binary-tree`](https://github.com/lacker/click/tree/master/examples/modeled-binary-tree)
is the smallest complete instance of the pattern every walk over a recursive
structure uses, including the Linux rbtree traversals. Its C does three
things — reject null, run `while (root->left != 0) root = root->left;`, return
the cursor — and the proof around it is worth reading as a unit.

The problem the contract solves is that the function stops in the middle of the
tree. It consumes a whole tree and hands back a pointer into it, so a
postcondition needs a name for the part it walked past. That name is a context
resource, and the frame it pushes each iteration is a matched arm that owns its
parent's cells through a constructor binding:

<!-- verified-example: mdtests/resource_arm_binding_struct_base.md -->
```click
resource ctx_at(child: struct tree_node*) {
    field model: Context;
    match model {
        Context::Top => {},
        Context::Left(parent, value, sibling_model, up_model) => {
            owns parent->value;
            owns parent->left;
            owns parent->right;
            owns sibling: tree_at(parent->right);
            owns up: ctx_at(parent);
            fact parent != 0;
            fact parent->left == child;
            fact parent->value == value;
            fact sibling.model == sibling_model;
            fact up.model == up_model;
        },
    }
}
```

A frame owns the parent's three cells, the subtree the walk did not take, and
the frame above it. The pure `plug(ctx, sub)` rebuilds the whole model from a
frame stack and the focused subtree, so the contract's real claim is one
equation: `ensures plug(ctx.model, sub.model) == old(t.model);`, beside
`produces ctx: ctx_at(result);` and `produces sub: tree_at(result);`. It says
the walk lost nothing — not that the result is some well-formed tree, but that
it is the same tree, with the same nodes in the same order. The position it
stopped at is the second clause,
`ensures heap_left(sub.model) == HeapTree::Empty;`.

The loop carries the same pair the contract produces, and its measure is the
focused subtree:

<!-- verified-example: mdtests/loop_context_frame_refold_rejected.md -->
```click
loop {
    owns ctx: ctx_at(root);
    owns t: tree_at(root);
    decreases t;
    invariant t.model != HeapTree::Empty;
    invariant plug(ctx.model, t.model) == old(t.model);
}
```

The fixture named above is this walk with one extra fold, refused for that
fold; the passing walk is the example itself.

One iteration is five steps, and each is an ordinary tactic:

1. `match t.model` inside `preserve` supplies the constructor. The binder's
   model at an arbitrary loop head is a fresh symbolic value, so nothing can
   `unfold` it until a proof `match` names the arm; the `HeapTree::Empty` arm
   closes by `contradiction` on the first invariant.
2. `unfold(t) as { left: l, right: rt }` takes the node apart into its three
   cells and its two child instances.
3. `fold(ctx_at(root->left), { model: Context::Left(...) }, { sibling: rt, up:
   ctx })` builds the new frame from the parent's cells, the untaken sibling,
   and the old frame. Those children are consumed by the fold, which is what
   keeps the frame stack linear — a body that folds a second frame from the
   same children is refused by name.
4. `step()` runs `root = root->left`.
5. `close_invariants()` rebinds `ctx` and `t` by proved argument equality: the
   binder arguments are read in the state the body reached, so `tree_at(root)`
   is now the left child's instance, and the structural measure sees a direct
   contained child of what the head held.

The `plug` invariant moves forward with a `have` per iteration: `plug` of the
new frame at the left submodel unfolds to `plug` of the old frame at the whole
node, which the invariant already equates with `old(t.model)`.

What is left is the guard, and it is decided by arm selection rather than by a
case split. `requires t.model != HeapTree::Empty` entails the `HeapTree::Node`
arm at contract lowering, and that arm's own `fact p != 0` decides the opening
`if (root == 0)` with no `branch`. Inside the loop the rule runs backwards: the
guard `root->left != 0` contradicts the `HeapTree::Empty` arm's `fact p == 0`,
so the child the unfold exposes carries the next iteration's invariant. At the
exit the failed guard refutes the `HeapTree::Node` arm instead, and because
`Empty` has no fields the equation is published outright, which is the
postcondition. The rules are in [resources](resources.md) and
[loops and invariants](loops-and-invariants.md).

The same five steps, on an unchanged Linux body, are `mdtests/rb_first_last.md`:
`rb_at(n)` and `ctx_at(n, root)` replace the scaffold's resources, the loop
declares the same two binders and the same measure, and the extra work is the
packed parent word and the color, not the shape of the proof.

## How to read an example project

Read it in this order:

1. Read the project README.
2. Read one C file.
3. Read the matching `.click` sidecar.
4. Compare the sidecar with the closest mdtest.
5. Check which limitation the example is intentionally not solving yet.

The point of an example project is not to be exhaustive. It should make the next
missing feature obvious.

## Relationship to mdtests

Mdtests are regression tests. They should stay small, self-contained, and easy
to copy when adding a focused feature.

Example projects are larger fixtures. They can have several files and a more
realistic naming style. They should still avoid becoming design sketches: if an
example is under `examples/`, it should verify.

Some larger sidecars retain exact explicit proofs produced by `click expand`
so their verification cost stays predictable and the expansion boundary
remains covered. Their READMEs identify those regions. Treat long `using`
blocks as maintained expansion output; begin new proofs with the default prover
or a clear smart tactic, then profile before expanding.
