# Larger Example Projects

Small proof patterns live in `mdtests/`. Larger verification examples live in
`examples/`.

An example project should look like a tiny library verification effort: ordinary
C files, sidecar specs, and local documentation explaining the proof boundary.

## Current Examples

The current project fixtures are:

### Input Cursor

```text
examples/input-cursor/
```

This fixture defines a viewed `readable_input(data, len)` resource and an
`input_cursor(owner)` resource that owns cursor metadata while viewing the
nested input resource. Two cursor resources can therefore share one input and
advance independently. The example exercises explicit observation through
both composite layers and modular calls with precise metadata effects.

### JSON-C Reference Count

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

This gives Click a realistic shape to verify without pretending it already has
heap allocation or ownership transfer.

### Detachable Buffer

```text
examples/detachable-buffer/
```

This fixture separates one attached composite resource into independently
owned metadata and backing-storage resources, uses the detached backing through
an owner-independent helper, and then recombines both pieces. Attachedness is a
proof state rather than a runtime flag. The example exercises ownership moving
out of and back into a field-dependent composite resource through opaque call
summaries, without requiring allocation or deallocation.

### Borrowed Slice

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

### Ring Buffer

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

### Preallocated Linked List

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

### Binary Tree

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

### Recursive Zero List

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

### Owned Vector

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

### Perpetual Service

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

### Owned String

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

### Owned Split Buffer

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

### Owned Segmented Buffer

```text
examples/owned-segmented-buffer/
```

This fixture defines an `owned_segment(data, len)` composite resource and an
outer `owned_segmented_buffer(owner)` that contains two segment resources. It
exercises explicit observation and unfolding through nested owned composites,
mutation of one child while framing the other, and swapping the child-resource
parameters by changing only the outer metadata. A modular pipeline composes
initialization, both child mutations, and a nested first-child read.

## How To Read An Example Project

Read it in this order:

1. Read the project README.
2. Read one C file.
3. Read the matching `.click` sidecar.
4. Compare the sidecar with the closest mdtest.
5. Check which limitation the example is intentionally not solving yet.

The point of an example project is not to be exhaustive. It should make the next
missing feature obvious.

## Relationship To Mdtests

Mdtests are regression tests. They should stay small, self-contained, and easy
to copy when adding a focused feature.

Example projects are larger fixtures. They can have several files and a more
realistic naming style. They should still avoid becoming design sketches: if an
example is under `examples/`, it should verify.

Some larger sidecars retain exact certificates produced by `click expand` so
their verification cost stays predictable and the replay boundary remains
covered. Their READMEs identify those regions. Treat long `using` blocks as
maintained replay artifacts; begin new proofs with the default prover or a
clear smart tactic, then profile before expanding.
