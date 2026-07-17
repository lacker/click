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
