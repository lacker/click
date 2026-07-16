# Owned Vector

This project verifies a small vector whose metadata and backing array are owned
through composite resources. It is large enough to exercise state transitions,
dependent memory ranges, and calls through viewed resources without introducing
allocation or deallocation.

The C representation has three fields:

```c
struct vector {
    int32 len;
    int32 cap;
    int32* data;
};
```

The Click sidecar defines two resource states:

- `empty_vector(owner)` owns the metadata and backing array and establishes
  `owner->len == 0` and `1 <= owner->cap`.
- `vector(owner)` owns the same memory and establishes
  `1 <= owner->len <= owner->cap`.

Both resources record that the metadata and backing-array footprints are
separate. The backing resource depends on the stored `data` and `cap` fields,
so folding either resource tests dependent composite-resource definitions.

## Operations

- `vector_init` adopts raw metadata and backing memory and produces an empty
  vector.
- `vector_len` reads metadata through `views vector(owner)`.
- `vector_get` performs an indexed backing-array read through a viewed vector.
- `vector_set` mutates an arbitrary in-bounds element while preserving
  ownership and vector metadata.
- `vector_fill` uses `vector(owner)` directly and an explicit loop preservation
  proof to initialize its field-dependent backing range.
- `vector_replace_if` calls verified vector operations on both sides of a
  branch, then exports a common resource-and-fact interface with `advance`.
- `vector_push` transitions an empty vector to a nonempty vector.
- `vector_clear` transitions a nonempty vector back to an empty vector.
- `vector_pipeline` composes the mutating and indexed operations through their
  verified contracts. A named checkpoint exposes the vector view needed by the
  final getter; each call advances as one step without unfolding its body.

The integration test in `tests/examples.rs` verifies every C file against
`vector.click`.

## Current Boundary

The caller supplies the backing array, capacity is at least one, and the example
does not allocate, free, resize, or handle a full vector. Those operations need
resource-algebra features beyond composite resources.

Functions with several effects, produced resources, and pure postconditions
use one trailing grouped proof. Click executes each function body once and
checks every contract claim from that shared proof state.

The leaf-operation contracts state precise mutation footprints and memory
postconditions. The pipeline can therefore rely on a setter's result without
seeing its implementation, while unrelated vector metadata remains framed.
