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
- `vector_push` transitions an empty vector to a nonempty vector.
- `vector_clear` transitions a nonempty vector back to an empty vector.
- `vector_pipeline` performs both transitions inline and calls `vector_get`
  through viewed composite resources between mutations.

The integration test in `tests/examples.rs` verifies every C file against
`vector.click`.

## Current Boundary

The caller supplies the backing array, capacity is at least one, and the example
does not allocate, free, resize, or handle a full vector. Those operations need
resource-algebra features beyond composite resources.

The example also exposes two current proof-system limitations:

- An opaque call that consumes a memory-backed composite resource does not yet
  project its owned children into the callee's execution context. The pipeline
  expresses mutating transitions inline, while viewed calls are modular.
- Proving a produced resource and a pure result currently repeats much of the
  same execution proof.

These restrictions are documented here because this project is intended to
identify the next integration work while keeping every checked example valid.
