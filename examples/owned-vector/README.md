# Owned Vector

This project verifies a small vector whose metadata and backing array are owned
through composite resources. It is large enough to exercise state transitions,
dependent memory ranges, and ownership transfer across verified helper calls.

The C representation has three fields:

```c
struct vector {
    int32 len;
    int32 cap;
    int32* data;
};
```

The Click sidecar defines three vector states:

- `empty_vector(owner)` owns the metadata and backing array and establishes
  `owner->len == 0` and `1 <= owner->cap`.
- `nonempty_vector(owner)` owns the same memory and establishes
  `1 <= owner->len <= owner->cap`.
- `allocated_vector(owner)` additionally owns the backing allocation's
  lifetime. It permits runtime growth and records that the live prefix is
  initialized even though unused capacity may remain unreadable.

The resources record that the metadata and backing-array footprints are
separate. The backing resource depends on the stored `data` and `cap` fields,
so folding either resource tests dependent composite-resource definitions.

## Operations

- `vector_init` adopts raw metadata and backing memory and produces an empty
  vector.
- `vector_len` reads metadata through `views nonempty_vector(owner)`.
- `vector_get` performs an indexed backing-array read through a viewed vector.
- `vector_set` mutates an arbitrary in-bounds element while preserving
  ownership and vector metadata.
- `vector_fill` uses `nonempty_vector(owner)` directly and an explicit loop
  preservation proof to initialize its field-dependent backing range.
- `vector_replace_if` calls verified vector operations on both sides of a
  branch, then exports a common resource-and-fact interface with `reach`.
- `vector_push_first` transitions an empty vector to a nonempty vector.
- The focused sibling project `examples/vector-push` verifies a general
  in-capacity append without adding another proof unit to this larger sidecar.
- `vector_copy` copies an arbitrary live prefix between separate owned and
  viewed capacity ranges and exposes pointwise value preservation.
- `vector_grow` performs ordinary malloc-copy-install-free growth. Allocation
  failure leaves the vector unchanged; success adds one capacity slot,
  preserves every live element and the length, installs the fresh allocation,
  and retires the old allocation.
- `vector_clear` transitions a nonempty vector back to an empty vector.
- `vector_pipeline` composes the mutating and indexed operations through their
  verified contracts. A named checkpoint exposes the vector view needed by the
  final getter; each call advances as one step without unfolding its body.

The integration test in `tests/examples.rs` verifies the operations in
`vector.click`, including both allocation outcomes of growth. The general-push
proof is independently checked in `examples/vector-push`.

## Proof Style

The sidecar mixes concise smart proofs with expanded exact certificates. Read
the `vector_len` and other short accessor proofs first. Long `step() using`,
`summarize ... using`, and `derive using` blocks are checked replay artifacts
retained for predictable performance and expansion coverage; ordinary
authoring should begin with the corresponding smart tactic and expand only
after profiling.

## Current Boundary

`empty_vector` and `nonempty_vector` continue to model caller-supplied storage;
`allocated_vector` is the lifetime-owning state used by growth. Growth uses the
smallest useful policy, `new_cap = old_cap + 1`, to keep this project focused on
allocation/resource composition rather than capacity-policy arithmetic. It is
not a geometric-growth performance example.

Functions with several effects, produced resources, and pure postconditions
use one trailing grouped proof. Click executes each function body once and
checks every contract claim from that shared proof state.

The leaf-operation contracts state precise mutation footprints and memory
postconditions. The pipeline can therefore rely on a setter's result without
seeing its implementation, while unrelated vector metadata remains framed.
