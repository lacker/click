# Owned Segmented Buffer

This project verifies one composite resource over two independently owned
backing ranges.

```c
struct owned_segmented_buffer {
    int32 first_len;
    int32 second_len;
    int32* first_data;
    int32* second_data;
};
```

`owned_segmented_buffer(owner)` owns the four metadata fields and both backing
ranges selected by that metadata, records that both segments are nonempty, and
records that each backing range is separate from the metadata object.

The getter observes the composite. Each setter transfers exactly the cell it
writes: it views the metadata fields and owns the single element
`owner->first_data[index..index + 1]` or
`owner->second_data[index..index + 1]`, so the other segment and the rest of
its own segment are framed by ownership with no effect clause. The swap
operation changes only metadata, then refolds the same two ranges in the
opposite order. The pipeline composes initialization, both child mutations,
and a first-child read through verified function contracts. The swap remains a
focused direct proof because transporting its `old(...)` summary through a
multi-call stepped proof is a separate execution-proof concern.

The sidecar mixes concise smart proofs with expanded exact certificates. Read
the small getter/setter proofs first. Long `step()` blocks are checked
proof artifacts retained for predictable performance and expansion coverage.
Restricted equality chains use `simp() using`; expansion turns them into
explicit `rewrite` and `normalize` steps. Ordinary authoring should start with
smart tactics and expand only after profiling.

The caller supplies both backing arrays. Allocation, deallocation, resizing,
and recursive resource definitions are outside this example's scope.
