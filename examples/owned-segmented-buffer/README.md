# Owned Segmented Buffer

This project verifies an outer composite resource that contains two independently
owned inner composite resources.

```c
struct owned_segmented_buffer {
    int32 first_len;
    int32 second_len;
    int32* first_data;
    int32* second_data;
};
```

`owned_segment(data, length)` owns one backing range and records its
nonnegative length. `owned_segmented_buffer(owner)` owns the four metadata
fields, contains two `owned_segment` resources whose parameters depend on that
metadata, and records that both selectable segments are nonempty.

The getter and setters explicitly observe or unfold one composite layer at a
time. The setters mutate one child while framing the other. The swap operation
changes only metadata, then refolds the same two child resources in the
opposite order. The pipeline composes initialization, both child mutations,
and a first-child read through verified function contracts. The swap remains a
focused direct proof because transporting its `old(...)` summary through a
multi-call stepped proof is a separate execution-proof concern.

The sidecar mixes concise smart proofs with expanded exact certificates. Read
the small getter/setter proofs first. Long `step() using` and `derive using`
blocks are checked replay artifacts retained for predictable performance and
expansion coverage; ordinary authoring should start with smart tactics and
expand only after profiling.

The caller supplies both backing arrays. Allocation, deallocation, resizing,
and recursive resource definitions are outside this example's scope.
