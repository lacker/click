# Aliasing and frames

C pointer parameters may alias by default. Click follows that model.

If a function takes two pointers:

<!-- verified-example: mdtests/copy3_array_demo.md -->
```c
int32 copy_one(int32 dst[], int32 src[]) {
    dst[0] = src[0];
    return dst[0];
}
```

Click does not assume `dst` and `src` are different. If a proof depends on
non-overlap, state it:

<!-- verified-example: mdtests/copy3_array_demo.md -->
```click
requires separate(memory(dst[0..1]), memory(src[0..1]));
```

## Why aliasing matters

Suppose a function writes `dst[0]`. A postcondition about `src[0]` is not
automatically safe unless Click knows the write could not have changed the same
cell.

That fact can come from:

- a `separate(memory(...), memory(...))` requirement,
- a precise owned footprint,
- the loop's owned resources,
- or an explicit invariant.

## Ownership is the frame

A contract's owned memory is what it may write; everything else it can reach is
preserved:

<!-- verified-example: mdtests/copy3_array_demo.md -->
```click
views src[0..n];
owns dst[0..n];
```

`views` says a region is readable and unchanged.

`owns` says a region is allowed to change. It is a write bound, not a
postcondition about the final values.

A narrow write inside a wider range is a view of the whole plus ownership of
the piece:

<!-- verified-example: mdtests/field_derived_precise_effect_after_metadata_write.md -->
```click
views owned_buffer(owner);
owns owner[0..1];
owns (owner->data + owner->len)[0..2];
```

Function-level ranges are fixed at function entry. For a push operation,
`owns (owner->data + owner->len)[0..2]` denotes two cells at the old end even
if the function later updates `owner->len`. Click transports unchanged field
loads across certified writes when matching the executed stores to that
footprint. Which facts a statement step carries across such a write, and what
must be proved explicitly instead, is the step rule in
[Proof state and checked transitions](proof-state.md#what-a-step-carries).

## Old-Memory postconditions

You can also state preservation directly:

<!-- verified-example: mdtests/copy3_array_demo.md -->
```click
ensures src[0] == old(src[0]) by auto;
```

For larger regions, use quantified or range-shaped facts:

<!-- verified-example: mdtests/copy3_array_demo.md -->
```click
ensures forall (k: int32) {
    0 <= k and k < n implies src[k] == old(src[k])
} by auto;
```

Frame facts and separation often make these postconditions provable without
copying every old value into a separate variable.

## Loop frames

A loop frames by ownership. With no clause of its own, a loop may write exactly
the memory the function owns, and every viewed cell and every owned cell it did
not write is preserved across it.

A loop can narrow that authority the way a callee contract does:

<!-- verified-example: mdtests/local_array_loop_frame.md -->
```click
loop {
    owns p[0..n];
    invariant i >= 0;
}
```

A body store outside the loop's owned ranges is rejected at the store, and a
cell outside them holds its entry value after the loop with no invariant.
