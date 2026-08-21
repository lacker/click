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
- a precise `mutable` footprint,
- a loop effect summary,
- or an explicit invariant.

## Frame clauses

Frame clauses describe what memory a function preserves or may mutate:

<!-- verified-example: mdtests/copy3_array_demo.md -->
```click
immutable src[0..n] by frame;
mutable dst[0..n] by frame;
```

`immutable` says a region is unchanged.

`mutable` says a region is allowed to change. It is an effect summary, not a
postcondition about the final values.

Function-level ranges are fixed at function entry. For a push operation,
`mutable (owner->data + owner->len)[0..2]` denotes two cells at the old end even
if the function later updates `owner->len`. Click transports unchanged field
loads across certified writes when matching the executed stores to that
footprint. Which facts a proof step carries across such a write, and what
must be proved explicitly instead, is the step rule in
[Proof state and replay](proof-state-and-replay.md#what-a-step-carries).

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

Loops need their own frame reasoning. A loop can have a whole-loop effect:

<!-- verified-example: mdtests/copy3_array_demo.md -->
```click
loop {
    mutable p[0..n] by frame;
}
```

or a step-relative effect:

<!-- verified-example: mdtests/copy3_array_demo.md -->
```click
loop {
    step {
        mutable p[i..i + 1] by frame;
    }
}
```

Use whole-loop effects for stable regions and step effects for the cell or range
written by one iteration.
