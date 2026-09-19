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

## A global is not separated from an argument by its name

The same rule covers a file-scope object and a pointer parameter. A caller may
pass a global as an array argument, so a function that writes the global has
not preserved the argument's cells:

<!-- verified-example: mdtests/global_may_alias_an_array_argument.md -->
```c
int32 g[4];

void f(int32 a[], int32 n) {
    g[0] = 1;
}
```

A contract that reads `a[0]` while declaring no resource for `a` cannot carry
that read across the store to `g[0]`, however different the two names look.
`requires viewable(a[0..n])` says the range can be read; it says nothing about
where it is. State the separation:

<!-- verified-example: mdtests/a_separated_array_argument_survives_a_global_store.md -->
```click
requires separate(memory(a[0..n]), memory(g[0..1]));
```

Two file-scope objects are two declarations and stay separate with nothing
said, and so does a function-scope `static` array; the argument is the case
where the caller decides.

Declaring `views a[0..n]` instead settles the call site rather than the body:
a caller cannot hand the same bytes over as the owned global and lend them as
a view at the same time, so `f(g, 4)` is refused during planning.

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

A narrow write inside a composite the function owns is stated as ownership
of the whole plus a promise about the cells the function leaves alone; a
caller that only views the composite cannot see which of its cells the callee
wrote, so the promise is what frames them:

<!-- verified-example: mdtests/field_derived_precise_effect_after_metadata_write.md -->
```click
owns owned_buffer(owner);
ensures owner->data[0] == old(owner->data[0]);
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
