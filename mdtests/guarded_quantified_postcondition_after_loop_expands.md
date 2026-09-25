# A guarded quantified postcondition after a loop expands and re-verifies

`fill` sets every cell of `occ` to `1` and returns `1`, the shape of an
allocator's occupancy postcondition: `result == 1 implies forall (k: int32)
{ ... }`. After the loop, `simp()` closes the claim by introducing the guard
and the binder and instantiating the loop invariant; claim expansion renders
that proof as a `have` of the claim followed by `assumption()`. The `have`
and the claim lower the guarded quantifier with independent fresh binders,
and the rewrite used to fail with "`assumption` did not match any current
proposition goal". The expansion regression in
`src/surface/tests/expansion_tests.rs` expands this claim and re-verifies the
rewrite.

```c filename=guarded_quantified_postcondition_after_loop.c
int fill(int32* occ, int32 cap) {
    int32 i = 0;
    while (i < cap) {
        occ[i] = 1;
        i = i + 1;
    }
    return 1;
}
```

```click
verifying "guarded_quantified_postcondition_after_loop.c";

int fill(int32* occ, int32 cap) {
    owns occ[0..cap];
    requires 0 <= cap;
    ensures result == 1 implies forall (k: int32) {
        0 <= k and k < cap implies occ[k] == 1
    };
} by {
    step();
    step();
    loop {
        decreases cap - i;
        invariant 0 <= i;
        invariant i <= cap;
        invariant forall (k: int32) { 0 <= k and k < i implies occ[k] == 1 };
        owns occ[0..cap];
    }
    execute();
    simp();
}
```

```expect
pass
```
