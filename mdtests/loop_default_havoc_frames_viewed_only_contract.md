# A view-only contract frames its viewed memory across a clause-free loop

This contract owns no memory at all, so its write footprint is empty and the
loop body can write nothing the caller can see; the body writes only an
address-escaped local. A loop with no effect clause inherits that empty
footprint rather than becoming an unconditional havoc, so the viewed cell is
provably unchanged after the loop with no invariant naming it.

```c filename=loop_default_havoc_frames_viewed_only_contract.c
void loop_default_havoc_frames_viewed_only_contract(int32 r[], int32 n) {
    int32 x;
    int32* px;
    int32 i;
    x = 0;
    px = &x;
    i = 0;
    while (i < n) {
        *px = i;
        i = i + 1;
    }
}
```

```click
verifying "loop_default_havoc_frames_viewed_only_contract.c";

void loop_default_havoc_frames_viewed_only_contract(int32 r[], int32 n) {
    requires n >= 0;
    requires loadable(r[0..1]);
    views r[0..1];
    ensures r_preserved: r[0] == old(r[0]);
} by {
    step();
    step();
    step();
    step();
    step();
    step();
    loop {
        invariant i >= 0 and i <= n;
    }
    step();
    simp();
}
```

```expect
pass
```
