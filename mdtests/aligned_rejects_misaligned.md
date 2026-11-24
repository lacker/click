# A displaced pointer is refuted, not merely undecided

With `aligned(p, 8)` known, `p + 1` is provably misaligned for 8, so a
postcondition claiming otherwise fails as a false claim rather than an open
one.

```c filename=aligned_rejects_misaligned.c
int32 aligned_rejects_misaligned(uint8* p) {
    return 0;
}
```

```click
verifying "aligned_rejects_misaligned.c";

int32 aligned_rejects_misaligned(uint8* p) {
    requires aligned(p, 8);
    ensures aligned(p + 1, 8);
} by {
    step_until(function.exit);
    close();
}
```

```expect
fail: did not retain a complete proof for `aligned_rejects_misaligned.ensures_0`
```
