# A displaced pointer's misalignment is decided, not left open

With `aligned(p, 8)` known, the masked address of `p + 1` is provably
nonzero, so the C comparison evaluates to a known `0` and the postcondition
that pins that value closes. This is the refutation half of alignment
reasoning; a merely undecided claim could not establish `result == 0`.

```c filename=aligned_refutes_displaced.c
int32 aligned_refutes_displaced(uint8* p) {
    return ((unsigned long)(p + 1) & 7) == 0;
}
```

```click
verifying "aligned_refutes_displaced.c";

int32 aligned_refutes_displaced(uint8* p) {
    requires aligned(p, 8);
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
pass
```
