# A quantified invariant whose range is empty at a symbolic loop entry

The loop counter starts at the symbolic lower bound, so at loop entry the
invariant's guard `lo <= k and k < i` has no model. The smart proof must
certify that vacuous universal with an explicit `intro; intro;
contradiction(guard)` script: the guard's order facts form a strict cycle
over one term, which the kernel's context-free normalizer disproves. Before
this regression only constant bounds had a certificate.

```c filename=probe_fill.c
int32 probe_fill(int32 p[], int32 lo, int32 hi, int32 v) {
    int32 i;
    i = lo;
    while (i < hi) {
        p[i] = v;
        i = i + 1;
    }
    return i;
}
```

```click
verifying "probe_fill.c";

int32 probe_fill(int32 p[], int32 lo, int32 hi, int32 v) {
    requires 0 <= lo and lo <= hi and hi <= 1000;
    owns p[lo..hi];
    ensures result == hi;
    ensures forall (k: int32) { lo <= k and k < hi implies p[k] == v };
} by {
    step();
    step();
    loop as fill {
        invariant lo <= i and i <= hi;
        invariant forall (k: int32) { lo <= k and k < i implies p[k] == v };

        initialize by simp;
        preserve by {
            step();
            step();
            simp();
        }
    }
    step();
    simp();
}
```

```termination
pending: unranked loop
```

```expect
pass
```
