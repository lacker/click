# An inactive proof branch cannot certify the active branch ranking

The inactive branch has no backedge, but its constant measure must not
authorize a nondecreasing measure on the active branch.

```c filename=proof_branch_shared_loop.c
int32 count_to_bound(int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i++;
    }
    return i;
}
```

```click
verifying "proof_branch_shared_loop.c";

int32 count_to_bound(int32 n) {
    ensures result >= 0;
} by {
    step();
    step();
    if n < 0 {
        loop {
            decreases 0;
            invariant i == 0;
            invariant n < 0;
        }
    } else {
        have n >= 0 by close();
        loop {
            decreases 0;
            invariant 0 <= i and i <= n;
            initialize by close();
            maintain by { step(); }
        }
    }
}
```

```expect
fail: `0` decreases at the back edge
```
