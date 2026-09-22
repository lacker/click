# `loop` proves a natural `goto` cycle with multiple backedges

Several conditional paths may re-enter the same cycle header. The existing
`loop` proof supplies one invariant and termination measure for all of them.

```c filename=natural_goto_multiple_backedges.c
int32 count_down_by_cases(int32 n) {
again:
    if (n > 1) {
        n--;
        goto again;
    }
    if (n == 1) {
        n--;
        goto again;
    }
    goto done;
done:
    return 0;
}
```

```click
verifying "natural_goto_multiple_backedges.c";

int32 count_down_by_cases(int32 n) {
    requires n >= 0;
    ensures result == 0;
} by {
    loop {
        invariant n >= 0;
        decreases n;
    }
    simp();
}
```

```expect
pass
```
