# `loop` reports the frontier it was applied at

`loop` only applies when the execution frontier is at a C loop. Applied at a
declaration, it must report the current statement rather than searching ahead.

```c filename=sum_to.c
int32 sum_to(int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "sum_to.c";

int32 sum_to(int32 n) {
    requires n >= 0 and n <= 4;
    ensures nonneg: result >= 0;
} by {
    loop {
        invariant i >= 0;
    }
}
```

```expect
fail: requires the execution frontier to be at a loop
```
