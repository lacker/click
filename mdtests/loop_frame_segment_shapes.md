# loop framing supports several segment shapes

This checks loop framing beyond the whole-loop `p[0..n]` pattern: a growing
prefix and a multi-segment body framed by the default footprint the function
owns, and a stable whole-loop shifted suffix declared as loop-level `owns`.

```c filename=fill_prefix.c
int32 fill_prefix(int32 p[], int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        p[i] = i;
        i = i + 1;
    }
    return i;
}
```

```c filename=fill_tail.c
int32 fill_tail(int32 p[], int32 n) {
    int32 i;
    i = 1;
    while (i < n) {
        p[i] = i;
        i = i + 1;
    }
    return i;
}
```

```c filename=fill_two.c
int32 fill_two(int32 p[], int32 q[], int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        p[i] = i;
        q[i] = i;
        i = i + 1;
    }
    return i;
}
```

```click
verifying "fill_prefix.c";
verifying "fill_tail.c";
verifying "fill_two.c";

int32 fill_prefix(int32 p[], int32 n) {
    requires n >= 0;
    requires n <= 2147483647;
    requires loadable(p[0..n]);
    consumes p[0..n];
    ensures returns_n: result == n;
} by {
    step();
    step();
    loop {
        invariant i >= 0;
        invariant i <= n;
    }
    step();
    simp();
}

int32 fill_tail(int32 p[], int32 n) {
    requires n >= 1;
    requires n <= 2147483647;
    requires loadable(p[0..n]);
    consumes p[0..n];
    ensures returns_n: result == n;
} by {
    step();
    step();
    loop {
        invariant i >= 1;
        invariant i <= n;
        owns p[1..n];
    }
    step();
    simp();
}

int32 fill_two(int32 p[], int32 q[], int32 n) {
    requires n >= 0;
    requires n <= 2147483647;
    requires loadable(p[0..n]);
    requires loadable(q[0..n]);
    consumes p[0..n];
    consumes q[0..n];
    ensures returns_n: result == n;
} by {
    step();
    step();
    loop {
        invariant i >= 0;
        invariant i <= n;
    }
    step();
    simp();
}
```

```expect
pass
```
