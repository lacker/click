# loop frames support several segment shapes

This checks loop-level `frame` clauses beyond the whole-loop `p[0..n]`
pattern: explicit step-relative growing prefixes, stable whole-loop shifted
suffixes, and step-relative multi-segment mutable footprints.

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
    requires valid_range(p[0..n]);
    loop 0 {
        invariant i >= 0 by auto;
        invariant i <= n by auto;
        step {
            mutable p[0..i + 1] by frame;
        }
    }
    ensures returns_n: result == n by auto;
}

int32 fill_tail(int32 p[], int32 n) {
    requires n >= 1;
    requires n <= 2147483647;
    requires valid_range(p[0..n]);
    loop 0 {
        invariant i >= 1 by auto;
        invariant i <= n by auto;
        mutable p[1..n] by frame;
    }
    ensures returns_n: result == n by auto;
}

int32 fill_two(int32 p[], int32 q[], int32 n) {
    requires n >= 0;
    requires n <= 2147483647;
    requires valid_range(p[0..n]);
    requires valid_range(q[0..n]);
    loop 0 {
        invariant i >= 0 by auto;
        invariant i <= n by auto;
        step {
            mutable p[i..i + 1], q[i..i + 1] by frame;
        }
    }
    ensures returns_n: result == n by auto;
}
```

```expect
pass
```
