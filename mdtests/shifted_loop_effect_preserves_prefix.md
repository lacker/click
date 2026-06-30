# shifted loop effect preserves prefix

This checks that a shifted loop effect summary can prove an old-memory
postcondition. The loop writes `p[1..n]`, so `p[0]` remains equal to its
entry-state value without a handwritten unchanged-memory invariant.

```c filename=shifted_loop_effect_preserves_prefix.c
int32 shifted_loop_effect_preserves_prefix(int32 p[], int32 n) {
    int32 i;
    i = 1;
    while (i < n) {
        p[i] = i;
        i = i + 1;
    }
    return i;
}
```

```click
verifying "shifted_loop_effect_preserves_prefix.c";

int32 shifted_loop_effect_preserves_prefix(int32 p[], int32 n) {
    requires n >= 1;
    requires n <= 2147483647;
    requires valid_range(p[0..n]);
    requires write(p[0..n]);
    for loop(0) {
        invariant i >= 1;
        invariant i <= n;
        mutable (p + 1)[0..n - 1] by frame;
    }
    ensures keeps_first: p[0] == old(p[0]);
    ensures returns_n: result == n;
}
```

```expect
pass
```
