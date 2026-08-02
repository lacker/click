# shifted loop effect subset

This checks that a loop effect summary with a shifted pointer base composes with
an enclosing function-level mutable clause. The loop writes `p[1..n]`, stated
as `(p + 1)[0..n - 1]`, and the function-level effect allows the larger
`p[0..n]` range.

```c filename=shifted_loop_effect_subset.c
int32 shifted_loop_effect_subset(int32 p[], int32 n) {
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
verifying "shifted_loop_effect_subset.c";

int32 shifted_loop_effect_subset(int32 p[], int32 n) {
    requires n >= 1;
    requires n <= 2147483647;
    requires loadable(p[0..n]);
    consumes p[0..n];
    for loop(0) {
        invariant i >= 1;
        invariant i <= n;
        mutable (p + 1)[0..n - 1] by frame;
    }
    mutable p[0..n] by auto;
    ensures returns_n: result == n;
}
```

```expect
pass
```
