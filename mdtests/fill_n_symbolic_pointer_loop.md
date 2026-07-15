# fill_n verifies a symbolic pointer loop

This checks that `auto` can use a symbolic range requirement and loop
invariants to verify a pointer loop without unrolling the loop to a concrete
bound.

```c filename=fill_n_symbolic_pointer_loop.c
int32 fill_n_symbolic_pointer_loop(int32 p[], int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        p[i] = i;
        i = i + 1;
    }
    return i;
}
```

```click
verifying "fill_n_symbolic_pointer_loop.c";

int32 fill_n_symbolic_pointer_loop(int32 p[], int32 n) {
    requires n >= 0;
    requires n <= 2147483647;
    requires loadable(p, n * 4);
    consumes p[0..n];
    for loop(0) {
        invariant i >= 0;
        invariant i <= n;
    }
    ensures returns_n: result == n by auto;
}
```

```expect
pass
```
