# loop_quantified_memory_invariant verifies a proposition invariant

This checks that `invariant` accepts a full Click proposition, including a
bounded universal quantifier over current-state array reads.

```c filename=loop_quantified_memory_invariant.c
int32 loop_quantified_memory_invariant(int32 p[], int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "loop_quantified_memory_invariant.c";

int32 loop_quantified_memory_invariant(int32 p[], int32 n) {
    requires n >= 0 and n <= 2147483647;
    requires loadable(p[0..n]);
    for loop(0) {
        invariant i >= 0 and i <= n;
        invariant forall (int32 k) {
            0 <= k and k < n implies p[k] == p[k]
        };
    }
    ensures returns_n: result == n by auto;
}
```

```expect
pass
```
