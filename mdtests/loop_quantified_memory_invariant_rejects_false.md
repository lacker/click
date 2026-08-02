# loop_quantified_memory_invariant rejects a false proposition invariant

This checks that a false quantified proposition invariant fails at the loop
entry with the structural invariant label.

```c filename=loop_quantified_memory_invariant_rejects_false.c
int32 loop_quantified_memory_invariant_rejects_false(int32 p[], int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "loop_quantified_memory_invariant_rejects_false.c";

int32 loop_quantified_memory_invariant_rejects_false(int32 p[], int32 n) {
    requires n >= 1 and n <= 2147483647;
    requires loadable(p[0..n]);
    for loop(0) {
        invariant i >= 0 and i <= n;
        invariant forall (k: int32) {
            0 <= k and k < 1 implies p[k] == p[k] + 1
        };
    }
    ensures returns_n: result == n by auto;
}
```

```expect
fail: loop 0 invariant 1 entry
```
