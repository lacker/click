# count_to_n verifies a symbolic loop with invariants

This checks the loop verification-condition path: `auto` proves a postcondition
for a symbolic loop bound using loop invariants instead of concrete unrolling.

```c filename=count_to_n_loop_invariant.c
int32 count_to_n_loop_invariant(int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "count_to_n_loop_invariant.c";

int32 count_to_n_loop_invariant(int32 n) {
    requires n >= 0 and n <= 2147483647;
    at loop 0 {
        invariant i >= 0 and i <= n by auto;
    }
    ensures returns_n: result == n and result >= 0 by auto;
}
```

```expect
pass
```
