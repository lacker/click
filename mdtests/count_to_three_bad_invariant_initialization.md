# count_to_three rejects a false invariant at loop entry

This checks that `at loop` invariants report initialization failures separately
from preservation failures.

```c filename=count_to_three_bad_invariant_initialization.c
int32 count_to_three_bad_invariant_initialization() {
    int32 i;
    i = 0;
    while (i < 3) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "count_to_three_bad_invariant_initialization.c";

int32 count_to_three_bad_invariant_initialization() {
    at loop 0 {
        invariant i == 1 by auto;
    }

    ensures result == 3 by auto;
}
```

```expect
fail: at loop 0 invariant 0 entry
```
