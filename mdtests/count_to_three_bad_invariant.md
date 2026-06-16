# count_to_three rejects a false invariant

This checks that an `at loop` invariant is checked again after the loop body.

```c filename=count_to_three_bad_invariant.c
int32 count_to_three_bad_invariant() {
    int32 i;
    i = 0;
    while (i < 3) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "count_to_three_bad_invariant.c";

int32 count_to_three_bad_invariant() {
    at loop 0 {
        invariant i < 3 by auto;
    }

    ensures result == 3 by auto;
}
```

```expect
fail: left proof obligations
```
