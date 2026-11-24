# count_to_three rejects a false frontier-local fact

This checks that `have` proves its proposition at the current execution
frontier rather than merely adding it to the context.

```c filename=count_to_three_bad_assert.c
int32 count_to_three_bad_assert() {
    int32 i;
    i = 0;
    return i;
}
```

```click
verifying "count_to_three_bad_assert.c";

int32 count_to_three_bad_assert() {
    ensures result == 0;
} by {
    step_until(region(2).entry);
    have i == 1 by {
        close();
    }
}
```

```expect
fail: tactic 1
```
