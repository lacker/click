# count_to_three rejects a false statement assertion

This checks `at statement N` for a one-shot proof obligation.

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
    at statement 2 {
        assert i == 1 by auto;
    }

    ensures result == 0 by auto;
}
```

```expect
fail: at statement 2 assert 0
```
