# count_to_three checks structural loop invariants

This checks the first `.click` structural label form: `at loop 0` attaches
ghost checks to the first `while` loop head.

```c filename=count_to_three.c
int32 count_to_three() {
    int32 i;
    i = 0;
    while (i < 3) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "count_to_three.c";

int32 count_to_three() {
    at statement 2 {
        assert i == 0 by auto;
    }

    at loop 0 {
        invariant i >= 0 by auto;
        invariant i <= 3 by auto;
    }

    ensures result == 3 by auto;
}
```

```expect
pass
```
