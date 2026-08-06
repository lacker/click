# count_to_three checks structural loop invariants

This checks that `loop` proves the `while` loop at the execution frontier.

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
    for statement(2) {
        assert i == 0 by auto;
    }

    ensures result == 3;
} by {
    step();
    step();
    loop {
        invariant i >= 0;
        invariant i <= 3;
    }
    step();
    simp();
}
```

```expect
pass
```
