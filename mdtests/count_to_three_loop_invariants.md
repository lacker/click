# count_to_three checks structural loop invariants

This checks `.click` region proof blocks: `for loop(0)` attaches spec
checks to the first `while` loop code region.

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

    for loop(0) {
        invariant i >= 0;
        invariant i <= 3;
    }

    ensures result == 3 by auto;
}
```

```expect
pass
```
