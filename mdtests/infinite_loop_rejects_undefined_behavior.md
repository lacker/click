# A perpetual loop still checks finite undefined behavior

Nontermination does not hide a bad first iteration.

```c filename=infinite_loop_rejects_undefined_behavior.c
int32 bad_spin() {
    int32 x;
    x = 1;
    while (1) {
        x = x / 0;
    }
    return 0;
}
```

```click
verifying "infinite_loop_rejects_undefined_behavior.c";

int32 bad_spin() {
    for loop(0) {
        invariant x == 1;
    }

    ensures 0 == 0 by auto;
}
```

```expect
fail: division by zero
```
