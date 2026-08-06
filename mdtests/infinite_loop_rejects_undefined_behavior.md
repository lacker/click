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
    ensures 0 == 0;
} by {
    step();
    step();
    loop {
        invariant x == 1;
    }
    simp();
}
```

```expect
fail: division by zero
```
