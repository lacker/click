# a loop measure whose address escapes cannot be ranked

`*p = 10` resets `i` through its escaped address on every iteration, so the
loop never terminates even though `i = i - 1` looks like a ranked update.

```c filename=c_decreases_rejects_address_escaped_loop_measure.c
int32 spin(int32 n) {
    int32 i;
    int32* p;
    i = 10;
    p = &i;
    while (i > 0) {
        i = i - 1;
        *p = 10;
    }
    return 0;
}
```

```click
verifying "c_decreases_rejects_address_escaped_loop_measure.c";

int32 spin(int32 n) {
    ensures result == 0;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases i;
        invariant i >= 0;
    }
    step();
    simp();
}
```

```expect
fail: termination measure `i` in `spin` has its address taken
```
