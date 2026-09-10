# A loop-proof case after a body step keeps its execution position in expansion

`preserve by` increments `i` and only then splits on `flag == i`. The split
is evaluated at the frontier where it appears: the expanded certificate must
keep `step()` before the `if`, since hoisting the case before the increment
would make its condition denote the earlier `i`. Ordinary verification and
the independently checked expansion must agree.

```c filename=count_once.c
int32 count_once(int32 flag) {
    int32 i;
    i = 0;
    while (i < 1) { i = i + 1; }
    return i;
}
```

```click
verifying "count_once.c";
int32 count_once(int32 flag) {
    ensures result == 1;
} by {
    step();
    step();
    loop {
        invariant i >= 0;
        invariant i <= 1;
        initialize by simp;
        preserve by {
            step();
            if flag == i {
                have flag == i by { assumption(); }
            } else {
                have not (flag == i) by { assumption(); }
            }
            close_invariants();
        }
    }
    step();
    simp();
}
```

```expect
pass
```
