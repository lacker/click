# an arithmetic loop measure proves count-up termination

```c filename=c_decreases_count_up.c
int32 count_to_n(int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i++;
    }
    return i;
}
```

```click
verifying "c_decreases_count_up.c";

int32 count_to_n(int32 n) {
    requires n >= 0 and n <= 2147483647;
    ensures result == n;
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant i >= 0;
        invariant i <= n;
        initialize by simp;
        preserve by {
            step();
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
