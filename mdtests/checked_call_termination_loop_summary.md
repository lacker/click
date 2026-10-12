# A ranked loop retains the calls inside its checked summary

```c filename=c_decreases_loop.c
extern void may_spin(void);
int32 drain(int32 n) {
    while (n > 0) {
        may_spin();
        n = n - 1;
    }
    return n;
}
```

```click
verifying "c_decreases_loop.c";
extern void may_spin() diverges { ensures 1 == 1; }

int32 drain(int32 n) {
    requires n >= 0;
    ensures result == 0;
} by {
    loop {
        decreases n;
        invariant n >= 0;
        initialize by simp;
        preserve by {
            step();
            have 0 <= n - 1 by {
                apply(int32_positive_predecessor_is_nonnegative(n)) using { n > 0; }
            }
            step();
            close_invariants by {
                both { arithmetic() using { 0 <= n; } }
                and {
                    both { arithmetic() using { 0 <= n; } }
                    and { arithmetic() using { 0 <= n; } }
                }
            }
        }
    }
    step();
    simp();
}
```

```expect
fail: callee `may_spin` has no termination evidence
```
