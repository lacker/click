# Nested loop facts require checked extraction before arithmetic

The loop invariant is deliberately nested as `A and (B and C)`.  The
preservation proof first extracts the needed member, then uses it as the exact
premise of the arithmetic step.

```c filename=arithmetic_conjunction_provenance.c
int32 drain(int32 n) {
    while (n > 0) {
        n = n - 1;
    }
    return n;
}
```

```click
verifying "arithmetic_conjunction_provenance.c";

int32 drain(int32 n) {
    requires n >= 0 and (n <= 2147483647 and n == n);
    ensures result == 0;
} by {
    loop {
        decreases n;
        invariant n >= 0;
        initialize by {
            have n >= 0 by { extract(n >= 0); }
            assumption();
        }
        preserve by {
            have 0 <= n - 1 by {
                apply(int32_positive_predecessor_is_nonnegative(n)) using { n > 0; }
            }
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
