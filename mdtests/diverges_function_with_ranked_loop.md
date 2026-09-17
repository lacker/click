# a `diverges` function may still rank its other loops

The marker is about the function, not about every loop in it. The counting
loop carries its measure and its back-edge ranking members are checked as
usual; only the second loop is the one that may never exit.

```c filename=diverges_function_with_ranked_loop.c
int32 drain_then_wait(int32 n, int32 x) {
    while (n > 0) {
        n = n - 1;
    }
    while (x != 0) {
    }
    return n;
}
```

```click
verifying "diverges_function_with_ranked_loop.c";

int32 drain_then_wait(int32 n, int32 x) diverges {
    requires n >= 0;
    ensures result == 0;
} by {
    loop {
        decreases n;
        invariant n >= 0;
        initialize by simp;
        preserve by {
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
    loop diverges {
        invariant n == 0;
        initialize by simp;
        preserve by {
            step();
            close_invariants by { simp(); }
        }
    }
    step();
    simp();
}
```

```expect
pass
```
