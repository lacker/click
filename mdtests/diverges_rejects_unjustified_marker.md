# a `diverges` marker needs something that may not return

`diverges` is required on, and only on, a function that may not return. This
function's only loop is ranked and it calls nothing, so it has termination
evidence in everything but name, and the marker would hide that from every
caller. The refusal is local: it reads this function's loops and calls and no
other function's body.

```c filename=diverges_rejects_unjustified_marker.c
int32 drain(int32 n) {
    while (n > 0) {
        n = n - 1;
    }
    return n;
}
```

```click
verifying "diverges_rejects_unjustified_marker.c";

int32 drain(int32 n) diverges {
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
    step();
    simp();
}
```

```expect
fail: `drain` is declared `diverges`, but every loop it runs is ranked and every call it makes descends; remove the marker
```
