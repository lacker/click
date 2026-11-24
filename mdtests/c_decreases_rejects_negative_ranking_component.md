# a ranking component that can go negative fails at its own bundle member

The loop terminates and preserves both invariants, and `n - 6` does strictly
decrease on every back edge. It is still not a ranking: the loop reaches the
back edge with `n` equal to `1`, where `n - 6` is negative, so the measure is
not well founded. The back-edge bundle fails at the loop's own nonnegativity
member, which the diagnostic names.

```c filename=c_decreases_rejects_negative_ranking_component.c
int32 drift(int32 n) {
    while (n > 0) {
        n = n - 1;
    }
    return n;
}
```

```click
verifying "c_decreases_rejects_negative_ranking_component.c";

int32 drift(int32 n) {
    requires n >= 0 and n <= 100;
    ensures result == 0;
} by {
    loop {
        decreases n - 6;
        invariant n >= 0;
        invariant n <= 100;
        initialize by close();
        maintain by {
            have 0 <= to_integer(n - 1);
            step();
        }
    }
    step();
    close();
}
```

```expect
fail: `0 <= (to_integer(n) - 6)` at the back edge
```
