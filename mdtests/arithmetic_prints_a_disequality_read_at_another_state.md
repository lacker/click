# `solve() using` prints a sharpened bound whose premises are spelled at different states

Inside a loop body, `at(region(3).entry, i)` and `at(region(6).entry, i)`
name the same value when nothing between those statements writes `i`; they
lower to one kernel term. The certificate step that sharpens `i >= 0` with
`i != 0` into `0 < i` used to pair its two premises by their printed operands,
so citing the bound at one state and the disequality at another found a
plan the kernel accepted and then failed to print it, and the refusal blamed
the premises. The printed strict bound now takes its sides from the bound
alone; the kernel checks that the disequality names the same affine form.

When a plan exists but a step has no source spelling, the refusal now says so
instead of reporting the premises as insufficient.

```c filename=arithmetic_prints_a_disequality_read_at_another_state.c
int32 stop_at(int32 n) {
    int32 i = n;

    while (true) {
        if (i == 3) {
            break;
        }
        if (i == 0) {
            break;
        }
        i = 0;
    }
    return i;
}
```

```click
verifying "arithmetic_prints_a_disequality_read_at_another_state.c";

int32 stop_at(int32 n) {
    requires n >= 0;
    ensures result == 3 or result == 0;
} by {
    step();
    step();
    loop {
        decreases i;
        invariant i >= 0;

        initialize by solve();
        preserve by {
            if i == 3 {
                step();
                step();
            } else {
                step();
                step();
                if i == 0 {
                    step();
                    step();
                } else {
                    step();
                    step();
                    step();
                }
            }
        }
    }
    step();
    solve();
}
```

```expect
pass
```
