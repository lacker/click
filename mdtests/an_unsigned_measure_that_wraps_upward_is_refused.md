# An unsigned measure that wraps upward is refused

`while (x < 4u) x++;` declares `decreases 3 - x` over the `uint32` counter.
The mathematical difference `3 - x` falls on every iteration, but C computes
it in `uint32`: on the last iteration `x` goes from 3 to 4 and the measure
goes from 0 to 2^32 - 1. The decrease member compares the two wrapped values
C computes, `2 - x <u 3 - x` at the entry value of `x`, which is false at
`x == 3`, so it stays open. Ranking the wrapped value is what keeps an
unsigned measure well founded: `<` on the naturals below 2^32 has no
infinite descent, and a back edge that wraps is not a descent in it.

```c filename=an_unsigned_measure_that_wraps_upward_is_refused.c
int32 fill(uint32 x) {
    while (x < 4u) {
        x++;
    }
    return 0;
}
```

```click
verifying "an_unsigned_measure_that_wraps_upward_is_refused.c";

int32 fill(uint32 x) {
    ensures result == 0;
} by {
    loop {
        decreases 3 - x;
        initialize by { simp(); }
        preserve by {
            step();
            close_invariants();
        }
    }
    execute();
    simp();
}
```

```expect
fail: `0u32 - at(statement(1).entry, x) + 2u32 < 0u32 - at(statement(1).entry, x) + 3u32` remained open; this loop declares `decreases`, so the bundle also has `0 <= 3 - x` at the back edge, `3 - x` decreases at the back edge
```
