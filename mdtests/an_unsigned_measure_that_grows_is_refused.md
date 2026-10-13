# An unsigned measure that grows is refused

`while (x < 4u) x++;` declares `decreases x` over the `uint32` counter, but
the body moves `x` up. The decrease member is `x + 1 <u x` at the entry
value of `x`, which is false under the guard `x <u 4`, so it stays open. The
unsigned carrier waives only nonnegativity, which every unsigned value has;
the strict descent is owed exactly as an int32 measure owes it.

```c filename=an_unsigned_measure_that_grows_is_refused.c
int32 fill(uint32 x) {
    while (x < 4u) {
        x++;
    }
    return 0;
}
```

```click
verifying "an_unsigned_measure_that_grows_is_refused.c";

int32 fill(uint32 x) {
    ensures result == 0;
} by {
    loop {
        decreases x;
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
fail: `at(statement(1).entry, x) + 1u32 < at(statement(1).entry, x)` remained open; this loop declares `decreases`, so the bundle also has `0 <= x` at the back edge, `x` decreases at the back edge
```
