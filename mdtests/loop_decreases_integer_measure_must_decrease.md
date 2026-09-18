# an Integer loop measure still has to decrease

The measure is `Integer`-valued and its nonnegativity closes, but the body
never moves what it reads: it counts `m` down while `level(n)` reads `n`. The
back edge therefore compares the measure against itself, and the ranking member
stays open. The other carrier buys no leniency: `<` on the Integers is the
strict order, and the obligation is the one an int32 measure produces.

```c filename=loop_decreases_integer_measure_must_decrease.c
int32 drain(int32 n, int32 m) {
    while (m > 0) {
        m = m - 1;
    }
    return m;
}
```

```click
verifying "loop_decreases_integer_measure_must_decrease.c";

function level(n: int32) -> Integer {
    to_integer(n)
}

int32 drain(int32 n, int32 m) {
    requires n >= 0;
    requires m >= 0;
    ensures result == 0;
} by {
    loop {
        decreases level(n);
        invariant 0 <= n;
        invariant 0 <= m;
        initialize by { simp(); }
        preserve by {
            have 0 <= m - 1 by {
                apply(int32_positive_predecessor_is_nonnegative(m)) using {
                    m > 0;
                }
            }
            have 0 <= level(n) by {
                unfold(level(n));
                apply(int32_less_equal_to_integer(0, n)) using {
                    0 <= n;
                }
                simp();
            }
            step();
            close_invariants by { simp(); };
        }
    }
    step();
    simp();
}
```

```expect
fail: `level(n)` decreases at the back edge
```
