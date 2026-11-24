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
import click::integer;
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
        initialize by { close(); }
        maintain by {
            have 0 <= to_integer(m - 1);
            have 0 <= level(n) by {
                unfold(level(n));
            }
            step();
        }
    }
    step();
    close();
}
```

```expect
fail: `level(n)` decreases at the back edge
```
