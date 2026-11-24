# a lexicographic recursion measure is ordered

The tuple is compared component by component from the left, so the order of
its components is part of the measure. Ackermann's first base call passes
`(m - 1, 1)`. Ranked by `(n, m)`, that call must lower `n` to `1` or keep
`n == 1` and lower `m`, and nothing the proof knows establishes either. The
proof is the one that verifies `(m, n)` in
[`c_decreases_lexicographic_recursion.md`](c_decreases_lexicographic_recursion.md).

```c filename=c_decreases_lexicographic_recursion_order.c
int ack(int m, int n) {
    if (m == 0) {
        return 1;
    }
    if (n == 0) {
        return ack(m - 1, 1);
    }
    return ack(m - 1, ack(m, n - 1));
}
```

```click
verifying "c_decreases_lexicographic_recursion_order.c";

int32 ack(int32 m, int32 n) {
    decreases (n, m);
    requires m >= 0;
    requires n >= 0;
    ensures result >= 0;
} by {
    branch {
        true => {
            step();
            close();
        }
        false => {}
    }
    have m > 0 by {
        close() using {
            m >= 0;
            m != 0;
        };
    }
    have 0 <= to_integer(m - 1);
    have to_integer(m - 1) < to_integer(m);
    branch {
        true => {
            step();
            step();
            close();
        }
        false => {}
    }
    have n > 0 by {
        close() using {
            n >= 0;
            n != 0;
        };
    }
    have 0 <= to_integer(n - 1);
    have to_integer(n - 1) < to_integer(n);
}
```

```expect
fail: `(n, m)` decreases at the recursive call
```
