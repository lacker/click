# a C recursion measure may be a lexicographic tuple

Ackermann's function has no single numeric measure: the inner call keeps `m`
and lowers `n`, and the outer calls lower `m` while `n` may grow arbitrarily.
The function-level `decreases` slot takes the loop slot's tuple syntax. Click
reads the tuple at `ack`'s own entry and again at each call to `ack` inside it,
and each call owes the loop back edge's bundle: every component is
nonnegative, and some component is strictly smaller while every earlier one
is unchanged. The outer call's second argument is the inner call's result,
whose nonnegativity is the inner call's postcondition.

```c filename=c_decreases_lexicographic_recursion.c
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
verifying "c_decreases_lexicographic_recursion.c";

int32 ack(int32 m, int32 n) {
    decreases (m, n);
    requires m >= 0;
    requires n >= 0;
    ensures result >= 0;
} by {
    branch then {
        step();
        simp();
    } else {}
    have m > 0 by {
        arithmetic() using {
            m >= 0;
            m != 0;
        }
    }
    have 0 <= m - 1 by {
        apply(int32_positive_predecessor_is_nonnegative(m)) using {
            m > 0;
        }
    }
    have m - 1 < m by {
        apply(int32_positive_predecessor_strictly_decreases(m)) using {
            m > 0;
        }
    }
    branch then {
        step();
        step();
        simp();
    } else {}
    have n > 0 by {
        arithmetic() using {
            n >= 0;
            n != 0;
        }
    }
    have 0 <= n - 1 by {
        apply(int32_positive_predecessor_is_nonnegative(n)) using {
            n > 0;
        }
    }
    have n - 1 < n by {
        apply(int32_positive_predecessor_strictly_decreases(n)) using {
            n > 0;
        }
    }
    execute();
    simp();
}
```

```expect
pass
```
