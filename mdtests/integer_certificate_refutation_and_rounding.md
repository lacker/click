# Integer certificates by refutation and by rounding

A mathematical `Integer` certificate may assume the integer negation of a
bound goal with `negated_goal` and conclude with a contradiction. `divide`
divides a bound by a common factor of its coefficients and rounds its
constant, which is valid only over the integers.

```click
theorem refute_the_negated_goal(x: Integer) {
    requires 2 * x <= 10;
    ensures x <= 5 by {
        arithmetic_certificate {
            premise 0: 2 * x <= 10 => 2 * x <= 10;
            negated_goal => 5 < x;
            scale 1 by 2 => 2 * 6 <= 2 * x;
            add 0, 2 => 2 * x + 2 * 6 <= 10 + 2 * x;
            conclusion 3;
        }
    }
}

theorem contradictory_premises_prove_any_bound(x: Integer, y: Integer) {
    requires x <= 0;
    requires 1 <= x;
    ensures y <= 7 by {
        arithmetic_certificate {
            premise 0: x <= 0 => x <= 0;
            premise 1: 1 <= x => 1 <= x;
            add 0, 1 => x + 1 <= 0 + x;
            conclusion 2;
        }
    }
}

theorem round_a_halved_bound(x: Integer) {
    requires 2 * x <= 5;
    ensures x <= 2 by {
        arithmetic_certificate {
            premise 0: 2 * x <= 5 => 2 * x <= 5;
            divide 0 by 2 => x <= 2;
            conclusion 1;
        }
    }
}
```

```expect
pass
```
