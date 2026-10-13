# A negated goal must be the integer negation

The negation of `x <= 5` over the integers is `5 < x`, that is `6 <= x`.
Writing the rational negation `5 <= x` is refused.

```click
theorem rational_negation(x: Integer) {
    requires 2 * x <= 10;
    ensures x <= 5 by {
        arithmetic_certificate {
            premise 0: 2 * x <= 10 => 2 * x <= 10;
            negated_goal => 5 <= x;
            conclusion 0;
        }
    }
}
```

```expect
fail: node 1 does not state what its rule derives from its inputs
```
