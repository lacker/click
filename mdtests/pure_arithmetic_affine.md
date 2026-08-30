# arithmetic checks explicit signed-affine consequences

`arithmetic` closes only the current goal. Its `using` block is the complete
premise universe for the linear certificate. When inequalities are combined,
each selected inequality has coefficient one; repeating a fact explicitly
permits a larger positive coefficient.

```click
theorem subtract_two_is_nonnegative(n: int32) {
    requires 1 < n;

    ensures 0 <= n - 2 by {
        arithmetic() using {
            1 < n;
        }
    }
}

theorem strict_order_is_transitive(a: int32, b: int32, c: int32) {
    requires a <= b;
    requires b < c;

    ensures a < c by {
        arithmetic() using {
            a <= b;
            b < c;
        }
    }
}

theorem affine_normalization_cancels_x(x: int32) {
    requires 0 <= x;
    requires x <= 1073741823;

    ensures 2 * x < x + (x + 1) by {
        arithmetic() using {
            0 <= x;
            x <= 1073741823;
        }
    }
}

theorem affine_equalities_normalize_both_sides(n: int32) {
    requires 1 < n;

    ensures n - 2 == (n - 1) - 1 by {
        arithmetic() using {
            1 < n;
        }
    }
}
```

```expect
pass
```
