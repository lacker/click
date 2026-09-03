# arithmetic checks bounded nonlinear and bitwise consequences

The explicit arithmetic checker can use interval facts for bounded products,
constant remainders, and masked values. It also retains the shared-operand
rule for an arithmetic right shift of a nonnegative value.

```click
theorem bounded_product(x: int32, y: int32) {
    requires 0 <= x;
    requires x <= 10;
    requires 0 <= y;
    requires y <= 10;

    ensures x * y <= 100 by {
        arithmetic() using {
            0 <= x;
            x <= 10;
            0 <= y;
            y <= 10;
        }
    }
}

theorem bounded_remainder(x: int32) {
    requires 0 <= x;

    ensures 0 <= x % 4 by {
        arithmetic() using {
            0 <= x;
        }
    }
    ensures x % 4 < 4 by {
        arithmetic() using {
            0 <= x;
        }
    }
}

theorem bounded_mask(x: int32) {
    ensures (x & 255) <= 255 by {
        arithmetic();
    }
}

theorem nonnegative_right_shift(x: int32) {
    requires 0 <= x;

    ensures (x >> 1) <= x by {
        arithmetic() using {
            0 <= x;
        }
    }
}

theorem bounded_left_shift(x: int32) {
    requires 0 <= x;
    requires x <= 10;

    ensures (x << 2) <= 40 by {
        arithmetic() using {
            0 <= x;
            x <= 10;
        }
    }
}
```

```expect
pass
```
