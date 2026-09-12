# Public signed-int32 certificate composition

The signed-machine family keeps compound-operation evidence explicit. A direct
interval import is distinct from an affine atom interval, and a two-sided
affine conclusion names both operation roots.

Cross-domain composition uses a checked machine-to-`Integer` bridge theorem,
then applies only the homogeneous mathematical `Integer` certificate family.

```click
theorem signed_direct_compound(n: int32) {
    requires 0 <= n + 1;
    ensures 0 <= n + 1 by {
        arithmetic_certificate signed_int32 {
            premise 0: 0 <= n + 1 => 0 <= n + 1;
            interval_from_affine_direct 0 (n + 1) 0 2147483647;
            affine_conclusion 0 1 => 0 <= n + 1;
            conclusion 2;
        }
    }
}

theorem signed_pair_compound(n: int32) {
    requires 0 <= n;
    requires n <= 100;
    ensures n + 1 <= n + 2 by {
        arithmetic() using {
            0 <= n;
            n <= 100;
        }
    }
}

theorem machine_to_integer_then_integer_arithmetic(x: int32) {
    requires 0 <= x;
    ensures 0 <= to_integer(x) + 1 by {
        have to_integer(0) <= to_integer(x) by {
            apply(int32_less_equal_to_integer(0, x));
        }
        arithmetic_certificate {
            premise 0: to_integer(0) <= to_integer(x) => to_integer(0) <= to_integer(x);
            trivial => to_integer(x) + 1 >= to_integer(x);
            add 0, 1 => 0 <= to_integer(x) + 1;
            conclusion 2;
        }
    }
}
```

```expect
pass
```
