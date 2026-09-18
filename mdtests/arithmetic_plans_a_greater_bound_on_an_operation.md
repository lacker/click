# `arithmetic()` plans a `>=` goal over an int32 operation

`n - 1 >= 0` follows from `n >= 1`, and `n - 1 < n` from `n >= 0`; the second
already verified while the first failed as unable to establish definedness.
The planner only read goals spelled `<`, `<=`, `==`, and `!=` when it looked
for the operation whose overflow evidence the conclusion needs, so a goal
spelled `>=` or `>` over an operation never got a plan. It now reads those
orderings from the other side, the way the certificate checker already does.

```c filename=arithmetic_plans_a_greater_bound_on_an_operation.c
int32 predecessor(int32 n) {
    return 0;
}
```

```click
verifying "arithmetic_plans_a_greater_bound_on_an_operation.c";

int32 predecessor(int32 n) {
    requires n >= 1;
    ensures result == 0;
} by {
    have n - 1 >= 0 by { arithmetic() using { n >= 1; } }
    have n > n - 1 by { arithmetic() using { n >= 1; } }
    step();
    simp();
}
```

```expect
pass
```
