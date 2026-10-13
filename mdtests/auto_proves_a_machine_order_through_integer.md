# `auto` proves a machine order through its `Integer` reading

A `uint64` or `int64` order goal is proved as the order of its operands'
`Integer` observations, and carried back by
`uint64_to_integer_less_than_implies_less_than` or its `<=` form.

```click
theorem machine_goal(i: uint64, n: uint64) {
    requires i < n;
    requires n <= 1000u64;
    ensures i < 1000u64 by {
        have i < 1000u64 by auto;
        assumption();
    }
}
```

```expect
pass
```
