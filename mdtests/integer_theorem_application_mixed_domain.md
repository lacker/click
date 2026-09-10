# Integer theorem applications reject machine arguments

```click
theorem mixed(integer_value: Integer, machine_value: int32) {
    requires integer_value == integer_value;
    ensures integer_value + 1 > integer_value by { simp(); }
}

theorem mixed_domain(x: Integer, y: int32) {
    requires x == x;
    ensures x + 1 > x by {
        apply(mixed(y, x));
    }
}
```

```expect
fail: expected a specification-side Integer expression
```
