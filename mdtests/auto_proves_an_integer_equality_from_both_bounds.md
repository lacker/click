# `auto` proves an `Integer` equality from both bounds

An equality goal `l == r` is proved as `l <= r` and `r <= l`, each by the
solver, joined by `equal_from_bounds`.

```click
theorem equality_goal(a: Integer, b: Integer, c: Integer) {
    requires a == b + c;
    requires b == 2;
    requires c == 3;
    ensures a == 5 by {
        have a == 5 by auto;
        assumption();
    }
}
```

```expect
pass
```
