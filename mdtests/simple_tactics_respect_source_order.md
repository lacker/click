# simple tactics respect source order

A later theorem application cannot be moved before an earlier goal-closing
tactic. Explicit proof scripts check in source order.

```click
theorem exact_zero(x: int32) {
    requires x == 0;

    ensures x == 0 by {
        assumption();
    }
}

theorem no_reordering(x: int32) {
    requires x == 0;

    ensures x == 0 by {
        assumption();
        apply(exact_zero(x));
    }
}
```

```expect
fail: follows a goal-closing tactic
```
