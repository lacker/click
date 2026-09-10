# Integer theorem application requires exact guards

```click
theorem guarded(x: Integer) {
    requires x == 0;
    ensures x + 1 > x by { simp(); }
}

theorem missing_guard(x: Integer) {
    requires x == x;
    ensures x + 1 > x by {
        apply(guarded(x));
    }
}
```

```expect
fail: required exact fact
```
