# Integer theorem application cannot use an altered guard

```click
theorem guarded(x: Integer) {
    requires x == 0;
    ensures x + 1 > x by { simp(); }
}

theorem altered_guard(x: Integer) {
    requires x == 1;
    ensures x + 1 > x by {
        apply(guarded(x));
    }
}
```

```expect
fail: required exact fact
```
