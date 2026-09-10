# Integer theorem application cannot use an altered guard

```click
theorem guarded(x: Integer) {
    requires x == 0;
    ensures x + 1 > x by { simp(); }
}

theorem altered_guard(x: Integer) {
    requires x == x;
    ensures x + 1 > x by {
        apply(guarded(x)) using { x == 1; };
    }
}
```

```expect
fail: kernel lowering produced 0 paths
```
