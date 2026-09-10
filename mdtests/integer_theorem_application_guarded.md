# Integer theorem application discharges a nontrivial guard

```click
theorem guarded(x: Integer) {
    requires x == 0;
    ensures x == 0 by { simp(); }
}

theorem use_guarded(x: Integer) {
    requires x == 0;
    ensures x == 0 by {
        apply(guarded(x));
    }
}
```

```expect
pass
```
