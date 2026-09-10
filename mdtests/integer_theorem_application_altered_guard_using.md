# Integer theorem application rejects an altered explicit guard

```click
theorem guarded(x: Integer) {
    requires x == 0;
    ensures x + 1 > x by { simp(); }
}

theorem altered_guard_using(x: Integer) {
    requires x == x;
    ensures x + 1 > x by {
        apply(guarded(x)) using { x == 1; };
    }
}
```

```expect
fail: unavailable exact premise
```
