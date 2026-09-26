# Integer theorem application rejects an altered explicit guard

The refusal names the premise as it was written; it used to print the
kernel proposition's Debug form.

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
fail: `apply using` requires an unavailable exact premise: `x == 1`
```
