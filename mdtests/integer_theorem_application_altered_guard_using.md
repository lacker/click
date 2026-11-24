# An Integer theorem application reports its instantiated requirement

```click
theorem guarded(x: Integer) {
    requires x == 0;
    ensures x + 1 > x by close();
}

theorem altered_guard_using(x: Integer) {
    requires x == x;
    ensures x + 1 > x by {
        apply(guarded(x));
    }
}
```

```expect
fail: theorem `guarded` has an unproved obligation
```
