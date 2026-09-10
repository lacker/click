# Integer theorem arguments are substituted simultaneously

```click
theorem ordered(a: Integer, b: Integer) {
    requires a == 0;
    requires b == 1;
    ensures b == 1 by { simp(); }
}

theorem swapped(a: Integer, b: Integer) {
    requires a == 1;
    requires b == 0;
    ensures a == 1 by {
        apply(ordered(b, a));
    }
}
```

```expect
pass
```
