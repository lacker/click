# Applying a named theorem exposes its premises as obligations

```click
theorem nonnegative(n: Integer) {
    requires n >= 0;
    ensures n >= 0 by close();
}
theorem positive(n: Integer) {
    requires n > 0;
    ensures n >= 0 by {
        apply(nonnegative(n));
    }
}

theorem nonpositive(n: Integer) {
    requires n <= 0;
    ensures true by { close(); }
}
theorem integer_literal_argument() {
    ensures true by {
        apply(nonpositive(-9223372036854775809));
    }
}

```

```expect
pass
```
