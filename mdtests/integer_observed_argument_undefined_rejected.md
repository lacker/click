# Capturing an Integer argument must check machine evaluation

```click
theorem reflexive(n: Integer) {
    ensures n == n by close();
}

theorem undefined_argument(a: int32) {
    ensures 0 == 0 by {
        apply(reflexive(to_integer(a + 1)));
        close();
    }
}
```

```expect
fail: proof step
```
