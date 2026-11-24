# A compound addition theorem still requires its outer overflow guard

```click
theorem add_observation(left: int32, right: int32) {
    requires defined(left + right);
    ensures to_integer(left + right) == to_integer(left) + to_integer(right);
}

theorem missing(a: int32, b: int32, c: int32) {
    requires defined(a + b);
    ensures a == a by {
        apply(add_observation(a + b, c));
        close();
    }
}
```

```expect
fail: theorem `add_observation` has an unproved obligation
```
