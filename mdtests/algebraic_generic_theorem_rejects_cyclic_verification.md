# a generic theorem cannot establish its own concrete instance

```click
theorem circular<T>(value: T) {
    ensures value == value by {
        apply(circular(value));
        assumption();
    }
}

theorem expose(value: int32) {
    ensures value == value by {
        apply(circular(value));
        assumption();
    }
}
```

```expect
fail: unknown theorem `circular`
```
