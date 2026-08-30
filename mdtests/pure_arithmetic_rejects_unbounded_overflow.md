# arithmetic does not treat int32 as unbounded integers

Without bounds, the affine-looking expressions below may overflow before the
comparison is made.

```click
theorem unbounded_affine_overflow(x: int32) {
    ensures 2 * x < x + (x + 1) by {
        arithmetic();
    }
}
```

```expect
fail: defined without overflow
```
