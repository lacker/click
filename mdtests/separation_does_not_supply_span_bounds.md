# Separation does not imply that an endpoint is nonnegative

```click
theorem no_span_fact(p: int32*, q: int32*, n: int32) {
    requires separate(memory(p[0..n]), memory(q[0..1]));
    ensures 0 <= n by { known(); }
}
```

```expect
fail: `known()` could not close the current goal
```
