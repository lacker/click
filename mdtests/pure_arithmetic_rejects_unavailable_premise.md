# arithmetic requires every listed premise exactly

```click
theorem omitted_bound(n: int32) {
    ensures 0 <= n - 2 by {
        arithmetic() using {
            1 < n;
        }
    }
}
```

```expect
fail: arithmetic using` premise 0 is not exactly available
```
