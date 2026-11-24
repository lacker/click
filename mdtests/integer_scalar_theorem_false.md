# mathematical Integer false theorem

This checks that a false mathematical Integer claim remains unproved.

```click quick-solve
theorem integer_false(x: Integer) {
    ensures x < x by {
        close();
    }
}
```

```expect
fail: could not establish `x < x`
```
