# mathematical Integer false theorem

This checks that a false mathematical Integer claim remains unproved.

```click
theorem integer_false(x: Integer) {
    ensures x < x by {
        simp();
    }
}
```

```expect
fail: Integer less-than is true
```
