# proof if rejects unproved case

This checks that proof-level `if` requires both cases to prove the current
claim. The true case proves `x == 0`, but the false case cannot.

```click
theorem not_always_zero(x: int32) {
    ensures x == 0 by {
        if x == 0 {
            simp();
        } else {
            simp();
        }
    }
}
```

```expect
fail: `simp` failed for `not_always_zero.ensures_0`: simplified proposition was not true: int32 equality is true
  available pure facts: [not (int32 equality is true)]
```
