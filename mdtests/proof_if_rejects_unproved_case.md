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
fail: kernel goal: int32 =(v0, 0) is true
  recent premises (showing 1 of 1):
    int32 =(v0, 0) is false
```
