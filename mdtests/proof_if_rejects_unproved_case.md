# proof if rejects unproved case

This checks that proof-level `if` requires both cases to prove the current
claim. The true case proves `x == 0`, but the false case cannot.

```click
theorem not_always_zero(x: int32) {
    ensures x == 0 by {
        if x == 0 {
            close();
        } else {
            close();
        }
    }
}
```

```expect
fail: could not establish `x == 0`
  stage: proof step
  location: tactic 0 > else arm tactic 1
  goal: x == 0
  recent premises (showing 1 of 1):
    x != 0
```
