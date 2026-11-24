# Model getter conflicts reach the shared inconsistency checker

Equality closure connects `pending(a)` and `pending(b)` through `a == b`.
The conflicting checked values make the premises impossible, so any conclusion
follows without restating the getter equality.

```click quick-solve
spec enum Walk { Active, Done }
function pending(w: Walk) -> int32 { match w { Walk::Active => 1, Walk::Done => 0, } }
theorem conflicting_aliases(a: Walk, b: Walk, flag: int32) {
    requires a == b;
    requires pending(a) == 1;
    requires pending(b) == 0;
    ensures flag == 42 by { close(); }
}
```

```expect
pass
```
