# Distinct model getter values are compatible without a model alias

Without `a == b`, one model can be active and the other done. The unrelated
conclusion must not follow from their different getter values.

```click quick-solve
spec enum Walk { Active, Done }
function pending(w: Walk) -> int32 { match w { Walk::Active => 1, Walk::Done => 0, } }
theorem conflicting_aliases(a: Walk, b: Walk, flag: int32) {
    requires pending(a) == 1;
    requires pending(b) == 0;
    ensures flag == 42 by { close(); }
}
```

```expect
fail: could not establish `flag == 42`
```
