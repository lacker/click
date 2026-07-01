# pure theorem predicate unfolding

This checks that pure theorem proof scripts can unfold predicate assumptions and
then simplify the theorem goal.

```click
predicate nonnegative(int32 x) {
    x >= 0
}

theorem nonnegative_means_ge_zero(x: int32) {
    requires nonnegative(x);

    ensures x >= 0 by {
        unfold(nonnegative);
        simp();
    }
}
```

```expect
pass
```
