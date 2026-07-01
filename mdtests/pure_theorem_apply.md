# pure theorem application

This checks that a pure theorem proof can apply an earlier theorem declaration.

```click
predicate nonnegative(int32 x) {
    x >= 0
}

theorem nonnegative_body(x: int32) {
    requires nonnegative(x);

    ensures x >= 0 by {
        unfold(nonnegative);
        simp();
    }
}

theorem reuses_nonnegative_body(y: int32) {
    requires nonnegative(y);

    ensures y >= 0 by {
        apply(nonnegative_body(y));
        simp();
    }
}
```

```expect
pass
```
