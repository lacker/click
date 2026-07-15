# pure theorem rejects resource fold step

This checks that theorem proof scripts cannot manipulate the resource context.

```click
resource token(x: int32);

theorem fold_step_is_not_pure(x: int32) {
    ensures x == x by {
        fold(token(x));
        simp();
    }
}
```

```expect
fail: proof step `fold` is not available in the pure proof for theorem `fold_step_is_not_pure`
```
