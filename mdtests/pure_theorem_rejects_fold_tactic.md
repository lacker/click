# pure theorem rejects resource fold tactic

This checks that theorem proof scripts cannot manipulate the resource context.

```click
abstract resource token(x: int32);

theorem fold_tactic_is_not_pure(x: int32) {
    ensures x == x by {
        fold(token(x));
        simp();
    }
}
```

```expect
fail: tactic `fold` is not available in the pure proof for theorem `fold_tactic_is_not_pure`
```
