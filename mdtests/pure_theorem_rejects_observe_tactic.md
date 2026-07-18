# pure theorem rejects resource observe tactic

This checks that theorem proof scripts cannot inspect the resource context.

```click
resource token(x: int32);

theorem observe_tactic_is_not_pure(x: int32) {
    ensures x == x by {
        observe(token(x));
        simp();
    }
}
```

```expect
fail: tactic `observe` is not available in the pure proof for theorem `observe_tactic_is_not_pure`
```
