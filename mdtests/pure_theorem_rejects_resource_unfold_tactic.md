# pure theorem rejects resource unfold tactic

This checks that theorem proof scripts cannot manipulate the resource context.

```click
resource token(x: int32);

theorem resource_unfold_tactic_is_not_pure(x: int32) {
    ensures x == x by {
        unfold(token(x));
        simp();
    }
}
```

```expect
fail: tactic `unfold` is not available in the pure proof for theorem `resource_unfold_tactic_is_not_pure`
```
