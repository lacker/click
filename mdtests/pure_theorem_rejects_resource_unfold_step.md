# pure theorem rejects resource unfold step

This checks that theorem proof scripts cannot manipulate the resource context.

```click
resource token(x: int32);

theorem resource_unfold_step_is_not_pure(x: int32) {
    ensures x == x by {
        unfold(token(x));
        simp();
    }
}
```

```expect
fail: proof step `unfold` is not available in the pure proof for theorem `resource_unfold_step_is_not_pure`
```
