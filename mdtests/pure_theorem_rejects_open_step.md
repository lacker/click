# pure theorem rejects resource open step

This checks that theorem proof scripts cannot manipulate the resource context.

```click
affine resource token(x: int32);

theorem open_step_is_not_pure(x: int32) {
    ensures x == x by {
        open(token(x));
        simp();
    }
}
```

```expect
fail: proof step `open` cannot prove pure theorem `open_step_is_not_pure`
```
