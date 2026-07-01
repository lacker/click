# pure theorem rejects resource close step

This checks that theorem proof scripts cannot manipulate the resource context.

```click
affine resource token(x: int32);

theorem close_step_is_not_pure(x: int32) {
    ensures x == x by {
        close(token(x));
        simp();
    }
}
```

```expect
fail: proof step `close` cannot prove pure theorem `close_step_is_not_pure`
```
